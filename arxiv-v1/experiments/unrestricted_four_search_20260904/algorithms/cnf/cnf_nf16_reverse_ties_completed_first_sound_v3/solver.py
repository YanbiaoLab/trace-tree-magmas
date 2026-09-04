#!/usr/bin/env python3
# Strict independent ablation executable: cnf_only.
# Post-competition CNF baseline: one independent 120-second search budget.
from __future__ import annotations
import gc
import hashlib
import itertools
import json
import re
import sys
import threading
import time
from dataclasses import dataclass
from itertools import combinations, permutations
from typing import Hashable, Iterable, Iterator, Sequence

SEARCH_BUDGET_SECONDS = 120.0
PROTOCOL_MIN_LIFETIME_SECONDS = 1.5

def release_unused_memory():
    """Return unreachable objects/pages between independent search stages."""
    gc.collect()
    if not sys.platform.startswith("linux"):
        return
    try:
        import ctypes
        trim = ctypes.CDLL(None).malloc_trim
        trim.argtypes = (ctypes.c_size_t,)
        trim.restype = ctypes.c_int
        trim(0)
    except (AttributeError, ImportError, OSError):
        pass

def strip_outer(s):
    while s.startswith("(") and s.endswith(")"):
        d = 0
        for i, c in enumerate(s):
            d += c == "("
            d -= c == ")"
            if d == 0 and i + 1 < len(s):
                return s
        s = s[1:-1]
    return s

def parse_side(s):
    
    
    
    
    s = strip_outer(re.sub(r"[^a-z()]+", "*", s.lower()).strip("*"))
    d = 0
    cut = -1
    for i, c in enumerate(s):
        d += c == "("
        d -= c == ")"
        if c == "*" and d == 0:
            cut = i
    if cut >= 0:
        return (parse_side(s[:cut]), parse_side(s[cut + 1:]))
    if len(s) == 1 and "a" <= s <= "z":
        return s
    raise ValueError("bad term")

def parse_eq(s):
    a, b = s.split("=")
    return parse_side(a), parse_side(b)

def variables(t, out=None):
    out = [] if out is None else out
    if isinstance(t, str):
        if t not in out:
            out.append(t)
    else:
        variables(t[0], out)
        variables(t[1], out)
    return out

def rename_term(t, env):
    if isinstance(t, str):
        return env.get(t, t)
    return (rename_term(t[0], env), rename_term(t[1], env))

FALSE_CERTIFICATE_LIMIT = 1_024_000

BANNED_CERTIFICATE_TOKENS = (
    "sorry", "admit", "sorryAx", "mkSorry", "axiom", "opaque",
    "dbg_trace", "dbgTrace", "run_tac", "initialize", "builtin_initialize",
    "elab", "elab_rules", "macro", "macro_rules", "syntax", "notation",
    "infix", "prefix", "postfix",
    "unsafe", "implemented_by", "extern", "unsafeCast", "unsafeIO",
    "unsafePerformIO",
)

BANNED_CERTIFICATE_COMMANDS = (
    "#eval", "#exit", "#reduce", "#synth", "#check_eval",
)

def strict_certificate_gate(code):
    """Accept only a complete, policy-compatible false certificate.

    This gate is intentionally independent of every model family.  In
    particular it runs *after* source specialization or opposite-operation
    transport, because those semantics-preserving text transformations may
    change the final UTF-8 byte count or fail after a compiler template evolves.
    Rejection is fail-closed: the portfolio may continue to a later certified
    model, but an incomplete candidate is never sent to Judge.
    """
    if not isinstance(code, str) or not code or "\x00" in code:
        return None
    if len(code.encode("utf-8")) > FALSE_CERTIFICATE_LIMIT:
        return None
    if "import JudgeProblem" not in code or "def submission" not in code:
        return None
    if any(re.search(rf"\b{re.escape(token)}\b", code)
           for token in BANNED_CERTIFICATE_TOKENS):
        return None
    if any(token in code for token in BANNED_CERTIFICATE_COMMANDS):
        return None
    return code

CNF_E =("E",)

CNF_COMPLETION_RULE_CAP = 16
CNF_COMPLETION_ROUND_CAP = 16
CNF_COMPLETION_OVERLAP_CAP = 250_000
CNF_SOURCE_TABLEAU_CAP = 250_000

DEBUG =False

def cnf_is_var (t ):
    return isinstance (t ,str )

def cnf_is_e (t ):
    return t ==CNF_E

def cnf_is_pair (t ):
    return (isinstance (t ,tuple )and len (t )==2 and t !=CNF_E and 
    t [0 ]!="K")

def cnf_strip_outer (s ):
    while s .startswith ("(")and s .endswith (")"):
        depth =0 
        for i ,c in enumerate (s ):
            depth +=c =="("
            depth -=c ==")"
            if depth ==0 and i +1 <len (s ):
                return s 
        s =s [1 :-1 ]
    return s

def cnf_parse_side (s ):
    s =cnf_strip_outer (re .sub (r"[^a-z()]+","*",s .lower ()).strip ("*"))
    depth =0 
    cut =-1 
    for i ,c in enumerate (s ):
        depth +=c =="("
        depth -=c ==")"
        if c =="*"and depth ==0 :
            cut =i 
    if cut >=0 :
        return cnf_parse_side (s [:cut ]),cnf_parse_side (s [cut +1 :])
    if len (s )==1 and "a"<=s <="z":
        return s 
    raise ValueError ("bad term")

def cnf_parse_eq (s ):
    a ,b =s .split ("=")
    return cnf_parse_side (a ),cnf_parse_side (b )

def cnf_vars_of (t ,out =None ):
    out =[]if out is None else out 
    if cnf_is_var (t ):
        if t not in out :
            out .append (t )
    elif cnf_is_pair (t ):
        cnf_vars_of (t [0 ],out )
        cnf_vars_of (t [1 ],out )
    return out

def cnf_rename (t ,env ):
    if cnf_is_var (t ):
        return env .get (t ,t )
    if cnf_is_pair (t ):
        return cnf_rename (t [0 ],env ),cnf_rename (t [1 ],env )
    return t

def cnf_subst (t ,env ,seen =None ):
    if cnf_is_var (t ):
        seen =set ()if seen is None else seen 
        if t in env and t not in seen :
            return cnf_subst (env [t ],env ,seen |{t })
        return t 
    if cnf_is_pair (t ):
        return cnf_subst (t [0 ],env ,seen ),cnf_subst (t [1 ],env ,seen )
    return t

def cnf_occurs (v ,t ,env ):
    t =cnf_subst (t ,env )
    return t ==v if cnf_is_var (t )else (
    cnf_is_pair (t )and (cnf_occurs (v ,t [0 ],env )or cnf_occurs (v ,t [1 ],env )))

def cnf_unify (a ,b ,base =None ):
    env ={}if base is None else dict (base )
    todo =[(a ,b )]
    while todo :
        a ,b =cnf_subst (todo .pop (),env )
        if a ==b :
            continue 
        if cnf_is_var (a ):
            if cnf_occurs (a ,b ,env ):
                return None 
            env [a ]=b 
        elif cnf_is_var (b ):
            if cnf_occurs (b ,a ,env ):
                return None 
            env [b ]=a 
        elif cnf_is_pair (a )and cnf_is_pair (b ):
            todo .extend (((a [0 ],b [0 ]),(a [1 ],b [1 ])))
        else :
            return None 
    return env

def cnf_rigid_match (pattern ,actual ,env =None ):
    env ={}if env is None else env 
    if cnf_is_var (pattern ):
        if pattern in env :
            return env if env [pattern ]==actual else None 
        env [pattern ]=actual 
        return env 
    if cnf_is_e (pattern ):
        return env if cnf_is_e (actual )else None 
    if not cnf_is_pair (actual ):
        return None 
    env =cnf_rigid_match (pattern [0 ],actual [0 ],env )
    return None if env is None else cnf_rigid_match (pattern [1 ],actual [1 ],env )

def cnf_walk (t ,path =()):
    yield path ,t 
    if cnf_is_pair (t ):
        yield from cnf_walk (t [0 ],path +(0 ,))
        yield from cnf_walk (t [1 ],path +(1 ,))

def cnf_put (t ,path ,value ):
    if not path :
        return value 
    child =cnf_put (t [path [0 ]],path [1 :],value )
    return (child ,t [1 ])if path [0 ]==0 else (t [0 ],child )

def cnf_tsize (t ):
    return 0 if not cnf_is_pair (t )else 1 +cnf_tsize (t [0 ])+cnf_tsize (t [1 ])

def cnf_orient (a ,b ):
    if a ==b :
        return None 
    va ,vb =set (cnf_vars_of (a )),set (cnf_vars_of (b ))
    sa ,sb =cnf_tsize (a ),cnf_tsize (b )
    a_gt_b =sa >sb or (sa ==sb and repr (a )<repr (b ))
    b_gt_a =sb >sa or (sa ==sb and repr (b )<repr (a ))
    # `Code a b o` defines only the result of a binary operation.  A variable
    # or constant cannot be a sound rewrite-rule left-hand side here.
    if vb <=va and a_gt_b and cnf_is_pair (a ):
        return a ,b 
    if va <=vb and b_gt_a and cnf_is_pair (b ):
        return b ,a 
    return None

def cnf_canon_rule (rule ):
    env ={}
    def go (t ):
        if cnf_is_var (t ):
            if t not in env :
                env [t ]=f"v{len (env )}"
            return env [t ]
        if cnf_is_pair (t ):
            return go (t [0 ]),go (t [1 ])
        return t 
    return go (rule [0 ]),go (rule [1 ])

def cnf_tagged (t ,prefix ):
    if cnf_is_var (t ):
        return prefix +t 
    if cnf_is_pair (t ):
        return cnf_tagged (t [0 ],prefix ),cnf_tagged (t [1 ],prefix )
    return t

def cnf_root_reduce (t ,rules ):
    for left ,right in rules :
        env =cnf_rigid_match (left ,t )
        if env is not None :
            return cnf_subst (right ,env )
    return t

def cnf_normal (t ,rules ,fuel =64 ):
    if cnf_is_pair (t ):
        t =cnf_normal (t [0 ],rules ,fuel ),cnf_normal (t [1 ],rules ,fuel )
        for _ in range (fuel ):
            q =cnf_root_reduce (t ,rules )
            if q ==t :
                return t 
            t =cnf_normal (q ,rules ,fuel -1 )
    return t

def cnf_critical_complete (seed ,cap =CNF_COMPLETION_ROUND_CAP ,
                           rule_cap =CNF_COMPLETION_RULE_CAP ,
                           overlap_cap =CNF_COMPLETION_OVERLAP_CAP ,
                           deadline =None ):
    rules =[]
    for rule in seed :
        rule =cnf_canon_rule (rule )
        if not cnf_is_pair (rule [0 ]):
            return None
        if rule not in rules :
            rules .append (rule )
    if not rules or len (rules )>rule_cap :
        return None
    overlaps =0
    for round_no in range (cap ):
        if deadline is not None and time .monotonic ()>=deadline :
            return None 
        additions =[]
        snapshot =list (rules )
        for i ,(left ,right )in enumerate (snapshot ):
            a ,b =cnf_tagged (left ,f"a{i }_{round_no }_"),cnf_tagged (right ,f"a{i }_{round_no }_")
            for j ,(other ,out )in enumerate (snapshot ):
                c ,d =cnf_tagged (other ,f"b{j }_{round_no }_"),cnf_tagged (out ,f"b{j }_{round_no }_")
                for path ,node in cnf_walk (a ):
                    overlaps +=1
                    if overlaps >overlap_cap :
                        return None
                    if deadline is not None and time .monotonic ()>=deadline :
                        return None 
                    if cnf_is_var (node )or cnf_is_e (node ):
                        continue 
                    env =cnf_unify (node ,c )
                    if env is None :
                        continue 
                    x =cnf_normal (cnf_subst (b ,env ),snapshot )
                    y =cnf_normal (cnf_subst (cnf_put (a ,path ,d ),env ),snapshot )
                    rule =cnf_orient (x ,y )
                    if rule is None :
                        continue 
                    rule =cnf_canon_rule (rule )
                    if rule not in rules and rule not in additions :
                        additions .append (rule )
        if not additions :
            break 
        rules .extend (sorted (additions ,key =lambda r :(cnf_tsize (r [0 ]),repr (r ))))
        if len (rules )>rule_cap :
            return None 
    return rules

def cnf_replace_all (t ,old ,new ):
    if t ==old :
        return new 
    if cnf_is_pair (t ):
        return cnf_replace_all (t [0 ],old ,new ),cnf_replace_all (t [1 ],old ,new )
    return t

def cnf_diagonal_simplify (t ):
    if not cnf_is_pair (t ):
        return t 
    a ,b =cnf_diagonal_simplify (t [0 ]),cnf_diagonal_simplify (t [1 ])
    return CNF_E if a ==b else (a ,b )

def cnf_candidate_seeds (source ):
    left ,right =source 
    seeds =[]
    has_diagonal =any (cnf_is_pair (t )and t [0 ]==t [1 ]
    for side in source for _p ,t in cnf_walk (side ))
    if has_diagonal :
        a ,b =cnf_diagonal_simplify (left ),cnf_diagonal_simplify (right )
        main =cnf_orient (a ,b )
        if main :
            seeds .append ([main ,(("d","d"),CNF_E )])
    compounds_left ={t for _p ,t in cnf_walk (left )if cnf_is_pair (t )}
    compounds_right ={t for _p ,t in cnf_walk (right )if cnf_is_pair (t )}
    common =sorted (compounds_left &compounds_right ,
    key =lambda t :(-cnf_tsize (t ),repr (t )))
    for n ,shared in enumerate (common [:4 ]):
        fresh =f"u{n }"
        main =cnf_orient (cnf_replace_all (left ,shared ,fresh ),
        cnf_replace_all (right ,shared ,fresh ))
        if main :
            seeds .append ([main ])
        outside =set (cnf_vars_of (cnf_replace_all (left ,shared ,CNF_E )))|set (
        cnf_vars_of (cnf_replace_all (right ,shared ,CNF_E )))
        boundary =[v for v in cnf_vars_of (shared )if v in outside ]
        if boundary :
            generalized =cnf_rename (
            shared ,{v :f"g{n }_{i }"for i ,v in enumerate (boundary )})
            main =cnf_orient (cnf_replace_all (left ,shared ,generalized ),
            cnf_replace_all (right ,shared ,generalized ))
            if main :
                seeds .append ([main ])
    main =cnf_orient (left ,right )
    if main :
        seeds .append ([main ])
    out ,seen =[],set ()
    for seed in seeds :
        key =tuple (cnf_canon_rule (r )for r in seed )
        if key not in seen :
            seen .add (key )
            out .append (seed )
    return out

def cnf_source_tableau (source ,rules ,cap =CNF_SOURCE_TABLEAU_CAP ,deadline =None ):
    if any (not cnf_is_pair (left )for left ,_right in rules ):
        return False ,0
    nodes ,cache =[],{}
    def build (t ):
        if not cnf_is_pair (t ):
            return t 
        if t in cache :
            return cache [t ]
        a ,b =build (t [0 ]),build (t [1 ])
        result =f"T{len (nodes )}"
        nodes .append ((a ,b ,result ))
        cache [t ]=result 
        return result 
    roots =build (source [0 ]),build (source [1 ])
    known_nf =tuple (cnf_vars_of (source [0 ])+[v for v in cnf_vars_of (source [1 ])
    if v not in cnf_vars_of (source [0 ])])+tuple (
    n [2 ]for n in nodes )
    calls =0 

    def redex (t ):
        if any (cnf_rigid_match (left ,t )is not None for left ,_right in rules ):
            return True 
        return cnf_is_pair (t )and (redex (t [0 ])or redex (t [1 ]))

    def visit (depth ,equations ,misses ):
        nonlocal calls 
        calls +=1 
        if calls >cap or (deadline is not None and calls &1023 ==0 and 
        time .monotonic ()>=deadline ):
            return False 
        env ={}
        for a ,b in equations :
            env =cnf_unify (a ,b ,env )
            if env is None :
                return True 
        norm =lambda t :cnf_subst (t ,env )
        if norm (roots [0 ])==norm (roots [1 ]):
            return True 
        for a ,b in misses :
            pair =norm (a ),norm (b )
            if any (cnf_rigid_match (left ,pair )is not None for left ,_ in rules ):
                return True 
        if any (redex (norm (t ))for t in known_nf ):
            return True 
        if depth ==len (nodes ):
            return False 
        a ,b ,result =nodes [depth ]
        for i ,(left ,right )in enumerate (rules ):
            pre =f"B{depth }_{i }_"
            ll ,rr =cnf_tagged (left ,pre ),cnf_tagged (right ,pre )
            if not visit (depth +1 ,equations +((a ,ll [0 ]),(b ,ll [1 ]),
            (result ,rr )),misses ):
                return False 
        return visit (depth +1 ,equations +((result ,(a ,b )),),
        misses +((a ,b ),))
    return visit (0 ,(),()),calls

def cnf_rhs_nf_safe (left ,right ):
    if cnf_is_e (right ):
        return True 
    return any (node ==right for side in left for _p ,node in cnf_walk (side ))

def cnf_closed_match (pattern ,value ,env =None ):
    return cnf_rigid_match (pattern ,value ,env )

def cnf_closed_subst (t ,env ):
    if cnf_is_var (t ):
        return env [t ]
    if cnf_is_pair (t ):
        return cnf_closed_subst (t [0 ],env ),cnf_closed_subst (t [1 ],env )
    return t

def cnf_is_nf (value ,rules ):
    return (not cnf_is_pair (value )or 
    (cnf_is_nf (value [0 ],rules )and cnf_is_nf (value [1 ],rules )and 
    not any (cnf_closed_match (left ,value )is not None 
    for left ,_ in rules )))

def cnf_closed_op (a ,b ,rules ):
    hits =[]
    for left ,right in rules :
        env =cnf_closed_match (left ,(a ,b ))
        if env is not None :
            hits .append (cnf_closed_subst (right ,env ))
    if not hits :
        return (a ,b ),None 
    if any (value !=hits [0 ]for value in hits ):
        raise ValueError ("nonfunctional on normal forms")
    return hits [0 ],hits [0 ]

def cnf_closed_eval (term ,env ,rules ,steps ):
    if cnf_is_var (term ):
        return env [term ]
    a =cnf_closed_eval (term [0 ],env ,rules ,steps )
    b =cnf_closed_eval (term [1 ],env ,rules ,steps )
    out ,hit =cnf_closed_op (a ,b ,rules )
    steps .append ((a ,b ,out ,hit ))
    return out

def cnf_target_witness (target ,rules ,deadline =None ):
    if any (not cnf_is_pair (left )for left ,_right in rules ):
        return None
    values =[CNF_E ]
    for _ in range (3 ):
        values .append (("K",values [-1 ]))
    seen =set (values )
    for _round in range (3 ):
        old =list (values )
        for a ,b in itertools .product (old ,repeat =2 ):
            value =(a ,b )
            if value not in seen and cnf_is_nf (value ,rules ):
                seen .add (value );values .append (value )
                if len (values )>=48 :
                    break 
        if len (values )>=48 :
            break 
        for value in old :
            lifted =("K",value )
            if lifted not in seen :
                seen .add (lifted );values .append (lifted )
                if len (values )>=48 :
                    break 
    tv =cnf_vars_of (target [0 ])
    cnf_vars_of (target [1 ],tv )
    for witness_index ,vals in enumerate (
    itertools .product (values ,repeat =len (tv ))):
        if (deadline is not None and witness_index &255 ==0 and 
        time .monotonic ()>=deadline ):
            return None 
        env =dict (zip (tv ,vals ))
        steps =[]
        try :
            left =cnf_closed_eval (target [0 ],env ,rules ,steps )
            right =cnf_closed_eval (target [1 ],env ,rules ,steps )
        except ValueError :
            continue 
        if left !=right :
            return vals ,left ,right ,steps 
    return None

def cnf_lean_term (t ):
    if cnf_is_var (t ):
        return t 
    if cnf_is_e (t ):
        return "e"
    if isinstance (t ,tuple )and len (t )==2 and t [0 ]=="K":
        return f"(k {cnf_lean_term (t [1 ])})"
    return f"(p {cnf_lean_term (t [0 ])} {cnf_lean_term (t [1 ])})"

def cnf_op_term (t ,vals =None ):
    if cnf_is_var (t ):
        return (vals or {}).get (t ,t )
    return f"(op {cnf_op_term (t [0 ],vals )} {cnf_op_term (t [1 ],vals )})"

def cnf_eval_term (t ,vals =None ):
    if cnf_is_var (t ):
        return (vals or {}).get (t ,t )
    return f"(eval {cnf_eval_term (t [0 ],vals )} {cnf_eval_term (t [1 ],vals )})"

def cnf_internal_terms (equation ):
    out ,seen =[],set ()
    def go (t ):
        if not cnf_is_pair (t ):
            return 
        go (t [0 ]);go (t [1 ])
        if t not in seen :
            seen .add (t );out .append (t )
    go (equation [0 ]);go (equation [1 ])
    return out

def cnf_constructor (rule ,index ):
    left ,right =rule 
    vs =cnf_vars_of (left )
    cnf_vars_of (right ,vs )
    binders =f" ({' '.join (vs )} : CM)"if vs else ""
    return (f"  | r{index }{binders } : Code {cnf_lean_term (left [0 ])} "
    f"{cnf_lean_term (left [1 ])} {cnf_lean_term (right )}")

def cnf_nf_projection (term ,needle ,proof ):
    """Project NF of a syntactic subterm without recursive simp unfolding."""
    if term ==needle :
        return proof 
    if not cnf_is_pair (term ):
        return None 
    left =cnf_nf_projection (term [0 ],needle ,proof +".1")
    return left or cnf_nf_projection (term [1 ],needle ,proof +".2.1")

def cnf_closed_code (rule ,index ,a ,b ):
    env =cnf_closed_match (rule [0 ],(a ,b ))
    if env is None :
        return None 
    args =" ".join (cnf_lean_term (env [v ])for v in cnf_vars_of (rule [0 ]))
    return f"Code.r{index }"+(f" {args }"if args else "")

def cnf_clash_proof (a ,b ):
    path =[]
    while True :
        ka ="e"if cnf_is_e (a )else "k"if a [0 ]=="K"else "p"
        kb ="e"if cnf_is_e (b )else "k"if b [0 ]=="K"else "p"
        if ka !=kb :
            bits ={"e":"false","k":"false","p":"false"}
            bits [ka ],bits [kb ]="false","true"
            q ="q"
            for bit in path :
                q =f"({'U'if bit ==2 else 'L'if bit ==0 else 'R'} {q })"
            f =(f"(fun q => match {q } with | e => {bits ['e']} | k _ => "
            f"{bits ['k']} | p _ _ => {bits ['p']})")
            return f"Bool.noConfusion (congrArg {f } bad)"
        if ka =="k":
            a ,b =a [1 ],b [1 ];path .append (2 )
        elif ka =="p":
            if a [0 ]!=b [0 ]:
                a ,b =a [0 ],b [0 ];path .append (0 )
            else :
                a ,b =a [1 ],b [1 ];path .append (1 )
        else :
            raise ValueError ("equal terms")

CNF_CORE =r'''import JudgeProblem
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace submission
inductive CM where | e : CM | k : CM → CM | p : CM → CM → CM
namespace CM
def L : CM → CM | .p a _ => a | _ => .e
def R : CM → CM | .p _ b => b | _ => .e
def U : CM → CM | .k a => a | _ => .e
def sz : CM → Nat | .e => 0 | .k a => sz a + 1 | .p a b => sz a + sz b + 2
'''

def cnf_compile_lean (source ,target ,rules ,witness ,deadline =None ):
    if any (not cnf_is_pair (left )for left ,_right in rules ):
        raise ValueError ("non-pair rewrite lhs is outside the CNF model language")
    vals ,nl ,nr ,raw_steps =witness 
    value_steps =[]
    def collect_value (t ):
        if cnf_is_e (t ):
            return 
        if isinstance (t ,tuple )and len (t )==2 and t [0 ]=="K":
            collect_value (t [1 ]);return 
        collect_value (t [0 ]);collect_value (t [1 ])
        if any (cnf_closed_match (left ,t )is not None for left ,_right in rules ):
            raise ValueError ("non-normal target assignment")
        value_steps .append ((t [0 ],t [1 ],t ,None ))
    for value in vals :
        collect_value (value )
    raw_steps =value_steps +raw_steps 
    sv =cnf_vars_of (source [0 ]);cnf_vars_of (source [1 ],sv )
    tv =cnf_vars_of (target [0 ]);cnf_vars_of (target [1 ],tv )
    ctors ="\n".join (cnf_constructor (rule ,i )for i ,rule in enumerate (rules ))
    nodes =cnf_internal_terms (source )
    node_index ={term :i for i ,term in enumerate (nodes )}
    def nf_name (term ):
        return "h"+term if cnf_is_var (term )else f"N{node_index [term ]}"
    def dag_term (t ):
        return t if not cnf_is_pair (t )else f"T{node_index [t ]}"

        # Compile the already exhaustive Python tableau into a layered Lean case
        # analysis.  This proof-backend optimization neither adds nor removes
        # rewrite systems from the mathematical search language.
    abstract_nodes =[(dag_term (t [0 ]),dag_term (t [1 ]),f"T{i }")
    for i ,t in enumerate (nodes )]
    roots =dag_term (source [0 ]),dag_term (source [1 ])
    known_nf =[(v ,"h"+v )for v in sv ]
    known_nf +=[(f"T{i }",f"N{i }")for i in range (len (nodes ))]
    # Keep the three independent contradiction theories out of each other's
    # E-matching space.  In particular, loading Code constructors and redex
    # lemmas together makes `grind` form an irrelevant Cartesian product on
    # larger source terms.  The symbolic tableau is unchanged: these are only
    # three complete ways in which a tableau leaf was classified as closed.
    structural_context =", ".join (
    ["nf_p_left","nf_p_right","nf_p_no","sz"])
    code_context =", ".join (
    [f"Code.r{i }"for i in range (len (rules ))]+["sz"])
    redex_context =", ".join (
    ["nf_p_left","nf_p_right","nf_p_no"]+
    [f"redex{i }_not_nf"for i in range (len (rules ))]+["sz"])
    leaf_tactic =(
    "first | omega | contradiction | "
    "grind (config := { splits := 1, gen := 6 }) ["+
    structural_context +"] | "
    "grind (config := { splits := 1, gen := 6 }) ["+
    code_context +"] | "
    "grind (config := { splits := 1, gen := 6 }) ["+
    redex_context +"]")

    def leaf_redex (t ):
        if not cnf_is_pair (t ):
            return None 
        for ri ,(left ,_right )in enumerate (rules ):
            bindings =cnf_rigid_match (left ,t )
            if bindings is not None :
                return (),ri ,bindings 
        got =leaf_redex (t [0 ])
        if got is not None :
            path ,ri ,bindings =got 
            return (0 ,)+path ,ri ,bindings 
        got =leaf_redex (t [1 ])
        if got is not None :
            path ,ri ,bindings =got 
            return (1 ,)+path ,ri ,bindings 
        return None 

    def classify_leaf (equations ,misses ):
        env ={}
        for a ,b in equations :
            env =cnf_unify (a ,b ,env )
            if env is None :
                return "skip"
        norm =lambda t :cnf_subst (t ,env )
        if norm (roots [0 ])==norm (roots [1 ]):
            return "skip"
        for a ,b ,_no_name in misses :
            pair =norm (a ),norm (b )
            for _ri ,(left ,_right )in enumerate (rules ):
                bindings =cnf_rigid_match (left ,pair )
                if bindings is None :
                    continue 
                return "skip"
        for term ,_proof in known_nf :
            got =leaf_redex (norm (term ))
            if got is None :
                continue 
            return "skip"
        return None 

    def branch_state (index ,ri ,equations ,misses ):
        a ,b ,out =abstract_nodes [index ]
        if ri ==len (rules ):
            return (equations +((out ,(a ,b )),),
            misses +((a ,b ,f"n{index }"),))
        left ,right =rules [ri ]
        ren ={v :f"v{index }_{ri }_{j }"
        for j ,v in enumerate (cnf_vars_of (left ))}
        return (equations +((a ,cnf_rename (left [0 ],ren )),
        (b ,cnf_rename (left [1 ],ren )),
        (out ,cnf_rename (right ,ren ))),misses )

    def split_call (index ):
        patterns =[]
        for ri ,(left ,_right )in enumerate (rules ):
            names =[f"v{index }_{ri }_{j }"
            for j ,_v in enumerate (cnf_vars_of (left ))]
            names .append (f"hc{index }_{ri }")
            patterns .append ("⟨"+", ".join (names )+"⟩")
        patterns .append (f"⟨hr{index }, n{index }⟩")
        return f"rcases B{index } with "+" | ".join (patterns )

        # Choose one global split order by minimizing the symbolic open frontier.
        # After each split Lean closes exactly the leaves that the tableau already
        # classified, avoiding both repeated leaf scripts and a full Cartesian
        # product before simplification.
    frontier =[((),())]
    remaining =list (range (len (nodes )))
    split_order =[]
    while remaining :
        if deadline is not None and time .monotonic ()>=deadline :
            raise TimeoutError ("source proof scheduling deadline")
        choices =[]
        for index in remaining :
            next_frontier =[]
            for equations ,misses in frontier :
                for ri in range (len (rules )+1 ):
                    eqs ,mis =branch_state (index ,ri ,equations ,misses )
                    if classify_leaf (eqs ,mis )is None :
                        next_frontier .append ((eqs ,mis ))
                        if len (next_frontier )>200000 :
                            raise ValueError ("source proof frontier too large")
            choices .append ((len (next_frontier ),-index ,index ,next_frontier ))
        _count ,_tie ,index ,frontier =min (choices ,key =lambda item :item [:2 ])
        split_order .append (index )
        remaining .remove (index )
    schedule =[]
    for index in split_order :
        schedule .append (f"  all_goals {split_call (index )}")
        schedule .append (f"  all_goals try ({leaf_tactic })")
    schedule .append (f"  all_goals {leaf_tactic }")
    source_script ="\n".join (schedule )
    generals =[]
    for i ,t in enumerate (nodes ):
        a ,b =dag_term (t [0 ]),dag_term (t [1 ])
        generals .append (f"  generalize H{i } : eval {a } {b } = T{i }")
    bcases ="\n".join (generals +[
    f"  change {roots [0 ]} = {roots [1 ]}",
    ]+[
    f"  have B{i } : EvalCases {dag_term (t [0 ])} {dag_term (t [1 ])} T{i } := by\n"
    f"    rw [← H{i }]\n"
    f"    exact eval_cases {dag_term (t [0 ])} {dag_term (t [1 ])}"
    for i ,t in enumerate (nodes )])
    nfacts ="\n".join (
    f"  have N{i } : NF T{i } := by\n"
    f"    rw [← H{i }]\n"
    f"    exact eval_nf {nf_name (t [0 ])} {nf_name (t [1 ])}"
    for i ,t in enumerate (nodes ))

    code_clauses ,code_case_arms =[],[]
    for i ,(left ,right )in enumerate (rules ):
        vs =cnf_vars_of (left );cnf_vars_of (right ,vs )
        binders =f"∃ {' '.join (vs )} : CM, "if vs else ""
        code_clauses .append (
        f"({binders }a = {cnf_lean_term (left [0 ])} ∧ "
        f"b = {cnf_lean_term (left [1 ])} ∧ o = {cnf_lean_term (right )} ∧ "
        f"sz a = sz {cnf_lean_term (left [0 ])} ∧ "
        f"sz b = sz {cnf_lean_term (left [1 ])} ∧ "
        f"sz o = sz {cnf_lean_term (right )})")
        witness =("⟨"+(("_, "*len (vs ))if vs else "")+
        "rfl, rfl, rfl, rfl, rfl, rfl⟩")
        body ="Or.inr ("*i +"Or.inl "+witness +")"*i 
        code_case_arms .append (f"  | r{i } => exact {body }")
    code_cases_def =" ∨ ".join (code_clauses +["False"])

    nf_cases ,redex_lemmas =[],[]
    for i ,(left ,right )in enumerate (rules ):
        if cnf_is_e (right ):
            proof ="by trivial"
        else :
            projected =(cnf_nf_projection (left [0 ],right ,"ha")or 
            cnf_nf_projection (left [1 ],right ,"hb"))
            if projected is None :
                raise ValueError ("RHS is not an NF-safe input subterm")
            proof =projected 
        nf_cases .append (f"  | r{i } => exact {proof }")
        vs =cnf_vars_of (left );cnf_vars_of (right ,vs )
        args =" ".join (vs )
        binders =f" ({args } : CM)"if vs else ""
        call =f"Code.r{i }"+(f" {args }"if args else "")
        redex_lemmas .append (f'''theorem redex{i }_not_nf{binders } :
    ¬ NF (p {cnf_lean_term (left [0 ])} {cnf_lean_term (left [1 ])}) := by
  intro h
  exact h.2.2 ⟨{cnf_lean_term (right )}, {call }⟩
''')

    case_defs ,eval_ctors ,eval_unpack_arms =[],[],[]
    for i ,(left ,right )in enumerate (rules ):
        vs =cnf_vars_of (left );cnf_vars_of (right ,vs )
        args =f" ({' '.join (vs )} : CM)"if vs else ""
        call =(" "+" ".join (vs ))if vs else ""
        facts =(f"a = {cnf_lean_term (left [0 ])} ∧ b = {cnf_lean_term (left [1 ])} ∧ "
        f"o = {cnf_lean_term (right )} ∧ sz a = sz {cnf_lean_term (left [0 ])} ∧ "
        f"sz b = sz {cnf_lean_term (left [1 ])} ∧ "
        f"sz o = sz {cnf_lean_term (right )}")
        case_defs .append (
        f"@[grind unfold] abbrev C{i }{args } (a b o : CM) : Prop := {facts }")
        eval_ctors .append (f"  | r{i }{args } (h : C{i }{call } a b o) : EvalCases a b o")
        if vs :
            unpack ="⟨"+", ".join (vs +[f"hc{i }"])+"⟩"
            eval_unpack_arms .append (
            f"    · rcases cc{i } with {unpack }\n"
            f"      exact .r{i }{call } hc{i }")
        else :
            eval_unpack_arms .append (f"    · exact .r{i } cc{i }")
    eval_ctors .append (
    "  | raw (h : o = p a b ∧ sz o = sz a + sz b + 2) "
    "(n : ¬ ∃ q, Code a b q) : EvalCases a b o")
    eval_cases_block =f'''{chr (10 ).join (case_defs )}
inductive EvalCases (a b o : CM) : Prop
{chr (10 ).join (eval_ctors )}
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with {' | '.join ([f'cc{i }'for i in range (len (rules ))]+['impossible'])}
{chr (10 ).join (eval_unpack_arms )}
    · contradiction
  · exact .raw ⟨eval_raw h, eq_sz (eval_raw h)⟩ h
'''

    unique ,order ={},[]
    for a ,b ,out ,hit in raw_steps :
        key =a ,b 
        if key not in unique :
            unique [key ]=out ,hit 
            order .append (key )
    lemmas ,hist =[],[]
    for i ,(a ,b )in enumerate (order ):
        out ,hit =unique [(a ,b )]
        la ,lb ,lo =cnf_lean_term (a ),cnf_lean_term (b ),cnf_lean_term (out )
        if hit is None :
            lemmas .append (f'''theorem t{i } : ¬ ∃ o, Code {la } {lb } o := by
  rintro ⟨o, h⟩
  have c := code_cases h
  unfold CodeCases at c
  grind (config := {{ splits := 12, gen := 12 }}) [sz]
theorem e{i } : eval {la } {lb } = {lo } := eval_raw t{i }
''')
        else :
            choices =[(j ,cnf_closed_code (rule ,j ,a ,b ))
            for j ,rule in enumerate (rules )
            if cnf_closed_code (rule ,j ,a ,b )is not None ]
            ctor =choices [0 ][1 ]
            lemmas .append (f'''theorem e{i } : eval {la } {lb } = {lo } := by
  rw [eval, dif_pos ⟨{lo }, {ctor }⟩]
  have h := Classical.choose_spec
    (show ∃ q, Code {la } {lb } q from ⟨{lo }, {ctor }⟩)
  have c := code_cases h
  unfold CodeCases at c
  grind (config := {{ splits := 12, gen := 12 }}) [sz]
''')
        hist .append ((f"e{i }",f"(eval {la } {lb })",lo ))

    def reduce_proof (expr ):
        cur ,proofs =expr ,[]
        changed =True 
        while changed :
            changed =False 
            for name ,lhs ,rhs in hist :
                if lhs in cur :
                    context =cur .replace (lhs ,"q",1 )
                    cur =cur .replace (lhs ,rhs ,1 )
                    proofs .append (name if context =="q"else 
                    f"congrArg (fun q => {context }) {name }")
                    changed =True 
        proof ="rfl"
        for item in proofs :
            proof =item if proof =="rfl"else f"({proof }).trans ({item })"
        return cur ,proof 

    env =dict (zip (tv ,map (cnf_lean_term ,vals )))
    le ,lp =reduce_proof (cnf_eval_term (target [0 ],env ))
    re_ ,rp =reduce_proof (cnf_eval_term (target [1 ],env ))
    if le !=cnf_lean_term (nl )or re_ !=cnf_lean_term (nr ):
        raise ValueError ("target proof reduction mismatch")
    step_index ={pair :i for i ,pair in enumerate (order )}
    def nf_value (v ):
        if cnf_is_e (v ):
            return "by trivial"
        if isinstance (v ,tuple )and len (v )==2 and v [0 ]=="K":
            return nf_value (v [1 ])
        index =step_index [(v [0 ],v [1 ])]
        return f"⟨{nf_value (v [0 ])}, {nf_value (v [1 ])}, t{index }⟩"
    def carrier_value (v ):
        if cnf_is_e (v ):
            return "ce"
        if isinstance (v ,tuple )and len (v )==2 and v [0 ]=="K":
            return f"(ck {carrier_value (v [1 ])})"
        return f"⟨{cnf_lean_term (v )}, {nf_value (v )}⟩"
    apps =" ".join (carrier_value (v )for v in vals )
    return CNF_CORE +f'''inductive Code : CM → CM → CM → Prop
{ctors }
def CodeCases (a b o : CM) : Prop := {code_cases_def }
theorem code_cases {{a b o : CM}} (h : Code a b o) : CodeCases a b o := by
  cases h with
{chr (10 ).join (code_case_arms )}
def NF : CM → Prop
  | .e => True
  | .k a => NF a
  | .p a b => NF a ∧ NF b ∧ ¬ ∃ o, Code a b o
@[grind →] theorem nf_p_left {{a b : CM}} (h : NF (p a b)) : NF a := h.1
@[grind →] theorem nf_p_right {{a b : CM}} (h : NF (p a b)) : NF b := h.2.1
@[grind →] theorem nf_p_no {{a b : CM}} (h : NF (p a b)) : ¬ ∃ o, Code a b o := h.2.2
theorem eq_sz {{a b : CM}} (h : a = b) : sz a = sz b := congrArg sz h
theorem ne_p_left (a b : CM) : a ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q <;> omega
theorem ne_p_right (a b : CM) : b ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q <;> omega
theorem code_nf {{a b o : CM}} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
{chr (10 ).join (nf_cases )}
{''.join (redex_lemmas )}noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by simp [eval, h]
theorem eval_nf {{a b : CM}} (ha : NF a) (hb : NF b) : NF (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact code_nf ha hb (Classical.choose_spec h)
  · rw [eval_raw h]
    exact ⟨ha, hb, h⟩
{eval_cases_block }
theorem source_raw ({' '.join (sv )} : CM)
    {' '.join ('(h'+v +' : NF '+v +')'for v in sv )} :
    {cnf_eval_term (source [0 ])} = {cnf_eval_term (source [1 ])} := by
  classical
{bcases }
{nfacts }
{source_script }
def Carrier := {{t : CM // NF t}}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagma : Magma Carrier where op := op
theorem source_holds ({' '.join (sv )} : Carrier) :
    {cnf_op_term (source [0 ])} = {cnf_op_term (source [1 ])} := by
  apply Subtype.ext
  exact source_raw {' '.join (v +'.1'for v in sv )} {' '.join (v +'.2'for v in sv )}
def ce : Carrier := ⟨e, by trivial⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, a.2⟩
def tower : Nat → Carrier | 0 => ce | n+1 => ck (tower n)
theorem tower_sz (n : Nat) : sz (tower n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tower, ck, sz, ih]
theorem tower_injective : Function.Injective tower := by
  intro a b h
  have q := congrArg (fun x : Carrier => sz x.1) h
  simpa only [tower_sz] using q
{''.join (lemmas )}end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagma, CM.source_holds, ?_⟩
  intro target
  have bad := congrArg Subtype.val (target {apps })
  change {cnf_eval_term (target [0 ],env )} = {cnf_eval_term (target [1 ],env )} at bad
  have hl : {cnf_eval_term (target [0 ],env )} = {cnf_lean_term (nl )} := {lp }
  have hr : {cnf_eval_term (target [1 ],env )} = {cnf_lean_term (nr )} := {rp }
  have bad := hl.symm.trans (bad.trans hr)
  exact {cnf_clash_proof (nl ,nr )}
'''

def cnf_search (source ,target ,deadline =None ):
    for seed in cnf_candidate_seeds (source ):
        if deadline is not None and time .monotonic ()>=deadline :
            return None 
        completed =cnf_critical_complete (seed ,deadline =deadline )
        systems =[]
        if completed and completed !=seed :
            systems .append (completed )
        systems .append (seed )
        for rules in systems :
            if deadline is not None and time .monotonic ()>=deadline :
                return None 
            if (not rules or any (not cnf_is_pair (left )for left ,_right in rules )or
                any (not cnf_rhs_nf_safe (left ,right )for left ,right in rules )):
                continue 
            good ,_calls =cnf_source_tableau (source ,rules ,deadline =deadline )
            if not good :
                continue 
            witness =cnf_target_witness (target ,rules ,deadline =deadline )
            if witness is None :
                continue 
            try :
                code =cnf_compile_lean (source ,target ,rules ,witness ,deadline )
            except (ValueError ,TimeoutError )as exc :
                if DEBUG :
                    print (f"cnf compile: {type (exc ).__name__ }: {exc }",file =sys .stderr )
                continue 
            if len (code .encode ("utf-8"))<=FALSE_CERTIFICATE_LIMIT :
                return code 
            if DEBUG :
                print (f"cnf certificate bytes={len (code .encode ('utf-8'))}",file =sys .stderr )
    return None


_PAPER_LAST_COMPILE = None
_PAPER_HEARTBEAT_STOP = threading.Event()
_PAPER_HEARTBEAT_THREAD = None
_paper_original_cnf_compile_lean = cnf_compile_lean


def _paper_start_heartbeat():
    """Keep the provider's original command stream attached during search."""
    global _PAPER_HEARTBEAT_THREAD

    def pulse():
        while not _PAPER_HEARTBEAT_STOP.is_set():
            print("# isolated-search-heartbeat", file=sys.stderr, flush=True)
            _PAPER_HEARTBEAT_STOP.wait(1.0)

    _PAPER_HEARTBEAT_THREAD = threading.Thread(target=pulse, daemon=True)
    _PAPER_HEARTBEAT_THREAD.start()


def _paper_stop_heartbeat():
    _PAPER_HEARTBEAT_STOP.set()
    if _PAPER_HEARTBEAT_THREAD is not None:
        _PAPER_HEARTBEAT_THREAD.join(timeout=0.25)


def _paper_complete_without_candidate(terminal):
    """Send an explicit completion frame, then await runner-side teardown."""
    print(json.dumps({
        "call": "isolated_search_complete",
        "terminal": terminal,
    }, ensure_ascii=False, separators=(",", ":")), flush=True)
    while True:
        time.sleep(60.0)


def _paper_cnf_compile_lean(source, target, rules, witness, deadline):
    global _PAPER_LAST_COMPILE
    code = _paper_original_cnf_compile_lean(source, target, rules, witness, deadline)
    _PAPER_LAST_COMPILE = {
        "rule_count": len(rules),
        "certificate_bytes": len(code.encode("utf-8")),
        "certificate_sha256": hashlib.sha256(code.encode("utf-8")).hexdigest(),
    }
    return code


cnf_compile_lean = _paper_cnf_compile_lean


def _paper_diagnostic(payload):
    print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")), file=sys.stderr, flush=True)


def main():
    global _PAPER_LAST_COMPILE
    _paper_start_heartbeat()
    raw = sys.stdin.readline()
    if not raw:
        return 2
    startup = json.loads(raw)
    problem = startup["problem"]
    _PAPER_LAST_COMPILE = None
    started = time.monotonic()
    try:
        source = parse_eq(problem["equation1"])
        target = parse_eq(problem["equation2"])
        order = []
        for term in source + target:
            variables(term, order)
        alpha = {variable: "q%d" % index for index, variable in enumerate(order)}
        source = tuple(rename_term(term, alpha) for term in source)
        target = tuple(rename_term(term, alpha) for term in target)
        deadline = time.monotonic() + SEARCH_BUDGET_SECONDS
        candidate = cnf_search(source, target, deadline)
    except Exception as error:
        elapsed_value = time.monotonic() - started
        terminal = {
            "phase": "isolated_search_terminal",
            "search_program": "cnf_only",
            "status": "ERROR",
            "error_type": type(error).__name__,
            "error": str(error),
            "elapsed_seconds": round(elapsed_value, 6),
        }
        _paper_diagnostic(terminal)
        _paper_complete_without_candidate(terminal)
    finally:
        release_unused_memory()
    elapsed_value = time.monotonic() - started
    elapsed = round(elapsed_value, 6)
    terminal = {
        "phase": "isolated_search_terminal",
        "search_program": "cnf_only",
        "status": "FOUND" if candidate else "NO_MODEL_FOUND",
        "configured_search_seconds": SEARCH_BUDGET_SECONDS,
        "elapsed_seconds": elapsed,
        "compile": _PAPER_LAST_COMPILE,
    }
    _paper_diagnostic(terminal)
    candidate = strict_certificate_gate(candidate)
    if candidate is None:
        _paper_complete_without_candidate(terminal)
    certificate_bytes = len(candidate.encode("utf-8"))
    metadata = {
        "experiment_schema": "isolated-infinite-search-v1",
        "search_program": "cnf_only",
        "subprocedure": "cnf_normal_form",
        "profile": "cnf_nf16_reverse_ties_completed_first_sound_v3",
        "completion_rule_cap": CNF_COMPLETION_RULE_CAP,
        "completion_round_cap": CNF_COMPLETION_ROUND_CAP,
        "completion_overlap_cap": CNF_COMPLETION_OVERLAP_CAP,
        "source_tableau_cap": CNF_SOURCE_TABLEAU_CAP,
        "configured_search_seconds": SEARCH_BUDGET_SECONDS,
        "search_elapsed_seconds": elapsed,
        "certificate_bytes": certificate_bytes,
        **(_PAPER_LAST_COMPILE or {}),
    }
    print(json.dumps({
        "call": "judge",
        "verdict": "false",
        "code": candidate,
        "metadata": metadata,
    }, ensure_ascii=False, separators=(",", ":")), flush=True)
    response_line = sys.stdin.readline()
    if not response_line:
        return 2
    if json.loads(response_line).get("status") == "accepted":
        return 0
    terminal["status"] = "CANDIDATE_REJECTED"
    _paper_diagnostic(terminal)
    _paper_complete_without_candidate(terminal)


if __name__ == "__main__":
    raise SystemExit(main())
