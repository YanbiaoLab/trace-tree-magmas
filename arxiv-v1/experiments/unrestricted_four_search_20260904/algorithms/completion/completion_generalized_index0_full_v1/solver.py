#!/usr/bin/env python3
# Strict independent ablation executable: completion_only.
# Enabled subprocedure: strict_completion.  All other v13 jobs are filtered.
# Search budget: 120 seconds; certificate compiler unchanged.
from __future__ import annotations
import base64
import bisect
import ctypes
from ctypes import wintypes
from dataclasses import asdict as _pa_asdict, dataclass
import functools
import heapq
import gc
import hashlib
import itertools
from itertools import product
import json
import lzma
import math
import os
import random
import re
import signal
import sys
import threading
import time
import traceback
from array import array

MAX_FALSE_CERTIFICATE_BYTES = 1_024_000
SEARCH_BUDGET_SECONDS = 120.0
PROTOCOL_MIN_LIFETIME_SECONDS = 1.5

_v13_DEADLINE = time.monotonic() + 115.0

_v13_COMPLETION_CACHE = {}

_v13_SELECTION_CACHE = {}

_v13_STRICT_FAILURES = []

_v13_STRICT_LAST_SOURCE_CERT = None

_v13_JUDGE_FALLBACKS = ()

_v13_STRUCTURAL_ORDER_PROBE_LEAVES = 2048

def _v13_strip_outer(s):
    while s.startswith('(') and s.endswith(')'):
        d = 0
        for i, c in enumerate(s):
            d += c == '('
            d -= c == ')'
            if d == 0 and i + 1 < len(s):
                return s
        s = s[1:-1]
    return s

def _v13_parse_side(s):
    s = _v13_strip_outer(re.sub('[^a-z()]+', '*', s.lower()).strip('*'))
    d = 0
    cut = -1
    for i, c in enumerate(s):
        d += c == '('
        d -= c == ')'
        if c == '*' and d == 0:
            cut = i
    if cut >= 0:
        return (_v13_parse_side(s[:cut]), _v13_parse_side(s[cut + 1:]))
    if len(s) == 1 and 'a' <= s <= 'z':
        return s
    raise ValueError('bad term')

def _v13_parse_eq(s):
    a, b = s.split('=')
    return (_v13_parse_side(a), _v13_parse_side(b))

def _v13_variables(t, out=None):
    out = [] if out is None else out
    if isinstance(t, str):
        if t not in out:
            out.append(t)
    else:
        _v13_variables(t[0], out)
        _v13_variables(t[1], out)
    return out

def _v13_formal_variables(equation):
    """Return variables in the stable order used by Judge equation binders."""
    out = _v13_variables(equation[0])
    _v13_variables(equation[1], out)
    if out and all((re.fullmatch('q\\d+', name) for name in out)):
        return sorted(out, key=lambda name: int(name[1:]))
    return out

def _v13_strict_source_certificate(term, output, rules, leaf_cap=2000000, repair_sink=None, stats_sink=None, priority=False, order_override=None):
    raw_rules = tuple(((left, right) for left, right, _vs in rules))

    def resolve(t, env, seen=None):
        seen = set() if seen is None else seen
        if isinstance(t, str):
            if t not in env or t in seen:
                return t
            return resolve(env[t], env, seen | {t})
        return (resolve(t[0], env, seen), resolve(t[1], env, seen))

    def has(v, t, env):
        t = resolve(t, env)
        return t == v if isinstance(t, str) else has(v, t[0], env) or has(v, t[1], env)

    def solve(equations):
        env, todo = ({}, list(equations))
        while todo:
            a, b = resolve(todo.pop(), env)
            if a == b:
                continue
            if isinstance(a, str):
                if has(a, b, env):
                    return None
                env[a] = b
            elif isinstance(b, str):
                if has(b, a, env):
                    return None
                env[b] = a
            else:
                todo.extend(((a[0], b[0]), (a[1], b[1])))
        return env

    def branch_term(t, prefix):
        return prefix + t if isinstance(t, str) else (branch_term(t[0], prefix), branch_term(t[1], prefix))

    def rigid_match(pattern, actual, bindings=None):
        bindings = {} if bindings is None else bindings
        if isinstance(pattern, str):
            if pattern in bindings:
                return bindings if bindings[pattern] == actual else None
            bindings[pattern] = actual
            return bindings
        if isinstance(actual, str):
            return None
        bindings = rigid_match(pattern[0], actual[0], bindings)
        return None if bindings is None else rigid_match(pattern[1], actual[1], bindings)
    nodes = []
    node_depths = []

    def build(t, depth=0):
        if isinstance(t, str):
            return t
        a, b = (build(t[0], depth + 1), build(t[1], depth + 1))
        result = '__t' + str(len(nodes))
        nodes.append((a, b, result))
        node_depths.append(depth)
        return result
    root = build(term)
    known_nf = tuple(_v13_variables(term)) + tuple((node[2] for node in nodes))
    if order_override is None:
        order = tuple(sorted(range(len(nodes)), key=lambda i: (node_depths[i], -i)))
    else:
        order = tuple(order_override)
    counts = {'occurs': 0, 'goal': 0, 'raw': 0, 'nf': 0, 'open': 0, 'memo': 0}
    leaves = 0
    calls = 0
    term_work = 0
    peak_term_mass = 0
    proved = set()

    def term_mass(t):
        return 1 if isinstance(t, str) else 1 + term_mass(t[0]) + term_mass(t[1])

    def code_match(pair, env, normal=None, prefix=None):
        actual = normal(pair) if normal else resolve(pair, env)
        candidates = raw_rules if prefix is None else raw_rules[:prefix]
        return any((rigid_match(left, actual) is not None for left, _right in candidates))

    def has_redex(t, env, normal=None):
        t = normal(t) if normal else resolve(t, env)
        if isinstance(t, str):
            return False
        return code_match(t, env, normal) or has_redex(t[0], env, normal) or has_redex(t[1], env, normal)

    def close(kind):
        nonlocal leaves
        leaves += 1
        counts[kind] += 1
        if leaves > leaf_cap:
            raise OverflowError('strict source tableau leaf cap')

    def visit(depth, equations, misses):
        nonlocal calls, term_work, peak_term_mass
        calls += 1
        if time.monotonic() >= _v13_DEADLINE:
            raise TimeoutError('strict source tableau deadline')
        env = solve(equations)
        if env is None:
            close('occurs')
            return
        normal_cache = {}

        def normal(t):
            if t in normal_cache:
                return normal_cache[t]
            if isinstance(t, str):
                value = t if t not in env else normal(env[t])
            else:
                value = (normal(t[0]), normal(t[1]))
            normal_cache[t] = value
            return value
        mass = sum((term_mass(normal(t)) for t in (root, output)))
        for a, b, result in nodes:
            mass += term_mass(normal(a)) + term_mass(normal(b)) + term_mass(normal(result))
        term_work += mass
        peak_term_mass = max(peak_term_mass, mass)
        if normal(root) == normal(output):
            close('goal')
            return
        if any((code_match((a, b), env, normal, prefix) for a, b, prefix in misses)):
            close('raw')
            return
        if any((has_redex(t, env, normal) for t in known_nf)):
            close('nf')
            return
        names = {}

        def canonical(t):
            t = normal(t)
            if isinstance(t, str):
                if t not in names:
                    names[t] = len(names)
                return names[t]
            return (canonical(t[0]), canonical(t[1]))
        signature = [root, output]
        for a, b, result in nodes:
            signature.extend((a, b, result))
        signature.extend(known_nf)
        key = (depth, tuple((canonical(t) for t in signature)), tuple(((canonical(a), canonical(b), prefix) for a, b, prefix in misses)))
        if key in proved:
            counts['memo'] += 1
            return
        if depth == len(order):
            if repair_sink is not None:
                wanted = normal(output)
                for a, b, prefix in misses:
                    if prefix != len(raw_rules):
                        continue
                    item = ((normal(a), normal(b)), wanted)
                    if item not in repair_sink and len(repair_sink) < 512:
                        repair_sink.append(item)
            close('open')
            return
        open_before = counts['open']
        index = order[depth]
        a, b, result = nodes[index]
        for rule_index, (left, right) in enumerate(raw_rules):
            prefix = '__b' + str(index) + 'r' + str(rule_index) + '_'
            left0 = branch_term(left, prefix)
            right0 = branch_term(right, prefix)
            visit(depth + 1, equations + ((a, left0[0]), (b, left0[1]), (result, right0)), misses + (((a, b, rule_index),) if priority and rule_index else ()))
        visit(depth + 1, equations + ((result, (a, b)),), misses + ((a, b, len(raw_rules)),))
        if counts['open'] == open_before:
            proved.add(key)
    try:
        visit(0, (), ())
    except (MemoryError, OverflowError, RecursionError, TimeoutError):
        if stats_sink is not None:
            stats_sink.update(counts, leaves=leaves, states=calls, term_work=term_work, peak_term_mass=peak_term_mass)
        return None
    if stats_sink is not None:
        stats_sink.update(counts, leaves=leaves, states=calls, term_work=term_work, peak_term_mass=peak_term_mass)
    if counts['open']:
        return None
    return {'leaves': leaves, 'states': calls, 'memoized': len(proved), 'source_nodes': len(nodes), 'rules': len(rules), 'closures': counts, 'split_order': order, 'term_work': term_work, 'peak_term_mass': peak_term_mass}

def _v13_needs_layered_source_pruning(certificate):
    """Estimate whether non-arithmetic closures justify staged `grind` calls."""
    closures = certificate['closures']
    structural = closures['goal'] + closures['raw'] + closures['nf']
    return certificate['leaves'] <= 500 or structural >= 50

def _v13_rename_term(t, env):
    if isinstance(t, str):
        return env.get(t, t)
    return (_v13_rename_term(t[0], env), _v13_rename_term(t[1], env))

def _v13_pterm(t):
    if isinstance(t, str):
        return t
    if t == ('E',):
        return 'e'
    if len(t) == 2 and t[0] == '@':
        return f'(k {_v13_pterm(t[1])})'
    return f'(p {_v13_pterm(t[0])} {_v13_pterm(t[1])})'

def _v13_opterm(t, vals=None):
    if isinstance(t, str):
        return (vals or {}).get(t, t)
    return f'(op {_v13_opterm(t[0], vals)} {_v13_opterm(t[1], vals)})'

def _v13_paths(t, want, path=()):
    if isinstance(t, str):
        if t == want:
            yield path
    elif t == ('E',):
        return
    elif len(t) == 2 and t[0] == '@':
        yield from _v13_paths(t[1], want, path + (2,))
    else:
        yield from _v13_paths(t[0], want, path + (0,))
        yield from _v13_paths(t[1], want, path + (1,))

def _v13_subpaths(t, want, path=()):
    if t == want:
        yield path
    if isinstance(t, str) or t == ('E',):
        return
    if len(t) == 2 and t[0] == '@':
        return
    yield from _v13_subpaths(t[0], want, path + (0,))
    yield from _v13_subpaths(t[1], want, path + (1,))

def _v13_selector(path, name='q'):
    x = name
    for bit in path:
        x = f"({('U' if bit == 2 else 'R' if bit else 'L')} {x})"
    return x

def _v13_refute_closed_eq(a, b):
    path = ()
    while True:
        ka = 'e' if a[0] == 0 else 'k' if a[0] == 1 else 'p'
        kb = 'e' if b[0] == 0 else 'k' if b[0] == 1 else 'p'
        if ka != kb:
            bits = {'e': 'false', 'k': 'false', 'p': 'false'}
            bits[ka], bits[kb] = ('false', 'true')
            q = _v13_selector(path)
            discr = f"(fun q => match {q} with | e => {bits['e']} | k _ => {bits['k']} | p _ _ => {bits['p']})"
            return f'Bool.noConfusion (congrArg {discr} bad)'
        if ka == 'k':
            a, b, path = (a[1], b[1], path + (2,))
        elif ka == 'p':
            if a[1] != b[1]:
                a, b, path = (a[1], b[1], path + (0,))
            else:
                a, b, path = (a[2], b[2], path + (1,))
        else:
            raise ValueError('equal closed terms')

def _v13_constraints(a, b, path=()):
    if isinstance(a, str) or isinstance(b, str):
        return [(a, b, path)]
    if a == b:
        return []
    ak = 'e' if a == ('E',) else 'k' if len(a) == 2 and a[0] == '@' else 'p'
    bk = 'e' if b == ('E',) else 'k' if len(b) == 2 and b[0] == '@' else 'p'
    if ak != bk:
        return [(a, b, path)]
    if ak == 'k':
        return _v13_constraints(a[1], b[1], path + (2,))
    if ak == 'e':
        return []
    return _v13_constraints(a[0], b[0], path + (0,)) + _v13_constraints(a[1], b[1], path + (1,))

def _v13_subst(t, env):
    if isinstance(t, str):
        seen = set()
        while t in env and t not in seen:
            seen.add(t)
            value = env[t]
            if value == t:
                break
            t = value
        return t
    return (_v13_subst(t[0], env), _v13_subst(t[1], env))

def _v13_occurs(v, t, env):
    t = _v13_subst(t, env)
    if isinstance(t, str):
        return t == v
    return _v13_occurs(v, t[0], env) or _v13_occurs(v, t[1], env)

def _v13_replace_vars(t, env, seen=None):
    seen = set() if seen is None else seen
    if isinstance(t, str):
        if t not in env or t in seen:
            return t
        return _v13_replace_vars(env[t], env, seen | {t})
    if t == ('E',):
        return t
    if len(t) == 2 and t[0] == '@':
        return ('@', _v13_replace_vars(t[1], env, seen))
    return (_v13_replace_vars(t[0], env, seen), _v13_replace_vars(t[1], env, seen))

def _v13_has_var(v, t):
    if isinstance(t, str):
        return t == v
    if t == ('E',):
        return False
    if len(t) == 2 and t[0] == '@':
        return _v13_has_var(v, t[1])
    return _v13_has_var(v, t[0]) or _v13_has_var(v, t[1])

def _v13_occurrence_path(v, t, path=()):
    if isinstance(t, str):
        return path if t == v else None
    if t == ('E',):
        return None
    if len(t) == 2 and t[0] == '@':
        return _v13_occurrence_path(v, t[1], path + (2,))
    return _v13_occurrence_path(v, t[0], path + (0,)) or _v13_occurrence_path(v, t[1], path + (1,))

def _v13_lt_proof(t, path):
    bit, rest = (path[0], path[1:])
    child, other = (t[bit], t[1 - bit])
    step = f'sz_lt_p_left {_v13_pterm(child)} {_v13_pterm(other)}' if bit == 0 else f'sz_lt_p_right {_v13_pterm(other)} {_v13_pterm(child)}'
    if not rest:
        return step
    return f'Nat.lt_trans ({_v13_lt_proof(child, rest)}) ({step})'

class _v13_ProofEndpointError(RuntimeError):
    pass


@dataclass(frozen=True)
class _v13_EqProof:
    left: object
    right: object
    lean: str
    node: object = None


def _v13_eq_refl(term):
    return _v13_EqProof(term, term, 'rfl', ('refl',))


def _v13_eq_assumption(left, right, lean):
    return _v13_EqProof(left, right, lean, ('leaf', lean))


def _v13_eq_symm(proof):
    if proof.left == proof.right:
        return _v13_eq_refl(proof.left)
    return _v13_EqProof(
        proof.right,
        proof.left,
        f'Eq.symm ({proof.lean})',
        ('symm', proof),
    )


def _v13_eq_trans(first, second):
    if first.right != second.left:
        raise _v13_ProofEndpointError(
            f'equality endpoint mismatch: {first.right!r} != {second.left!r}'
        )
    if first.left == first.right:
        return second
    if second.left == second.right:
        return first
    return _v13_EqProof(
        first.left,
        second.right,
        f'Eq.trans ({first.lean}) ({second.lean})',
        ('trans', first, second),
    )


def _v13_eq_congr_k(proof):
    if proof.left == proof.right:
        return _v13_eq_refl(('@', proof.left))
    return _v13_EqProof(
        ('@', proof.left),
        ('@', proof.right),
        f'congrArg (fun q => k q) ({proof.lean})',
        ('congr_k', proof),
    )


def _v13_eq_congr_pair_left(proof, right):
    if proof.left == proof.right:
        return _v13_eq_refl((proof.left, right))
    return _v13_EqProof(
        (proof.left, right),
        (proof.right, right),
        f'congrArg (fun q => p q {_v13_pterm(right)}) ({proof.lean})',
        ('congr_pair_left', proof, right),
    )


def _v13_eq_congr_pair_right(left, proof):
    if proof.left == proof.right:
        return _v13_eq_refl((left, proof.left))
    return _v13_EqProof(
        (left, proof.left),
        (left, proof.right),
        f'congrArg (fun q => p {_v13_pterm(left)} q) ({proof.lean})',
        ('congr_pair_right', left, proof),
    )


def _v13_eq_project(proof, coordinate):
    if coordinate == 2:
        if not (isinstance(proof.left, tuple) and isinstance(proof.right, tuple) and
                len(proof.left) == 2 and len(proof.right) == 2 and
                proof.left[0] == '@' and proof.right[0] == '@'):
            raise _v13_ProofEndpointError('unary projection applied to non-unary equality')
        left, right, selector = proof.left[1], proof.right[1], 'U'
    else:
        if not (isinstance(proof.left, tuple) and isinstance(proof.right, tuple) and
                len(proof.left) == 2 and len(proof.right) == 2 and
                proof.left != ('E',) and proof.right != ('E',) and
                proof.left[0] != '@' and proof.right[0] != '@'):
            raise _v13_ProofEndpointError('pair projection applied to non-pair equality')
        left, right = proof.left[coordinate], proof.right[coordinate]
        selector = 'L' if coordinate == 0 else 'R'
    if left == right:
        return _v13_eq_refl(left)
    return _v13_EqProof(
        left,
        right,
        f'congrArg (fun q => {selector} q) ({proof.lean})',
        ('project', selector, proof),
    )


def _v13_normalization_proof_typed(t, env, seen=None):
    seen = set() if seen is None else seen
    if isinstance(t, str):
        if t not in env or t in seen:
            return (t, _v13_eq_refl(t))
        rhs, lemma = env[t]
        head = lemma if isinstance(lemma, _v13_EqProof) else _v13_eq_assumption(t, rhs, lemma)
        if head.left != t or head.right != rhs:
            raise _v13_ProofEndpointError(
                f'environment proof has endpoints {head.left!r}, {head.right!r}; '
                f'expected {t!r}, {rhs!r}'
            )
        normal, tail = _v13_normalization_proof_typed(rhs, env, seen | {t})
        return (normal, _v13_eq_trans(head, tail))
    if t == ('E',):
        return (t, _v13_eq_refl(t))
    if len(t) == 2 and t[0] == '@':
        a, pa = _v13_normalization_proof_typed(t[1], env, seen)
        return (('@', a), _v13_eq_congr_k(pa))
    a, pa = _v13_normalization_proof_typed(t[0], env, seen)
    b, pb = _v13_normalization_proof_typed(t[1], env, seen)
    left = _v13_eq_congr_pair_left(pa, t[1])
    right = _v13_eq_congr_pair_right(a, pb)
    return ((a, b), _v13_eq_trans(left, right))


def _v13_normalization_proof(t, env, seen=None):
    normal, proof = _v13_normalization_proof_typed(t, env, seen)
    return (normal, proof.lean)


def _v13_materialize_equality_context(eqs):
    """Name every tableau equality at its exact symbolic endpoints.

    Dependent case splits may rewrite the types of Step witnesses.  Keeping a
    raw proof string alive across later unifier substitutions can therefore
    attach a projection proof to an endpoint it no longer has.  Materialized
    local facts make Lean check every boundary once, while the Python proof
    objects retain the same checked endpoints for deterministic composition.
    """
    bindings = []
    typed = []
    for index, (left, right, proof) in enumerate(eqs):
        lean = proof.lean if isinstance(proof, _v13_EqProof) else proof
        name = f'peq{index}'
        # A separate let prevents expected-type information from the eventual
        # goal flowing back into this premise.  Its type is already determined
        # by the source hypothesis/projection itself, so repeating the often
        # large symbolic endpoint here would only inflate the certificate.
        bindings.append(f'let {name} := {lean};')
        typed.append((left, right, _v13_eq_assumption(left, right, name)))
    return bindings, typed


def _v13_close_materialized_equality(bindings, proof):
    """Compile a checked equality DAG to explicitly typed Lean ``let`` facts."""
    memo = {}
    steps = list(bindings)

    def compile_node(current):
        cached = memo.get(id(current))
        if cached is not None:
            return cached
        node = current.node
        kind = node[0]
        if kind in ('leaf', 'refl'):
            return current.lean
        if kind == 'symm':
            expression = f'Eq.symm ({compile_node(node[1])})'
        elif kind == 'trans':
            expression = f'Eq.trans ({compile_node(node[1])}) ({compile_node(node[2])})'
        elif kind == 'congr_k':
            expression = f'congrArg (fun q => k q) ({compile_node(node[1])})'
        elif kind == 'congr_pair_left':
            expression = (
                f'congrArg (fun q => p q {_v13_pterm(node[2])}) '
                f'({compile_node(node[1])})'
            )
        elif kind == 'congr_pair_right':
            expression = (
                f'congrArg (fun q => p {_v13_pterm(node[1])} q) '
                f'({compile_node(node[2])})'
            )
        elif kind == 'project':
            expression = (
                f'congrArg (fun q => {node[1]} q) ({compile_node(node[2])})'
            )
        else:
            raise _v13_ProofEndpointError(f'unknown equality proof node: {kind!r}')
        name = f'pst{len(memo)}'
        # The leaves above carry explicit endpoints.  Each operation is then
        # inferred independently in its own let-binding, which prevents the
        # final goal from pushing a stale expected endpoint into a nested
        # projection while keeping near-limit certificates compact.
        steps.append(f'let {name} := {expression};')
        memo[id(current)] = name
        return name

    result = compile_node(proof)
    return '(' + ' '.join(steps + [result]) + ')'


def _v13_unify_cycle_proof(eqs):
    original_eqs = list(eqs)
    lines, typed_eqs = _v13_materialize_equality_context(original_eqs)
    env, todo = ({}, list(typed_eqs))
    while todo:
        a, b, h = todo.pop(0)
        original_a, original_b = a, b
        a, pa = _v13_normalization_proof_typed(original_a, env)
        b, pb = _v13_normalization_proof_typed(original_b, env)
        given = h if isinstance(h, _v13_EqProof) else _v13_eq_assumption(original_a, original_b, h)
        pr = _v13_eq_trans(_v13_eq_trans(_v13_eq_symm(pa), given), pb)
        if a == b:
            continue
        if isinstance(b, str) and (not isinstance(a, str)):
            a, b, pr = (b, a, _v13_eq_symm(pr))
        if isinstance(a, str):
            if _v13_has_var(a, b):
                return (a, b, _v13_close_materialized_equality(lines, pr))
            env[a] = (b, pr)
        else:
            ak = 'e' if a == ('E',) else 'k' if len(a) == 2 and a[0] == '@' else 'p'
            bk = 'e' if b == ('E',) else 'k' if len(b) == 2 and b[0] == '@' else 'p'
            if ak != bk:
                return None
            if ak == 'e':
                continue
            if ak == 'k':
                todo.insert(0, (a[1], b[1], _v13_eq_project(pr, 2)))
                continue
            todo.insert(0, (a[1], b[1], _v13_eq_project(pr, 1)))
            todo.insert(0, (a[0], b[0], _v13_eq_project(pr, 0)))
    return None

def _v13_compact_cycle_proof(proof, limit=1800):
    return proof

def _v13_proof_unifier(eqs):
    env, todo = ({}, list(eqs))
    while todo:
        a, b, h = todo.pop(0)
        original_a, original_b = a, b
        a, pa = _v13_normalization_proof_typed(original_a, env)
        b, pb = _v13_normalization_proof_typed(original_b, env)
        given = h if isinstance(h, _v13_EqProof) else _v13_eq_assumption(original_a, original_b, h)
        pr = _v13_eq_trans(_v13_eq_trans(_v13_eq_symm(pa), given), pb)
        if a == b:
            continue
        if isinstance(b, str) and (not isinstance(a, str)):
            a, b, pr = (b, a, _v13_eq_symm(pr))
        if isinstance(a, str):
            if _v13_has_var(a, b):
                return None
            env[a] = (b, pr)
        elif isinstance(b, str):
            if _v13_has_var(b, a):
                return None
            env[b] = (a, _v13_eq_symm(pr))
        else:
            ak = 'e' if a == ('E',) else 'k' if len(a) == 2 and a[0] == '@' else 'p'
            bk = 'e' if b == ('E',) else 'k' if len(b) == 2 and b[0] == '@' else 'p'
            if ak != bk:
                return None
            if ak == 'e':
                continue
            if ak == 'k':
                todo.insert(0, (a[1], b[1], _v13_eq_project(pr, 2)))
                continue
            todo.insert(0, (a[1], b[1], _v13_eq_project(pr, 1)))
            todo.insert(0, (a[0], b[0], _v13_eq_project(pr, 0)))
    return env

def _v13_unified_equality(eqs, a, b):
    lines, typed_eqs = _v13_materialize_equality_context(eqs)
    env = _v13_proof_unifier(typed_eqs)
    if env is None:
        return None
    na, pa = _v13_normalization_proof_typed(a, env)
    nb, pb = _v13_normalization_proof_typed(b, env)
    if na != nb:
        return None
    proof = _v13_eq_trans(pa, _v13_eq_symm(pb))
    return _v13_close_materialized_equality(lines, proof)

def _v13_tag(t, prefix):
    if isinstance(t, str):
        return prefix + ':' + t
    return (_v13_tag(t[0], prefix), _v13_tag(t[1], prefix))

def _v13_select_term(t, path):
    for bit in path:
        if not isinstance(t, tuple):
            raise AssertionError('selector entered a variable')
        t = t[1] if bit == 2 else t[bit]
    return t

def _v13_at_path(t, path):
    for bit in path:
        t = t[1] if bit == 2 else t[bit]
    return t

def _v13_replace_at(t, path, value):
    if not path:
        return value
    bit = path[0]
    if bit:
        return (t[0], _v13_replace_at(t[1], path[1:], value))
    return (_v13_replace_at(t[0], path[1:], value), t[1])

def _v13_internal_paths(t, path=()):
    if isinstance(t, str):
        return []
    return _v13_internal_paths(t[0], path + (0,)) + _v13_internal_paths(t[1], path + (1,)) + [(path, t)]

def _v13_size_poly(t):
    if isinstance(t, str):
        return {t: 1, '#': 0}
    if t == ('E',):
        return {'#': 0}
    if len(t) == 2 and t[0] == '@':
        out = _v13_size_poly(t[1])
        out['#'] = out.get('#', 0) + 1
        return out
    a, b = (_v13_size_poly(t[0]), _v13_size_poly(t[1]))
    out = {k: a.get(k, 0) + b.get(k, 0) for k in set(a) | set(b)}
    out['#'] = out.get('#', 0) + 2
    return out

def _v13_infeasible(rows):
    vs = sorted({v for r, _ in rows for v in r})
    for v in vs:
        pos, neg, zero = ([], [], [])
        for r, b in rows:
            c = r.get(v, 0)
            (pos if c > 0 else neg if c < 0 else zero).append((r, b))
        nxt = [({k: x for k, x in r.items() if k != v}, b) for r, b in zero]
        for p, bp in pos:
            for n, bn in neg:
                ap, an = (p[v], -n[v])
                keys = (set(p) | set(n)) - {v}
                q = {k: an * p.get(k, 0) + ap * n.get(k, 0) for k in keys}
                q = {k: x for k, x in q.items() if x}
                nxt.append((q, an * bp + ap * bn))
        seen, rows = (set(), [])
        for r, b in nxt:
            key = (tuple(sorted(r.items())), b)
            if key not in seen:
                seen.add(key)
                rows.append((r, b))
        if any((not r and b < 0 for r, b in rows)):
            return True
        if len(rows) > 6000:
            return False
    return any((not r and b < 0 for r, b in rows))

def _v13_size_row(a, b, strict=1):
    x, y = (_v13_size_poly(a), _v13_size_poly(b))
    keys = (set(x) | set(y)) - {'#'}
    return ({k: x.get(k, 0) - y.get(k, 0) for k in keys if x.get(k, 0) != y.get(k, 0)}, y.get('#', 0) - x.get('#', 0) - strict)

def _v13_normalize_output_law(source, target):
    left, right = source
    if isinstance(left, str) and (not isinstance(right, str)):
        output = left
    elif isinstance(right, str) and (not isinstance(left, str)):
        output = right
    else:
        return None
    order = _v13_variables(source[0])
    order += [v for v in _v13_variables(source[1]) if v not in order]
    order += [v for side in target for v in _v13_variables(side) if v not in order]
    ren, serial = ({output: 'x'}, 0)
    for v in order:
        if v == output:
            continue
        ren[v] = f'v{serial}'
        serial += 1
    return (tuple((_v13_rename_term(t, ren) for t in source)), tuple((_v13_rename_term(t, ren) for t in target)), ren)

def _v13_trace_model(source, target, skip=0, tableau_depth=0):
    formal_target = _v13_formal_variables(target)
    normalized = _v13_normalize_output_law(source, target)
    if normalized is None:
        return None
    source, target, ren = normalized
    formal_target = [ren[name] for name in formal_target]
    left, right = source
    if left == 'x':
        term, rev = (right, False)
    elif right == 'x':
        term, rev = (left, True)
    else:
        return None
    ns = _v13_internal_paths(term)
    if len(ns) < 2 or len(ns) > 8:
        return None
    inner = ns[:-1]
    sv = _v13_variables(source[0]) + [z for z in _v13_variables(source[1]) if z not in _v13_variables(source[0])]
    masks = sorted(range(1 << len(inner)), key=lambda q: (q.bit_count(), q))
    for mask in masks:
        active = {path for i, (path, _) in enumerate(inner) if mask >> i & 1}
        result, steps, inactive = ({}, [], [])

        def build(t, path=()):
            if isinstance(t, str):
                return t
            a, b = (build(t[0], path + (0,)), build(t[1], path + (1,)))
            if path in active:
                h = f'H{len(steps)}'
                steps.append((path, h, a, b))
                result[path] = h
                return h
            result[path] = (a, b)
            if path:
                inactive.append((path, a, b))
            return (a, b)
        root = build(term)
        ra, rb = root
        visible_inactive = [q for q in inactive if not any((len(a) < len(q[0]) and q[0][:len(a)] == a for a in active))]
        out_path = next(_v13_paths((ra, rb), 'x'), None)
        recursive = None
        if out_path is None:
            pair = (ra, rb)
            for key_coord in (0, 1):
                container_coord = 1 - key_coord
                key, container = (pair[key_coord], pair[container_coord])
                key_path = next((q for q in _v13_subpaths(container, key) if q), None)
                if key_path is None:
                    continue
                for si, (_sp, tail, step_a, step_b) in enumerate(steps):
                    recover = (step_a, step_b)[key_coord]
                    other = (step_a, step_b)[container_coord]
                    x_path = next(_v13_subpaths(recover, 'x'), None)
                    tail_path = next((q for q in _v13_subpaths(container, tail) if q), None)
                    other_path = next((q for q in _v13_subpaths(container, other) if q), None)
                    if x_path is not None and tail_path is not None and (other_path is not None):
                        recursive = (key_coord, container_coord, key_path, si, tail_path, other_path, x_path)
                        break
                if recursive:
                    break
            if recursive is None:
                continue
        else:
            get = _v13_selector(out_path[1:], 'a' if out_path[0] == 0 else 'b')
        hs = [h for _, h, _, _ in steps]
        bind = ' '.join(sv + hs)
        qnames = [f'q_{z}' for z in sv + hs]
        qren = dict(zip(sv + hs, qnames))
        qprems = [f'Step {_v13_pterm(_v13_subst(a, qren))} {_v13_pterm(_v13_subst(b, qren))} {qren[h]}' for _path, h, a, b in steps]
        premises = '\n'.join((f'      (s{i} : Step {_v13_pterm(a)} {_v13_pterm(b)} {h})' for i, (_, h, a, b) in enumerate(steps)))
        shape_fields = ', '.join(sv + hs + [f's{i}' for i in range(len(steps))] + ['rfl', 'rfl', 'rfl'])
        lean = f"""mutual\ninductive Code : CM → CM → CM → Prop\n  | law ({bind} : CM)\n{premises} :\n      Code {_v13_pterm(ra)} {_v13_pterm(rb)} x\ninductive Step : CM → CM → CM → Prop\n  | raw (a b : CM) : Step a b (p a b)\n  | hit {{a b o : CM}} (h : Code a b o) : Step a b o\nend\ntheorem code_shape {{a b o : CM}} (h : Code a b o) :\n    ∃ {' '.join(qnames)} : CM, {' ∧ '.join(qprems + [f'a = {_v13_pterm(_v13_subst(ra, qren))}', f'b = {_v13_pterm(_v13_subst(rb, qren))}', f"o = {qren['x']}"])} := by\n  exact match h with\n  | .law {' '.join(sv + hs + [f's{i}' for i in range(len(steps))])} => ⟨{shape_fields}⟩\n"""
        ix = (ra, rb, 'x')

        def invariant_pairs():
            pairs = {(i, j) for i in range(3) for j in range(3) if i != j}

            def proves(want, assumed):

                def branch(k, env, rows):
                    if k == len(steps):
                        tri = tuple((_v13_replace_vars(z, env) for z in ix))
                        rs = list(rows) + [_v13_size_row(tri[want[1]], tri[want[0]], 0)]
                        names = {v for r, _c in rs for v in r}
                        rs += [({v: -1}, 0) for v in names]
                        return _v13_infeasible(rs)
                    _path, h, a, b = steps[k]
                    a, b = (_v13_replace_vars(a, env), _v13_replace_vars(b, env))
                    raw = dict(env)
                    raw[h] = (a, b)
                    if not branch(k + 1, raw, rows):
                        return False
                    tri = (a, b, h)
                    hit_rows = list(rows) + [_v13_size_row(tri[i], tri[j]) for i, j in assumed]
                    return branch(k + 1, env, hit_rows)
                return branch(0, {}, [])
            while True:
                nxt = {q for q in pairs if proves(q, pairs)}
                if nxt == pairs:
                    return sorted(pairs)
                pairs = nxt
        size_pairs = [(recursive[0], recursive[1]), (2, recursive[1])] if recursive else invariant_pairs()
        if not size_pairs:
            continue
        bridge_pair = next((q for q in ((0, 1), (1, 0)) if q in size_pairs), None)
        mutual_bound = False

        def bt(i):
            return ('sz a', 'sz b', 'sz o')[i]
        bounds = ' ∧ '.join((f'{bt(i)} < {bt(j)}' for i, j in size_pairs))
        structural_bounds = []
        for small, large in size_pairs:
            path = next((q for q in _v13_subpaths(ix[large], ix[small]) if q), None)
            if path is None:
                structural_bounds = []
                break
            structural_bounds.append(_v13_lt_proof(ix[large], path))

        def bound_tuple(xs):
            return xs[0] if len(xs) == 1 else f'⟨{xs[0]}, {bound_tuple(xs[1:])}⟩'

        def bound_tree(k, hitbounds, indent):
            pad = '  ' * indent
            if k == 0 and structural_bounds:
                return pad + 'exact ' + bound_tuple(structural_bounds)
            if k == len(steps):
                names = ' '.join(hitbounds)
                at = ' at ' + names + ' ⊢' if names else ''
                return pad + f'simp only [getOut, L, R, U, sz]{at} <;> omega'
            return pad + f'cases s{k} with\n' + pad + '| raw =>\n' + bound_tree(k + 1, hitbounds, indent + 1) + '\n' + pad + f'| hit s{k}h =>\n' + pad + f'  have s{k}hB := code_bounds s{k}h\n' + bound_tree(k + 1, hitbounds + [f's{k}hB'], indent + 1)
        if recursive:
            kc, cc, key_path, si, tail_path, other_path, x_path = recursive
            _sp, tail, step_a, step_b = steps[si]
            pair = (ra, rb)
            qpair = (_v13_subst(ra, qren), _v13_subst(rb, qren))
            recover, other = ((step_a, step_b)[kc], (step_a, step_b)[cc])
            qrecover, qother, qtail = (_v13_subst(z, qren) for z in (recover, other, tail))
            qcontainer = qpair[cc]
            key_lt = _v13_lt_proof(qcontainer, key_path)
            raw_container = _v13_replace_vars(qcontainer, {qtail: (_v13_subst(step_a, qren), _v13_subst(step_b, qren))})
            raw_lt = _v13_lt_proof(raw_container, next(_v13_subpaths(raw_container, qren['x'])))
            other_lt = _v13_lt_proof(qcontainer, other_path)
            inner_lt = f'Nat.lt_trans ({_v13_lt_proof(qrecover, x_path)}) (code_key_small h{si})' if x_path else f'code_key_small h{si}'
            key_name, container_name = ('a', 'b') if kc == 0 else ('b', 'a')
            hargs = '{a q b o : CM}' if kc == 0 else '{a b q o : CM}'
            hcode = 'Code a b o) (k : Code q b o) : a = q' if kc == 0 else 'Code a b o) (k : Code a q o) : b = q'
            step_unique_name = 'step_first_unique' if kc == 0 else 'step_second_unique'
            step_args_unique = '{a q b o : CM}' if kc == 0 else '{a b q o : CM}'
            step_sig = 'Step a b o) (k : Step q b o) : a = q' if kc == 0 else 'Step a b o) (k : Step a q o) : b = q'
            raw_small = 'sz_lt_p_right a b' if cc == 1 else 'sz_lt_p_left a b'
            raw_small_q = 'sz_lt_p_right q b' if cc == 1 else 'sz_lt_p_left a q'
            root_eq = 'hb.symm.trans kb' if cc == 1 else 'ha.symm.trans ka'
            rren = {z: 'r_' + z for z in qnames}
            rqtail, rqother = (_v13_subst(qtail, rren), _v13_subst(qother, rren))
            proj_x = f"congrArg (fun z => {_v13_selector(x_path, 'z')}) er" if x_path else 'er'
            lean += f"def getKey (c : CM) : CM := {_v13_selector(key_path, 'c')}\ntheorem code_key {{a b o : CM}} (h : Code a b o) : getKey {container_name} = {key_name} := by\n  cases h <;> rfl\ntheorem code_key_unique {hargs} (h : {hcode} :=\n  (code_key h).symm.trans (code_key k)\ntheorem code_key_small {{a b o : CM}} (h : Code a b o) : sz {key_name} < sz {container_name} := by\n  rcases code_shape h with ⟨{', '.join(qnames + [f's{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n  subst a\n  subst b\n  exact {key_lt}\ntheorem code_bounds {{a b o : CM}} (h : Code a b o) :\n    {bounds} := by\n  rcases code_shape h with ⟨{', '.join(qnames + [f's{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n  subst a\n  subst b\n  subst o\n  constructor\n  · exact {key_lt}\n  ·\n    cases s{si} with\n    | raw =>\n      exact {raw_lt}\n    | hit h{si} =>\n      exact Nat.lt_trans ({inner_lt}) ({other_lt})\ntheorem {step_unique_name} {step_args_unique} (h : {step_sig} := by\n  cases h with\n  | raw =>\n    cases k with\n    | raw => rfl\n    | hit hc =>\n      have hb := code_bounds hc\n      have hp := {raw_small}\n      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim\n  | hit hc =>\n    cases k with\n    | raw =>\n      have hb := code_bounds hc\n      have hp := {raw_small_q}\n      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim\n    | hit hk => exact code_key_unique hc hk\ntheorem code_unique {{a b o q : CM}} (h : Code a b o) (k : Code a b q) : o = q := by\n  rcases code_shape h with ⟨{', '.join(qnames + [f'hs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n  rcases code_shape k with ⟨{', '.join(('r_' + z for z in qnames)) + ', ' + ', '.join((f'rs{i}' for i in range(len(steps))))}, ka, kb, ko⟩\n  have et := congrArg (fun z => {_v13_selector(tail_path, 'z')}) ({root_eq})\n  have eo := congrArg (fun z => {_v13_selector(other_path, 'z')}) ({root_eq})\n  change {_v13_pterm(qtail)} = {_v13_pterm(rqtail)} at et\n  change {_v13_pterm(qother)} = {_v13_pterm(rqother)} at eo\n  rw [eo.symm, et.symm] at rs{si}\n  have er := {step_unique_name} hs{si} rs{si}\n  have ex : {qren['x']} = r_{qren['x']} := {proj_x}\n  exact ho.trans (ex.trans ko.symm)\n"
        else:
            mproofs = []
            if bridge_pair:
                bs, bl = bridge_pair
                for small, large in size_pairs:
                    st, lt = (ix[small], ix[large])
                    path = next((q for q in _v13_subpaths(lt, st) if q), None)
                    proof = _v13_lt_proof(lt, path) if path is not None else None
                    if proof is None:
                        for k, (_sp, h, sa, sb) in enumerate(steps):
                            tri = (sa, sb, h)
                            mid = (tri[2], tri[bl])
                            if tri[bs] != st:
                                continue
                            path = next((q for q in _v13_subpaths(lt, mid) if q), None)
                            if mid == lt:
                                proof = f'step_bound s{k}'
                            elif path is not None:
                                proof = f'Nat.lt_trans (step_bound s{k}) ({_v13_lt_proof(lt, path)})'
                            if proof is not None:
                                break
                    if proof is None:
                        mproofs = []
                        break
                    proof = proof.replace(' x', ' o')
                    mproofs.append(proof)
            if mproofs and (not structural_bounds):
                mutual_bound = True

                def and_proof(xs):
                    return xs[0] if len(xs) == 1 else f'⟨{xs[0]}, {and_proof(xs[1:])}⟩'
                bn = size_pairs.index(bridge_pair)
                bp = '(code_bounds hc)' + '.2' * bn + ('' if bn == len(size_pairs) - 1 else '.1')
                bp = bp.replace('code_bounds hc', 'code_bounds_core ⟨_, _, _, hc⟩')
                core_proofs = [re.sub('step_bound (s\\d+)', 'step_bound_core ⟨_, _, _, \\1⟩', q) for q in mproofs]
                av = ('a', 'b')
                lean += f"def getOut (a b : CM) : CM := {get}\ntheorem code_get {{a b o : CM}} (h : Code a b o) : getOut a b = o := by\n  cases h <;> rfl\ntheorem code_unique {{a b o q : CM}} (h : Code a b o) (k : Code a b q) : o = q :=\n  (code_get h).symm.trans (code_get k)\ndef CodeArg := (a : CM) ×' (b : CM) ×' (o : CM) ×' Code a b o\ndef StepArg := (a : CM) ×' (b : CM) ×' (o : CM) ×' Step a b o\nmutual\ntheorem code_bounds_core (q : CodeArg) :\n    {bounds.replace('a', 'q.1').replace('b', 'q.2.1').replace('o', 'q.2.2.1')} := by\n  rcases q with ⟨a, b, o, h⟩\n  rcases code_shape h with ⟨{', '.join(sv + hs + [f's{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n  subst a\n  subst b\n  subst x\n  exact {and_proof(core_proofs)}\ntermination_by sz q.1\ndecreasing_by simp_all [sz] <;> omega\ntheorem step_bound_core (q : StepArg) :\n    sz {('q.1', 'q.2.1')[bridge_pair[0]]} < sz (p q.2.2.1 {('q.1', 'q.2.1')[bridge_pair[1]]}) := by\n  rcases q with ⟨a, b, o, h⟩\n  cases h with\n  | raw => simp only [sz] <;> omega\n  | hit hc => exact Nat.lt_trans ({bp}) (sz_lt_p_right o {av[bridge_pair[1]]})\ntermination_by sz (p q.2.2.1 q.1)\ndecreasing_by simp_all only [sz] <;> omega\nend\ntheorem code_bounds {{a b o : CM}} (h : Code a b o) : {bounds} :=\n  code_bounds_core ⟨a, b, o, h⟩\ntheorem step_bound {{a b o : CM}} (h : Step a b o) :\n    sz {av[bridge_pair[0]]} < sz (p o {av[bridge_pair[1]]}) :=\n  step_bound_core ⟨a, b, o, h⟩\n"
            else:
                if structural_bounds:
                    qstruct = []
                    for small, large in size_pairs:
                        qlarge = _v13_subst(ix[large], qren)
                        path = next((q for q in _v13_subpaths(ix[large], ix[small]) if q))
                        qstruct.append(_v13_lt_proof(qlarge, path))
                    bound_body = f"  rcases code_shape h with ⟨{', '.join(qnames + [f's{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n  subst a\n  subst b\n  subst o\n  exact {bound_tuple(qstruct)}"
                else:
                    bound_cases = bound_tree(0, [], 1)
                    shape_fields = ', '.join(sv + hs + [f's{i}' for i in range(len(steps))] + ['ha', 'hb', 'ho'])
                    bound_body = f'  rcases code_shape h with ⟨{shape_fields}⟩\n  subst a\n  subst b\n  subst x\n{bound_cases}'
                if structural_bounds:
                    bounds_decl = f'theorem code_bounds {{a b o : CM}} (h : Code a b o) : {bounds} := by\n{bound_body}\n'
                else:
                    core_bounds = bounds.replace('a', 'q.1').replace('b', 'q.2.1').replace('o', 'q.2.2.1')

                    def structural_decrease(coord):
                        return all((any((path for path in _v13_subpaths(ix[coord], (sa, sb)[coord]))) for _sp, _h, sa, sb in steps))
                    termination_coord = 1 if structural_decrease(1) else 0
                    termination_measure = 'q.2.1' if termination_coord else 'q.1'
                    termination_tactic = 'decreasing_by simp_all only [sz] <;> omega' if termination_coord else 'decreasing_by\n  all_goals try subst o\n  all_goals simp_all only [sz] <;> omega'
                    langle, rangle = (chr(10216), chr(10217))
                    core_body = re.sub('code_bounds (s\\d+h)', lambda m: f'code_bounds_core {langle}_, _, _, {m.group(1)}{rangle}', bound_body)
                    unpack = f'{langle}a, b, o, h{rangle}'
                    packed = f'{langle}a, b, o, h{rangle}'
                    bounds_decl = f'def CodeArg :=\n  PSigma fun a : CM => PSigma fun b : CM => PSigma fun o : CM => Code a b o\ntheorem code_bounds_core (q : CodeArg) : {core_bounds} := by\n  rcases q with {unpack}\n{core_body}\ntermination_by sz {termination_measure}\n{termination_tactic}\ntheorem code_bounds {{a b o : CM}} (h : Code a b o) : {bounds} :=\n  code_bounds_core {packed}'
                lean += f'def getOut (a b : CM) : CM := {get}\ntheorem code_get {{a b o : CM}} (h : Code a b o) : getOut a b = o := by\n  cases h <;> rfl\ntheorem code_unique {{a b o q : CM}} (h : Code a b o) (k : Code a b q) : o = q :=\n  (code_get h).symm.trans (code_get k)\n{bounds_decl}\n'

        def bound_proj(pair, name='code_bounds hc'):
            n = size_pairs.index(pair)
            return f'({name})' + '.2' * n + ('' if n == len(size_pairs) - 1 else '.1')
        step_conflicts = {}
        for coord, label in ((0, 'first'), (1, 'second')):
            if (2, coord) not in size_pairs:
                continue
            theorem = f'step_ne_{label}'
            arg = 'a' if coord == 0 else 'b'
            step_conflicts[coord] = theorem
            lean += f'theorem {theorem} {{a b : CM}} : ¬ Step a b {arg} := by\n  intro h\n  cases h with\n  | hit hc =>\n    have hb := {bound_proj((2, coord))}\n    omega\n'
        step_bridge = bridge_pair
        for small, large in () if mutual_bound else ((0, 1), (1, 0)):
            if (small, large) in size_pairs:
                av = ('a', 'b')
                step_bridge = (small, large)
                lean += f'theorem step_bound {{a b o : CM}} (h : Step a b o) :\n    sz {av[small]} < sz (p o {av[large]}) := by\n  cases h with\n  | raw => simp [sz] <;> omega\n  | hit hc =>\n    have hb := {bound_proj((small, large))}\n    simp [sz] at hb ⊢ <;> omega\n'
                break
        simp_core = 'L, R, U, sz' if recursive else 'getOut, L, R, U, sz'
        lean += '\nnoncomputable def eval (a b : CM) : CM := by\n  classical\n  exact if h : ∃ o, Code a b o then Classical.choose h else p a b\ntheorem eval_hit {{a b o : CM}} (h : Code a b o) : eval a b = o := by\n  rw [eval, dif_pos ⟨o, h⟩]\n  exact code_unique (Classical.choose_spec ⟨o, h⟩) h\ntheorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by\n  rw [eval, dif_neg h]\ntheorem eval_step (a b : CM) : Step a b (eval a b) := by\n  by_cases h : ∃ o, Code a b o\n  · rcases h with ⟨o, hc⟩\n    rw [eval_hit hc]\n    exact Step.hit hc\n  · rw [eval_raw h]\n    exact Step.raw a b\n'
        step_args = []
        for i, (_path, h, a, b) in enumerate(steps):
            step_args.append(f's{i}')
        qsteps = [(f'qs{i}', qren[h], _v13_subst(a, qren), _v13_subst(b, qren)) for i, (_path, h, a, b) in enumerate(steps)]
        qra, qrb = (_v13_subst(ra, qren), _v13_subst(rb, qren))

        def cycle_leaf(aa, bb, qa, qb, pad):
            eqs = _v13_constraints(aa, qa)
            split = len(eqs)
            eqs += _v13_constraints(bb, qb)
            lines = []
            for z, (_a, _b, path) in enumerate(eqs):
                hyp = 'ha' if z < split else 'hb'
                basea, baseb = (aa, qa) if z < split else (bb, qb)
                lines += [pad + f'have e{z} := congrArg (fun q => {_v13_selector(path)}) {hyp}', pad + f'change {_v13_pterm(_v13_select_term(basea, path))} = {_v13_pterm(_v13_select_term(baseb, path))} at e{z}']
            got = _v13_unify_cycle_proof([(a0, b0, f'e{z}') for z, (a0, b0, _p) in enumerate(eqs)])
            if got is None:
                return None
            var, context, cyc = got
            path = _v13_occurrence_path(var, context)
            cyc = _v13_compact_cycle_proof(cyc)
            lines += [pad + f'have cyc : {_v13_pterm(var)} = {_v13_pterm(context)} := {cyc}', pad + f'have hlt : sz {_v13_pterm(var)} < sz {_v13_pterm(context)} := {_v13_lt_proof(context, path)}', pad + 'exact (Nat.ne_of_lt hlt) (congrArg sz cyc)']
            return '\n'.join(lines)
        step_no_first = False
        code_no_pair_left = False
        code_no_pair_right = False

        def split_steps(k, hits, env, aa, bb, indent, expanded=(), extra_eqs=(), stepfacts=(), negfacts=(), goal_out='o', negoutfacts=()):
            nonlocal allsteps
            pad = '  ' * indent

            def context_eqs():
                out = []

                def add(x, y, hyp):
                    for ea, eb, path in _v13_constraints(x, y):
                        proof = hyp if not path else f'congrArg (fun q => {_v13_selector(path)}) ({hyp})'
                        out.append((ea, eb, proof))
                add(_v13_replace_vars(aa, env), _v13_replace_vars(qra, env), 'ha')
                add(_v13_replace_vars(bb, env), _v13_replace_vars(qrb, env), 'hb')
                actual_out = goal_out if goal_out == 'o' else _v13_replace_vars(goal_out, env)
                add(actual_out, _v13_replace_vars(qren['x'], env), 'ho')
                for ea, eb, hp in extra_eqs:
                    add(_v13_replace_vars(ea, env), _v13_replace_vars(eb, env), hp)
                return out
            if k < len(allsteps) and step_conflicts:
                proof, hname, sa, sb = allsteps[k]
                so = _v13_replace_vars(hname, env)
                for coord, theorem in step_conflicts.items():
                    side = _v13_replace_vars(sa if coord == 0 else sb, env)
                    ep = _v13_unified_equality(context_eqs(), so, side)
                    if ep is not None:
                        return pad + f'have he : {_v13_pterm(so)} = {_v13_pterm(side)} := {ep}\n' + pad + f'exact {theorem} (by simpa only [he] using {proof})'
            if k == len(allsteps):
                aa0, bb0 = (_v13_replace_vars(aa, env), _v13_replace_vars(bb, env))
                qa, qb, qo = (_v13_replace_vars(qra, env), _v13_replace_vars(qrb, env), _v13_replace_vars(qren['x'], env))
                go0 = goal_out if goal_out == 'o' else _v13_replace_vars(goal_out, env)
                ceqs = context_eqs()
                for nn, noaa, nobb in negfacts:
                    noaa, nobb = (_v13_replace_vars(noaa, env), _v13_replace_vars(nobb, env))
                    for hp, ia, ib, io in hits:
                        ia, ib = (_v13_replace_vars(ia, env), _v13_replace_vars(ib, env))
                        ea = _v13_unified_equality(ceqs, ia, noaa)
                        eb = _v13_unified_equality(ceqs, ib, nobb)
                        if ea is not None and eb is not None:
                            return '\n'.join([pad + f'have ena : {_v13_pterm(ia)} = {_v13_pterm(noaa)} := {ea}', pad + f'have enb : {_v13_pterm(ib)} = {_v13_pterm(nobb)} := {eb}', pad + f'apply {nn}', pad + f'refine ⟨{_v13_pterm(io)}, ?_⟩', pad + f'simpa only [ena, enb] using {hp}'])
                pair_candidates = [('hc', aa0, bb0, go0)] + list(hits)
                for nn, noaa, noout in negoutfacts:
                    noaa, noout = (_v13_replace_vars(noaa, env), _v13_replace_vars(noout, env))
                    for hp, ia, ib, io in pair_candidates:
                        ia, ib, io = (_v13_replace_vars(ia, env), _v13_replace_vars(ib, env), _v13_replace_vars(io, env))
                        ea = _v13_unified_equality(ceqs, ia, noaa)
                        eo = _v13_unified_equality(ceqs, io, noout)
                        if ea is not None and eo is not None:
                            return '\n'.join([pad + f'have ena : {_v13_pterm(ia)} = {_v13_pterm(noaa)} := {ea}', pad + f'have eno : {_v13_pterm(io)} = {_v13_pterm(noout)} := {eo}', pad + f'apply {nn}', pad + f'refine ⟨{_v13_pterm(ib)}, ?_⟩', pad + f'simpa only [ena, eno] using {hp}'])
                for hp, ia, ib, io in pair_candidates:
                    ia, ib = (_v13_replace_vars(ia, env), _v13_replace_vars(ib, env))
                    nia, pia = _v13_normalization_proof(ia, _v13_proof_unifier(ceqs) or {})
                    nib, pib = _v13_normalization_proof(ib, _v13_proof_unifier(ceqs) or {})
                    if not isinstance(nia, tuple):
                        continue
                    for coord, theorem, enabled in ((0, 'code_no_pair_left', code_no_pair_left), (1, 'code_no_pair_right', code_no_pair_right)):
                        if not enabled or nib != nia[coord]:
                            continue
                        return '\n'.join([pad + f'have epa : {_v13_pterm(ia)} = {_v13_pterm(nia)} := {pia}', pad + f'have epb : {_v13_pterm(ib)} = {_v13_pterm(nib)} := {pib}', pad + f'apply {theorem} {_v13_pterm(nia[0])} {_v13_pterm(nia[1])}', pad + f'exact ⟨_, by simpa only [epa, epb] using {hp}⟩'])
                if isinstance(aa0, tuple):
                    pair_rules = ((0, 'code_no_pair_left', code_no_pair_left), (1, 'code_no_pair_right', code_no_pair_right))
                    for coord, theorem, enabled in pair_rules:
                        if not enabled:
                            continue
                        ek = _v13_unified_equality(ceqs, bb0, aa0[coord])
                        if ek is not None:
                            return '\n'.join([pad + f'have ek : {_v13_pterm(bb0)} = {_v13_pterm(aa0[coord])} := {ek}', pad + f'apply {theorem}', pad + 'refine ⟨_, ?_⟩', pad + 'simpa only [ek] using hc'])
                for nn, noaa, nobb in negfacts:
                    noaa, nobb = (_v13_replace_vars(noaa, env), _v13_replace_vars(nobb, env))
                    ea = _v13_unified_equality(ceqs, aa0, noaa)
                    eb = _v13_unified_equality(ceqs, bb0, nobb)
                    if ea is not None and eb is not None:
                        return '\n'.join([pad + f'have ena : {_v13_pterm(aa0)} = {_v13_pterm(noaa)} := {ea}', pad + f'have enb : {_v13_pterm(bb0)} = {_v13_pterm(nobb)} := {eb}', pad + f'apply {nn}', pad + 'refine ⟨_, ?_⟩', pad + 'simpa only [ena, enb] using hc'])
                structural = cycle_leaf(aa0, bb0, qa, qb, pad)
                if structural is not None:
                    return structural
                eqitems = context_eqs()
                merged_cycle = _v13_unify_cycle_proof(eqitems)
                if merged_cycle is not None:
                    var, context, cyc = merged_cycle
                    path = _v13_occurrence_path(var, context)
                    cyc = _v13_compact_cycle_proof(cyc)
                    return '\n'.join([pad + f'have cyc : {_v13_pterm(var)} = {_v13_pterm(context)} := {cyc}', pad + f'have hlt : sz {_v13_pterm(var)} < sz {_v13_pterm(context)} := {_v13_lt_proof(context, path)}', pad + 'exact (Nat.ne_of_lt hlt) (congrArg sz cyc)'])
                peqs = [(a0, b0, ()) for a0, b0, _hp in eqitems]
                rows = [_v13_size_row(aa0, qa, 0), _v13_size_row(qa, aa0, 0), _v13_size_row(bb0, qb, 0), _v13_size_row(qb, bb0, 0)]
                for ea, eb, _p in peqs:
                    rows += [_v13_size_row(ea, eb, 0), _v13_size_row(eb, ea, 0)]
                rows += [_v13_size_row((qa, qb, qo)[i], (qa, qb, qo)[j]) for i, j in size_pairs]
                if step_bridge:
                    small, large = step_bridge
                    for _bn, out, sa, sb in stepfacts:
                        tri = tuple((_v13_replace_vars(z, env) for z in (sa, sb, out)))
                        rows.append(_v13_size_row(tri[small], (tri[2], tri[large])))
                for _hp, ia, ib, io in hits:
                    tri = tuple((_v13_replace_vars(z, env) for z in (ia, ib, io)))
                    rows += [_v13_size_row(tri[i], tri[j]) for i, j in size_pairs]
                names0 = {v for r, _c in rows for v in r}
                rows += [({v: -1}, 0) for v in names0]
                if not _v13_infeasible(rows):
                    todo = next((h for h in hits if h[0] not in expanded), None)
                    if todo is None or len(expanded) >= tableau_depth:
                        return None
                    hp, ia, ib, io = todo
                    d = len(expanded)
                    vals = [f'u{d}_{z}' for z in sv + hs]
                    eren = dict(zip(sv + hs, vals))
                    estep_names = [f'u{d}s{i}' for i in range(len(steps))]
                    eqa, eqb, eqo = (f'u{d}a', f'u{d}b', f'u{d}o')
                    fresh = [(estep_names[i], eren[h], _v13_subst(a, eren), _v13_subst(b, eren)) for i, (_path, h, a, b) in enumerate(steps)]
                    new_eqs = tuple(extra_eqs) + ((ia, _v13_subst(ra, eren), eqa), (ib, _v13_subst(rb, eren), eqb), (io, eren['x'], eqo))
                    learned = None
                    proof_eqs = list(eqitems) + list(new_eqs)
                    for sp, so, sa, sb in fresh:
                        for coord, theorem in step_conflicts.items():
                            side = sa if coord == 0 else sb
                            ep = _v13_unified_equality(proof_eqs, so, side)
                            if ep is not None:
                                learned = (sp, so, side, theorem, ep)
                                break
                        if learned:
                            break
                    fields = ', '.join(vals + estep_names + [eqa, eqb, eqo])
                    if learned:
                        sp, so, side, theorem, ep = learned
                        return pad + f'rcases code_shape {hp} with ⟨{fields}⟩\n' + pad + f'have he : {_v13_pterm(so)} = {_v13_pterm(side)} := {ep}\n' + pad + f'exact {theorem} (by simpa only [he] using {sp})'
                    oldsteps = allsteps
                    allsteps = fresh
                    body = split_steps(0, hits, env, aa, bb, indent, expanded + (hp,), new_eqs, stepfacts, negfacts, goal_out, negoutfacts)
                    allsteps = oldsteps
                    if body is None:
                        return None
                    return pad + f'rcases code_shape {hp} with ⟨{fields}⟩\n' + body
                lines = [pad + 'have hcB := code_bounds hc']
                lines += [pad + f'have {h}B := code_bounds {h}' for h, _a, _b, _o in hits]
                if step_bridge:
                    lines += [pad + f'have {bn} := {bn}' for bn, _out, _sa, _sb in stepfacts]
                for z, (ea, eb, proof) in enumerate(eqitems):
                    lines += [pad + f'have p{z} := {proof}', pad + f'change {_v13_pterm(ea)} = {_v13_pterm(eb)} at p{z}', pad + f'have z{z} := congrArg sz p{z}']
                if tableau_depth:
                    names = ' '.join(['hcB'] + [f'{h}B' for h, _a, _b, _o in hits] + ([bn for bn, _o, _a, _b in stepfacts] if step_bridge else []) + [f'z{z}' for z in range(len(eqitems))])
                    lines += [pad + f'simp only [{simp_core}] at {names}', pad + 'omega']
                    return '\n'.join(lines)
                penv = {}
                for z, (ea, eb, _path) in enumerate(peqs):
                    if isinstance(ea, str) and ea not in penv and (not _v13_has_var(ea, eb)):
                        penv[ea] = (eb, f'p{z}')
                    elif isinstance(eb, str) and eb not in penv and (not _v13_has_var(eb, ea)):
                        penv[eb] = (ea, f'p{z}.symm')
                if isinstance(goal_out, str):
                    penv[goal_out] = (qo, 'ho')

                def bproj(name, n):
                    if len(size_pairs) == 1:
                        return name
                    return name + '.2' * n + ('' if n == len(size_pairs) - 1 else '.1')
                bineq = []
                for n, (i, j) in enumerate(size_pairs):
                    tri = (aa0, bb0, go0)
                    ui, pi = _v13_normalization_proof(tri[i], penv)
                    vj, pj = _v13_normalization_proof(tri[j], penv)
                    bineq.append((ui, vj, bproj('hcB', n), pi, pj, tri[i], tri[j]))
                for h, ia, ib, io in hits:
                    tri = tuple((_v13_replace_vars(z, env) for z in (ia, ib, io)))
                    for n, (i, j) in enumerate(size_pairs):
                        ui, pi = _v13_normalization_proof(tri[i], penv)
                        vj, pj = _v13_normalization_proof(tri[j], penv)
                        bineq.append((ui, vj, bproj(h + 'B', n), pi, pj, tri[i], tri[j]))

                def rewrites(name, ps):
                    qs = list(dict.fromkeys((p for p in ps if p != 'rfl')))
                    return [] if not qs else [pad + f"rw [{', '.join(qs)}] at {name}"]
                for u, v, hp, pu, pv, ou, ov in bineq:
                    if u == v:
                        lines += [pad + f'have hx := {hp}', *rewrites('hx', (pu, pv)), pad + f'have selflt : sz {_v13_pterm(u)} < sz {_v13_pterm(u)} := hx', pad + 'exact (Nat.lt_irrefl _ selflt).elim']
                        return '\n'.join(lines)
                    reverse = next((q for q in bineq if q[0] == v and q[1] == u), None)
                    if reverse:
                        lines += [pad + f'have hx : sz {_v13_pterm(u)} < sz {_v13_pterm(v)} := by', pad + f'  have q := {hp}', pad + f'  have eu : sz {_v13_pterm(ou)} = sz {_v13_pterm(u)} := congrArg sz ({pu})', pad + f'  have ev : sz {_v13_pterm(ov)} = sz {_v13_pterm(v)} := congrArg sz ({pv})', pad + f'  have q1 : sz {_v13_pterm(u)} < sz {_v13_pterm(ov)} := lt_of_eq_of_lt eu.symm q', pad + '  exact lt_of_lt_of_eq q1 ev', pad + f'have hy : sz {_v13_pterm(v)} < sz {_v13_pterm(u)} := by', pad + f'  have q := {reverse[2]}', pad + f'  have ev : sz {_v13_pterm(reverse[5])} = sz {_v13_pterm(v)} := congrArg sz ({reverse[3]})', pad + f'  have eu : sz {_v13_pterm(reverse[6])} = sz {_v13_pterm(u)} := congrArg sz ({reverse[4]})', pad + f'  have q1 : sz {_v13_pterm(v)} < sz {_v13_pterm(reverse[6])} := lt_of_eq_of_lt ev.symm q', pad + '  exact lt_of_lt_of_eq q1 eu', pad + 'exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim']
                        return '\n'.join(lines)
                direct = None
                for h, ia, ib, io in hits:
                    tri = tuple((_v13_replace_vars(z, env) for z in (ia, ib, io)))
                    norms = [_v13_normalization_proof(z, penv) for z in tri]
                    for n, (small, large) in enumerate(size_pairs):
                        ns, ps = norms[small]
                        nl, pl = norms[large]
                        path = next((q for q in _v13_subpaths(ns, nl) if q), None)
                        if path is None:
                            continue
                        rw_norm = [p for p in (pl, ps) if p != 'rfl']
                        direct = lines + [pad + f'have badlt : sz {_v13_pterm(tri[large])} < sz {_v13_pterm(tri[small])} := by', *([] if not rw_norm else [pad + f"  rw [{', '.join(rw_norm)}]"]), pad + f'  exact {_v13_lt_proof(ns, path)}', pad + f"exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) {bproj(h + 'B', n)}).elim"]
                        break
                    if direct is not None:
                        break
                if direct is not None:
                    return '\n'.join(direct)

                def inequality_cycle(rs):
                    adj = {}
                    for u, v, hp, pu, pv, ou, ov in rs:
                        adj.setdefault(u, []).append((v, hp, pu, pv, ou, ov))
                    for start in adj:
                        todo = [(start, [])]
                        seen = set()
                        while todo:
                            cur, chain = todo.pop()
                            if cur in seen:
                                continue
                            seen.add(cur)
                            for nxt, hp, pu, pv, ou, ov in adj.get(cur, []):
                                nc = chain + [(cur, nxt, hp, pu, pv, ou, ov)]
                                if nxt == start:
                                    return nc
                                todo.append((nxt, nc))
                cyc = inequality_cycle(bineq)
                if cyc:
                    cn = []
                    for n, (u, v, hp, pu, pv, ou, ov) in enumerate(cyc):
                        cn += [pad + f'have g{n} : sz {_v13_pterm(u)} < sz {_v13_pterm(v)} := by', pad + f'  have q := {hp}', pad + f'  have eu : sz {_v13_pterm(ou)} = sz {_v13_pterm(u)} := congrArg sz ({pu})', pad + f'  have ev : sz {_v13_pterm(ov)} = sz {_v13_pterm(v)} := congrArg sz ({pv})', pad + '  exact lt_of_eq_of_lt eu.symm (lt_of_lt_of_eq q ev)']
                    trans = 'g0'
                    for n in range(1, len(cyc)):
                        trans = f'Nat.lt_trans ({trans}) g{n}'
                    cn += [pad + f'have selflt := {trans}', pad + 'exact (Nat.lt_irrefl _ selflt).elim']
                    return '\n'.join(lines + cn)
                names = ' '.join(['hcB'] + [f'{h}B' for h, _a, _b, _o in hits] + [f'z{z}' for z in range(len(peqs))])
                lines.append(pad + f'simp only [{simp_core}] at {names}')
                lines.append(pad + 'omega')
                return '\n'.join(lines)
            proof, hname, sa, sb = allsteps[k]
            hit_name = proof + 'h'
            prefix = ''
            nextfacts = stepfacts
            if step_bridge:
                bn = proof + 'B'
                prefix = pad + f'have {bn} := step_bound {proof}\n'
                nextfacts += ((bn, hname, sa, sb),)
            nextneg = negfacts
            if step_no_first:
                nn = proof + 'N'
                prefix += pad + f'have {nn} := step_no_first {proof}\n'
                nextneg += ((nn, hname, sa),)
            nextout = negoutfacts
            if step_no_output:
                nn = proof + 'O'
                prefix += pad + f'have {nn} := step_no_output {proof}\n'
                nextout += ((nn, (hname, sa), sb),)
            rawenv = env.copy()
            rawenv[hname] = (_v13_replace_vars(sa, env), _v13_replace_vars(sb, env))
            rawcode = split_steps(k + 1, hits, rawenv, aa, bb, indent + 1, expanded, extra_eqs, nextfacts, nextneg, goal_out, nextout)
            hitcode = split_steps(k + 1, hits + [(hit_name, sa, sb, hname)], env, aa, bb, indent + 1, expanded, extra_eqs, nextfacts, nextneg, goal_out, nextout)
            if rawcode is None or hitcode is None:
                return None
            return prefix + pad + f'cases {proof} with\n' + pad + '| raw =>\n' + rawcode + '\n' + pad + f'| hit {hit_name} =>\n' + hitcode
        learned_first = None
        learned_first_direct = False
        learned_pair_left = None
        learned_pair_right = None
        learned_output = None
        step_no_output = False
        needs_output_horn = False
        for _path, na, nb in inactive:
            if not isinstance(nb, tuple):
                continue
            nv, nc = nb
            for _up, nu, nua, _nub in steps:
                if na != nu:
                    continue
                if any((vu == nv and va == nc and (vb == nua) for _vp, vu, va, vb in steps)):
                    needs_output_horn = True
                    break
            if needs_output_horn:
                break
        if len(steps) > 1:
            oldsteps = locals().get('allsteps', ())
            allsteps = qsteps
            learned_pair_left = split_steps(0, [], {}, ('v', 'k'), 'v', 1)
            allsteps = oldsteps
            if learned_pair_left is not None:
                lean += f"theorem code_no_pair_left (v k : CM) :\n    ¬ ∃ o, Code (p v k) v o := by\n  rintro ⟨o, hc⟩\n  rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n{learned_pair_left}\n"
                code_no_pair_left = True
            if needs_output_horn:
                oldsteps = locals().get('allsteps', ())
                allsteps = qsteps
                learned_pair_right = split_steps(0, [], {}, ('v', 'k'), 'k', 1)
                allsteps = oldsteps
            if learned_pair_right is not None:
                lean += f"theorem code_no_pair_right (v k : CM) :\n    ¬ ∃ o, Code (p v k) k o := by\n  rintro ⟨o, hc⟩\n  rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n{learned_pair_right}\n"
                code_no_pair_right = True
            oldsteps = locals().get('allsteps', ())
            allsteps = [('st', 'o', 'a', 'b')] + qsteps
            learned_first = split_steps(0, [], {}, 'o', 'a', 1, goal_out='u')
            allsteps = oldsteps
            if code_no_pair_left and learned_first is not None:
                hit = re.search('(?s)  \\| hit sth =>\\n(.*)\\Z', learned_first)
                if hit is not None:
                    learned_first = f"  cases st with\n  | raw =>\n    rintro ⟨u, hc⟩\n    exact code_no_pair_left a b ⟨u, hc⟩\n  | hit sth =>\n    rintro ⟨u, hc⟩\n    rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n{hit.group(1)}"
                    learned_first_direct = True
        if learned_first is not None:
            if code_no_pair_left and (2, 0) in size_pairs and ((1, 0) in size_pairs):
                out_small = bound_proj((2, 0), 'code_bounds sh')
                key_small = bound_proj((1, 0), 'code_bounds hk')
                lean += f'theorem step_no_first {{a b o : CM}} (st : Step a b o) :\n    ¬ ∃ u, Code o a u := by\n  cases st with\n  | raw => exact code_no_pair_left a b\n  | hit sh =>\n    rintro ⟨u, hk⟩\n    have ho := {out_small}\n    have ha := {key_small}\n    omega\n'
            else:
                learned_first_body = learned_first if learned_first_direct else f"  rintro ⟨u, hc⟩\n  rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n{learned_first}"
                lean += f'theorem step_no_first {{a b o : CM}} (st : Step a b o) :\n    ¬ ∃ u, Code o a u := by\n{learned_first_body}\n'
            step_no_first = True
        if len(steps) > 1 and needs_output_horn:
            oldsteps = locals().get('allsteps', ())
            allsteps = [('st', 'o', 'a', 'b')] + qsteps
            learned_output = split_steps(0, [], {}, ('o', 'a'), 'k', 1, goal_out='b')
            allsteps = oldsteps
        if learned_output is not None:
            lean += f"theorem step_no_output {{a b o : CM}} (st : Step a b o) :\n    ¬ ∃ k, Code (p o a) k b := by\n  rintro ⟨k, hc⟩\n  rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n{learned_output}\n"
            step_no_output = True

        def chain_horn_shortcut(a, b, deps):
            if not step_no_output or not isinstance(b, tuple) or (1, 0) not in size_pairs or ((2, 0) not in size_pairs):
                return None
            for ui in deps:
                _up, u, aa, ab = steps[ui]
                if a != u:
                    continue
                v, c = b
                vi = next((i for i in deps if steps[i][1] == v and steps[i][2] == c and (steps[i][3] == aa)), None)
                if vi is None:
                    continue

                def shape_eqs(env):
                    out = []

                    def add(x, y, hyp):
                        for ea, eb, path in _v13_constraints(_v13_replace_vars(x, env), _v13_replace_vars(y, env)):
                            proof = hyp if not path else f'congrArg (fun q => {_v13_selector(path)}) ({hyp})'
                            out.append((ea, eb, proof))
                    add(a, qra, 'ha')
                    add(b, qrb, 'hb')
                    add('o', qren['x'], 'ho')
                    return out
                raw_u = {u: (aa, ab)}
                chosen = None
                for qj, (_qproof, qo, qi, qk) in enumerate(qsteps):
                    eqs = shape_eqs(raw_u)
                    ein = _v13_unified_equality(eqs, _v13_replace_vars(qi, raw_u), _v13_replace_vars(b, raw_u))
                    eout = _v13_unified_equality(eqs, _v13_replace_vars(qo, raw_u), _v13_replace_vars(aa, raw_u))
                    if ein is not None and eout is not None:
                        chosen = (qj, qo, qi, qk, ein, eout)
                        break
                if chosen is None:
                    continue
                qj, qo, qi, qk, ein, eout = chosen
                raw_q = dict(raw_u)
                raw_q[qo] = (_v13_replace_vars(qi, raw_u), _v13_replace_vars(qk, raw_u))
                reqs = shape_eqs(raw_q)
                lhs = _v13_replace_vars(aa, raw_q)
                rhs = (_v13_replace_vars(b, raw_q), _v13_replace_vars(qk, raw_q))
                he = _v13_unified_equality(reqs, lhs, rhs)
                if he is None:
                    continue
                su, sv, qs = (f's{ui}', f's{vi}', f'qs{qj}')
                su_hit, q_hit = (su + 'h', qs + 'h')
                hu = bound_proj((2, 0), f'code_bounds {su_hit}')
                hk = bound_proj((1, 0), 'code_bounds hc')
                return f"  rintro ⟨o, hc⟩\n  rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩\n  have {sv}B := step_bound {sv}\n  have {sv}O := step_no_output {sv}\n  cases {su} with\n  | raw =>\n    cases {qs} with\n    | raw =>\n      have he : {_v13_pterm(lhs)} = {_v13_pterm(rhs)} := {he}\n      have hs := congrArg sz he\n      simp only [{simp_core}] at {sv}B hs\n      omega\n    | hit {q_hit} =>\n      have ein : {_v13_pterm(qi)} = {_v13_pterm(b)} := {ein}\n      have eout : {_v13_pterm(qo)} = {_v13_pterm(aa)} := {eout}\n      apply {sv}O\n      refine ⟨{_v13_pterm(qk)}, ?_⟩\n      simpa only [ein, eout] using {q_hit}\n  | hit {su_hit} =>\n    have hu := {hu}\n    have hk := {hk}\n    omega"
        badmask, nr_calls = (False, {})
        for j, (path, a, b) in enumerate(inactive):
            deps = [i for i, (_q, h, _c, _d) in enumerate(steps) if h in _v13_variables(a) + _v13_variables(b)]
            allsteps = [(f's{i}', steps[i][1], steps[i][2], steps[i][3]) for i in deps] + qsteps
            par = ' '.join(sv + [hs[i] for i in deps])
            spar = '\n'.join((f'    (s{i} : Step {_v13_pterm(c)} {_v13_pterm(d)} {h})' for i in deps for _q, h, c, d in [steps[i]]))
            shortcut = None
            if learned_first is not None:
                for i in deps:
                    _sp, h, c, _d = steps[i]
                    if a == h and b == c:
                        shortcut = f'  exact step_no_first s{i}\n'
                        break
            if shortcut is None:
                shortcut = chain_horn_shortcut(a, b, deps)
            treecode = shortcut or split_steps(0, [], {}, a, b, 1)
            if treecode is None:
                badmask = True
                break
            nr_calls[j] = ' '.join(sv + [hs[i] for i in deps] + [f's{i}' for i in deps])
            lean += f"""theorem nr{j} ({par} : CM)\n{spar} :\n    ¬ ∃ o, Code {_v13_pterm(a)} {_v13_pterm(b)} o := by\n{('' if shortcut else f"  rintro ⟨o, hc⟩{chr(10)}  rcases code_shape hc with ⟨{', '.join(qnames + [f'qs{i}' for i in range(len(steps))])}, ha, hb, ho⟩{chr(10)}")}{treecode}\n"""
        if badmask:
            continue

        def eval_syntax(t, path=()):
            if isinstance(t, str):
                return t
            return f'(eval {eval_syntax(t[0], path + (0,))} {eval_syntax(t[1], path + (1,))})'
        amap = {path: h for path, h, _a, _b in steps}

        def sym_eval(t, path=()):
            if isinstance(t, str):
                return t
            if path in amap:
                return amap[path]
            return f'(eval {sym_eval(t[0], path + (0,))} {sym_eval(t[1], path + (1,))})'
        args = ' '.join(sv)
        have_steps = []
        for i, (path, _h, _a, _b) in enumerate(steps):
            node = _v13_at_path(term, path)
            ea = eval_syntax(node[0], path + (0,))
            eb = eval_syntax(node[1], path + (1,))

            def side_eq(child, child_path, goal, name):
                start, cur, lines = (sym_eval(child, child_path), sym_eval(child, child_path), [])
                for j, (qpath, aa, bb) in enumerate(inactive):
                    if qpath[:len(child_path)] != child_path:
                        continue
                    lhs, rhs = (f'(eval {_v13_pterm(aa)} {_v13_pterm(bb)})', _v13_pterm((aa, bb)))
                    while lhs in cur:
                        ctx = cur.replace(lhs, 'q', 1)
                        new = cur.replace(lhs, rhs, 1)
                        ep = f'eval_raw (nr{j} {nr_calls[j]})'
                        pf = f'({ep})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({ep})'
                        lines.append(f"      {(cur if not lines else '_')} = {new} := {pf}")
                        cur = new
                if cur != _v13_pterm(goal):
                    return None
                head = f"  have {name} : {(ea if name.endswith('a') else eb)} = {_v13_pterm(goal)} := by\n    change {start} = {_v13_pterm(goal)}"
                if not lines:
                    return head + '\n    rfl'
                if len(lines) == 1:
                    return head + '\n    exact ' + lines[0].split(' := ', 1)[1]
                return head + '\n    calc\n' + '\n'.join(lines)
            pa = side_eq(node[0], path + (0,), _a, f'e{i}a')
            pb = side_eq(node[1], path + (1,), _b, f'e{i}b')
            if pa is None or pb is None:
                badmask = True
                break
            have_steps.append(f'  let H{i} := eval {ea} {eb}\n{pa}\n{pb}\n  have s{i} : Step {_v13_pterm(_a)} {_v13_pterm(_b)} H{i} := by\n    rw [← e{i}a, ← e{i}b]\n    exact eval_step {ea} {eb}')
        if badmask:
            continue
        raw_start, raw_cur = (sym_eval(term), sym_eval(term))
        raw_lines = []
        for j, (_path, aa, bb) in enumerate(visible_inactive):
            lhs, rhs = (f'(eval {_v13_pterm(aa)} {_v13_pterm(bb)})', _v13_pterm((aa, bb)))
            if lhs not in raw_cur:
                continue
            ctx = raw_cur.replace(lhs, 'q', 1)
            new = raw_cur.replace(lhs, rhs, 1)
            actual_j = inactive.index((_path, aa, bb))
            ep = f'eval_raw (nr{actual_j} {nr_calls[actual_j]})'
            pf = f'({ep})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({ep})'
            raw_lines.append(f"      {(raw_cur if not raw_lines else '_')} = {new} := {pf}")
            raw_cur = new
        if not raw_lines:
            raw_body = 'rfl'
        elif len(raw_lines) == 1:
            raw_body = raw_lines[0].split(' := ', 1)[1]
        else:
            raw_body = 'by\n    calc\n' + '\n'.join(raw_lines)
        raw_proof = f'  have rawEq : {raw_start} = {raw_cur} := ' + raw_body
        ctor = ' '.join(sv + hs + step_args)
        lean += f"theorem source_holds ({args} : CM) :\n    {_v13_pterm(left)} = {eval_syntax(right)} := by\n{chr(10).join(have_steps)}\n  change {_v13_pterm(left)} = {raw_start}\n{raw_proof}\n  exact (eval_hit (Code.law {ctor})){('.symm.trans rawEq.symm' if not rev else '.trans rawEq')}\nnoncomputable instance instMagma2 : Magma CM where op := eval\n"
        found = _v13_trace_witness(target, ra, rb, sv, steps, formal_target)
        if found is None:
            continue
        tv, vals, nl, nr, target_nodes = found
        shape_args = ', '.join(qnames + [f's{j}' for j in range(len(steps))])
        shape_pat = chr(10216) + shape_args + ', ha, hb, ho' + chr(10217)
        raw_nodes = [(a, b) for a, b, _o, proof in target_nodes if proof is None]
        raw_index = {q: i for i, q in enumerate(dict.fromkeys(raw_nodes))}
        for (a, b), i in raw_index.items():
            ntbody = None
            if recursive:
                clash = _v13_structural_clash(a, qra)
                hyp, closed = ('ha', a)
                if clash is None:
                    clash = _v13_structural_clash(b, qrb)
                    hyp, closed = ('hb', b)
                if clash is not None:
                    path, node, got = clash
                    ntbody = f'  rcases code_shape hc with {shape_pat}\n  have bad := congrArg (fun q => {_v13_selector(path)}) {hyp}\n  change {_v13_cm_lean(got)} = {_v13_pterm(node)} at bad\n  cases bad'
                kc, cc, key_path = recursive[:3]
                key_value, container_value = ((a, b)[kc], (a, b)[cc])
                got = _v13_closed_pick(container_value, key_path)
                if ntbody is None and got != key_value:
                    refute = _v13_refute_closed_eq(got, key_value).replace('bad', 'hk')
                    ntbody = f'  have hk := code_key hc\n  change {_v13_cm_lean(got)} = {_v13_cm_lean(key_value)} at hk\n  exact {refute}'
            else:
                clash = _v13_structural_clash(a, qra)
                hyp, closed = ('ha', a)
                if clash is None:
                    clash = _v13_structural_clash(b, qrb)
                    hyp, closed = ('hb', b)
                if clash is not None:
                    path, node, got = clash
                    ntbody = f"  rcases code_shape hc with ⟨{', '.join(qnames + [f's{j}' for j in range(len(steps))])}, ha, hb, ho⟩\n  have bad := congrArg (fun q => {_v13_selector(path)}) {hyp}\n  change {_v13_cm_lean(got)} = {_v13_pterm(node)} at bad\n  cases bad"
            if ntbody is None:
                oldsteps = locals().get('allsteps', ())
                allsteps = [(f's{j}', qren[h], _v13_subst(c, qren), _v13_subst(d, qren)) for j, (_path, h, c, d) in enumerate(steps)]
                target_tableau = split_steps(0, [], {}, _v13_from_closed(a), _v13_from_closed(b), 1)
                allsteps = oldsteps
                if target_tableau is not None:
                    ntbody = f'  rcases code_shape hc with {shape_pat}\n' + target_tableau
            if ntbody is None:
                repeated = _v13_repeated_leaf_clash(a, qra, b, qrb)
                if repeated:
                    (h1, p1, v1), (h2, p2, v2), _leaf = repeated
                    if v1 != v2:
                        refute = _v13_refute_closed_eq(v1, v2)
                        ntbody = f'  rcases code_shape hc with {shape_pat}\n  have e1 := congrArg (fun q => {_v13_selector(p1)}) {h1}\n  have e2 := congrArg (fun q => {_v13_selector(p2)}) {h2}\n  have bad := e1.trans e2.symm\n  exact {refute}'
            if False and ntbody is None:
                ae, be = (_v13_from_closed(a), _v13_from_closed(b))
                left_eqs = _v13_constraints(ae, qra)
                eqs = left_eqs + _v13_constraints(be, qrb)
                cert = _v13_unify_cycle_proof([(x, y, f'e{j}') for j, (x, y, _p) in enumerate(eqs)])
                if cert is not None:
                    lines = [f'  rcases code_shape hc with {shape_pat}']
                    for j, (x, y, path) in enumerate(eqs):
                        hyp = 'ha' if j < len(left_eqs) else 'hb'
                        lines += [f'  have e{j} := congrArg (fun q => {_v13_selector(path)}) {hyp}', f'  change {_v13_pterm(x)} = {_v13_pterm(y)} at e{j}']
                    var, context, cyc = cert
                    path = _v13_occurrence_path(var, context)
                    cyc = _v13_compact_cycle_proof(cyc)
                    lines += [f'  have cyc : {_v13_pterm(var)} = {_v13_pterm(context)} := {cyc}', f'  have hlt : sz {_v13_pterm(var)} < sz {_v13_pterm(context)} := {_v13_lt_proof(context, path)}', '  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)']
                    ntbody = '\n'.join(lines)
            if ntbody is None:
                # A failed symbolic no-Code derivation is not a Lean proof.
                # Abandon this trace model before any certificate is emitted.
                return None
            lean += f'theorem nt{i} : ¬ ∃ o, Code {_v13_cm_lean(a)} {_v13_cm_lean(b)} o := by\n  rintro ⟨o, hc⟩\n{ntbody}\n'
        apps = ' '.join((_v13_cm_lean(z) for z in vals))
        tenv = dict(zip(tv, vals))

        def target_chain(t, goal):
            cur, lines = (_v13_closed_eval(t, tenv), [])
            for aa, bb, out, proof in target_nodes:
                lhs, rhs = (f'(eval {_v13_cm_lean(aa)} {_v13_cm_lean(bb)})', _v13_cm_lean(out))
                raw_i = raw_index[aa, bb] if proof is None else None
                while lhs in cur:
                    ctx = cur.replace(lhs, 'q', 1)
                    new = cur.replace(lhs, rhs, 1)
                    ep = f'eval_raw nt{raw_i}' if proof is None else f'eval_hit {proof}'
                    pf = f'({ep})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({ep})'
                    lines.append(f"        {(cur if not lines else '_')} = {new} := {pf}")
                    cur = new
            if cur != _v13_cm_lean(goal):
                raise ValueError('target rewrite drift')
            if len(lines) == 1:
                return (_v13_closed_eval(t, tenv), lines[0].split(' := ', 1)[1])
            return (_v13_closed_eval(t, tenv), 'by\n      calc\n' + '\n'.join(lines) if lines else 'rfl')
        lstart, lp = target_chain(target[0], nl)
        rstart, rp = target_chain(target[1], nr)
        refute = _v13_refute_closed_eq(nl, nr).replace('bad', 'bad2')
        lean += f'end CM\nend submission\nopen submission\nopen submission.CM\nnoncomputable def submission : Goal := by\n  refine ⟨CM, CM.instMagma2, ?_, ?_⟩\n  · intro {args}\n    exact CM.source_holds {args}\n  · intro target\n    have bad := target {apps}\n    have hl : {lstart} = {_v13_cm_lean(nl)} := {lp}\n    have hr : {rstart} = {_v13_cm_lean(nr)} := {rp}\n    have bad2 := hl.symm.trans (bad.trans hr)\n    exact {refute}\n'
        if skip:
            skip -= 1
            continue
        return 'import Lean.Elab.Tactic.Omega\n' + _v13_TCORE + lean

def _v13_trace_witness(target, root_a, root_b, srcvars=None, steps=None, formal_names=None):
    vs = list(formal_names) if formal_names is not None else _v13_formal_variables(target)
    chain = [_v13_E]
    for _ in range(10):
        chain.append(_v13_K(chain[-1]))
    atoms = [_v13_E, _v13_K(_v13_E), _v13_K(_v13_K(_v13_E)), _v13_K(_v13_K(_v13_K(_v13_E)))]
    rich = atoms[:]
    for _ in range(3):
        old = rich[:]
        rich += [_v13_K(x) for x in old] + [_v13_P(x, y) for x in old for y in old]
        rich = list(dict.fromkeys(rich))

    def ground(t, env):
        if isinstance(t, str):
            return env[t]
        return _v13_P(ground(t[0], env), ground(t[1], env))
    code_cache, active_codes = ({}, set())

    def solve_code(a, b, wanted=None, depth=0):
        if steps is None or depth > 16:
            return None
        key = (a, b, wanted)
        if key in code_cache:
            return code_cache[key]
        if key in active_codes:
            return None
        env = _v13_cm_match(root_a, a, {})
        if env is None:
            return None
        env = _v13_cm_match(root_b, b, env)
        if env is None:
            return None
        if wanted is not None:
            env = _v13_cm_match('x', wanted, env)
            if env is None:
                return None
        active_codes.add(key)
        hs = [q[1] for q in steps]

        def is_ground(t, e):
            return all((z in e for z in _v13_variables(t)))

        def search(e, remaining, proofs):
            if not remaining:
                e = dict(e)
                for z in srcvars + hs:
                    if z not in e:
                        e[z] = _v13_E
                if 'x' not in e:
                    e['x'] = _v13_E
                try:
                    if ground(root_a, e) != a or ground(root_b, e) != b:
                        return None
                    vals = [_v13_cm_lean(e[z]) for z in srcvars + hs]
                    ps = [proofs[i] for i in range(len(steps))]
                    return (e['x'], '(Code.law ' + ' '.join(vals + ps) + ')')
                except (KeyError, TypeError):
                    return None
            for i in remaining:
                _path, h, sa, sb = steps[i]
                rest = tuple((j for j in remaining if j != i))
                options = []
                if h in e:
                    eraw = _v13_cm_match((sa, sb), e[h], dict(e))
                    if eraw is not None:
                        try:
                            options.append((eraw, f'(Step.raw {_v13_cm_lean(ground(sa, eraw))} {_v13_cm_lean(ground(sb, eraw))})'))
                        except KeyError:
                            pass
                elif is_ground(sa, e) and is_ground(sb, e):
                    eraw = dict(e)
                    eraw[h] = _v13_P(ground(sa, e), ground(sb, e))
                    options.append((eraw, f'(Step.raw {_v13_cm_lean(ground(sa, e))} {_v13_cm_lean(ground(sb, e))})'))
                if is_ground(sa, e) and is_ground(sb, e):
                    ia, ib = (ground(sa, e), ground(sb, e))
                    sub = solve_code(ia, ib, e.get(h), depth + 1)
                    if sub is not None and (h not in e or e[h] == sub[0]):
                        ehit = dict(e)
                        ehit[h] = sub[0]
                        options.append((ehit, f'(Step.hit {sub[1]})'))
                for enext, proof in options:
                    pnext = dict(proofs)
                    pnext[i] = proof
                    answer = search(enext, rest, pnext)
                    if answer is not None:
                        return answer
            return None
        answer = search(env, tuple(range(len(steps))), {})
        active_codes.remove(key)
        code_cache[key] = answer
        return answer

    def ev(t, env, seen):
        if isinstance(t, str):
            return env[t]
        a, b = (ev(t[0], env, seen), ev(t[1], env, seen))
        hit = solve_code(a, b)
        if hit is None:
            out, proof = (_v13_P(a, b), None)
        else:
            out, proof = hit
        seen.append((a, b, out, proof))
        return out

    def try_vals(vals):
        seen = []
        try:
            env = dict(zip(vs, vals))
            a, b = (ev(target[0], env, seen), ev(target[1], env, seen))
        except ValueError:
            return None
        if a != b:
            return (vs, vals, a, b, seen)
    for pool in (atoms, chain, rich):
        for n in range(min(30000, len(pool) ** len(vs))):
            q, vals = (n, [])
            for _ in vs:
                vals.append(pool[q % len(pool)])
                q //= len(pool)
            answer = try_vals(vals)
            if answer is not None:
                return answer
    rng = random.Random(0)
    for _ in range(200000):
        answer = try_vals([rng.choice(rich) for _ in vs])
        if answer is not None:
            return answer

def _v13_closed_pick(t, path):
    for bit in path:
        if t[0] != 2:
            return _v13_E
        t = t[1 + bit]
    return t

def _v13_structural_clash(closed, pattern):
    for path, node in _v13_internal_paths(pattern):
        got = _v13_closed_pick(closed, path)
        if got[0] != 2:
            return (path, node, got)

def _v13_repeated_leaf_clash(a, pa, b, pb):
    seen = {}

    def visit(closed, pattern, hyp, path=()):
        if isinstance(pattern, str):
            got = _v13_closed_pick(closed, path)
            if pattern in seen and seen[pattern][2] != got:
                return (seen[pattern], (hyp, path, got), pattern)
            seen[pattern] = (hyp, path, got)
            return None
        return visit(closed, pattern[0], hyp, path + (0,)) or visit(closed, pattern[1], hyp, path + (1,))
    return visit(a, pa, 'ha') or visit(b, pb, 'hb')

def _v13_closed_eval(t, env):
    if isinstance(t, str):
        return _v13_cm_lean(env[t])
    return f'(eval {_v13_closed_eval(t[0], env)} {_v13_closed_eval(t[1], env)})'

_v13_E = (0,)

def _v13_K(a):
    return (1, a)

def _v13_P(a, b):
    return (2, a, b)

def _v13_from_closed(t):
    if isinstance(t, str):
        return t
    if isinstance(t, int):
        return t
    if t[0] == 0:
        return ('E',)
    if t[0] == 1:
        return ('@', _v13_from_closed(t[1]))
    return (_v13_from_closed(t[1]), _v13_from_closed(t[2]))

def _v13_cm_match(pattern, value, env=None):
    env = {} if env is None else env
    if isinstance(pattern, tuple) and pattern and isinstance(pattern[0], int):
        return env if pattern == value else None
    if isinstance(pattern, str):
        if pattern in env:
            return env if env[pattern] == value else None
        env[pattern] = value
        return env
    if pattern == ('E',):
        return env if value == _v13_E else None
    if len(pattern) == 2 and pattern[0] == '@':
        if not isinstance(value, tuple) or len(value) != 2 or value[0] != 1:
            return None
        return _v13_cm_match(pattern[1], value[1], env)
    if not isinstance(value, tuple) or len(value) != 3 or value[0] != 2:
        return None
    env = _v13_cm_match(pattern[0], value[1], env)
    return None if env is None else _v13_cm_match(pattern[1], value[2], env)

def _v13_cm_lean(t):
    if t[0] == 0:
        return 'CM.e'
    if t[0] == 1:
        return f'(CM.k {_v13_cm_lean(t[1])})'
    return f'(CM.p {_v13_cm_lean(t[1])} {_v13_cm_lean(t[2])})'

_v13_CORE = 'import JudgeProblem\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\nnamespace submission\ninductive CM where\n  | e : CM\n  | k : CM → CM\n  | p : CM → CM → CM\nderiving DecidableEq\nnamespace CM\ndef eqb : CM → CM → Bool\n  | e, e => true\n  | e, k _ => false\n  | e, p _ _ => false\n  | k _, e => false\n  | k a, k b => eqb a b\n  | k _, p _ _ => false\n  | p _ _, e => false\n  | p _ _, k _ => false\n  | p a b, p c d =>\n      match eqb a c with\n      | true => eqb b d\n      | false => false\ntheorem band_true : {a b : Bool} → (a && b) = true → a = true ∧ b = true\n  | true, true, _ => ⟨rfl, rfl⟩\n  | false, _, h => Bool.noConfusion h\n  | true, false, h => Bool.noConfusion h\ntheorem eqb_self : (a : CM) → eqb a a = true\n  | e => rfl\n  | k a => eqb_self a\n  | p a b => by rw [eqb, eqb_self a, eqb_self b]\ntheorem eqb_eq : {a b : CM} → eqb a b = true → a = b\n  | e, e, _ => rfl\n  | e, k _, h => Bool.noConfusion h\n  | e, p _ _, h => Bool.noConfusion h\n  | k _, e, h => Bool.noConfusion h\n  | k a, k b, h => congrArg k (eqb_eq h)\n  | k _, p _ _, h => Bool.noConfusion h\n  | p _ _, e, h => Bool.noConfusion h\n  | p _ _, k _, h => Bool.noConfusion h\n  | p a b, p c d, h => by\n      change (match eqb a c with | true => eqb b d | false => false) = true at h\n      cases q : eqb a c with\n      | false =>\n        rw [q] at h\n        exact Bool.noConfusion h\n      | true =>\n        rw [q] at h\n        exact congrArg (fun z => p z b) (eqb_eq q) |>.trans\n          (congrArg (fun z => p c z) (eqb_eq h))\ndef L : CM → CM | e => e | k _ => e | p a _ => a\ndef R : CM → CM | e => e | k _ => e | p _ b => b\ndef U : CM → CM | e => e | k a => a | p _ _ => e\ndef sz : CM → Nat\n  | e => 0\n  | k a => sz a + 1\n  | p a b => (sz a + 1) + (sz b + 1)\ntheorem sz_lt_p_left (a b : CM) : sz a < sz (p a b) := by\n  change sz a < (sz a + 1) + (sz b + 1)\n  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))\n    (Nat.le_add_right (sz a + 1) (sz b + 1))\ntheorem sz_lt_p_right (a b : CM) : sz b < sz (p a b) := by\n  change sz b < (sz a + 1) + (sz b + 1)\n  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))\n    (Nat.le_add_left (sz b + 1) (sz a + 1))\n'

_v13_TCORE = _v13_CORE[:_v13_CORE.index('def eqb')] + _v13_CORE[_v13_CORE.index('def L'):]

_v13_CCORE = _v13_CORE[:_v13_CORE.index('def eqb')] + _v13_CORE[_v13_CORE.index('def L'):_v13_CORE.index('theorem sz_lt_p_left')]

def _v13_recompile_indexed_dag(lean, rule_arities, node_count):
    """Compile the source tableau to kernel-indexed, equality-free cases.

    `Code` is the single source of truth for rule inputs and outputs.  Raw
    branch contradictions are enumerated completely for every bound node and
    every Code constructor; they are not inferred from a lossy leaf cache.
    """
    code_match = re.search(
        r'inductive Code : CM → CM → CM → Prop\n(.*?)'
        r'(?=\n(?:attribute \[grind intro\] Code|@\[grind unfold\] abbrev C0|def CodeCases))',
        lean,
        re.DOTALL,
    )
    if code_match is None:
        return None
    code_ctors = [line for line in code_match.group(1).splitlines() if line.startswith('  | r')]
    if len(code_ctors) != len(rule_arities):
        return None
    eval_ctors = [line.replace(': Code ', ': EvalCases ', 1) for line in code_ctors]

    def split_terms(text):
        terms = []
        start = 0
        depth = 0
        for position, character in enumerate(text):
            if character == '(':
                depth += 1
            elif character == ')':
                depth -= 1
            elif character == ' ' and depth == 0:
                if start < position:
                    terms.append(text[start:position])
                start = position + 1
        if start < len(text):
            terms.append(text[start:])
        return terms

    no_code_helpers = []
    nf_code_helpers = []
    for rule, (line, arity) in enumerate(zip(code_ctors, rule_arities)):
        match = re.fullmatch(rf'  \| r{rule} \(([^)]*) : CM\) : Code (.*)', line)
        if match is None:
            return None
        variables = match.group(1).split()
        indices = split_terms(match.group(2))
        if len(variables) != arity or len(indices) != 3:
            return None
        no_code_helpers.append(
            f'theorem no_code_r{rule} '
            + '{' + ' '.join(variables) + ' : CM} '
            + f'(n : ¬ ∃ q, Code {indices[0]} {indices[1]} q) : False := '
            + f'n ⟨_, Code.r{rule} ' + ' '.join(variables) + '⟩'
        )
        nf_code_helpers.append(
            f'theorem nf_code_r{rule} '
            + '{' + ' '.join(variables) + ' : CM} '
            + f'(h : NF (p {indices[0]} {indices[1]})) : False := '
            + f'redex{rule}_not_nf ' + ' '.join(variables) + ' h'
        )
    bridge = ['theorem eval_cases_of_code {a b o : CM} (h : Code a b o) : EvalCases a b o := by', '  cases h with']
    for i, arity in enumerate(rule_arities):
        bridge.append(f"  | r{i} => exact .r{i}" + (' _' * arity))
    eval_block = (
        'inductive EvalCases : CM → CM → CM → Prop\n'
        + '\n'.join(eval_ctors)
        + '\n  | raw {a b : CM} (n : ¬ ∃ q, Code a b q) : EvalCases a b (p a b)\n'
        + '\n'.join(no_code_helpers) + '\n'
        + '\n'.join(nf_code_helpers) + '\n'
        + '\n'.join(bridge)
        + '\ntheorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by\n'
          '  by_cases h : ∃ o, Code a b o\n'
          '  · rw [eval, dif_pos h]\n'
          '    exact eval_cases_of_code (Classical.choose_spec h)\n'
          '  · rw [eval_raw h]\n'
          '    exact .raw h'
    )
    lean, count = re.subn(
        r'(?:inductive|def) EvalCases .*?\n(?=\n*theorem source_raw)',
        eval_block + '\n',
        lean,
        count=1,
        flags=re.DOTALL,
    )
    if count != 1:
        return None
    lean, count = re.subn(
        r'(?:@\[grind unfold\] abbrev C0|def CodeCases).*?(?=def NF)',
        '',
        lean,
        count=1,
        flags=re.DOTALL,
    )
    if count != 1:
        return None

    def remove_simpa_using(line):
        marker = 'by simpa only [*] using ('
        while marker in line:
            start = line.index(marker)
            opening = start + len(marker) - 1
            depth = 0
            closing = None
            for position in range(opening, len(line)):
                if line[position] == '(':
                    depth += 1
                elif line[position] == ')':
                    depth -= 1
                    if depth == 0:
                        closing = position
                        break
            if closing is None:
                return None
            line = line[:start] + line[opening + 1:closing] + line[closing + 1:]
        return line

    # The regular compiler names no intermediate evaluation results.  Indexed
    # dependent elimination needs variable indices, but deriving them does not
    # require another model/source-certificate search: every node is already
    # present as `B<i> := eval_cases a b`.  Reconstruct the same postorder DAG
    # mechanically and generalize each result exactly once.
    regular_nodes = []
    scan_source = False
    for original in lean.splitlines():
        if original.startswith('theorem source_raw'):
            scan_source = True
        elif scan_source and original.startswith('def Carrier'):
            scan_source = False
        if not scan_source:
            continue
        match = re.fullmatch(r'  have B(\d+) := eval_cases (.*)', original)
        if match is None:
            continue
        parts = split_terms(match.group(2))
        if len(parts) != 2:
            return None
        regular_nodes.append((int(match.group(1)), parts[0], parts[1]))
    if len(regular_nodes) != node_count or [index for index, _a, _b in regular_nodes] != list(range(node_count)):
        return None
    generalized_nodes = []
    result_terms = []
    for index, left, right in regular_nodes:
        for prior, result in enumerate(result_terms):
            left = left.replace(result, f'E{prior}')
            right = right.replace(result, f'E{prior}')
        result = f'(eval {left} {right})'
        result_terms.append(result)
        generalized_nodes.append((index, left, right, result))
    generalized_block = []
    for index, _left, _right, result in generalized_nodes:
        generalized_block.append(f'  generalize hE{index} : {result} = E{index}')
    for index, left, right, _result in generalized_nodes:
        generalized_block.append(
            f'  have B{index} : EvalCases {left} {right} E{index} := by '
            f'rw [← hE{index}]; exact eval_cases {left} {right}'
        )

    def nf_argument(term):
        internal = re.fullmatch(r'E(\d+)', term)
        if internal is not None:
            return f'N{internal.group(1)}'
        if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', term):
            return f'h{term}'
        return None

    lines = []
    seen_nodes = []
    source_active = False
    emitted_generalized_block = False
    for original in lean.splitlines():
        if original.startswith('theorem source_raw'):
            source_active = True
        if source_active and original.startswith('def Carrier'):
            lines.append('  all_goals first | rfl | omega | grind')
            lines.append('  all_goals done')
            source_active = False
        regular_b = re.fullmatch(r'  have B(\d+) := eval_cases (.*)', original) if source_active else None
        if regular_b is not None:
            if not emitted_generalized_block:
                lines.extend(generalized_block)
                emitted_generalized_block = True
            continue
        regular_n = re.fullmatch(r'  have N(\d+) : NF .* := (.*)', original) if source_active else None
        if regular_n is not None:
            index = int(regular_n.group(1))
            if index >= node_count:
                return None
            _node_index, left, right, _result = generalized_nodes[index]
            left_nf = nf_argument(left)
            right_nf = nf_argument(right)
            if left_nf is None or right_nf is None:
                return None
            lines.append(
                f'  have N{index} : NF E{index} := by '
                f'rw [← hE{index}]; exact eval_nf ({left_nf}) ({right_nf})'
            )
            continue
        split = re.match(r'  all_goals rcases B(\d+) with ', original) if source_active else None
        if split is not None:
            index = int(split.group(1))
            seen_nodes.append(index)
            # `rcases` implements dependent constructor equations by
            # substituting indices.  After an earlier split, an index can be a
            # rigid expression (`e`, `k _`, or `p _ _`) rather than a free
            # variable, which makes that substitution fail.  `cases` performs
            # the dependent elimination directly and safely removes impossible
            # constructors.  No later script may depend on names chosen for the
            # constructor fields.
            lines.append(f'  all_goals cases B{index}')
            lines.append('  all_goals first')
            for rule in range(len(rule_arities)):
                lines.append(f'  | exfalso; apply no_code_r{rule} <;> assumption')
            for rule in range(len(rule_arities)):
                lines.append(f'  | exfalso; apply nf_code_r{rule} <;> assumption')
            lines.append('  | rfl')
            lines.append('  | omega')
            lines.append('  | skip')
            continue
        if source_active and (
                original.strip() == 'all_goals try omega'
                or original.strip().startswith('all_goals try grind ')
                or original.strip().startswith('all_goals grind ')):
            continue
        if source_active and original.startswith('  | ') and 'Code.r' in original:
            # These hand-instantiated no-Code contradictions refer to the
            # fragile field names introduced by `rcases`.  The complete,
            # name-independent solve_by_elim rule below replaces all of them.
            continue
        if source_active and re.fullmatch(r'  \| have _ := \(.+\); omega', original):
            # Pure occurs leaves were rejected before this compiler is called.
            continue
        if source_active and original.strip() == '| simpa only [*]':
            original = original.replace('simpa only [*]', 'rfl')
        if source_active:
            original = remove_simpa_using(original)
            if original is None:
                return None
        lines.append(original)
    lean = '\n'.join(lines) + '\n'
    lean = re.sub(
        r'(?m)^(  \| exact )(n\d+ ⟨.*⟩)$',
        r'\1False.elim (\2)',
        lean,
    )
    for rule, arity in enumerate(rule_arities):
        lean = re.sub(
            rf'(?m)^(  \| exact False\.elim \(n\d+ ⟨_, Code\.r{rule})(?: [^⟩]*)?(⟩\))$',
            lambda match, arity=arity: match.group(1) + (' _' * arity) + match.group(2),
            lean,
        )
        redex = f'redex{rule}_not_nf'
        rewritten = []
        for line in lean.splitlines():
            marker = '(' + redex
            if marker in line:
                start = line.index(marker)
                depth = 0
                closing = None
                for position in range(start, len(line)):
                    if line[position] == '(':
                        depth += 1
                    elif line[position] == ')':
                        depth -= 1
                        if depth == 0:
                            closing = position
                            break
                if closing is None:
                    return None
                line = line[:start] + marker + (' _' * arity) + ')' + line[closing + 1:]
            rewritten.append(line)
        lean = '\n'.join(rewritten) + '\n'
    source_start = lean.find('theorem source_raw')
    source_end = lean.find('def Carrier', source_start)
    if source_start < 0 or source_end < 0:
        return None
    source_code = lean[source_start:source_end]
    forbidden = ('C0 ', 'CodeCases', 'simpa only [*]', 'subst_vars', 'have _ := (')
    if any(token in source_code for token in forbidden):
        return None
    if source_code.count('all_goals cases B') != node_count or 'all_goals done' not in source_code:
        return None
    if re.search(r'\bv\d+\b', source_code):
        # Indexed certificates must not depend on tactic-generated constructor
        # field names.  Reject instead of emitting a potentially ill-scoped
        # proof if a future regular compiler introduces a new such closure.
        return None
    return lean

def _v13_complete_model(source, target, nf_mode=False, operational=False, rule_limit=0, priority=False, structured=False, selection=0, step_kernel=False, residual_policy=0, explicit_nf=False, strict=False, strict_minimize=False, strict_semantic_minimize=False, strict_dag=False, strict_semantic_gate=False):
    global _v13_STRICT_LAST_MODEL, _v13_STRICT_LAST_SOURCE_CERT, _v13_STRICT_LAST_RULE_POOL
    if strict:
        _v13_STRICT_LAST_MODEL = None
        _v13_STRICT_LAST_SOURCE_CERT = None
        _v13_STRICT_LAST_RULE_POOL = None

    def walk(t, path=()):
        yield (path, t)
        if not isinstance(t, str):
            yield from walk(t[0], path + (0,))
            yield from walk(t[1], path + (1,))

    def put(t, path, value):
        if not path:
            return value
        q = put(t[path[0]], path[1:], value)
        return (q, t[1]) if path[0] == 0 else (t[0], q)

    def rvars(t, out=None):
        out = [] if out is None else out
        if isinstance(t, str):
            if t not in out:
                out.append(t)
        else:
            rvars(t[0], out)
            rvars(t[1], out)
        return out

    def unify(a, b):
        env, todo = ({}, [(a, b)])
        while todo:
            a, b = _v13_subst(todo.pop(), env)
            if a == b:
                continue
            if isinstance(a, str):
                if _v13_occurs(a, b, env):
                    return None
                env[a] = b
            elif isinstance(b, str):
                if _v13_occurs(b, a, env):
                    return None
                env[b] = a
            else:
                todo.extend(((a[0], b[0]), (a[1], b[1])))
        return env

    def match(pattern, term, env=None):
        env = {} if env is None else env
        if isinstance(pattern, str):
            if pattern in env:
                return env if env[pattern] == term else None
            env[pattern] = term
            return env
        if isinstance(term, str):
            return None
        env = match(pattern[0], term[0], env)
        return None if env is None else match(pattern[1], term[1], env)
    size_cache, count_cache, kbo_cache, normal_cache = ({}, {}, {}, {})

    def tsize(t):
        if t not in size_cache:
            size_cache[t] = 0 if isinstance(t, str) else 1 + tsize(t[0]) + tsize(t[1])
        return size_cache[t]

    def vcount(t):
        if t in count_cache:
            return count_cache[t]
        if isinstance(t, str):
            out = {t: 1}
        else:
            a, b = (vcount(t[0]), vcount(t[1]))
            out = {v: a.get(v, 0) + b.get(v, 0) for v in set(a) | set(b)}
        count_cache[t] = out
        return out

    def kbo_gt(a, b):
        key = (a, b)
        if key in kbo_cache:
            return kbo_cache[key]
        if a == b:
            result = False
        else:
            ca, cb = (vcount(a), vcount(b))
            if any((ca.get(v, 0) < n for v, n in cb.items())):
                result = False
            else:
                sa, sb = (tsize(a), tsize(b))
                if sa != sb:
                    result = sa > sb
                elif isinstance(a, str):
                    result = False
                elif isinstance(b, str):
                    result = True
                else:
                    result = kbo_gt(a[0], b[0]) if a[0] != b[0] else kbo_gt(a[1], b[1])
        kbo_cache[key] = result
        return result

    def root(t, rules):
        for left, right in rules:
            env = match(left, t)
            if env is not None:
                return _v13_subst(right, env)
        return t

    def normal(t, rules):
        key = (t, tuple(rules))
        if key in normal_cache:
            return normal_cache[key]
        if time.monotonic() >= _v13_DEADLINE:
            raise TimeoutError
        if isinstance(t, str):
            result = t
        else:
            reduced = (normal(t[0], rules), normal(t[1], rules))
            out = root(reduced, rules)
            if out == reduced:
                result = reduced
            else:
                if not kbo_gt(reduced, out):
                    raise ValueError
                result = normal(out, rules)
        normal_cache[key] = result
        return result

    def orient(a, b):
        if a == b:
            return None
        va, vb = (set(rvars(a)), set(rvars(b)))
        if vb <= va and kbo_gt(a, b):
            return (a, b)
        if va <= vb and kbo_gt(b, a):
            return (b, a)

    def canon_rule(rule):
        env = {}

        def go(t):
            if isinstance(t, str):
                if t not in env:
                    env[t] = f'q{len(env)}'
                return env[t]
            return (go(t[0]), go(t[1]))
        return (go(rule[0]), go(rule[1]))

    def deep(t, env, seen=frozenset()):
        if isinstance(t, str):
            if t not in env or t in seen:
                return t
            return deep(env[t], env, seen | {t})
        return (deep(t[0], env, seen), deep(t[1], env, seen))

    def unify_into(a, b, base):
        env, todo = (base.copy(), [(a, b)])
        while todo:
            a0, b0 = todo.pop()
            a0, b0 = (deep(a0, env), deep(b0, env))
            if a0 == b0:
                continue
            if isinstance(a0, str):
                if _v13_occurs(a0, b0, env):
                    return None
                env[a0] = b0
            elif isinstance(b0, str):
                if _v13_occurs(b0, a0, env):
                    return None
                env[b0] = a0
            else:
                todo.extend(((a0[0], b0[0]), (a0[1], b0[1])))
        return env

    def alpha_key(t):
        env = {}

        def go(q):
            if isinstance(q, str):
                if q not in env:
                    env[q] = f'z{len(env)}'
                return env[q]
            return (go(q[0]), go(q[1]))
        return go(t)
    source_vars = rvars(source[0])
    rvars(source[1], source_vars)

    def operation_residuals(rs):
        serial = [0]

        def dedup(states, cap=384):
            seen, out = (set(), [])
            for value, env, raw in states:
                value = deep(value, env)
                pack = value
                for v in reversed(source_vars):
                    pack = (deep(v, env), pack)
                key = (alpha_key(pack), raw)
                if key in seen:
                    continue
                seen.add(key)
                out.append((value, env, raw))
                if len(out) >= cap:
                    break
            return out

        def run(t, env):
            if time.monotonic() > deadline:
                raise TimeoutError
            if isinstance(t, str):
                return [(deep(t, env), env, False)]
            out = []
            for a, ea, _ in run(t[0], env):
                for b, eb, _ in run(t[1], ea):
                    if time.monotonic() > deadline:
                        raise TimeoutError
                    a, b = (deep(a, eb), deep(b, eb))
                    if not any((match(lhs, (a, b)) is not None for lhs, _ in rs)):
                        out.append(((a, b), eb, True))
                    for j, (lhs, rhs) in enumerate(rs):
                        serial[0] += 1
                        pre = f'h{serial[0]}_{j}'
                        ll, rr = (_v13_tag(lhs, pre), _v13_tag(rhs, pre))
                        ee = unify_into((a, b), ll, eb)
                        if ee is not None:
                            out.append((deep(rr, ee), ee, False))
                    if len(out) >= 768:
                        return dedup(out)
            return dedup(out)
        candidates = []
        for value, env, raw in run(term, {}):
            if not raw:
                continue
            rule = orient(deep(value, env), deep(outvar, env))
            if rule is None:
                continue
            rule = canon_rule(rule)
            if rule not in rs and rule not in candidates:
                candidates.append(rule)
        return sorted(candidates, key=lambda q: (tsize(q[1]), tsize(q[0]), repr(q)))
    left, right = source
    if isinstance(left, str) and (not isinstance(right, str)):
        term, outvar, reverse = (right, left, False)
    elif isinstance(right, str) and (not isinstance(left, str)):
        term, outvar, reverse = (left, right, True)
    else:
        return None
    first = orient(term, outvar)
    if not first:
        return None
    cache_key = (repr(source), operational, residual_policy if not strict or priority else 0, bool(strict_semantic_gate), bool(priority))
    cached_rules = _v13_COMPLETION_CACHE.get(cache_key)
    rules, deadline = ([q for q in cached_rules] if cached_rules is not None else [canon_rule(first)], min(_v13_DEADLINE, time.monotonic() + 3.0))
    completion_rule_cap = 64 if strict else 16
    ordered_beam_done = False
    try:
        if cached_rules is None and strict and priority and (residual_policy == -1) and (operational in (2, 3)):
            beam = [list(rules)]
            visited = set()
            winner = None
            for _depth in range(6):
                ranked = []
                for state in beam:
                    if time.monotonic() > deadline:
                        raise TimeoutError
                    state_key = tuple((canon_rule(rule) for rule in state))
                    if state_key in visited:
                        continue
                    visited.add(state_key)
                    check_rules = []
                    for check_left, check_right in state:
                        check_vars = rvars(check_left)
                        rvars(check_right, check_vars)
                        check_rules.append((check_left, check_right, check_vars))
                    check_stats = {}
                    check_cert = _v13_strict_source_certificate(term, outvar, check_rules, leaf_cap=250000, stats_sink=check_stats, priority=priority and (not explicit_nf))
                    if check_cert is not None:
                        winner = state
                        break
                    for residual in operation_residuals(state)[:8]:
                        child = state + [residual]
                        child_key = tuple((canon_rule(rule) for rule in child))
                        if child_key in visited:
                            continue
                        ranked.append((check_stats.get('open', 1 << 30), check_stats.get('leaves', 1 << 30), sum((tsize(a) + tsize(b) for a, b in child)), repr(child_key), child))
                if winner is not None:
                    break
                ranked.sort(key=lambda item: item[:-1])
                beam = [item[-1] for item in ranked[:64]]
                if not beam:
                    break
            if winner is None:
                _v13_STRICT_FAILURES.append(('ordered_residual_beam_open', (len(visited), len(beam))))
                return None
            rules = winner
            _v13_COMPLETION_CACHE[cache_key] = tuple(rules)
            ordered_beam_done = True
        if cached_rules is None and (not ordered_beam_done):
            agenda, head, residual_round = ([(0, 0)], 0, 0)
            for _round in range(16):
                while head < len(agenda) and operational != True:
                    i, j = agenda[head]
                    head += 1
                    left, right = rules[i]
                    other, out = rules[j]
                    a, b = (_v13_tag(left, f'a{i}_{j}'), _v13_tag(right, f'a{i}_{j}'))
                    c, d = (_v13_tag(other, f'b{i}_{j}'), _v13_tag(out, f'b{i}_{j}'))
                    if operational == 3 and (i != 0 or j != 0):
                        continue
                    if not strict:
                        occ = {}
                        for vp, vn in walk(a):
                            if isinstance(vn, str):
                                occ.setdefault(vn, []).append(vp)
                        for vv, _v13_paths in occ.items():
                            if len(_v13_paths) < 2 or len(_v13_paths) > 6:
                                continue
                            pindex = {p: n for n, p in enumerate(_v13_paths)}
                            for mask0 in (1 << bit for bit in range(len(_v13_paths))):
                                if time.monotonic() > deadline:
                                    raise TimeoutError

                                def mix(q, path=()):
                                    if isinstance(q, str):
                                        if q != vv:
                                            return q
                                        return d if mask0 & 1 << pindex[path] else c
                                    return (mix(q[0], path + (0,)), mix(q[1], path + (1,)))
                                x = normal(_v13_subst(b, {vv: c}), rules)
                                y = normal(mix(a), rules)
                                vrule = orient(x, y)
                                vrule = canon_rule(vrule) if vrule else None
                                if vrule and vrule not in rules:
                                    k = len(rules)
                                    rules.append(vrule)
                                    if len(rules) > completion_rule_cap:
                                        rules.pop()
                                        raise StopIteration
                                    for q in range(k + 1):
                                        agenda.append((k, q))
                                        if q != k:
                                            agenda.append((q, k))
                    if operational in (2, 3):
                        continue
                    for path, node in walk(a):
                        if time.monotonic() > deadline or len(agenda) > 4096:
                            raise TimeoutError
                        if isinstance(node, str):
                            continue
                        env = unify(node, c)
                        if env is None:
                            continue
                        x, y = (normal(_v13_subst(b, env), rules), normal(_v13_subst(put(a, path, d), env), rules))
                        rule = orient(x, y)
                        rule = canon_rule(rule) if rule else None
                        if rule and rule not in rules:
                            k = len(rules)
                            rules.append(rule)
                            if len(rules) > completion_rule_cap:
                                rules.pop()
                                raise StopIteration
                            for q in range(k + 1):
                                agenda.append((k, q))
                                if q != k:
                                    agenda.append((q, k))
                if strict and priority:
                    check_rules = []
                    for check_left, check_right in rules:
                        check_vars = rvars(check_left)
                        rvars(check_right, check_vars)
                        check_rules.append((check_left, check_right, check_vars))
                    if _v13_strict_source_certificate(term, outvar, check_rules, leaf_cap=250000, priority=priority and (not explicit_nf)) is not None:
                        break
                residuals = operation_residuals(rules) if not strict or priority else []
                if not residuals:
                    break
                choice = residual_policy // 4 ** residual_round % 4
                choice = min(choice, len(residuals) - 1)
                rules.append(residuals[choice])
                residual_round += 1
                k = len(rules) - 1
                if len(rules) > completion_rule_cap:
                    rules.pop()
                    raise StopIteration
                for q in range(k + 1):
                    agenda.append((k, q))
                    if q != k:
                        agenda.append((q, k))
            _v13_COMPLETION_CACHE[cache_key] = tuple(rules)
    except StopIteration:
        if strict:
            _v13_STRICT_FAILURES.append(('completion_rule_cap', len(rules)))
            _v13_COMPLETION_CACHE.pop(cache_key, None)
            return None
        _v13_COMPLETION_CACHE[cache_key] = tuple(rules)
    except (TimeoutError, ValueError, RecursionError) as error:
        if strict:
            _v13_STRICT_FAILURES.append(('completion_failed', type(error).__name__))
        return None
    cooked = []
    for i, (left, right) in enumerate(rules):
        vs = rvars(left)
        rvars(right, vs)
        env = {v: f'v{i}{j}' for j, v in enumerate(vs)}
        cooked.append((_v13_subst(left, env), _v13_subst(right, env), list(env.values())))
    rules = cooked
    if strict:
        _v13_STRICT_LAST_RULE_POOL = tuple(rules)
    if selection and rule_limit and (len(rules) > rule_limit):
        selection_key = (repr(source), repr(target), operational, residual_policy, rule_limit)
        ordered_subsets = _v13_SELECTION_CACHE.get(selection_key)
        atoms = ['A', 'B']
        pool = atoms + [(atoms[i], atoms[j]) for i in range(2) for j in range(2)]
        sv0 = rvars(source[0])
        rvars(source[1], sv0)
        tv0 = rvars(target[0])
        rvars(target[1], tv0)

        def probe(rs, equation, vs, cap):

            def pop(a, b):
                t = (a, b)
                for l, r, _ in rs:
                    e = match(l, t)
                    if e is not None:
                        return _v13_subst(r, e)
                return t

            def ev(t, env):
                return env[t] if isinstance(t, str) else pop(ev(t[0], env), ev(t[1], env))
            good = 0
            total = min(cap, len(pool) ** len(vs))
            for n in range(total):
                q, vals = (n, [])
                for _ in vs:
                    vals.append(pool[q % len(pool)])
                    q //= len(pool)
                env = dict(zip(vs, vals))
                good += ev(equation[0], env) == ev(equation[1], env)
            return (good, total)
        if ordered_subsets is None:
            beam = [(0,)]
            ranked = []
            for _ in range(1, rule_limit):
                nxt = set()
                for chosen in beam:
                    for j in range(1, len(rules)):
                        if j not in chosen:
                            nxt.add(tuple(sorted(chosen + (j,))))
                ranked = []
                for chosen in nxt:
                    rs = [rules[j] for j in chosen]
                    sh, st = probe(rs, source, sv0, 216)
                    th, tt = probe(rs, target, tv0, 96)
                    weight = sum((tsize(rules[j][1]) for j in chosen))
                    ranked.append(((sh, tt - th, -weight, -sum(chosen)), chosen))
                ranked.sort(reverse=True)
                beam = [q for _score, q in ranked[:32]]
            ordered_subsets = tuple((q for _score, q in ranked))
            _v13_SELECTION_CACHE[selection_key] = ordered_subsets
        if ordered_subsets:
            pick = ordered_subsets[min(selection - 1, len(ordered_subsets) - 1)]
            rules = [rules[j] for j in pick]
    elif rule_limit:
        rules = rules[:rule_limit]
    saturated_rules = list(rules)

    def prefix_ok(rs):

        def pop(a, b):
            t = (a, b)
            for l, r, _ in rs:
                e = match(l, t)
                if e is not None:
                    return _v13_subst(r, e)
            return t

        def pev(t, e):
            return e[t] if isinstance(t, str) else pop(pev(t[0], e), pev(t[1], e))
        pool, seen = (['A', 'B'], {'A', 'B'})
        for _ in range(3):
            old = list(pool)
            for a, b in itertools.product(old, repeat=2):
                z = pop(a, b)
                if z not in seen:
                    seen.add(z)
                    pool.append(z)
                if len(pool) >= 14:
                    break
            if len(pool) >= 14:
                break
        vv = _v13_variables(source[0])
        vv += [v for v in _v13_variables(source[1]) if v not in vv]
        total = min(12000, len(pool) ** len(vv))
        for n in range(total):
            q, vals = (n, [])
            for _ in vv:
                vals.append(pool[q % len(pool)])
                q //= len(pool)
            e = dict(zip(vv, vals))
            if pev(source[0], e) != pev(source[1], e):
                return False
        return True
    shortened = False
    if not prefix_ok(saturated_rules):
        if strict:
            _v13_STRICT_FAILURES.append(('bounded_source_failure', len(rules)))
        _v13_COMPLETION_CACHE.pop(cache_key, None)
        return None
    if nf_mode:
        rules = saturated_rules
        if not strict or strict_minimize:
            changed = True
            while changed:
                changed = False
                for i in range(len(rules) - 1, 0, -1):
                    raw = [(a, b) for j, (a, b, _v) in enumerate(rules) if j != i]
                    try:
                        nl = normal(rules[i][0], raw)
                    except (ValueError, RecursionError):
                        continue
                    if nl != rules[i][0]:
                        rules.pop(i)
                        changed = True

        def strict_completion_gate(completed, require_confluence=True):

            def reject(reason, detail=None):
                _v13_STRICT_FAILURES.append((reason, detail))
                return False
            raw = [(left, right) for left, right, _variables in completed]
            if not raw:
                return reject('empty_rules')
            for left, right in raw:
                if isinstance(left, str):
                    return reject('variable_lhs', left)
                if not set(rvars(right)) <= set(rvars(left)):
                    return reject('extra_rhs_variable', (left, right))
                if not kbo_gt(left, right):
                    return reject('not_kbo_decreasing', (left, right))
            if not require_confluence:
                return True
            try:
                for i, (left_i, right_i) in enumerate(raw):
                    left_i = _v13_tag(left_i, f'strict_l{i}_')
                    right_i = _v13_tag(right_i, f'strict_l{i}_')
                    for j, (left_j, right_j) in enumerate(raw):
                        left_j = _v13_tag(left_j, f'strict_r{i}_{j}_')
                        right_j = _v13_tag(right_j, f'strict_r{i}_{j}_')
                        for path, node in walk(left_i):
                            if isinstance(node, str):
                                continue
                            env = unify(node, left_j)
                            if env is None:
                                continue
                            upper = normal(_v13_subst(right_i, env), raw)
                            inner = normal(_v13_subst(put(left_i, path, right_j), env), raw)
                            if upper != inner:
                                return reject('ordinary_critical_pair', (i, j, path, upper, inner, raw))
                        occurrences = {}
                        for path, node in walk(left_i):
                            if isinstance(node, str):
                                occurrences.setdefault(node, []).append(path)
                        for variable, paths0 in occurrences.items():
                            if len(paths0) < 2:
                                continue
                            upper = normal(_v13_subst(right_i, {variable: left_j}), raw)
                            for changed_path in paths0:
                                mixed = _v13_subst(left_i, {variable: left_j})
                                mixed = put(mixed, changed_path, right_j)
                                if upper != normal(mixed, raw):
                                    return reject('nonlinear_variable_peak', (i, j, changed_path))
                if normal(source[0], raw) != normal(source[1], raw):
                    return reject('source_normal_forms_differ')
            except (ValueError, RecursionError, TimeoutError) as error:
                return reject('normalization_failed', type(error).__name__)
            return True

        def nf_closure_certificate(left0, right0, completed):
            raw_lefts = [left1 for left1, _right1, _vs1 in completed]

            def inherited(t):
                best0 = None
                for side0 in (0, 1):
                    for path0, node0 in walk(left0[side0]):
                        if node0 == t and (best0 is None or len(path0) < len(best0[1])):
                            best0 = (side0, path0)
                return best0

            def certify(t):
                route0 = inherited(t)
                if route0 is not None:
                    return ('subtree', route0)
                if isinstance(t, str):
                    return None
                ca, cb = (certify(t[0]), certify(t[1]))
                if ca is None or cb is None:
                    return None
                if any((unify(t, lhs0) is not None for lhs0 in raw_lefts)):
                    return None
                return ('pair', ca, cb)
            return certify(right0)
        semantic_source_cert = None
        if strict and strict_semantic_gate:
            for _repair_round in range(12):
                repairs, base_stats = ([], {})
                source_cert0 = _v13_strict_source_certificate(term, outvar, rules, leaf_cap=250000, repair_sink=repairs, stats_sink=base_stats, priority=priority and (not explicit_nf))
                if source_cert0 is not None:
                    semantic_source_cert = source_cert0
                    break
                existing = {canon_rule((a, b)) for a, b, _vs in rules}
                proposals = []
                for left0, wanted0 in repairs:
                    rights = [wanted0]
                    wanted_vars = rvars(wanted0)
                    left_vars = rvars(left0)
                    if wanted_vars and left_vars:
                        for values0 in itertools.islice(itertools.product(left_vars, repeat=len(wanted_vars)), 128):
                            rights.append(_v13_subst(wanted0, dict(zip(wanted_vars, values0))))
                    rights += [node for side0 in left0 for _path, node in walk(side0)]
                    for right0 in rights:
                        bases = [(left0, right0)]
                        keep0, fresh0 = (set(rvars(right0)), [0])

                        def abstract_irrelevant(t):
                            if not set(rvars(t)) & keep0:
                                value0 = f'__g{fresh0[0]}'
                                fresh0[0] += 1
                                return value0
                            if isinstance(t, str):
                                return t
                            return (abstract_irrelevant(t[0]), abstract_irrelevant(t[1]))
                        generalized0 = (abstract_irrelevant(left0), right0)
                        if generalized0 != bases[0]:
                            bases.insert(0, generalized0)
                        for base0 in bases:
                            proposal = canon_rule(base0)
                            if proposal in existing or proposal in proposals or (not kbo_gt(*proposal)) or (not set(rvars(proposal[1])) <= set(rvars(proposal[0]))):
                                continue
                            proposals.append(proposal)
                if not proposals:
                    _v13_STRICT_FAILURES.append(('semantic_repair_stalled', (len(repairs), tuple(repairs[:2]))))
                    break

                def cook_repair(proposal0, index0):
                    left0, right0 = proposal0
                    vs0 = rvars(left0)
                    rvars(right0, vs0)
                    rename0 = {v: f'v{index0}{j}' for j, v in enumerate(vs0)}
                    return (_v13_subst(left0, rename0), _v13_subst(right0, rename0), list(rename0.values()))
                best = None
                for left0, right0 in proposals[:96]:
                    if time.monotonic() >= deadline:
                        break
                    cooked0 = cook_repair((left0, right0), len(rules))
                    trial = rules + [cooked0]
                    if any((nf_closure_certificate(a, b, trial) is None for a, b, _vs in trial)):
                        continue
                    trial_stats = {}
                    trial_cert = _v13_strict_source_certificate(term, outvar, trial, leaf_cap=250000, stats_sink=trial_stats, priority=priority and (not explicit_nf))
                    score = (0 if trial_cert is not None else trial_stats.get('open', 1 << 30), trial_stats.get('leaves', 1 << 30), tsize(left0) + tsize(right0), repr(left0))
                    if best is None or score < best[0]:
                        best = (score, cooked0, trial_cert)
                    if trial_cert is not None:
                        break
                chosen = ([best[1]], best[2]) if best is not None and (best[2] is not None or best[0][0] <= base_stats.get('open', 0)) else None
                pair_best = None
                if chosen is None:
                    for pi, pj in itertools.combinations(proposals[:24], 2):
                        if time.monotonic() >= deadline:
                            break
                        cooked_i = cook_repair(pi, len(rules))
                        cooked_j = cook_repair(pj, len(rules) + 1)
                        trial = rules + [cooked_i, cooked_j]
                        if any((nf_closure_certificate(a, b, trial) is None for a, b, _vs in trial)):
                            continue
                        trial_stats = {}
                        trial_cert = _v13_strict_source_certificate(term, outvar, trial, leaf_cap=250000, stats_sink=trial_stats, priority=priority and (not explicit_nf))
                        pair_score = (0 if trial_cert is not None else trial_stats.get('open', 1 << 30), trial_stats.get('leaves', 1 << 30), sum((tsize(a) + tsize(b) for a, b in (pi, pj))), repr((pi, pj)))
                        if pair_best is None or pair_score < pair_best[0]:
                            pair_best = (pair_score, (cooked_i, cooked_j), trial_cert)
                        if trial_cert is not None:
                            break
                    if pair_best is not None and (pair_best[2] is not None or pair_best[0][0] <= base_stats.get('open', 0)):
                        chosen = (list(pair_best[1]), pair_best[2])
                if chosen is None:
                    _v13_STRICT_FAILURES.append(('semantic_repair_no_progress', (base_stats.get('open'), len(proposals), None if best is None else best[0][:3], None if pair_best is None else pair_best[0][:3])))
                    break
                rules.extend(chosen[0])
                if chosen[1] is not None:
                    semantic_source_cert = chosen[1]
                    break
                if len(rules) > completion_rule_cap:
                    del rules[completion_rule_cap:]
                    _v13_STRICT_FAILURES.append(('completion_rule_cap', len(rules) + 1))
                    break
        if strict and (not strict_completion_gate(rules, require_confluence=not strict_semantic_gate)):
            return None
        if strict and strict_semantic_minimize and (len(rules) > 1):
            minimized = None
            for count in range(1, len(rules)):
                for tail in itertools.combinations(range(1, len(rules)), count - 1):
                    candidate = [rules[i] for i in (0,) + tail]
                    candidate_routes = [nf_closure_certificate(left, right, candidate) for left, right, _variables in candidate]
                    if all((route is not None for route in candidate_routes)) and _v13_strict_source_certificate(term, outvar, candidate, priority=priority and (not explicit_nf)) is not None:
                        minimized = candidate
                        break
                if minimized is not None:
                    break
            if minimized is not None:
                rules = minimized
        routes = [nf_closure_certificate(left, right, rules) for left, right, _variables in rules]
        if strict and any((route is None for route in routes)):
            _v13_STRICT_FAILURES.append(('rhs_not_nf_closed', routes))
            return None
        source_cert = None if strict_dag else semantic_source_cert
        if strict and source_cert is None:
            node_count = len(_v13_internal_paths(term))
            reverse_order = tuple(reversed(range(node_count)))
            if strict_dag:
                source_cert = _v13_strict_source_certificate(term, outvar, rules, priority=priority and (not explicit_nf))
            else:
                structural = _v13_strict_source_certificate(term, outvar, rules, leaf_cap=_v13_STRUCTURAL_ORDER_PROBE_LEAVES, priority=priority and (not explicit_nf), order_override=reverse_order)
                if structural is not None and structural['closures']['nf'] * 16 < max(1, structural['leaves']):
                    source_cert = structural
                else:
                    breadth_first = _v13_strict_source_certificate(term, outvar, rules, priority=priority and (not explicit_nf))
                    source_cert = breadth_first or structural
            if source_cert is None:
                _v13_STRICT_FAILURES.append(('source_tableau_open', len(rules)))
                return None
        if strict:
            natural_order = tuple(range(source_cert['source_nodes']))
            reverse_order = tuple(reversed(natural_order))
            significant_nf = source_cert['closures']['nf'] * 16 >= max(1, source_cert['leaves'])
            should_search_order = strict_dag or significant_nf or tuple(source_cert['split_order']) != reverse_order
        if strict and should_search_order and (source_cert['states'] >= 500):
            natural_order = tuple(range(source_cert['source_nodes']))
            if natural_order != tuple(source_cert['split_order']):
                alternate = _v13_strict_source_certificate(term, outvar, rules, priority=priority and (not explicit_nf), order_override=natural_order)
                if alternate is not None and alternate['states'] < source_cert['states']:
                    source_cert = alternate
        if strict and should_search_order and (source_cert['states'] >= 100):
            natural_order = tuple(range(source_cert['source_nodes']))
            reverse_order = tuple(reversed(natural_order))
            root_first_natural = (reverse_order[0],) + natural_order[:-1] if natural_order else ()
            seed_orders = {tuple(source_cert['split_order']), natural_order, reverse_order, root_first_natural}
            candidate_orders = set(seed_orders)
            for seed in seed_orders:
                for position in range(len(seed) - 1):
                    trial = list(seed)
                    trial[position], trial[position + 1] = (trial[position + 1], trial[position])
                    candidate_orders.add(tuple(trial))
            for order0 in sorted(candidate_orders):
                if order0 == tuple(source_cert['split_order']):
                    continue
                alternate = _v13_strict_source_certificate(term, outvar, rules, priority=priority and (not explicit_nf), order_override=order0)
                if alternate is not None and alternate['states'] < source_cert['states']:
                    source_cert = alternate
            seen_orders = set(candidate_orders)
            for _round in range(2 * source_cert['source_nodes']):
                base_order = tuple(source_cert['split_order'])
                best = source_cert
                for position in range(len(base_order) - 1):
                    trial = list(base_order)
                    trial[position], trial[position + 1] = (trial[position + 1], trial[position])
                    order0 = tuple(trial)
                    if order0 in seen_orders:
                        continue
                    seen_orders.add(order0)
                    alternate = _v13_strict_source_certificate(term, outvar, rules, priority=priority and (not explicit_nf), order_override=order0)
                    if alternate is not None and alternate['states'] < best['states']:
                        best = alternate
                if best is source_cert:
                    break
                source_cert = best

        def ground(t, env):
            return env[t] if isinstance(t, str) else _v13_P(ground(t[0], env), ground(t[1], env))

        def hit(a, b):
            for i, (left, right, vs) in enumerate(rules):
                env = _v13_cm_match(left, _v13_P(a, b))
                if env is not None:
                    return (ground(right, env), i, env)

        def ev(t, env, steps):
            if isinstance(t, str):
                return env[t]
            a, b = (ev(t[0], env, steps), ev(t[1], env, steps))
            got = hit(a, b)
            value = got[0] if got else _v13_P(a, b)
            steps.append((a, b, got))
            return value
        tv = _v13_formal_variables(target)
        pool = [_v13_E]
        for _ in range(8):
            pool.append(_v13_K(pool[-1]))
        found = None
        for n in range(min(30000, len(pool) ** len(tv))):
            q, vals = (n, [])
            for _ in tv:
                vals.append(pool[q % len(pool)])
                q //= len(pool)
            steps, env = ([], dict(zip(tv, vals)))
            nl, nr = (ev(target[0], env, steps), ev(target[1], env, steps))
            if nl != nr and all((got is None for _a, _b, got in steps)):
                found = (vals, nl, nr, steps)
                break
        if not found:
            if strict:
                deterministic = None

                def dev(t, env, steps0):
                    if isinstance(t, str):
                        return env[t]
                    a0 = dev(t[0], env, steps0)
                    b0 = dev(t[1], env, steps0)
                    hits0 = []
                    for left0, right0, _vs0 in rules:
                        match0 = _v13_cm_match(left0, _v13_P(a0, b0))
                        if match0 is not None:
                            value0 = ground(right0, match0)
                            if value0 not in hits0:
                                hits0.append(value0)
                    if len(hits0) > 1:
                        raise ValueError('nondeterministic ground Code')
                    value0 = hits0[0] if hits0 else _v13_P(a0, b0)
                    steps0.append((a0, b0, value0 if hits0 else None))
                    return value0
                for n in range(min(30000, len(pool) ** len(tv))):
                    q, vals = (n, [])
                    for _ in tv:
                        vals.append(pool[q % len(pool)])
                        q //= len(pool)
                    steps0, env0 = ([], dict(zip(tv, vals)))
                    try:
                        nl0 = dev(target[0], env0, steps0)
                        nr0 = dev(target[1], env0, steps0)
                    except ValueError:
                        continue
                    if nl0 != nr0:
                        deterministic = (vals, nl0, nr0, steps0)
                        break
                if deterministic is not None:
                    _v13_STRICT_FAILURES.append(('deterministic_target_witness', sum((got is not None for _a, _b, got in deterministic[3]))))
                    found = deterministic
                elif source_cert is not None:
                    set_witness = None

                    def sev(t, env, memo0):
                        key0 = t
                        if key0 in memo0:
                            return memo0[key0]
                        if isinstance(t, str):
                            result0 = frozenset((env[t],))
                        else:
                            values0 = set()
                            for a0 in sev(t[0], env, memo0):
                                for b0 in sev(t[1], env, memo0):
                                    hits0 = []
                                    for left0, right0, _vs0 in rules:
                                        match0 = _v13_cm_match(left0, _v13_P(a0, b0))
                                        if match0 is not None:
                                            hits0.append(ground(right0, match0))
                                    values0.update(hits0 or (_v13_P(a0, b0),))
                                    if len(values0) > 256:
                                        raise OverflowError
                            result0 = frozenset(values0)
                        memo0[key0] = result0
                        return result0
                    for n in range(min(30000, len(pool) ** len(tv))):
                        q, vals = (n, [])
                        for _ in tv:
                            vals.append(pool[q % len(pool)])
                            q //= len(pool)
                        env0 = dict(zip(tv, vals))
                        try:
                            left_set = sev(target[0], env0, {})
                            right_set = sev(target[1], env0, {})
                        except OverflowError:
                            continue
                        if left_set.isdisjoint(right_set):
                            set_witness = (len(left_set), len(right_set))
                            break
                    if set_witness is not None:
                        _v13_STRICT_FAILURES.append(('set_disjoint_target_witness', set_witness))
            if not found and strict:
                _v13_STRICT_FAILURES.append(('no_target_witness', (len(rules), tuple(((a, b) for a, b, _vs in rules)))))
            if not found:
                return None
        if strict:
            _v13_STRICT_LAST_SOURCE_CERT = source_cert
            _v13_STRICT_LAST_MODEL = {'source': source, 'target': target, 'source_term': term, 'source_output': outvar, 'source_reversed': reverse, 'rules': tuple(((left, right, tuple(vs)) for left, right, vs in rules)), 'rhs_routes': tuple(routes), 'target_witness': found, 'source_certificate': source_cert}
        nf_macros = []
        if strict_dag:
            universe = [t for left, right, _ in rules for t in (left[0], left[1], right)]
            contexts = {}
            for top in universe:
                for _path, node in walk(top):
                    vs0 = rvars(node)
                    if isinstance(node, str) or len(vs0) != 1 or (not 2 <= tsize(node) <= 48):
                        continue
                    pattern = _v13_subst(node, {vs0[0]: '@'})
                    contexts[repr(pattern)] = pattern
            scored = []
            for pattern in contexts.values():
                count = sum((match(pattern, node) is not None for top in universe for _path, node in walk(top)))
                if count >= 2:
                    scored.append(((tsize(pattern) - 1) * (count - 1), pattern))
            nf_macros = [pattern for _score, pattern in sorted(scored, key=lambda item: (-item[0], tsize(item[1]), repr(item[1])))[:8]]
            nf_macros.sort(key=lambda term0: (tsize(term0), repr(term0)))

        def nf_pt0(t, upto):
            for j in range(upto - 1, -1, -1):
                env = match(nf_macros[j], t)
                if env is not None:
                    return f"(S{j} {nf_pt0(env['@'], upto)})"
            return t if isinstance(t, str) else f'(p {nf_pt0(t[0], upto)} {nf_pt0(t[1], upto)})'

        def nf_pt(t):
            return nf_pt0(t, len(nf_macros))
        nf_mdefs = '\n'.join((f"{('@[grind unfold] ' if strict_dag else '')}def S{i} (x : CM) : CM := {nf_pt0(_v13_subst(pattern, {'@': 'x'}), i)}" for i, pattern in enumerate(nf_macros)))

        def cmsz(t):
            if isinstance(t, str):
                return f'sz {t}'
            if strict_dag:
                return f'(({cmsz(t[0])}+1)+({cmsz(t[1])}+1))'
            return f'(({cmsz(t[0])} + 1) + ({cmsz(t[1])} + 1))'
        nf_szlemmas = ''
        ctors, clauses, cases, case_defs = ([], [], [], [])
        for i, (left, right, vs) in enumerate(rules):
            args = f" ({' '.join(vs)} : CM)" if vs else ''
            call = ' ' + ' '.join(vs) if vs else ''
            ctors.append(f'  | r{i}{args} : Code {nf_pt(left[0])} {nf_pt(left[1])} {nf_pt(right)}')
            bind = f"∃ {' '.join(vs)}, " if vs else ''
            facts = f'a = {nf_pt(left[0])} ∧ b = {nf_pt(left[1])} ∧ o = {nf_pt(right)} ∧ sz a = {cmsz(left[0])} ∧ sz b = {cmsz(left[1])} ∧ sz o = {cmsz(right)}'
            if strict_dag:
                cargs = f"({' '.join(vs)} : CM) " if vs else ''
                case_defs.append(f'@[grind unfold] abbrev C{i} {cargs}(a b o : CM) : Prop := {facts}')
                ccall = ' '.join(vs) + ' ' if vs else ''
                clause = bind + f'C{i} {ccall}a b o'
            else:
                clause = bind + facts
            clauses.append(clause)
            fields = ['_'] * len(vs) + ['rfl'] * 6
            body = 'Or.inr (' * i + ('' if i == len(rules) - 1 else 'Or.inl ') + f"⟨{', '.join(fields)}⟩" + ')' * i
            cases.append(f'  | r{i} => exact {body}')
        dcase = ' ∨ '.join(('(' + x + ')' for x in clauses))
        edef = ' ∨ '.join(('(' + x + ')' for x in clauses + ['o = p a b ∧ sz o = ((sz a + 1) + (sz b + 1)) ∧ ¬ ∃ q, Code a b q']))
        ecases = []
        for i, (_left, _right, vs) in enumerate(rules):
            fields = ['_'] * len(vs) + ['rfl'] * 6
            body = 'Or.inr (' * i + 'Or.inl ⟨' + ', '.join(fields) + '⟩' + ')' * i
            ecases.append(f'    | r{i} => exact {body}')
        eraw = 'Or.inr (' * len(rules) + '⟨eval_raw h, eq_sz (eval_raw h), h⟩' + ')' * len(rules)
        eval_cases_hit = '    exact Or.inl cc' if len(rules) == 1 else '    rcases cc with ' + ' | '.join((f'c{i}' for i in range(len(rules)))) + '\n' + '\n'.join(('    · exact ' + ('Or.inr (' * i + 'Or.inl c' + str(i) + ')' * i) for i in range(len(rules))))
        if strict_dag:
            eval_ctors, eval_hits = ([], [])
            for i, (left, right, vs) in enumerate(rules):
                args = f" ({' '.join(vs)} : CM)" if vs else ''
                call = ' ' + ' '.join(vs) if vs else ''
                facts = f'(h : C{i}{call} a b o)'
                eval_ctors.append(f'  | r{i}{args} {facts}: EvalCases a b o')
            eval_ctors.append('  | raw (h : o = p a b ∧ sz o = ((sz a + 1) + (sz b + 1))) (n : ¬ ∃ q, Code a b q) : EvalCases a b o')
            eval_hits = []
            for i, (_left, _right, vs) in enumerate(rules):
                names = [f'w{i}{j}' for j in range(len(vs))]
                pattern = names + [f'h{i}']
                call = ' ' + ' '.join(names) if names else ''
                eval_hits.append(f"    · rcases c{i} with ⟨{', '.join(pattern)}⟩\n      exact .r{i}{call} h{i}")
            eval_cases_hit_indexed = eval_hits[0].replace('    · ', '    ', 1) if len(rules) == 1 else '    rcases cc with ' + ' | '.join((f'c{i}' for i in range(len(rules)))) + '\n' + '\n'.join(eval_hits)
            eval_cases_code = f'inductive EvalCases (a b o : CM) : Prop\n{chr(10).join(eval_ctors)}\nattribute [grind cases] EvalCases\ntheorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by\n  by_cases h : ∃ o, Code a b o\n  · let o := Classical.choose h\n    have hc : Code a b o := Classical.choose_spec h\n    have cc := code_cases hc\n    have hv : eval a b = o := by rw [eval, dif_pos h]\n    rw [hv]\n    unfold CodeCases at cc\n{eval_cases_hit_indexed}\n  · exact .raw ⟨eval_raw h, eq_sz (eval_raw h)⟩ h'
        else:
            eval_cases_code = f'def EvalCases (a b o : CM) : Prop := {edef}\ntheorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by\n  by_cases h : ∃ o, Code a b o\n  · let o := Classical.choose h\n    have hc : Code a b o := Classical.choose_spec h\n    have cc := code_cases hc\n    have hv : eval a b = o := by rw [eval, dif_pos h]\n    rw [hv]\n    unfold CodeCases at cc\n{eval_cases_hit}\n  · exact {eraw}'
        nfcases, nflemmas, nfredex, nfexists = ([], [], [], [])
        rrefs = ', '.join((f'Code.r{i}' for i in range(len(rules))))
        for i, (left, right, vs) in enumerate(rules):
            args = f" ({' '.join(vs)} : CM)" if vs else ''
            call = ' ' + ' '.join(vs) if vs else ''
            nfredex.append(f'theorem redex{i}_not_nf{args} :\n    ¬ NF (p {nf_pt(left[0])} {nf_pt(left[1])}) := by\n  intro h\n  exact h.2.2 ⟨{nf_pt(right)}, Code.r{i}{call}⟩\n')

            def known_nf(t):
                best = None
                for side0 in (0, 1):
                    for path, node in walk(left[side0]):
                        if node == t and (best is None or len(path) < len(best[1])):
                            best = (side0, path)
                if best is None:
                    return None
                side0, path = best
                pr = 'ha' if side0 == 0 else 'hb'
                for bit in path:
                    pr += '.1' if bit == 0 else '.2.1'
                return pr
            fresh = []

            def nf_term(t):
                pr = known_nf(t)
                if pr is not None:
                    return pr
                if isinstance(t, str):
                    raise ValueError('RHS variable not in LHS')
                name = f'no{i}_{len(fresh)}'
                fresh.append((name, t[0], t[1]))
                return f"⟨{nf_term(t[0])}, {nf_term(t[1])}, {name}{(' ' if vs else '')}{' '.join(vs)} ha hb⟩"
            proof = nf_term(right)
            for name, aa, bb in fresh:
                nflemmas.append(f'theorem {name}{args} (ha : NF {_v13_pterm(left[0])}) (hb : NF {_v13_pterm(left[1])}) :\n    ¬ ∃ o, Code {_v13_pterm(aa)} {_v13_pterm(bb)} o := by\n  rintro ⟨o, h⟩\n  cases h <;> grind (config := {{ splits := 16, gen := 12 }}) [NF, L, R, U, sz]\n')
            nfcases.append(f'  | r{i} => exact {proof}')
        sv = _v13_variables(source[0])
        sv += [v for v in _v13_variables(source[1]) if v not in sv]

        def es(t):
            return t if isinstance(t, str) else f'(eval {es(t[0])} {es(t[1])})'
        ns = _v13_internal_paths(term)
        path_index = {path: i for i, (path, _t) in enumerate(ns)}

        def dag_value(t, path):
            return t if isinstance(t, str) else f'E{path_index[path]}'
        if strict_dag:
            generalizations = []
            bcase_lines = []
            for i, (path, t) in enumerate(ns):
                aa = dag_value(t[0], path + (0,))
                bb = dag_value(t[1], path + (1,))
                generalizations.append(f'  generalize hE{i} : eval {aa} {bb} = E{i}')
                bcase_lines.append(f'  have B{i} : EvalCases {aa} {bb} E{i} := by rw [← hE{i}]; exact eval_cases {aa} {bb}')
            bcases = '\n'.join(generalizations + bcase_lines)
        else:
            bcases = '\n'.join((f'  have B{i} := eval_cases {es(t[0])} {es(t[1])}' for i, (_path, t) in enumerate(ns)))
        hm = match(rules[0][0], term)
        if hm is None:
            return None
        hargs = ' '.join((_v13_pterm(hm[v]) for v in rules[0][2]))
        bcases += f'\n  have Hsrc : Code {_v13_pterm(term[0])} {_v13_pterm(term[1])} {_v13_pterm(outvar)} := .r0 {hargs}'

        def nfp(t, path=()):
            if isinstance(t, str):
                return 'h' + t
            if strict_dag:
                left_proof = ('h' + t[0]) if isinstance(t[0], str) else f'N{path_index[path + (0,)]}'
                right_proof = ('h' + t[1]) if isinstance(t[1], str) else f'N{path_index[path + (1,)]}'
                return f'eval_nf ({left_proof}) ({right_proof})'
            return f'eval_nf ({nfp(t[0])}) ({nfp(t[1])})'
        if strict_dag:
            nfacts = '\n'.join((f"  have N{i} : NF E{i} := by rw [← hE{i}]; exact {nfp(t, path)}" for i, (path, t) in enumerate(ns)))
        else:
            nfacts = '\n'.join((f"  have N{i} : NF {es(t)} := {nfp(t)}" for i, (_path, t) in enumerate(ns)))
        nfctx = 'NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, ' + ', '.join((f'redex{i}_not_nf' for i in range(len(rules)))) + ', ' + ', '.join((f'Code.r{i}' for i in range(len(rules)))) + (', ' + ', '.join((f'S{i}' for i in range(len(nf_macros)))) if nf_macros else '') + ', L, R, U, sz'
        rawctx = 'ne_p_left, ne_p_right, eq_sz, ' + ', '.join((f'Code.r{i}' for i in range(len(rules)))) + (', ' + ', '.join((f'S{i}' for i in range(len(nf_macros)))) if nf_macros else '') + ', L, R, U, sz'

        def eval_case_patterns(index):
            patterns = []
            for rule_index, (_left, _right, rule_vars) in enumerate(rules):
                if strict_dag:
                    fields = [f'v{index}{rule_index}{j}' for j in range(len(rule_vars))] + [f'{kind}{index}{rule_index}' for kind in ('a', 'b', 'o', 'x', 'y', 'z')]
                else:
                    fields = [f'b{index}_{rule_index}_{v}' for v in rule_vars] + [f'b{index}_{rule_index}_{kind}' for kind in ('a', 'b', 'o', 'sa', 'sb', 'so')]
                patterns.append('⟨' + ', '.join(fields) + '⟩')
            if strict_dag:
                patterns.append(f'⟨o{index}x, z{index}x, n{index}x⟩')
            else:
                patterns.append(f'⟨b{index}_raw_o, b{index}_raw_so, b{index}_raw_no⟩')
            return ' | '.join(patterns)
        rule_offsets = []
        total_rule_vars = 0
        for _left, _right, rule_vars in rules:
            rule_offsets.append(total_rule_vars)
            total_rule_vars += len(rule_vars)

        def short_leaf_var(index, rule_index, position):
            offset = rule_offsets[rule_index] + position
            return f'v{offset}{index}'
        split_macro = ''

        def split_call(index):
            patterns = []
            for ri, (_left, _right, rvs) in enumerate(rules):
                args = [short_leaf_var(index, ri, j) for j in range(len(rvs))]
                args += ['rfl', 'rfl', 'rfl', f's{index}a', f's{index}b', f's{index}o']
                patterns.append('⟨' + ', '.join(args) + '⟩')
            patterns.append(f'⟨rfl, s{index}x, n{index}⟩')
            return f'rcases B{index} with ' + ' | '.join(patterns)

        def leaf_ren(index, rule_index, rule_vars):
            return {v: short_leaf_var(index, rule_index, j) for j, v in enumerate(rule_vars)}
        leaf_scripts = []
        split_order = tuple(source_cert.get('split_order', reversed(range(len(ns)))))
        if strict_dag:
            abstract_nodes = []
            for i, (path, node) in enumerate(ns):
                abstract_nodes.append((dag_value(node[0], path + (0,)), dag_value(node[1], path + (1,)), f'E{i}'))

            def leaf_resolve(t, env, seen=None):
                seen = set() if seen is None else seen
                if isinstance(t, str):
                    if t not in env or t in seen:
                        return t
                    return leaf_resolve(env[t], env, seen | {t})
                return (leaf_resolve(t[0], env, seen), leaf_resolve(t[1], env, seen))

            def leaf_occurs(v, t, env):
                t = leaf_resolve(t, env)
                return t == v if isinstance(t, str) else leaf_occurs(v, t[0], env) or leaf_occurs(v, t[1], env)

            def leaf_solve(equations):
                env, todo, had_occurs = ({}, [(a, b) for a, b, _h in equations], False)
                while todo:
                    a, b = leaf_resolve(todo.pop(), env)
                    if a == b:
                        continue
                    if isinstance(a, str):
                        if leaf_occurs(a, b, env):
                            had_occurs = True
                            continue
                        env[a] = b
                    elif isinstance(b, str):
                        if leaf_occurs(b, a, env):
                            had_occurs = True
                            continue
                        env[b] = a
                    else:
                        todo.extend(((a[0], b[0]), (a[1], b[1])))
                return env, had_occurs

            def leaf_match(pattern, actual, bindings=None):
                bindings = {} if bindings is None else bindings
                if isinstance(pattern, str):
                    if pattern in bindings:
                        return bindings if bindings[pattern] == actual else None
                    bindings[pattern] = actual
                    return bindings
                if isinstance(actual, str):
                    return None
                bindings = leaf_match(pattern[0], actual[0], bindings)
                return None if bindings is None else leaf_match(pattern[1], actual[1], bindings)

            def leaf_redex(t):
                if isinstance(t, str):
                    return None
                for ri, (left, _right, rvs) in enumerate(rules):
                    bindings = leaf_match(left, t)
                    if bindings is not None:
                        return ((), ri, bindings, rvs)
                got = leaf_redex(t[0])
                if got is not None:
                    path, *tail = got
                    return ((0,) + path, *tail)
                got = leaf_redex(t[1])
                if got is not None:
                    path, *tail = got
                    return ((1,) + path, *tail)
            known_nf = [(v, 'h' + v) for v in sv]
            known_nf += [(f'E{i}', f'N{i}') for i in range(len(ns))]
            seen_scripts = set()
            leaf_scripts_by_depth = {}
            leaf_script_counts = {'goal': 0, 'raw': 0, 'nf': 0}
            indexed_open = 0

            def add_script(script, kind, depth):
                depth_scripts = leaf_scripts_by_depth.setdefault(depth, [])
                if script not in depth_scripts:
                    depth_scripts.append(script)
                if script not in seen_scripts:
                    seen_scripts.add(script)
                    leaf_scripts.append(script)
                    leaf_script_counts[kind] += 1

            def leaf_classify(equations, misses):
                solved, had_occurs = leaf_solve(equations)
                root = f'E{len(ns) - 1}'
                goal_left = root if source[0] == term else source[0]
                goal_right = root if source[1] == term else source[1]
                macro_names = ', '.join((f'S{i}' for i in range(len(nf_macros))))
                if leaf_resolve(goal_left, solved) == leaf_resolve(goal_right, solved):
                    return ('goal', 'first | rfl | omega | grind')
                for aa, bb, no_name in misses:
                    naa = leaf_resolve(aa, solved)
                    nbb = leaf_resolve(bb, solved)
                    pair = (naa, nbb)
                    for ri, (left, right, rvs) in enumerate(rules):
                        bindings = leaf_match(left, pair)
                        if bindings is None:
                            continue
                        args = ' '.join((nf_pt(bindings[v]) for v in rvs))
                        script = f'exfalso; apply {no_name}; refine ⟨{nf_pt(_v13_subst(right, bindings))}, Code.r{ri}' + (' ' + args if args else '') + '⟩'
                        return ('raw', script)
                for known, nf_name in known_nf:
                    normalized = leaf_resolve(known, solved)
                    redex = leaf_redex(normalized)
                    if redex is None:
                        continue
                    path, ri, bindings, rvs = redex
                    args = ' '.join((nf_pt(bindings[v]) for v in rvs))
                    call = f'redex{ri}_not_nf' + (' ' + args if args else '')
                    proof = nf_name
                    for side in path:
                        proof = ('nf_p_left' if side == 0 else 'nf_p_right') + f' ({proof})'
                    script = f'exact False.elim (({call}) ({proof}))'
                    return ('nf', script)
                if had_occurs:
                    return ('occurs', None)
                return (None, None)

            def leaf_visit(depth, equations, misses):
                kind, script = leaf_classify(equations, misses)
                nonlocal indexed_open
                if kind is not None:
                    if kind == 'occurs':
                        indexed_open += 1
                    else:
                        add_script(script, kind, depth)
                    return
                if depth == len(ns):
                    return
                index = split_order[depth]
                aa, bb, out = abstract_nodes[index]
                for ri, (left, right, rvs) in enumerate(rules):
                    ren = leaf_ren(index, ri, rvs)
                    leaf_visit(depth + 1, equations + [(aa, _v13_subst(left[0], ren), f'a{index}{ri}'), (bb, _v13_subst(left[1], ren), f'b{index}{ri}'), (out, _v13_subst(right, ren), f'o{index}{ri}')], misses)
                leaf_visit(depth + 1, equations + [(out, (aa, bb), f'o{index}x')], misses + [(aa, bb, f'n{index}x')])
            leaf_visit(0, [], [])
            source_cert['leaf_scripts'] = dict(leaf_script_counts)
            source_cert['leaf_scripts']['total'] = len(leaf_scripts)
            source_cert['indexed_open'] = indexed_open
            tree_counts = {'splits': 0, 'occurs': 0, 'scripts': 0, 'open': 0, 'scope_errors': 0}
            scope_error_details = []
            leaf_local_names = {f'n{i}' for i in range(len(ns))}
            leaf_local_names.update((short_leaf_var(i, ri, j) for i in range(len(ns)) for ri, (_left, _right, rvs) in enumerate(rules) for j in range(len(rvs))))

            def leaf_tree(depth, equations, misses, indent=2, bound=None):
                bound = set() if bound is None else bound
                kind, script = leaf_classify(equations, misses)
                if kind is not None:
                    if kind == 'occurs':
                        tree_counts['occurs'] += 1
                        tree_counts['open'] += 1
                        return [' ' * indent + 'contradiction']
                    else:
                        tree_counts['scripts'] += 1
                        refs = set(re.findall('\\b[A-Za-z][A-Za-z0-9_]*\\b', script)) & leaf_local_names
                        if not refs <= bound:
                            tree_counts['scope_errors'] += 1
                            if len(scope_error_details) < 20:
                                scope_error_details.append({'depth': depth, 'missing': tuple(sorted(refs - bound)), 'script': script})
                    return [' ' * indent + line for line in script.splitlines()]
                if depth == len(ns):
                    tree_counts['open'] += 1
                    return [' ' * indent + 'contradiction']
                tree_counts['splits'] += 1
                index = split_order[depth]
                aa, bb, out = abstract_nodes[index]
                branches = []
                for ri, (left, right, rvs) in enumerate(rules):
                    ren = leaf_ren(index, ri, rvs)
                    branches.append((equations + [(aa, _v13_subst(left[0], ren), f'a{index}{ri}'), (bb, _v13_subst(left[1], ren), f'b{index}{ri}'), (out, _v13_subst(right, ren), f'o{index}{ri}')], misses, set(ren.values())))
                branches.append((equations + [(out, (aa, bb), f'o{index}x')], misses + [(aa, bb, f'n{index}')], {f'n{index}'}))
                lines = [' ' * indent + split_call(index)]
                for branch_index, (child_equations, child_misses, child_bound) in enumerate(branches):
                    child = leaf_tree(depth + 1, child_equations, child_misses, indent + 1, bound | child_bound)
                    lines.append(' ' * indent + '· ' + child[0].strip())
                    lines.extend(child[1:])
                return lines
            leaf_tree_lines = leaf_tree(0, [], [])
            source_cert['leaf_tree'] = dict(tree_counts)
            if scope_error_details:
                source_cert['scope_error_details'] = scope_error_details
        layered_pruning = strict and (not strict_dag) and _v13_needs_layered_source_pruning(source_cert)
        nfsteps = []
        for i in split_order:
            name = f'B{i}'
            if explicit_nf:
                nfsteps.append('  all_goals rcases ' + name + ' with ' + eval_case_patterns(i))
            else:
                nfsteps.append('  all_goals rcases ' + name + ' with ' + ' | '.join([name] * (len(rules) + 1)))
            if not explicit_nf:
                nfsteps.append('  all_goals try simp_all only [NF]')
            elif strict:
                nfsteps.append('  all_goals try omega')
                if strict_dag and nf_szlemmas:
                    nfsteps.append('  all_goals try (simp only [' + ', '.join((f'sz_S{j}' for j in range(len(nf_macros)))) + '] at *; omega)')
                if layered_pruning:
                    nfsteps.append('  all_goals try grind (config := { splits := 1, gen := 6 }) [' + nfctx + ']')
            if not (strict and explicit_nf):
                nfsteps.append('  all_goals try grind (config := { splits := 10, gen := 10 }) [' + nfctx + ']')
        if strict and explicit_nf and (source_cert['leaves'] > 200) and (not strict_dag):
            nfsteps.append('  all_goals try grind (config := { splits := 4, gen := 12 }) [eq_sz, ne_p_left, ne_p_right, L, R, U, sz]')
        if strict_dag:
            shared_steps = []
            for depth, i in enumerate(split_order, 1):
                shared_steps.append('  all_goals ' + split_call(i))
                scripts0 = leaf_scripts_by_depth.get(depth, ())
                if scripts0:
                    shared_steps.append('  all_goals first')
                    for script0 in scripts0:
                        script_lines = script0.splitlines()
                        shared_steps.append('  | ' + script_lines[0])
                        shared_steps.extend(('    ' + line for line in script_lines[1:]))
                    shared_steps.append('  | skip')
            shared_steps.append('  all_goals done')
            nf_schedule = '\n'.join(shared_steps)
        else:
            final_splits, final_gen = (10, 10) if layered_pruning else (20, 14)
            nfsteps.append(f'  all_goals grind (config := {{ splits := {final_splits}, gen := {final_gen} }}) [' + nfctx + ']')
            nf_schedule = '\n'.join(nfsteps)
        self_shape = not strict
        if self_shape:
            for left0, right0, _vs0 in rules:
                ue = unify(left0[0], left0[1])
                if ue is None:
                    continue
                rr = deep(right0, ue)
                if isinstance(rr, str) or rr[0] != rr[1]:
                    self_shape = False
                    break
        selfcode = ''
        if self_shape:
            sb = []
            for i, (left0, right0, vs0) in enumerate(rules):
                pats = ', '.join(vs0 + ['ha', 'hb', 'ho', 'sa', 'sb', 'so'])
                ue = unify(left0[0], left0[1])
                if ue is None:
                    body = '    exfalso\n    grind (config := { splits := 10, gen := 10 }) [L, R, U, sz]'
                else:
                    rr = deep(right0, ue)
                    root0 = _v13_pterm(rr[0])
                    shape = f'{_v13_pterm(right0)} = p {root0} {root0}'
                    body = f'    have hs : {shape} := by\n      grind (config := {{ splits := 10, gen := 10 }}) [L, R, U, sz]\n    refine ⟨{root0}, ho.trans hs, ?_⟩\n    rw [← hs, ← ho]\n    exact hn'
                sb.append(f'  · rcases c{i} with ⟨{pats}⟩\n{body}')
            sb.append(f'  · rcases c{len(rules)} with ⟨ho, miss⟩\n    refine ⟨q, ho, ?_⟩\n    rw [ho] at hn\n    exact hn')
            selfcode = f"theorem eval_self_shape (q : CM) (hq : NF q) :\n    ∃ w, eval q q = p w w ∧ NF (p w w) := by\n  have hn := eval_nf hq hq\n  have c := eval_cases q q\n  rcases c with {' | '.join((f'c{i}' for i in range(len(rules) + 1)))}\n{chr(10).join(sb)}\n"
        summary_intro = ''
        if self_shape:
            squares = [(path, node) for path, node in _v13_internal_paths(term) if node[0] == node[1]]
            if squares:
                spath, snode = squares[0]
                sw = '_w0'
                sterm = _v13_replace_at(term, spath, (sw, sw))

                def ses(t, path=()):
                    if path == spath:
                        return f'(p {sw} {sw})'
                    if isinstance(t, str):
                        return t
                    return f'(eval {ses(t[0], path + (0,))} {ses(t[1], path + (1,))})'

                def snfp(t, path=()):
                    if path == spath:
                        return 'Hself0'
                    if isinstance(t, str):
                        return 'h' + t
                    return f'eval_nf ({snfp(t[0], path + (0,))}) ({snfp(t[1], path + (1,))})'
                summary_intro = f'  obtain ⟨{sw}, Eself0, Hself0⟩ := eval_self_shape {es(snode[0])} ({nfp(snode[0])})\n  rw [Eself0]\n'
                ns = [(path, node) for path, node in _v13_internal_paths(term) if path[:len(spath)] != spath]
                bcases = '\n'.join((f'  have B{i} := eval_cases {ses(t[0], path + (0,))} {ses(t[1], path + (1,))}' for i, (path, t) in enumerate(ns)))
                hm = match(rules[0][0], sterm)
                if hm is None:
                    return None
                hargs = ' '.join((_v13_pterm(hm[v]) for v in rules[0][2]))
                bcases += f'\n  have Hsrc : Code {_v13_pterm(sterm[0])} {_v13_pterm(sterm[1])} {_v13_pterm(outvar)} := .r0 {hargs}'
                nfacts = '\n'.join((f'  have N{i} : NF {ses(t, path)} := {snfp(t, path)}' for i, (path, t) in enumerate(ns)))
                nfsteps = []
                for i in range(len(ns) - 1, -1, -1):
                    name = f'B{i}'
                    if explicit_nf:
                        nfsteps.append('  all_goals rcases ' + name + ' with ' + eval_case_patterns(i))
                    else:
                        nfsteps.append('  all_goals rcases ' + name + ' with ' + ' | '.join([name] * (len(rules) + 1)))
                    if not explicit_nf:
                        nfsteps.append('  all_goals try simp_all only [NF]')
                    elif strict:
                        nfsteps.append('  all_goals try omega')
                    if not (strict and explicit_nf):
                        nfsteps.append('  all_goals try grind (config := { splits := 10, gen := 10 }) [' + nfctx + ']')
                if strict and explicit_nf and (source_cert['leaves'] > 200):
                    nfsteps.append('  all_goals try grind (config := { splits := 4, gen := 12 }) [eq_sz, ne_p_left, ne_p_right, L, R, U, sz]')
                nfsteps.append('  all_goals grind (config := { splits := 20, gen := 14 }) [' + nfctx + ']')
                nf_schedule = '\n'.join(nfsteps)
                if step_kernel and (not explicit_nf):
                    root = f'B{len(ns) - 1}'
                    nf_schedule = '  rcases ' + root + ' with ' + (eval_case_patterns(len(ns) - 1) if explicit_nf else ' | '.join([root] * (len(rules) + 1))) + '\n  all_goals simp_all only [NF]\n  all_goals grind (config := { splits := 24, gen := 18 }) [EvalCases, CodeCases, ' + nfctx + ']'
        vals, nl, nr, steps = found
        code_cases_block = f"{(chr(10).join(case_defs) + chr(10) if case_defs else '')}def CodeCases (a b o : CM) : Prop := {dcase}\ntheorem code_cases {{a b o : CM}} (h : Code a b o) : CodeCases a b o := by\n  unfold CodeCases\n  cases h with\n{chr(10).join(cases)}\n"
        grind_fwd = '@[grind →] ' if strict_dag else ''
        nf_helpers = f'{grind_fwd}theorem nf_p_left {{a b : CM}} (h : NF (p a b)) : NF a := h.1\n{grind_fwd}theorem nf_p_right {{a b : CM}} (h : NF (p a b)) : NF b := h.2.1\ntheorem eq_sz {{a b : CM}} (h : a = b) : sz a = sz b := congrArg sz h\n'
        if not strict_dag:
            nf_helpers = 'theorem nf_p_no {a b : CM} (h : NF (p a b)) : ¬ ∃ o, Code a b o := h.2.2\n' + nf_helpers + 'theorem ne_p_left (a b : CM) : a ≠ p a b := by\n  intro h\n  have q := congrArg sz h\n  simp [sz] at q\n  omega\ntheorem ne_p_right (a b : CM) : b ≠ p a b := by\n  intro h\n  have q := congrArg sz h\n  simp [sz] at q\n  omega\n'
        constructor_grind = '@[grind →] theorem p_inj {a b c d : CM}\n    (h : p a b = p c d) : a = c ∧ b = d := CM.p.inj h\n' if strict_dag else ''
        code_grind = 'attribute [grind intro] Code\n' if strict_dag else ''
        helper_gap = '\n' if strict_dag else ''
        source_gap = '\n\n\n' if strict_dag else '\n\n'
        evalcore = f"{(nf_mdefs + chr(10) if nf_mdefs else '')}{constructor_grind}{(nf_szlemmas + chr(10) if nf_szlemmas else '')}inductive Code : CM → CM → CM → Prop\n{chr(10).join(ctors)}\n{code_grind}{code_cases_block}def NF : CM → Prop\n  | e => True\n  | k a => NF a\n  | p a b => NF a ∧ NF b ∧ ¬ ∃ o, Code a b o\n{nf_helpers}{helper_gap}{chr(10).join(nfredex)}\n{(chr(10).join(nfexists) + chr(10) if nfexists else '')}{chr(10).join(nflemmas)}\ntheorem code_nf {{a b o : CM}} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by\n  cases h with\n{chr(10).join(nfcases)}\nnoncomputable def eval (a b : CM) : CM := by\n  classical\n  exact if h : ∃ o, Code a b o then Classical.choose h else p a b\ntheorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by\n  rw [eval, dif_neg h]\ntheorem eval_nf {{a b : CM}} (ha : NF a) (hb : NF b) : NF (eval a b) := by\n  by_cases h : ∃ o, Code a b o\n  · rw [eval, dif_pos h]\n    exact code_nf ha hb (Classical.choose_spec h)\n  · rw [eval_raw h]\n    exact ⟨ha, hb, h⟩\n{eval_cases_code}{source_gap}theorem source_raw ({' '.join(sv)} : CM) {' '.join(('(h' + v + ' : NF ' + v + ')' for v in sv))} :\n    {es(source[0])} = {es(source[1])} := by\n  classical\n{summary_intro}{bcases}\n{nfacts}\n{nf_schedule}\ndef Carrier := {{t : CM // NF t}}\nnoncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩\nnoncomputable instance instMagmaNF : Magma Carrier where op := op\ntheorem source_holds ({' '.join(sv)} : Carrier) : {_v13_opterm(source[0])} = {_v13_opterm(source[1])} := by\n  apply Subtype.ext\n  exact source_raw {' '.join((v + '.1' for v in sv))} {' '.join((v + '.2' for v in sv))}\ndef ce : Carrier := ⟨e, by simp [NF]⟩\ndef ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩\n"
        core_code = _v13_CCORE
        if strict_dag:
            for projection in ('def L : CM → CM | e => e | k _ => e | p a _ => a\n', 'def R : CM → CM | e => e | k _ => e | p _ b => b\n', 'def U : CM → CM | e => e | k a => a | p _ _ => e\n'):
                core_code = core_code.replace(projection, '')
        lean = core_code + evalcore
        if strict_dag:
            lean = _v13_recompile_indexed_dag(lean, tuple(len(vs) for _left, _right, vs in rules), len(ns))
            if lean is None:
                return None
        ntcache, hist = ({}, [])
        for i, (a, b, got) in enumerate(steps):
            cached = ntcache.get((a, b))
            if cached is None:
                if got is None:
                    theorem_name, value = (f'nt{i}', _v13_P(a, b))
                    lean += f'theorem {theorem_name} : ¬ ∃ o, Code {_v13_cm_lean(a)} {_v13_cm_lean(b)} o := by\n  rintro ⟨o, h⟩\n  cases h\n'
                    proof_name = f'eval_raw {theorem_name}'
                else:
                    matches0 = []
                    for ri, (left0, right0, rvs0) in enumerate(rules):
                        env0 = _v13_cm_match(left0, _v13_P(a, b))
                        if env0 is None:
                            continue
                        out0 = ground(right0, env0)
                        matches0.append((out0, ri, rvs0, env0))
                    if not matches0 or any((out0 != got for out0, _ri, _rvs, _env in matches0)):
                        if strict:
                            _v13_STRICT_FAILURES.append(('target_compiler_inconsistent', (len(matches0), got, tuple((out0 for out0, _ri, _rvs, _env in matches0)))))
                        return None
                    _out0, ri0, rvs0, env0 = matches0[0]
                    args0 = ' '.join((_v13_cm_lean(env0[v]) for v in rvs0))
                    ctor0 = f'Code.r{ri0}' + (f' {args0}' if args0 else '')
                    theorem_name, value = (f'et{i}', got)
                    lean += f'theorem {theorem_name} : eval {_v13_cm_lean(a)} {_v13_cm_lean(b)} = {_v13_cm_lean(got)} := by\n  rw [eval, dif_pos ⟨{_v13_cm_lean(got)}, {ctor0}⟩]\n  have hc := Classical.choose_spec\n    (show ∃ q, Code {_v13_cm_lean(a)} {_v13_cm_lean(b)} q from\n      ⟨{_v13_cm_lean(got)}, {ctor0}⟩)\n  have hu : ∀ q, Code {_v13_cm_lean(a)} {_v13_cm_lean(b)} q → q = {_v13_cm_lean(got)} := by\n    intro q h\n    cases h <;> simp_all\n  exact hu _ hc\n'
                    proof_name = theorem_name
                cached = (proof_name, value)
                ntcache[a, b] = cached
            proof_name, value = cached
            hist.append((proof_name, f'(eval {_v13_cm_lean(a)} {_v13_cm_lean(b)})', _v13_cm_lean(value)))

        def nfeq(start):
            cur, proofs = (start, [])
            for pr, lhs, rhs in hist:
                while lhs in cur:
                    ctx = cur.replace(lhs, 'q', 1)
                    cur = cur.replace(lhs, rhs, 1)
                    proofs.append(f'({pr})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({pr})')
            if not proofs:
                return 'rfl'
            out = proofs[0]
            for p0 in proofs[1:]:
                out = f'({out}).trans ({p0})'
            return out
        env = dict(zip(tv, vals))
        lp, rp = (nfeq(_v13_closed_eval(target[0], env)), nfeq(_v13_closed_eval(target[1], env)))

        def cv(t):
            if t[0] == 0:
                return 'ce'
            if t[0] == 1:
                return f'(ck {cv(t[1])})'
            raise ValueError
        apps = ' '.join((cv(x) for x in vals))
        refute = _v13_refute_closed_eq(nl, nr).replace('bad', 'nb')
        lean += f'end CM\nend submission\nopen submission\nopen submission.CM\nnoncomputable def submission : Goal := by\n  refine ⟨CM.Carrier, CM.instMagmaNF, CM.source_holds, ?_⟩\n  intro target\n  have bad := congrArg Subtype.val (target {apps})\n  change {_v13_closed_eval(target[0], env)} = {_v13_closed_eval(target[1], env)} at bad\n  have hl : {_v13_closed_eval(target[0], env)} = {_v13_cm_lean(nl)} := {lp}\n  have hr : {_v13_closed_eval(target[1], env)} = {_v13_cm_lean(nr)} := {rp}\n  have nb := hl.symm.trans (bad.trans hr)\n  exact {refute}\n'
        return lean
    places = None
    for left, right, _ in rules:
        here = set()
        for side in (0, 1):
            for path, node in walk(left[side]):
                if node == right:
                    here.add((side, path))
        places = here if places is None else places & here
    common = bool(places)
    side, outpath = min(places, key=lambda q: len(q[1])) if common else (0, ())
    getout = _v13_selector(outpath, 'a' if side == 0 else 'b')

    def ground(t, env):
        return env[t] if isinstance(t, str) else _v13_P(ground(t[0], env), ground(t[1], env))

    def hit(a, b):
        for i, (left, right, vs) in enumerate(rules):
            env = _v13_cm_match(left, _v13_P(a, b))
            if env is not None:
                args = ' '.join((_v13_cm_lean(env[x]) for x in vs))
                return (ground(right, env), f"(Code.r{i}{(' ' if args else '')}{args})")
    tv = _v13_formal_variables(target)
    pool = [_v13_E]
    for _ in range(8):
        pool.append(_v13_K(pool[-1]))

    def ev(t, env, steps):
        if isinstance(t, str):
            return env[t]
        a, b = (ev(t[0], env, steps), ev(t[1], env, steps))
        got = hit(a, b)
        value, proof = got if got else (_v13_P(a, b), None)
        steps.append((a, b, proof))
        return value
    found = None
    for n in range(min(30000, len(pool) ** len(tv))):
        q, vals = (n, [])
        for _ in tv:
            vals.append(pool[q % len(pool)])
            q //= len(pool)
        steps, env = ([], dict(zip(tv, vals)))
        nl, nr = (ev(target[0], env, steps), ev(target[1], env, steps))
        if nl != nr and (common or all((proof is None for _a, _b, proof in steps))):
            found = (vals, nl, nr, steps)
            break
    if not found:
        return None
    names = ('a', 'b', 'o')
    bspecs = []
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            best = None
            for k in range(1, 5):
                cs = []
                for a, b, _ in rules:
                    ps = [_v13_size_poly(x) for x in (a[0], a[1], b)]
                    keys = set(ps[i]) | set(ps[j])
                    d = {x: ps[j].get(x, 0) - k * ps[i].get(x, 0) for x in keys}
                    if any((v < 0 for x, v in d.items() if x != '#')):
                        break
                    cs.append(d.get('#', 0))
                else:
                    if min(cs) >= 0:
                        best = (i, j, k, min(cs))
            if best:
                bspecs.append(best)
    if not common and (not any((q[0] == 2 for q in bspecs))):
        bspecs.append((2, 0, 0, 0))

    def nsz(t):
        return f'sz {t}' if isinstance(t, str) else f'(({nsz(t[0])}+1)+({nsz(t[1])}+1))'

    def bound(z, i, j, k, c):
        return f'{k} * sz {z[i]} + {c} ≤ sz {z[j]}'

    def nbound(z, i, j, k, c):
        return f'{k} * ({nsz(z[i])}) + {c} ≤ {nsz(z[j])}'
    universe = [t for left, right, _ in rules for t in (left[0], left[1], right)]
    contexts = {}
    for top in universe:
        for _path, q in walk(top):
            vs0 = rvars(q)
            if isinstance(q, str) or len(vs0) != 1 or (not 1 <= tsize(q) <= 40):
                continue
            pat = _v13_subst(q, {vs0[0]: '@'})
            contexts[repr(pat)] = pat
    scored = []
    for pat in contexts.values():
        count = sum((match(pat, q) is not None for top in universe for _p, q in walk(top)))
        if count >= 2:
            scored.append(((tsize(pat) - 1) * (count - 1), pat))
    macros = [q for _score, q in sorted(scored, key=lambda z: (-z[0], tsize(z[1]), repr(z[1])))[:8]] if len(rules) >= 4 or priority else []
    macros.sort(key=lambda q: (tsize(q), repr(q)))

    def pt0(t, upto):
        for j in range(upto - 1, -1, -1):
            e = match(macros[j], t)
            if e is not None:
                return f"(S{j} {pt0(e['@'], upto)})"
        return t if isinstance(t, str) else f'(p {pt0(t[0], upto)} {pt0(t[1], upto)})'

    def pt(t):
        return pt0(t, len(macros))
    mdefs = '\n'.join((f"def S{i} (x : CM) : CM := {pt0(_v13_subst(q, {'@': 'x'}), i)}" for i, q in enumerate(macros)))
    mref = ''.join((f', S{i}' for i in range(len(macros))))
    bgoal = ' ∧ '.join((bound(names, *q) for q in bspecs))

    def hname(i):
        return f'H{i}'
    hdefs = []
    for i, (left, _right, vs) in enumerate(rules):
        bind = f"∃ {' '.join(vs)}, " if vs else ''
        hdefs.append(f'def {hname(i)} (a b : CM) : Prop := {bind}a = {pt(left[0])} ∧ b = {pt(left[1])}')

    def guard(i, a='a', b='b'):
        if not priority or not i:
            return ''
        return f"¬ ({' ∨ '.join((f'{hname(j)} {a} {b}' for j in range(i)))})"
    ctors, rdefs, hitdefs, missdefs, autohits = ([], [], [], [], [])
    for i, (left, right, vs) in enumerate(rules):
        args = f" ({' '.join(vs)} : CM)" if vs else ''
        call = ' ' + ' '.join(vs) if vs else ''
        triple = (left[0], left[1], right)
        inst = ' ∧ '.join((bound(tuple((_v13_pterm(x) for x in triple)), *q) for q in bspecs))
        ninst = ' ∧ '.join((nbound(triple, *q) for q in bspecs))
        cname = f'c{i}' if bspecs else f'r{i}'
        g = guard(i, pt(left[0]), pt(left[1]))
        extra = (f' (miss : {g})' if g else '') + (f' (down : {inst})' if bspecs else '')
        ctors.append(f'  | {cname}{args}{extra} : Code {pt(left[0])} {pt(left[1])} {pt(right)}')
        if bspecs:
            disjoint = bool(g) and all((unify(left, rules[j][0]) is None for j in range(i)))
            marg = f' (miss : {g})' if g and (not disjoint) else ''
            if disjoint:
                autohits.append(i)
                defs = ', '.join([hname(j) for j in range(i)] + [f'S{j}' for j in range(len(macros))] + ['sz_lt_p_left', 'sz_lt_p_right', 'sz'])
                mcall = f' (by grind [{defs}])'
            else:
                mcall = ' miss' if g else ''
            rdefs.append(f'theorem Code.r{i}{args}{marg} : Code {pt(left[0])} {pt(left[1])} {pt(right)} :=\n  .c{i}{call}{mcall} (by change {ninst}; omega)')
            if priority:
                gmarg = f' (miss : {guard(i)})' if guard(i) else ''
                gmcall = ' miss' if guard(i) else ''
                pats = ', '.join(vs + ['ha', 'hb'])
                hitdefs.append(f'theorem hit{i} {{a b : CM}} (h : {hname(i)} a b){gmarg} : ∃ o, Code a b o := by\n  rcases h with ⟨{pats}⟩\n  subst a; subst b\n  exact ⟨{pt(right)}, .c{i}{call}{gmcall} (by change {ninst}; omega)⟩')
                prior = '\n'.join((f'  have m{j} := missH{j} h' for j in range(i)))
                gproof = f'\n{prior}\n  have g : {guard(i)} := by grind' if i else ''
                missdefs.append(f"theorem missH{i} {{a b : CM}} (h : ¬ ∃ o, Code a b o) : ¬ {hname(i)} a b := by\n  intro q{gproof}\n  exact h (hit{i} q{(' g' if i else '')})")
    clauses = []
    for i, (x, y, vs) in enumerate(rules):
        bind = f"∃ {' '.join(vs)}, " if vs else ''
        g = guard(i)
        rich = len(rules) >= 4 or priority
        clauses.append(bind + f'a = {pt(x[0])} ∧ b = {pt(x[1])} ∧ o = {pt(y)}' + (' ∧ ' + (f'{g} ∧ ' if g else '') + f'sz a = {nsz(x[0])} ∧ sz b = {nsz(x[1])} ∧ sz o = {nsz(y)}' if rich else ''))
    cproof = []
    for i, (_x, _y, vs) in enumerate(rules):
        body = 'Or.inr (' * i + ('' if i == len(rules) - 1 else 'Or.inl ') + 'h' + ')' * i
        intro = f'(fun h => {body}) '
        cname = f'c{i}' if bspecs else f'r{i}'
        case_vars = [f'case{i}_{name}' for name in vs]
        case_miss = f'case{i}_miss'
        case_down = f'case{i}_down'
        binders = case_vars + ([case_miss] if guard(i) else []) + ([case_down] if bspecs else [])
        fields = case_vars + ['rfl'] * 3
        if len(rules) >= 4 or priority:
            if guard(i):
                fields.append(case_miss)
            fields += ['rfl'] * 3
        cproof.append(f"  | {cname} {' '.join(binders)} => exact {intro}⟨{', '.join(fields)}⟩")
    ccase = f"def CodeCases (a b o : CM) : Prop := {' ∨ '.join(('(' + x + ')' for x in clauses))}\ntheorem code_cases {{a b o : CM}} (h : Code a b o) : CodeCases a b o := by\n  unfold CodeCases\n  cases h with\n{chr(10).join(cproof)}"
    bound_cases = []
    if bspecs:
        for i, (_x, _y, vs) in enumerate(rules):
            cname = f'c{i}'
            case_vars = [f'bound{i}_{name}' for name in vs]
            case_miss = [f'bound{i}_miss'] if guard(i) else []
            case_down = f'bound{i}_down'
            binders = case_vars + case_miss + [case_down]
            bound_cases.append(f"  | {cname} {' '.join(binders)} => exact {case_down}")
    bcode = f'theorem code_bounds {{a b o : CM}} (h : Code a b o) : {bgoal} := by\n  cases h with\n{chr(10).join(bound_cases)}\n' if bspecs else ''
    fcode = f"theorem code_fun {{a b o q : CM}} (h : Code a b o) (k : Code a b q) : o = q := by\n  have ch := code_cases h\n  have ck := code_cases k\n  unfold CodeCases at ch ck\n  grind [{', '.join(hdefs and [hname(i) for i in range(len(rules))] or [])}{mref}, sz_lt_p_left, sz_lt_p_right, sz]\n" if priority else ''
    bref = ', code_bounds' if bspecs else ''
    rref = ''.join((f', Code.r{i}' for i in range(len(rules))))
    href = ''.join((f', {hname(i)}, missH{i}' for i in range(len(rules)))) if priority else ''
    if priority:
        rref = ''.join((f', Code.r{i}' for i in autohits))
    vcode, vnames = ([], [])
    for n, (i, j, k, c) in enumerate(bspecs):
        if i != 2:
            continue
        proj = 'q' if len(bspecs) == 1 else 'q' + '.2' * n + ('' if n == len(bspecs) - 1 else '.1')
        sidej = ('a', 'b', 'o')[j]
        name = f'eval_case{len(vnames)}'
        vnames.append(name)
        chosen_eq = 'eval_hit hc' if common or priority else 'by rw [eval, dif_pos h]'
        positive = 'rcases h with ⟨o, hc⟩\n    right; refine ⟨o, hc, eval_hit hc, ?_⟩' if common else 'let o := Classical.choose h\n    have hc : Code a b o := Classical.choose_spec h\n    right; refine ⟨o, hc, ?_, ?_⟩\n    · exact ' + chosen_eq
        bhead, btail = ('    ', '    ') if common else ('    · ', '      ')
        vcode.append(f'theorem {name} (a b : CM) :\n    (¬ ∃ o, Code a b o) ∧ eval a b = p a b ∨\n    ∃ o, Code a b o ∧ eval a b = o ∧ {k} * sz o + {c} ≤ sz {sidej} := by\n  by_cases h : ∃ o, Code a b o\n  · {positive}\n{bhead}have q := code_bounds hc\n{btail}exact {proj}\n  · exact Or.inl ⟨h, eval_raw h⟩')
    compact = (len(rules) >= 4 or shortened) and (not (structured and len(rules) <= 4 and (len(_v13_internal_paths(term)) <= 8)))
    if compact:
        vnames = ['eval_shape']
        shapepf = 'eval_hit hc' if common or priority else 'by rw [eval, dif_pos h]'
        vcode = [f'theorem eval_shape (a b : CM) :\n    Or (And (Not (Exists fun o => Code a b o)) (eval a b = p a b))\n       (Exists fun o => And (Code a b o) (And (CodeCases a b o) (eval a b = o))) := by\n  by_cases h : Exists fun o => Code a b o\n  · let o := Classical.choose h\n    have hc : Code a b o := Classical.choose_spec h\n    exact Or.inr ⟨o, hc, code_cases hc, {shapepf}⟩\n  · exact Or.inl ⟨h, eval_raw h⟩']
    priority_hit = f'theorem eval_hit {{a b o : CM}} (hc : Code a b o) : eval a b = o := by\n  rw [eval, dif_pos ⟨o, hc⟩]\n  exact code_fun (Classical.choose_spec (show ∃ q, Code a b q from ⟨o, hc⟩)) hc\n' if priority else ''
    evaldefs = f'def getOut (a b : CM) : CM := {getout}\ntheorem code_get {{a b o : CM}} (h : Code a b o) : getOut a b = o := by cases h <;> rfl\n{bcode}{fcode}noncomputable def eval (a b : CM) : CM := by\n  classical\n  exact if ∃ o, Code a b o then getOut a b else p a b\ntheorem eval_hit {{a b o : CM}} (h : Code a b o) : eval a b = o := by\n  rw [eval, if_pos ⟨o, h⟩]\n  exact code_get h\ntheorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by simp [eval, h]\n' if common else f'{bcode}{fcode}noncomputable def eval (a b : CM) : CM := by\n  classical\n  exact if h : ∃ o, Code a b o then Classical.choose h else p a b\n{priority_hit}theorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by\n  rw [eval, dif_neg h]\n'
    evalrules = []
    if priority:
        for i, (left, right, vs) in enumerate(rules):
            args = f" ({' '.join(vs)} : CM)" if vs else ''
            call = ' ' + ' '.join(vs) if vs else ''
            g = guard(i, pt(left[0]), pt(left[1]))
            disjoint = bool(g) and all((unify(left, rules[j][0]) is None for j in range(i)))
            marg = f' (miss : {g})' if g and (not disjoint) else ''
            mcall = ' miss' if g and (not disjoint) else ''
            evalrules.append(f'theorem eval_r{i}{args}{marg} : eval {pt(left[0])} {pt(left[1])} = {pt(right)} := eval_hit (Code.r{i}{call}{mcall})')
    erref = ''.join((f', eval_r{i}' for i in range(len(evalrules))))
    raw_misses = ' ∧ '.join((f'¬ {hname(i)} a b' for i in range(len(rules))))
    step_cases_def = ' ∨ '.join(('(' + x + ')' for x in clauses + [f'o = p a b ∧ {raw_misses}']))
    step_hit_proofs = []
    for i, (_x, _y, vs) in enumerate(rules):
        body = 'Or.inr (' * i + 'Or.inl h' + ')' * i
        cname = f'c{i}' if bspecs else f'r{i}'
        case_vars = [f'step{i}_{name}' for name in vs]
        case_miss = f'step{i}_miss'
        case_down = f'step{i}_down'
        binders = case_vars + ([case_miss] if guard(i) else []) + ([case_down] if bspecs else [])
        fields = case_vars + ['rfl'] * 3
        if len(rules) >= 4 or priority:
            if guard(i):
                fields.append(case_miss)
            fields += ['rfl'] * 3
        step_hit_proofs.append(f"    | {cname} {' '.join(binders)} => exact (fun h => {body}) ⟨{', '.join(fields)}⟩")
    raw_fields = ', '.join(['rfl'] + [f'missH{i} miss' for i in range(len(rules))])
    raw_body = 'Or.inr (' * len(rules) + f'⟨{raw_fields}⟩' + ')' * len(rules)
    stepcode = f'inductive Step : CM → CM → CM → Prop\n  | raw (a b : CM) (miss : ¬ ∃ o, Code a b o) : Step a b (p a b)\n  | hit {{a b o : CM}} (h : Code a b o) : Step a b o\ndef StepCases (a b o : CM) : Prop := {step_cases_def}\ntheorem step_cases {{a b o : CM}} (h : Step a b o) : StepCases a b o := by\n  cases h with\n  | raw miss => exact {raw_body}\n  | hit h =>\n    cases h with\n{chr(10).join(step_hit_proofs)}\ntheorem eval_step (a b : CM) : Step a b (eval a b) := by\n  by_cases h : ∃ o, Code a b o\n  · let o := Classical.choose h\n    have hc : Code a b o := Classical.choose_spec h\n    rw [eval_hit hc]\n    exact Step.hit hc\n  · rw [eval_raw h]\n    exact Step.raw a b h\n' if step_kernel and priority else ''
    lean = f"{mdefs}\ntheorem sz_lt_p_left (a b : CM) : sz a < sz (p a b) := by simp [sz]; omega\ntheorem sz_lt_p_right (a b : CM) : sz b < sz (p a b) := by simp [sz]; omega\n{(chr(10).join(hdefs) if priority else '')}\ninductive Code : CM → CM → CM → Prop\n{chr(10).join(ctors)}\n{chr(10).join(rdefs)}\n{chr(10).join(hitdefs)}\n{chr(10).join(missdefs)}\n{ccase}\ntheorem code_transport {{a a' b b' o : CM}} (ha : a = a') (hb : b = b') (h : Code a' b' o) : Code a b o := by\n  cases ha; cases hb; exact h\n{evaldefs}\n{chr(10).join(evalrules)}\n{chr(10).join(vcode)}\n{stepcode}\n"

    def es(t):
        return t if isinstance(t, str) else f'(eval {es(t[0])} {es(t[1])})'
    ns, sv = (_v13_internal_paths(term), _v13_variables(source[0]))
    sv += [v for v in _v13_variables(source[1]) if v not in sv]
    bcases = '\n'.join((f'  have B{i} := {name} {es(t[0])} {es(t[1])}' for i, (_path, t) in enumerate(ns) for name in vnames))
    if compact:
        hm = match(rules[0][0], term)
        if hm is not None:
            hargs = ' '.join((pt(hm[v]) for v in rules[0][2]))
            bcases += f'\n  have Hsrc : Code {pt(term[0])} {pt(term[1])} {pt(outvar)} := Code.r0 {hargs}'

    def ustate(a, b, env):
        env, todo = (env.copy(), [(a, b)])
        while todo:
            a, b = _v13_subst(todo.pop(), env)
            if a == b:
                continue
            if isinstance(a, str):
                if _v13_occurs(a, b, env):
                    return None
                env[a] = b
            elif isinstance(b, str):
                if _v13_occurs(b, a, env):
                    return None
                env[b] = a
            else:
                todo += [(a[0], b[0]), (a[1], b[1])]
        return env

    def deep_subst(t, env, seen=frozenset()):
        if isinstance(t, str):
            if t not in env or t in seen:
                return t
            return deep_subst(env[t], env, seen | {t})
        return (deep_subst(t[0], env, seen), deep_subst(t[1], env, seen))

    def vpaths(a, b, path=(), out=None):
        out = [set(), set()] if out is None else out
        if isinstance(a, tuple) and isinstance(b, tuple):
            vpaths(a[0], b[0], path + (0,), out)
            vpaths(a[1], b[1], path + (1,), out)
        elif isinstance(a, tuple) and isinstance(b, str):
            out[0].add(path)
            out[1].add(path)
        elif isinstance(a, str) and isinstance(b, tuple):
            out[0].add(path)
            out[1].add(path)
        return out

    def bullet(lines, sub, n):
        q = '  ' * (n + 1)
        lines.append('  ' * n + '· ' + sub[0][len(q):])
        lines.extend(sub[1:])
    sels, norms, facts = ({}, {}, [])

    def sat(t, path):
        for bit in path:
            t = t[bit]
        return t

    def szl(t):
        if isinstance(t, str):
            return f'sz {t}'
        return f'(({szl(t[0])}+1)+({szl(t[1])}+1))'

    def canonical(t, env=None):
        env = {} if env is None else env
        if isinstance(t, str):
            if t not in env:
                env[t] = f'w{len(env)}'
            return env[t]
        return (canonical(t[0], env), canonical(t[1], env))

    def zproj(eq, rhs, pre, pad, keep=None):
        out, names = ([], [])
        for m, (path, t0) in enumerate(walk(rhs)):
            if keep is not None and path not in keep:
                continue
            if path and (keep is None or path not in keep):
                continue
            name = f'{pre}_{m}'
            names.append(name)
            sn = sels.setdefault(path, len(sels))
            ct = canonical(rhs)
            key = (ct, path, sn)
            rec = norms.setdefault(key, [len(norms), 0])
            rec[1] += 1
            nn = rec[0]
            fi = len(facts)
            facts.append((pad, name, nn, eq, rhs, path, sn, key))
            out.append(pad + f'@@{fi}@@')
        return (out, names)

    def dred(s):
        ts = re.findall('\\(|\\)|[^\\s()]+', s)
        at = 0

        def rd():
            nonlocal at
            if at >= len(ts):
                raise ValueError
            if ts[at] != '(':
                q = ts[at]
                at += 1
                return q
            at += 1
            q = []
            while at < len(ts) and ts[at] != ')':
                q.append(rd())
            if at >= len(ts):
                raise ValueError
            at += 1
            return tuple(q)

        def red(q):
            if isinstance(q, str):
                return q
            q = tuple((red(x) for x in q))
            if len(q) == 2 and q[0] in ('L', 'R', 'U'):
                f, x = q
                if isinstance(x, tuple) and x:
                    if x[0] == 'p':
                        return x[1] if f == 'L' else x[2] if f == 'R' else 'e'
                    if x[0] == 'k':
                        return x[1] if f == 'U' else 'e'
                if x == 'e':
                    return 'e'
            return q

        def wr(q):
            return q if isinstance(q, str) else '(' + ' '.join((wr(x) for x in q)) + ')'
        try:
            q = rd()
            return wr(red(q)) if at == len(ts) else s
        except (ValueError, IndexError):
            return s

    def eqchain(name, start, goal, hist, pad):
        start, goal = (dred(start), dred(goal))
        structural = congruence_proof(start, goal, hist)
        if structural is not None:
            return [pad + f'have {name} : {start} = {goal} := {structural}']
        out = [pad + f'have {name} : {start} = {goal} := by', pad + '  calc']
        cur, first, path = (start, True, [])
        todo = list(hist)
        while cur != goal and any((lhs in cur for _pr, lhs, _rhs in todo)):
            pr, lhs, rhs = max((q for q in todo if q[1] in cur), key=lambda q: len(q[1]))
            todo.remove((pr, lhs, rhs))
            while lhs in cur:
                ctx = cur.replace(lhs, 'q', 1)
                new = dred(cur.replace(lhs, rhs, 1))
                pf = f'({pr})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({pr})'
                path.append((cur, new, pf))
                cur, first = (new, False)
        if cur != goal:
            target_tokens = re.findall('\\(|\\)|[^\\s()]+', goal)

            def distance(s):
                ts = re.findall('\\(|\\)|[^\\s()]+', s)
                return 4 * abs(len(ts) - len(target_tokens)) + sum((a != b for a, b in zip(ts, target_tokens)))
            queue, serial, seen, answer = ([(distance(start), 0, 0, start, [])], 0, {start}, None)
            edges = []
            for pr, lhs, rhs in hist:
                lhs, rhs = (dred(lhs), dred(rhs))
                if lhs != rhs:
                    edges += [(lhs, rhs, pr), (rhs, lhs, f'({pr}).symm')]
            cap = max([len(start), len(goal)] + [len(x) for e in edges for x in e[:2]]) * 3 + 40
            while queue and len(seen) < 500:
                _score, depth, _serial, cur, steps0 = heapq.heappop(queue)
                choices = []
                for lhs, rhs, pr in edges:
                    pos = cur.find(lhs)
                    if pos < 0:
                        continue
                    new = dred(cur[:pos] + rhs + cur[pos + len(lhs):])
                    if len(new) > cap or new in seen:
                        continue
                    choices.append((distance(new), -len(lhs), pos, lhs, rhs, pr, new))
                for score, _neglen, pos, lhs, rhs, pr, new in sorted(choices):
                    ctx = cur[:pos] + 'q' + cur[pos + len(lhs):]
                    pf = f'({pr})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({pr})'
                    steps1 = steps0 + [(cur, new, pf)]
                    if new == goal:
                        answer = steps1
                        break
                    seen.add(new)
                    serial += 1
                    heapq.heappush(queue, (score + depth + 1, depth + 1, serial, new, steps1))
                if answer is not None:
                    break
            if answer is None:
                return None
            path = answer
        if not path:
            return [pad + f'have {name} : {start} = {goal} := rfl']
        for i, (old, new, pf) in enumerate(path):
            out.append(pad + f"    {(old if i == 0 else '_')} = {new} := {pf}")
        return out

    def normalized_chain(name, start, goal, hist, pad):
        direct = eqchain(name, start, goal, hist, pad)
        if direct is not None:
            return direct
        env, chosen = ({}, [])
        changed = True
        while changed:
            changed = False
            for pr, lhs, rhs in hist:
                a, b = (dred(lhs), dred(rhs))
                if re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', a) and a not in env and (a != b):
                    env[a] = b
                    chosen.append((pr, a, b))
                    changed = True
                elif re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', b) and b not in env and (a != b):
                    env[b] = a
                    chosen.append((f'({pr}).symm', b, a))
                    changed = True

        def text_sub(s):
            for _ in range(min(len(env) + 1, 8)):
                old = s
                for v, rhs in env.items():
                    if re.search(f'\\b{re.escape(v)}\\b', rhs):
                        continue
                    if len(s) + s.count(v) * len(rhs) > 12000:
                        return '#overflow'
                    s = re.sub(f'\\b{re.escape(v)}\\b', rhs, s)
                if s == old:
                    break
            return dred(s)
        if text_sub(start) != text_sub(goal):
            return None
        extra = [(pr, lhs, rhs) for pr, lhs, rhs in chosen]
        return eqchain(name, start, goal, list(hist) + extra, pad)

    def normtext(start, hist):
        cur = dred(start)
        for _ in range(4 * len(hist) + 4):
            choices = [(lhs, rhs) for _pr, lhs, rhs in hist if dred(lhs) in cur and dred(lhs) != dred(rhs)]
            if not choices:
                break
            lhs, rhs = max(choices, key=lambda q: len(dred(q[0])))
            cur = dred(cur.replace(dred(lhs), dred(rhs), 1))
        return cur

    def expr_read(s):
        ts = re.findall('\\(|\\)|[^\\s()]+', dred(s))
        at = 0

        def rd():
            nonlocal at
            if ts[at] != '(':
                q = ts[at]
                at += 1
                return q
            at += 1
            q = []
            while ts[at] != ')':
                q.append(rd())
            at += 1
            return tuple(q)
        return rd()

    def expr_write(q):
        return q if isinstance(q, str) else '(' + ' '.join((expr_write(x) for x in q)) + ')'

    def congruence_proof(start, goal, hist):
        try:
            aa, bb = (expr_read(dred(start)), expr_read(dred(goal)))
            graph = {}
            for pr, lhs, rhs in hist:
                x, y = (expr_read(dred(lhs)), expr_read(dred(rhs)))
                if x == y:
                    continue
                graph.setdefault(x, []).append((y, pr))
                graph.setdefault(y, []).append((x, f'({pr}).symm'))
        except (ValueError, IndexError):
            return None
        memo, active = ({}, set())

        def cat(p, q):
            if p == 'rfl':
                return q
            if q == 'rfl':
                return p
            return f'({p}).trans ({q})'

        def prove(a0, b0):
            key = (a0, b0)
            if a0 == b0:
                return 'rfl'
            if key in memo:
                return memo[key]
            if key in active:
                return None
            active.add(key)
            reached, queue = ({a0: 'rfl'}, [a0])
            for x in queue:
                for y, ep in graph.get(x, ()):
                    if y not in reached:
                        reached[y] = cat(reached[x], ep)
                        queue.append(y)
            answer = reached.get(b0)
            if answer is None:
                candidates = sorted(reached, key=lambda x: 0 if isinstance(x, tuple) and isinstance(b0, tuple) and (len(x) == len(b0)) and (x[0] == b0[0]) else 1)
                for root in candidates:
                    if not isinstance(root, tuple) or not isinstance(b0, tuple) or len(root) != len(b0) or (root[0] != b0[0]):
                        continue
                    cur, cp = (list(root), 'rfl')
                    for i in range(1, len(cur)):
                        pi = prove(cur[i], b0[i])
                        if pi is None:
                            break
                        nxt = cur.copy()
                        nxt[i] = b0[i]
                        ctx = nxt.copy()
                        ctx[i] = 'zzq'
                        cp = cat(cp, f'congrArg (fun zzq => {expr_write(tuple(ctx))}) ({pi})')
                        cur = nxt
                    else:
                        answer = cat(reached[root], cp)
                        break
            active.remove(key)
            memo[key] = answer
            return answer
        return prove(aa, bb)

    def expr_match(pattern, value, names, env=None):
        env = {} if env is None else env
        if isinstance(pattern, str):
            if pattern in names:
                if pattern in env:
                    return env if env[pattern] == value else None
                env[pattern] = value
                return env
            return env if pattern == value else None
        if isinstance(value, str) or len(pattern) != len(value) or pattern[0] != value[0]:
            return None
        for a0, b0 in zip(pattern[1:], value[1:]):
            env = expr_match(a0, b0, names, env)
            if env is None:
                return None
        return env

    def symbolic_hit(node, hist):
        actual = tuple((expr_read(normtext(es(t), hist)) for t in node))
        for j, (left, right, vs) in enumerate(rules):
            pattern = expr_read(_v13_pterm(left))
            env = expr_match(pattern, ('p', actual[0], actual[1]), set(vs))
            if env is not None:

                def inst(t):
                    return expr_write(env[t]) if isinstance(t, str) else f'(p {inst(t[0])} {inst(t[1])})'
                return (j, vs, env, inst)

    def eqexpr(start, hist):
        cur, proofs, todo = (start, [], list(hist))
        while any((lhs in cur for _pr, lhs, _rhs in todo)):
            pr, lhs, rhs = max((q for q in todo if q[1] in cur), key=lambda q: len(q[1]))
            todo.remove((pr, lhs, rhs))
            while lhs in cur:
                ctx = cur.replace(lhs, 'q', 1)
                cur = cur.replace(lhs, rhs, 1)
                proofs.append(f'({pr})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({pr})')
        if not proofs:
            return 'rfl'
        out = proofs[0]
        for p0 in proofs[1:]:
            out = f'({out}).trans ({p0})'
        return out

    def reduce_expr(start, hist):
        cur, proofs, todo = (dred(start), [], list(hist))
        todo = [(pr, dred(lhs), dred(rhs)) for pr, lhs, rhs in todo if len(dred(rhs)) <= len(dred(lhs)) and dred(lhs) != dred(rhs)]
        for _ in range(4 * len(todo) + 4):
            choices = [q for q in todo if q[1] in cur]
            if not choices:
                break
            pr, lhs, rhs = max(choices, key=lambda q: len(dred(q[1])))
            todo.remove((pr, lhs, rhs))
            lhs, rhs = (dred(lhs), dred(rhs))
            while lhs in cur:
                ctx = cur.replace(lhs, 'q', 1)
                cur = dred(cur.replace(lhs, rhs, 1))
                proofs.append(f'({pr})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({pr})')
        if not proofs:
            return (cur, 'rfl')
        out = proofs[0]
        for p0 in proofs[1:]:
            out = f'({out}).trans ({p0})'
        return (cur, out)

    def leafhist(pr, lhs, rhs, base=()):
        out = []
        for path, t in walk(rhs):
            f = _v13_selector(path)
            bp = f'(congrArg (fun q => {f}) ({pr})).symm'
            rr, rp = reduce_expr(_v13_selector(path, lhs), base)
            proof = bp if rp == 'rfl' else f'({bp}).trans ({rp})'
            out.append((proof, _v13_pterm(t), rr))
        return out

    def tree(k, env, vals, n, eqs, raws=()):
        pad, (path, node) = ('  ' * n, ns[k])
        a = _v13_subst(vals.get(path + (0,), node[0]), env)
        b = _v13_subst(vals.get(path + (1,), node[1]), env)
        lines = [pad + f'rcases B{k} with B{k} | B{k}']
        raw = vals.copy()
        raw[path] = (a, b)
        close = None
        for j, (left, rright, vs) in enumerate(rules):
            hit = match(left, (a, b))
            if hit is not None:
                args = ' '.join((_v13_pterm(hit[v]) for v in vs))
                cp = '  ' * (n + 1)
                ha = normalized_chain(f'ha{k}', es(node[0]), _v13_pterm(_v13_subst(left[0], hit)), eqs, cp)
                hb = normalized_chain(f'hb{k}', es(node[1]), _v13_pterm(_v13_subst(left[1], hit)), eqs, cp)
                if ha is not None and hb is not None:
                    close = ha + hb
                    close += [cp + f'exact (B{k}.1 (Exists.intro {_v13_pterm(_v13_subst(rright, hit))} (code_transport ha{k} hb{k} (Code.r{j} {args})))).elim']
                    break
                continue
        if close:
            sub = close
        else:
            rp = '  ' * (n + 1)
            rprep, rn = zproj(f'B{k}.2', (es(node[0]), es(node[1])), f'zr{k}', rp, {(), (0,), (1,)})
            hist = (f'B{k}.2', es(node), f'(p {es(node[0])} {es(node[1])})')
            if k + 1 < len(ns):
                tail = tree(k + 1, env, raw, n + 1, eqs + [hist], raws + ((k, node, a, b),))
                if tail is None:
                    return None
                sub = rprep + tail
            else:
                fin = normalized_chain(f'fr{k}', es(term), _v13_pterm(outvar), eqs + [hist], rp)
                if fin is None:
                    allhist = eqs + [hist]
                    raw_index = k
                    raw_node = node
                    direct = None
                    for ri, rn0, ra0, rb0 in ((k, node, a, b),) + raws:
                        pair = (deep_subst(ra0, env), deep_subst(rb0, env))
                        for dj, (dl, dr, dvs) in enumerate(rules):
                            dm = match(dl, pair)
                            if dm is not None:
                                direct = (dj, dl, dr, dvs, dm)
                                raw_index, raw_node = (ri, rn0)
                                break
                        if direct is not None:
                            break
                    closing = symbolic_hit(node, allhist) if direct is None else None
                    if direct is None and closing is None:
                        for ri, rn0, _ra0, _rb0 in raws:
                            closing = symbolic_hit(rn0, allhist)
                            if closing is not None:
                                raw_index, raw_node = (ri, rn0)
                                break
                    if direct is None and closing is None:
                        sub = rprep + [rp + 'first | omega | grind [L, R, U, sz]']
                        bullet(lines, sub, n)
                        return lines
                    if direct is not None:
                        j, left, right, vs, mh = direct
                        inst = lambda t: _v13_pterm(_v13_subst(t, mh))
                    else:
                        j, vs, mh, inst = closing
                        left, right, _ = rules[j]
                    ha = normalized_chain(f'ra{k}', es(raw_node[0]), inst(left[0]), allhist, rp)
                    hb = normalized_chain(f'rb{k}', es(raw_node[1]), inst(left[1]), allhist, rp)
                    if ha is None or hb is None:
                        sub = rprep + [rp + 'first | omega | grind [L, R, U, sz]']
                        bullet(lines, sub, n)
                        return lines
                    args = ' '.join((_v13_pterm(mh[v]) if direct is not None else expr_write(mh[v]) for v in vs))
                    output = inst(right)
                    ex = f"{chr(10216)}{output}, code_transport ra{k} rb{k} (Code.r{j}{(' ' if args else '')}{args}){chr(10217)}"
                    sub = rprep + ha + hb + [rp + f'exact (B{raw_index}.1 {ex}).elim']
                else:
                    sub = rprep + fin + [rp + f"exact fr{k}{('' if reverse else '.symm')}"]
        bullet(lines, sub, n)
        hp = '  ' * (n + 1)
        hlines = [hp + f'rcases B{k} with ⟨o{k}, h{k}, e{k}, l{k}⟩', hp + f'have s{k} := code_cases h{k}']
        if common and k + 1 == len(ns):
            root = ns[-1][1]
            cur = _v13_selector(outpath, es(root[side]))
            calc = [hp + f'have cx : getOut {es(root[0])} {es(root[1])} = {_v13_pterm(outvar)} := by', hp + f'  change {cur} = {_v13_pterm(outvar)}', hp + '  calc']
            first = True
            todo = list(eqs)
            while any((lhs in cur for _pr, lhs, _rhs in todo)):
                pr, lhs, rhs = max((q for q in todo if q[1] in cur), key=lambda q: len(q[1]))
                todo.remove((pr, lhs, rhs))
                while lhs in cur:
                    ctx = cur.replace(lhs, 'q', 1)
                    new = cur.replace(lhs, rhs, 1)
                    pf = f'({pr})' if ctx == 'q' else f'congrArg (fun q => {ctx}) ({pr})'
                    calc.append(hp + f"    {(cur if first else '_')} = {new} := {pf}")
                    first, cur = (False, new)
            if cur != _v13_pterm(outvar):
                calc.append(hp + f'    _ = {_v13_pterm(outvar)} := rfl')
            if first and cur == _v13_pterm(outvar):
                calc[-1] = hp + '  rfl'
            finish = f'exact cx.symm.trans (cg{k}.trans e{k}.symm)' if not reverse else f'exact e{k}.trans (cg{k}.symm.trans cx)'
            hlines = hlines[:1] + [hp + f'have cg{k} := code_get h{k}'] + calc + [hp + finish]
            bullet(lines, hlines, n)
            return lines
        pats = []
        for j, (_left, _right, vs) in enumerate(rules):
            q = [f'q{k}{j}{x}' for x in range(len(vs))] + [f'a{k}{j}', f'b{k}{j}', f'c{k}{j}']
            pats.append('⟨' + ', '.join(q) + '⟩')
        hlines.append(hp + f'rcases s{k} with ' + (pats[0] if len(pats) == 1 else '(' + ' | '.join(pats) + ')'))
        for j, (left, right, vs) in enumerate(rules):
            ren = {v: f'q{k}{j}{x}' for x, v in enumerate(vs)}
            e2 = ustate((a, b), _v13_subst(left, ren), env)
            zpad = '  ' * (n + 2)
            zfacts, znames = ([], [])
            shapes = tuple((_v13_subst(t, ren) for t in (left[0], left[1], right)))
            for q, rhs, si in zip('abc', shapes, (0, 1, 2)):
                allowed = None
                extra = vpaths(shapes[0], shapes[1])[si] if e2 is None and si < 2 else set()
                if si == side or extra:
                    allowed = {(), *[outpath[:i] for i in range(1, len(outpath) + 1)], *extra}
                zs, ns0 = zproj(f'{q}{k}{j}', rhs, f'{q}{k}{j}', zpad, allowed)
                zfacts += zs
                znames += ns0
            zs, ns0 = zproj(f'e{k}.trans c{k}{j}', shapes[2], f'e{k}{j}', zpad)
            zfacts += zs
            znames += ns0
            if e2 is None:
                sub = zfacts + [zpad + 'first | omega | grind [L, R, U, sz]']
            else:
                keep = {()}
                keep |= {outpath[:i] for i in range(1, len(outpath) + 1)}
                mini, mn = ([], [])
                for q, rhs, si in zip('abc', (left[0], left[1], right), (0, 1, 2)):
                    zs, ns0 = zproj(f'{q}{k}_{j}', rhs, f'm{k}_{j}_{q}', zpad, keep if si == side else {()})
                    mini += zs
                    mn += ns0
                zs, ns0 = zproj(f'e{k}', right, f'm{k}_{j}_e', zpad, {()})
                mini += zs
                mn += ns0
                mini += [zpad + 'simp only [L, R, sz] at ' + ' '.join(mn)]
                nxt = vals.copy()
                nxt[path] = _v13_subst(right, ren)
                hist = [(f'a{k}{j}', es(node[0]), _v13_pterm(_v13_subst(left[0], ren))), (f'b{k}{j}', es(node[1]), _v13_pterm(_v13_subst(left[1], ren))), (f'e{k}.trans c{k}{j}', es(node), _v13_pterm(_v13_subst(right, ren)))]
                hist += leafhist(f'a{k}{j}', es(node[0]), shapes[0], eqs + hist)
                hist += leafhist(f'b{k}{j}', es(node[1]), shapes[1], eqs + hist)
                if k + 1 < len(ns):
                    tail = tree(k + 1, e2, nxt, n + 2, eqs + hist, raws)
                    if tail is None:
                        return None
                    sub = zfacts + tail
                else:
                    fname = f'f{k}{j}'
                    fin = eqchain(fname, es(term), _v13_pterm(outvar), eqs + hist, zpad)
                    if fin is None:
                        raise ValueError('unproved hit branch')
                    sub = zfacts + fin
                    sub.append(zpad + f"exact {fname}{('' if reverse else '.symm')}")
            bullet(hlines, sub, n + 1)
        bullet(lines, hlines, n)
        return lines
    if compact:
        ks = [len(ns) - 1] if step_kernel else range(len(ns))
        qlines = [f'rcases B{k} with B{k} | B{k}' for k in ks]
        proof_tree = '  ' + ' <;> '.join(qlines)
        proof_tree += f' <;> (try simp_all only) <;> have Z0 := code_bounds Hsrc <;> (try have Z1 := code_bounds left) <;> grind (config := {{ splits := 20, gen := 20 }}) [CodeCases{bref}{rref}{href}{erref}{mref}, sz_lt_p_left, sz_lt_p_right, L, R, U, sz]'
    else:
        try:
            proof_tree = '\n'.join(tree(0, {}, {}, 1, []))
        except ValueError:
            return None
    kernel = ''
    if step_kernel and priority:
        pindex = {path: i for i, (path, _t) in enumerate(ns)}

        def kval(t0, path):
            return t0 if isinstance(t0, str) else f't{pindex[path]}'
        prems, apps = ([], [])
        for i, (path, t0) in enumerate(ns):
            aa, bb = (kval(t0[0], path + (0,)), kval(t0[1], path + (1,)))
            prems.append(f'    (s{i} : Step {aa} {bb} t{i})')
            apps.append(f'(eval_step {es(t0[0])} {es(t0[1])})')
        kg = f't{len(ns) - 1} = {outvar}' if reverse else f'{outvar} = t{len(ns) - 1}'
        kfacts = '\n'.join((f'  have K{i} := step_cases s{i}' for i in range(len(ns))))
        split_lines = []
        local_ctx = f'StepCases{href}{mref}, sz_lt_p_left, sz_lt_p_right, L, R, U, sz'
        for i in range(len(ns) - 1, -1, -1):
            name = f'K{i}'
            split_lines.append('  all_goals rcases ' + name + ' with ' + ' | '.join([name] * (len(rules) + 1)))
            split_lines.append('  all_goals try grind (config := { splits := 10, gen := 10 }) [' + local_ctx + ']')
        split_lines.append('  all_goals grind (config := { splits := 20, gen := 14 }) [' + local_ctx + ']')
        ksplit = '\n'.join(split_lines)
        kernel = f"theorem source_kernel {{ {' '.join(sv + [f't{i}' for i in range(len(ns))])} : CM }}\n    (hs : Code {pt(term[0])} {pt(term[1])} {pt(outvar)})\n{chr(10).join(prems)} : {kg} := by\n{kfacts}\n{ksplit}\n"
        proof_tree = '  exact source_kernel Hsrc ' + ' '.join(apps)
    spcode = '\n'.join((f"theorem sp{i} {{a b : CM}} (h : a = b) : sz {_v13_selector(p, 'a')} = sz {_v13_selector(p, 'b')} := congrArg (fun q => sz {_v13_selector(p)}) h" for p, i in sels.items()))
    for fi, (pad, name, nn, eq, rhs, p, sn, key) in enumerate(facts):
        count = norms[key][1]
        line = f'have {name} := np{nn} ({eq})' if count >= 3 else f'have {name} : _ = {szl(sat(rhs, p))} := sp{sn} ({eq})'
        proof_tree = proof_tree.replace(f'@@{fi}@@', line)
    normcode = '\n'.join((f"theorem np{i} {{{' '.join(_v13_variables(t))} a : CM}} (h : a = {_v13_pterm(t)}) : sz {_v13_selector(p, 'a')} = {szl(sat(t, p))} := sp{sn} h" for (t, p, sn), (i, count) in norms.items() if count >= 3))
    lean += f"{spcode}\n{normcode}\n{kernel}\ntheorem source_holds ({' '.join(sv)} : CM) : {es(source[0])} = {es(source[1])} := by\n  classical\n{bcases}\n{proof_tree}\n"
    lean += 'noncomputable instance instMagma2 : Magma CM where op := eval\n'
    vals, nl, nr, steps = found
    rewrites, thist, ntcache = ([], [], {})
    for i, (a, b, proof) in enumerate(steps):
        if proof:
            pr = f'eval_hit {proof}'
            rewrites.append(pr)
        else:
            ni = ntcache.get((a, b), i)
            if (a, b) not in ntcache:
                ntcache[a, b] = i
                lean += f'theorem nt{i} : ¬ ∃ o, Code {_v13_cm_lean(a)} {_v13_cm_lean(b)} o := by\n  rintro ⟨o, h⟩\n  cases h\n'
            pr = f'eval_raw nt{ni}'
            rewrites.append(pr)
        got = hit(a, b)
        value = got[0] if got else _v13_P(a, b)
        thist.append((pr, f'(eval {_v13_cm_lean(a)} {_v13_cm_lean(b)})', _v13_cm_lean(value)))
    env, apps = (dict(zip(tv, vals)), ' '.join((_v13_cm_lean(x) for x in vals)))
    lp = eqexpr(_v13_closed_eval(target[0], env), thist)
    rp = eqexpr(_v13_closed_eval(target[1], env), thist)
    refute = _v13_refute_closed_eq(nl, nr).replace('bad', 'nb')
    lean += f"end CM\nend submission\nopen submission\nopen submission.CM\nnoncomputable def submission : Goal := by\n  refine ⟨CM, CM.instMagma2, ?_, ?_⟩\n  · intro {' '.join(sv)}\n    exact CM.source_holds {' '.join(sv)}\n  · intro target\n    have bad := target {apps}\n    have hl : {_v13_closed_eval(target[0], env)} = {_v13_cm_lean(nl)} := {lp}\n    have hr : {_v13_closed_eval(target[1], env)} = {_v13_cm_lean(nr)} := {rp}\n    have nb := hl.symm.trans (bad.trans hr)\n    exact {refute}\n"
    out = _v13_CCORE + lean
    for a, b in [('set_option maxRecDepth 100000\n', ''), ('deriving DecidableEq\n', ''), ('CodeCases', 'D'), ('code_transport', 'ct'), ('code_get', 'cg'), ('getOut', 'g'), ('eval_case0', 'ec'), ('source_holds', 'sh'), ('Code', 'C'), ('eval', 'v'), ('sz', 's'), ('np', 'n')]:
        out = out.replace(a, b)
    for i in range(len(sels)):
        out = out.replace(f'sp{i}', f't{i}')
    out = out.replace('CM', 'A')
    return out

def _v13_opposite_term(t):
    return t if isinstance(t, str) else (_v13_opposite_term(t[1]), _v13_opposite_term(t[0]))

def _v13_opposite_code(code, original_source=None, preserve_trace_source_call=False):
    changes = (('instance instMagma : Magma CM where\n  op := op', 'instance instMagma : Magma CM where\n  op a b := op b a'), ('noncomputable instance instMagma2 : Magma CM where op := eval', 'noncomputable instance instMagma2 : Magma CM where op a b := eval b a'), ('instance instMagma2 : Magma CM where op := eval', 'instance instMagma2 : Magma CM where op a b := eval b a'), ('instance instMagma : Magma C where op := fop', 'instance instMagma : Magma C where op a b := fop b a'), ('instance instMagmaC : Magma C where op := op', 'instance instMagmaC : Magma C where op a b := op b a'), ('instance instMagma : Magma Carrier where\n  op := op', 'instance instMagma : Magma Carrier where\n  op a b := op b a'), ('instance instMagma : Magma U where op := op', 'instance instMagma : Magma U where op a b := op b a'), ('noncomputable instance instMagmaNF : Magma Carrier where op := op', 'noncomputable instance instMagmaNF : Magma Carrier where op a b := op b a'))
    for old, new in changes:
        if old in code:
            code = code.replace(old, new, 1)
            if original_source is not None and 'CM.instMagma2' in code:
                original_variables = _v13_variables(original_source[0])
                original_variables += [variable for variable in _v13_variables(original_source[1]) if variable not in original_variables]
                mirrored_source = tuple((_v13_opposite_term(term) for term in original_source))
                mirrored_variables = _v13_variables(mirrored_source[0])
                mirrored_variables += [variable for variable in _v13_variables(mirrored_source[1]) if variable not in mirrored_variables]
                # The mirrored search has already built the complete call to
                # source_holds, including any arguments introduced by source
                # generalization/specialization.  Opposite transport changes
                # only the outer Goal binder order.  Reconstructing the call
                # from a bare theorem name used to discard specialization
                # arguments and could leave an unproved universal quantifier.
                pattern = '  · intro [^\\n]+\\n    exact ((?:CM\\.(?:source_holds|sh)) [^\\n]+)'

                def adapt_trace_source(match0):
                    call = match0.group(1)
                    if not preserve_trace_source_call:
                        call = call.split()[0] + ' ' + ' '.join(mirrored_variables)
                    return '  · intro ' + ' '.join(original_variables) + '\n    exact ' + call
                code, count = re.subn(pattern, adapt_trace_source, code, count=1)
                if count != 1:
                    return None
            if original_source is not None and 'CM.instMagmaNF' in code:
                ov = _v13_variables(original_source[0])
                ov += [v for v in _v13_variables(original_source[1]) if v not in ov]
                ms = tuple((_v13_opposite_term(t) for t in original_source))
                mv = _v13_variables(ms[0])
                mv += [v for v in _v13_variables(ms[1]) if v not in mv]
                pat = '(CM\\.instMagmaNF, )(.+?)(, \\?_)'

                def adapt_source(m):
                    field = m.group(2)
                    return m.group(1) + '(fun ' + ' '.join(ov) + ' => (' + field + ') ' + ' '.join(mv) + ')' + m.group(3)
                code, count = re.subn(pat, adapt_source, code, count=1)
                # Mirroring the magma without transporting the source proof
                # would make the generated Goal certify the wrong identity.
                # Treat a template-shape drift as an unsupported generator
                # case instead of returning partially transformed Lean code.
                if count != 1:
                    return None
            return code
    return None

def _v13_source_generalizations(source):
    occupied = set(_v13_variables(source[0]) + _v13_variables(source[1]))
    fresh = next((v for v in 'zyxwvutsrqponmlkjihgfedcba' if v not in occupied), None)
    if fresh is None:
        return []

    def leaves(t, side, path=()):
        if isinstance(t, str):
            return [(side, path, t)]
        return leaves(t[0], side, path + (0,)) + leaves(t[1], side, path + (1,))

    def replace(t, path, value):
        if not path:
            return value
        q = replace(t[path[0]], path[1:], value)
        return (q, t[1]) if path[0] == 0 else (t[0], q)
    occ = leaves(source[0], 0) + leaves(source[1], 1)
    groups = {}
    for side, path, var in occ:
        groups.setdefault(var, []).append((side, path))
    ranked, seen = ([], set())
    for var, ps in groups.items():
        if len(ps) < 2:
            continue
        movable = [i for i, (side, path) in enumerate(ps) if path or not isinstance(source[side], str)]
        cuts = []
        for width in range(1, min(3, len(movable)) + 1):
            cuts.extend(itertools.combinations(movable, width))
        for chosen0 in cuts:
            chosen = frozenset(chosen0)
            if len(chosen) == len(ps):
                continue

            def distance(a, b):
                side, path = ps[a]
                oside, opath = ps[b]
                if side != oside:
                    return len(path) + len(opath) + 2
                common = 0
                while common < len(path) and common < len(opath) and (path[common] == opath[common]):
                    common += 1
                return len(path) + len(opath) - 2 * common
            across = min((distance(a, b) for a in chosen for b in range(len(ps)) if b not in chosen))
            within = max((distance(a, b) for a in chosen for b in chosen), default=0)
            changed = list(source)
            for i in chosen:
                side, path = ps[i]
                changed[side] = replace(changed[side], path, fresh)
            changed = tuple(changed)
            if changed in seen:
                continue
            seen.add(changed)
            depth = sum((len(ps[i][1]) for i in chosen))
            ranked.append((len(chosen), -across, within, -depth, changed, {fresh: var}))
    for side in (0, 1):
        for path, node in _v13_internal_paths(source[side]):
            if not path:
                continue
            changed = list(source)
            changed[side] = replace(changed[side], path, fresh)
            changed = tuple(changed)
            if changed in seen:
                continue
            seen.add(changed)
            ranked.append((4, len(_v13_internal_paths(node)), 0, -len(path), changed, {fresh: node}))
    ranked.sort(key=lambda q: q[:4])
    return [(q[4], q[5]) for q in ranked[:32]]

def _v13_specialize_source_code(code, generalized, source, substitution):
    marker = 'def submission : Goal := by'
    cut = code.rfind(marker)
    if cut < 0:
        return None
    head, tail = (code[:cut], code[cut:])
    gvars = _v13_variables(generalized[0])
    gvars += [v for v in _v13_variables(generalized[1]) if v not in gvars]
    svars = _v13_variables(source[0])
    svars += [v for v in _v13_variables(source[1]) if v not in svars]

    def specialized_arg(v):
        value = substitution.get(v, v)
        return value if isinstance(value, str) else _v13_opterm(value)
    args = ' '.join((specialized_arg(v) for v in gvars))
    pattern = '  · intro [^\\n]+\\n    exact ((?:CM|A)\\.(?:source_holds|sh)) [^\\n]+'

    def direct(m):
        return f"  · intro {' '.join(svars)}\n    exact {m.group(1)} {args}"
    tail, count = re.subn(pattern, direct, tail, count=1)
    if count:
        return head + tail
    pattern = '((?:CM|A)\\.(?:source_holds|sh))(?=, \\?_⟩)'

    def inline(m):
        return f"(fun {' '.join(svars)} => {m.group(1)} {args})"
    tail, count = re.subn(pattern, inline, tail, count=1)
    return head + tail if count else None

def _v13_generalized_trace_model(source, target, index=0):
    choices = _v13_source_generalizations(source)
    if index >= len(choices) or time.monotonic() >= _v13_DEADLINE:
        return None
    generalized, substitution = choices[index]
    code = _v13_trace_model(generalized, target, 0, 1)
    return _v13_specialize_source_code(code, generalized, source, substitution) if code else None

def _v13_strict_trace_candidate(source, target, index=0, tableau_depth=0, generalized=False):
    code = _v13_generalized_trace_model(source, target, index) if generalized else _v13_trace_model(source, target, index, tableau_depth)
    if not code:
        return None
    forbidden = ('have boom : False', 'first | contradiction | omega', 'grind')
    if any((token in code for token in forbidden)):
        return None
    if len(code.encode('utf-8')) > MAX_FALSE_CERTIFICATE_BYTES:
        return None
    required = ('inductive Step', 'theorem code_unique', 'theorem source_holds', 'noncomputable instance instMagma2')
    if not all((token in code for token in required)):
        return None
    return code

def _v13_strict_completion_candidate(source, target, index=-1, operational=False, priority=False, residual_policy=0, strict_semantic_gate=False, compound_only=False):
    global _v13_STRICT_LAST_SOURCE_CERT, _v13_STRICT_LAST_MODEL, _v13_STRICT_LAST_FALLBACKS
    _v13_STRICT_LAST_FALLBACKS = ()

    def generate(dag):
        return _v13_complete_model(source, target, True, operational=operational, priority=priority, residual_policy=residual_policy, step_kernel=True, explicit_nf=True, strict=True, strict_dag=dag, strict_semantic_gate=strict_semantic_gate) if index < 0 else _v13_generalized_complete_model(source, target, index, True, residual_policy=residual_policy, step_kernel=True, compound_only=compound_only, strict=True, strict_dag=dag, strict_semantic_gate=strict_semantic_gate, operational=operational, priority=priority)

    regular = generate(False)
    if not regular:
        return None
    regular_cert = _v13_STRICT_LAST_SOURCE_CERT
    regular_model = _v13_STRICT_LAST_MODEL
    regular_bytes = len(regular.encode('utf-8'))
    nf_heavy = regular_cert['closures']['nf'] * 16 >= max(1, regular_cert['leaves'])
    case_work = regular_cert['leaves'] * (regular_cert['rules'] + 1)
    raw_work = regular_cert['closures']['raw'] * (regular_cert['rules'] + 1)
    # The old serialized-DAG emitter is replaced by a Code-derived recompilation
    # of this already generated regular certificate.  Pressure only chooses the
    # primary representation; it never narrows the model/search domain.  The
    # non-primary compiler is retained as a Judge fallback, so model/source/
    # witness search is never run a second time and neither certificate shape
    # is discarded.
    solo_v6_try_dag = regular_bytes > 20000 or (regular_bytes * 3 > 40000 and nf_heavy)
    prefer_indexed = solo_v6_try_dag or regular_bytes > 14000 or case_work > 3000 or raw_work > 2500
    certificate = regular_cert
    indexed = None
    if regular_model:
        try:
            indexed = _v13_recompile_indexed_dag(
                regular,
                tuple(len(variables) for _left, _right, variables in regular_model['rules']),
                regular_cert['source_nodes'],
            )
        except (TimeoutError, MemoryError, RecursionError):
            indexed = None
    regular_ok = regular_bytes <= MAX_FALSE_CERTIFICATE_BYTES
    indexed_ok = indexed is not None and len(indexed.encode('utf-8')) <= MAX_FALSE_CERTIFICATE_BYTES
    # Prefer the name-independent indexed source proof.  It performs explicit
    # dependent `cases` per evaluation node and avoids the large rcases/grind
    # closure that exhausted the historical 300 s Judge budget.
    code = indexed if indexed_ok else (regular if regular_ok else None)
    fallbacks = (regular,) if indexed_ok and regular_ok else ()
    # Exact solo_v6 regular domain: no rule-count, case-work, raw-work, or
    # v6_fixed legacy-domain cap can discard a regular certificate.
    _v13_STRICT_LAST_SOURCE_CERT = regular_cert
    if code is None or not certificate or certificate['closures']['open']:
        return None

    def finalize(candidate):
        if candidate is None or len(candidate.encode('utf-8')) > MAX_FALSE_CERTIFICATE_BYTES:
            return None
        try:
            source_start = candidate.index('theorem source_raw')
            source_end = candidate.index('def Carrier', source_start)
        except ValueError:
            return None
        source_code = candidate[source_start:source_end]
        forbidden = ('have boom : False', 'first | contradiction | omega', 'macro ')
        if any(token in candidate for token in forbidden):
            return None
        if 'inductive EvalCases :' in candidate:
            if ('all_goals done' not in source_code or 'CodeCases' in candidate or
                    source_code.count('all_goals cases B') != certificate['source_nodes']):
                return None
            if certificate['leaves'] > 200:
                heartbeat_limit = min(2500000, 1000000 + 4000 * certificate['leaves'])
                candidate = candidate.replace('set_option maxHeartbeats 1000000', f'set_option maxHeartbeats {heartbeat_limit}', 1)
        else:
            candidate = candidate.replace('set_option maxHeartbeats 1000000', 'set_option maxHeartbeats 2000000', 1)
        return candidate

    code = finalize(code)
    if code is None:
        return None
    _v13_STRICT_LAST_FALLBACKS = tuple(
        checked for checked in (finalize(candidate) for candidate in fallbacks)
        if checked is not None and checked != code
    )
    return code

def _v13_generalized_complete_model(source, target, index=0, nf_mode=False, residual_policy=0, step_kernel=False, compound_only=False, strict=False, strict_dag=False, strict_semantic_gate=False, operational=False, priority=False):
    choices = _v13_source_generalizations(source)
    if compound_only:
        choices = [choice for choice in choices if any((not isinstance(value, str) for value in choice[1].values()))]

        def abstraction_cost(choice):
            values = [value for value in choice[1].values() if not isinstance(value, str)]
            counts = {}
            for value in values:
                for var in _v13_variables(value):

                    def occurrences(t):
                        return int(t == var) if isinstance(t, str) else occurrences(t[0]) + occurrences(t[1])
                    counts[var] = counts.get(var, 0) + occurrences(value)
            nonlinear_loss = sum((max(0, count - 1) for count in counts.values()))
            return (nonlinear_loss, sum((len(_v13_internal_paths(v)) for v in values)))
        choices.sort(key=abstraction_cost)
    if index >= len(choices) or time.monotonic() >= _v13_DEADLINE:
        return None
    generalized, substitution = choices[index]
    code = _v13_complete_model(generalized, target, nf_mode=nf_mode, operational=operational if strict else True, priority=priority, rule_limit=0 if strict else 4, residual_policy=residual_policy, step_kernel=step_kernel, explicit_nf=strict, strict=strict, strict_dag=strict_dag, strict_semantic_gate=strict_semantic_gate)
    return _v13_specialize_source_code(code, generalized, source, substitution) if code else None

_v13_GUARDED_LEAN_HEAD = 'import JudgeProblem\nimport Mathlib\n\nset_option maxRecDepth 10000\n\nnamespace submission\n\ndef condEq {α β : Type} [DecidableEq α] (a b : α) (yes no : β) : β :=\n  match decEq a b with\n  | isTrue _ => yes\n  | isFalse _ => no\n\nlemma condEq_pos {α β : Type} [DecidableEq α]\n    {a b : α} {yes no : β} (h : a = b) : condEq a b yes no = yes := by\n  subst b\n  unfold condEq\n  cases decEq a a with\n  | isTrue _ => rfl\n  | isFalse h => exact (h rfl).elim\n\nlemma condEq_neg {α β : Type} [DecidableEq α]\n    {a b : α} {yes no : β} (h : a ≠ b) : condEq a b yes no = no := by\n  unfold condEq\n  cases decEq a b with\n  | isTrue hab => exact (h hab).elim\n  | isFalse _ => rfl\n\ninductive CM where\n  | e : CM\n  | k : CM → CM\n  | p : CM → CM → CM\n\nnamespace CM\n\ndef cmDecEq : (a b : CM) → Decidable (a = b)\n  | .e, .e => isTrue rfl\n  | .e, .k _ => isFalse (fun h => CM.noConfusion h)\n  | .e, .p _ _ => isFalse (fun h => CM.noConfusion h)\n  | .k _, .e => isFalse (fun h => CM.noConfusion h)\n  | .p _ _, .e => isFalse (fun h => CM.noConfusion h)\n  | .k a, .k b =>\n      match cmDecEq a b with\n      | isTrue h => isTrue (congrArg CM.k h)\n      | isFalse h => isFalse (fun hab => h (CM.k.inj hab))\n  | .k _, .p _ _ => isFalse (fun h => CM.noConfusion h)\n  | .p _ _, .k _ => isFalse (fun h => CM.noConfusion h)\n  | .p a b, .p c d =>\n      match cmDecEq a c with\n      | isFalse h => isFalse (fun hab => h (CM.p.inj hab).1)\n      | isTrue hac =>\n          match cmDecEq b d with\n          | isFalse h => isFalse (fun hab => h (CM.p.inj hab).2)\n          | isTrue hbd => isTrue (by cases hac; cases hbd; rfl)\n\ninstance instDecidableEq : DecidableEq CM := cmDecEq\n\ndef sz : CM → Nat\n  | .e => 0\n  | .k x => sz x + 1\n  | .p x y => (sz x + 1) + (sz y + 1)\n\n'

_v13_GUARDED_LEAN_PROOFS = 'lemma sz_p_pos (a b : CM) : 0 < sz (.p a b) := by\n  change 0 < (sz a + 1) + (sz b + 1)\n  exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ (sz a))\n    (Nat.le_add_right (sz a + 1) (sz b + 1))\n\nlemma sz_lt_p_left (a b : CM) : sz a < sz (.p a b) := by\n  change sz a < (sz a + 1) + (sz b + 1)\n  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))\n    (Nat.le_add_right (sz a + 1) (sz b + 1))\n\nlemma sz_dec_le (a : CM) : sz (dec a) ≤ sz a := by\n  cases a with\n  | e => exact Nat.le_refl 0\n  | k x =>\n      change sz x ≤ sz x + 1\n      exact Nat.le_add_right (sz x) 1\n  | p a b =>\n      by_cases hba : b = a\n      · subst b\n        rw [dec_p_eq]\n        rw [condEq_pos rfl]\n        change sz a + 1 ≤ (sz a + 1) + (sz a + 1)\n        exact Nat.le_add_right (sz a + 1) (sz a + 1)\n      · cases b with\n        | e =>\n            rw [dec_p_eq]\n            rw [condEq_neg hba]\n            exact Nat.zero_le _\n        | k b =>\n            rw [dec_p_eq]\n            rw [condEq_neg hba]\n            exact Nat.zero_le _\n        | p c x =>\n            by_cases hca : c = a\n            · subst c\n              rw [dec_p_p_eq]\n              rw [condEq_neg hba, condEq_pos rfl]\n              change sz x ≤ (sz a + 1) + (((sz a + 1) + (sz x + 1)) + 1)\n              exact Nat.le_trans (Nat.le_add_right (sz x) 1)\n                (Nat.le_trans (Nat.le_add_left (sz x + 1) (sz a + 1))\n                  (Nat.le_trans\n                    (Nat.le_add_right ((sz a + 1) + (sz x + 1)) 1)\n                    (Nat.le_add_left (((sz a + 1) + (sz x + 1)) + 1) (sz a + 1))))\n            · rw [dec_p_p_eq]\n              rw [condEq_neg hba, condEq_neg hca]\n              exact Nat.zero_le _\n\nlemma sz_dec_lt_of_ne_e (a : CM) (ha : a ≠ .e) : sz (dec a) < sz a := by\n  cases a with\n  | e => exact (ha rfl).elim\n  | k x =>\n      change sz x < sz x + 1\n      exact Nat.lt_succ_self (sz x)\n  | p a b =>\n      by_cases hba : b = a\n      · subst b\n        rw [dec_p_eq]\n        rw [condEq_pos rfl]\n        change sz a + 1 < (sz a + 1) + (sz a + 1)\n        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ (sz a))\n      · cases b with\n        | e =>\n            rw [dec_p_eq]\n            rw [condEq_neg hba]\n            exact sz_p_pos _ _\n        | k b =>\n            rw [dec_p_eq]\n            rw [condEq_neg hba]\n            exact sz_p_pos _ _\n        | p c x =>\n            by_cases hca : c = a\n            · subst c\n              rw [dec_p_p_eq]\n              rw [condEq_neg hba, condEq_pos rfl]\n              change sz x < (sz a + 1) + (((sz a + 1) + (sz x + 1)) + 1)\n              exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz x))\n                (Nat.le_trans (Nat.le_add_left (sz x + 1) (sz a + 1))\n                  (Nat.le_trans\n                    (Nat.le_add_right ((sz a + 1) + (sz x + 1)) 1)\n                    (Nat.le_add_left (((sz a + 1) + (sz x + 1)) + 1) (sz a + 1))))\n            · rw [dec_p_p_eq]\n              rw [condEq_neg hba, condEq_neg hca]\n              exact sz_p_pos _ _\n\nlemma ne_self_p (a b : CM) : a ≠ .p a b := by\n  intro h\n  have hs := congrArg sz h\n  exact (Nat.ne_of_lt (sz_lt_p_left a b)) hs\n\nlemma dec_ne_p_self (a b : CM) : dec a ≠ .p a b := by\n  intro h\n  have hle := sz_dec_le a\n  have hs := congrArg sz h\n  rw [hs] at hle\n  exact (Nat.lt_irrefl (sz a))\n    (Nat.lt_of_lt_of_le (sz_lt_p_left a b) hle)\n\nlemma dec_ne_self_of_dec_ne_e (a : CM) (ha : dec a ≠ .e) : dec a ≠ a := by\n  have hae : a ≠ .e := by\n    intro h\n    subst a\n    exact ha rfl\n  intro h\n  have hlt := sz_dec_lt_of_ne_e a hae\n  have hs := congrArg sz h\n  rw [hs] at hlt\n  exact (Nat.lt_irrefl (sz a)) hlt\n\nlemma dec_p_default (a b : CM) (hba : b ≠ a)\n    (hshape : ∀ x, b ≠ .p a x) : dec (.p a b) = .e := by\n  cases b with\n  | e =>\n      rw [dec_p_eq]\n      rw [condEq_neg hba]\n  | k x =>\n      rw [dec_p_eq]\n      rw [condEq_neg hba]\n  | p c x =>\n      have hca : c ≠ a := by\n        intro h\n        subst c\n        exact hshape x rfl\n      rw [dec_p_p_eq]\n      rw [condEq_neg hba, condEq_neg hca]\n\nlemma dec_p_same (a : CM) : dec (.p a a) = .k a := by\n  rw [dec_p_eq]\n  rw [condEq_pos rfl]\n\nlemma dec_p_nested (a x : CM) : dec (.p a (.p a x)) = x := by\n  have hba : .p a x ≠ a := by\n    intro h\n    exact ne_self_p a x h.symm\n  rw [dec_p_p_eq]\n  rw [condEq_neg hba, condEq_pos rfl]\n\nlemma op_right_e (a : CM) : op a .e = dec a := by\n  unfold op\n  rw [condEq_pos rfl]\n\nlemma op_normal (a b : CM) (hb : b ≠ .e) (ha : a ≠ .p b b) :\n    op a b = .p a b := by\n  unfold op\n  rw [condEq_neg hb, condEq_neg ha]\n\nlemma op_special (a b : CM) (hb : b ≠ .e) (ha : a = .p b b) :\n    op a b = .e := by\n  unfold op\n  rw [condEq_neg hb, condEq_pos ha]\n\nlemma decode_twice (y x : CM) : dec (op y (op y x)) = x := by\n  by_cases hx : x = .e\n  · subst x\n    by_cases hd : dec y = .e\n    · calc\n        dec (op y (op y .e)) = dec (op y (dec y)) := by rw [op_right_e]\n        _ = dec (op y .e) := by rw [hd]\n        _ = dec (dec y) := by rw [op_right_e]\n        _ = dec .e := by rw [hd]\n        _ = .e := rfl\n    · by_cases hy : y = .p (dec y) (dec y)\n      · have oy : op y (dec y) = .e := op_special y (dec y) hd hy\n        calc\n          dec (op y (op y .e)) = dec (op y (dec y)) := by rw [op_right_e]\n          _ = dec .e := by rw [oy]\n          _ = .e := rfl\n      · have hdy : dec y ≠ y := dec_ne_self_of_dec_ne_e y hd\n        have hshape : ∀ q, dec y ≠ .p y q := fun q => dec_ne_p_self y q\n        have hdefault : dec (.p y (dec y)) = .e :=\n          dec_p_default y (dec y) hdy hshape\n        have oy : op y (dec y) = .p y (dec y) := op_normal y (dec y) hd hy\n        calc\n          dec (op y (op y .e)) = dec (op y (dec y)) := by rw [op_right_e]\n          _ = dec (.p y (dec y)) := by rw [oy]\n          _ = .e := hdefault\n  · by_cases hy : y = .p x x\n    · subst y\n      have hinner : op (.p x x) x = .e := op_special (.p x x) x hx rfl\n      calc\n        dec (op (.p x x) (op (.p x x) x)) = dec (op (.p x x) .e) := by rw [hinner]\n        _ = dec (dec (.p x x)) := by rw [op_right_e]\n        _ = dec (.k x) := by rw [dec_p_same]\n        _ = x := rfl\n    · have hbig : y ≠ .p (.p y x) (.p y x) := by\n        intro h\n        have hs := congrArg sz h\n        have hlt := Nat.lt_trans (sz_lt_p_left y x)\n          (sz_lt_p_left (.p y x) (.p y x))\n        exact (Nat.ne_of_lt hlt) hs\n      have hpxe : CM.p y x ≠ CM.e := by\n        intro h\n        exact CM.noConfusion h\n      have hinner : op y x = .p y x := op_normal y x hx hy\n      have houter : op y (.p y x) = .p y (.p y x) :=\n        op_normal y (.p y x) hpxe hbig\n      calc\n        dec (op y (op y x)) = dec (op y (.p y x)) := by rw [hinner]\n        _ = dec (.p y (.p y x)) := by rw [houter]\n        _ = x := dec_p_nested y x\n\nlemma triple (z : CM) : op (op z z) z = .e := by\n  by_cases hz : z = .e\n  · subst z\n    have hee : op CM.e CM.e = CM.e := by\n      calc\n        op CM.e CM.e = dec CM.e := op_right_e CM.e\n        _ = CM.e := rfl\n    exact (congrArg (fun q => op q CM.e) hee).trans hee\n  · have hself : z ≠ .p z z := ne_self_p z z\n    have hinner : op z z = .p z z := op_normal z z hz hself\n    calc\n      op (op z z) z = op (.p z z) z := by rw [hinner]\n      _ = .e := op_special (.p z z) z hz rfl\n\n'

_v13_GE = ('e',)

def _v13_gk(x):
    return ('k', x)

def _v13_gp(x, y):
    return ('p', x, y)

def _v13_guarded_choose(name, a, b, x, decoded):
    return {'e': _v13_GE, 'a': a, 'b': b, 'x': x, 'ka': _v13_gk(a), 'inner': x, 'kinner': _v13_gk(x), 'pab': _v13_gp(a, b), 'dec': decoded}[name]

def _v13_guarded_dec(program, value):
    if value[0] == 'var':
        return ('dec', value)
    if value[0] == 'e':
        return _v13_GE
    if value[0] == 'k':
        return _v13_guarded_choose(program[0], _v13_GE, _v13_GE, value[1], _v13_GE)
    a, b = (value[1], value[2])
    if b == a:
        return _v13_guarded_choose(program[1], a, b, _v13_GE, _v13_GE)
    if b[0] == 'p' and b[1] == a:
        return _v13_guarded_choose(program[2], a, b, b[2], _v13_GE)
    return _v13_guarded_choose(program[3], a, b, _v13_GE, _v13_GE)

def _v13_guarded_op(program, a, b):
    decoded = _v13_guarded_dec(program, a)
    if b == _v13_GE:
        return _v13_guarded_choose(program[4], a, b, _v13_GE, decoded)
    if a == _v13_gp(b, b):
        return _v13_guarded_choose(program[5], a, b, _v13_GE, decoded)
    return _v13_guarded_choose(program[6], a, b, _v13_GE, decoded)

def _v13_guarded_programs():
    spaces = (('e', 'kinner', 'inner'), ('e', 'a', 'b', 'ka'), ('e', 'a', 'b', 'ka', 'x'), ('e', 'a', 'b', 'ka'), ('e', 'a', 'pab', 'dec'), ('pab', 'dec', 'a', 'b', 'e'), ('e', 'dec', 'a', 'b', 'pab'))
    yield from itertools.product(*spaces)

def _v13_guarded_trees(depth):
    pool = [_v13_GE]
    for _ in range(depth):
        old = tuple(pool)
        pool.extend((_v13_gk(x) for x in old))
        pool.extend((_v13_gp(x, y) for x in old for y in old))
        pool = list(dict.fromkeys(pool))
    return pool

def _v13_guarded_eval(term, env, operation):
    if isinstance(term, str):
        return env[term]
    return operation(_v13_guarded_eval(term[0], env, operation), _v13_guarded_eval(term[1], env, operation))

def _v13_guarded_names(equation):
    return _v13_formal_variables(equation)

def _v13_guarded_holds(equation, program, pool, opposite=False):
    operation = (lambda a, b: _v13_guarded_op(program, b, a)) if opposite else lambda a, b: _v13_guarded_op(program, a, b)
    names = _v13_guarded_names(equation)
    for values in itertools.product(pool, repeat=len(names)):
        if time.monotonic() >= _v13_DEADLINE:
            return False
        env = dict(zip(names, values))
        if _v13_guarded_eval(equation[0], env, operation) != _v13_guarded_eval(equation[1], env, operation):
            return False
    return True

def _v13_guarded_witness(equation, program, pool, opposite=False):
    operation = (lambda a, b: _v13_guarded_op(program, b, a)) if opposite else lambda a, b: _v13_guarded_op(program, a, b)
    names = _v13_guarded_names(equation)
    for values in itertools.product(pool, repeat=len(names)):
        if time.monotonic() >= _v13_DEADLINE:
            return None
        env = dict(zip(names, values))
        left = _v13_guarded_eval(equation[0], env, operation)
        right = _v13_guarded_eval(equation[1], env, operation)
        if left != right:
            return (env, left, right)

def _v13_guarded_contract(program):
    a, b, c, x = (('var', q) for q in 'abcx')
    return all((_v13_guarded_dec(program, _v13_GE) == _v13_GE, _v13_guarded_dec(program, _v13_gk(x)) == x, _v13_guarded_dec(program, _v13_gp(a, a)) == _v13_gk(a), _v13_guarded_dec(program, _v13_gp(a, _v13_gp(a, x))) == x, _v13_guarded_dec(program, _v13_gp(a, _v13_GE)) == _v13_GE, _v13_guarded_dec(program, _v13_gp(a, _v13_gk(b))) == _v13_GE, _v13_guarded_dec(program, _v13_gp(a, _v13_gp(c, x))) == _v13_GE, _v13_guarded_op(program, a, _v13_GE) == _v13_guarded_dec(program, a), _v13_guarded_op(program, _v13_gp(b, b), b) == _v13_GE, _v13_guarded_op(program, a, b) == _v13_gp(a, b)))

def _v13_guarded_source_term(term):
    return ('v', term) if isinstance(term, str) else ('op', _v13_guarded_source_term(term[0]), _v13_guarded_source_term(term[1]))

def _v13_guarded_rewrite(term):
    if term[0] in ('v', 'e'):
        return term
    if term[0] == 'dec':
        value = _v13_guarded_rewrite(term[1])
        if value[0] == 'op' and value[2][0] == 'op' and (value[1] == value[2][1]):
            return _v13_guarded_rewrite(value[2][2])
        return ('dec', value)
    left, right = (_v13_guarded_rewrite(term[1]), _v13_guarded_rewrite(term[2]))
    if left[0] == 'op' and left[1] == left[2] == right:
        return _v13_GE
    if right == _v13_GE:
        return _v13_guarded_rewrite(('dec', left))
    return ('op', left, right)

def _v13_guarded_source_closed(source, opposite):
    semantic = tuple((_v13_opposite_term(t) for t in source)) if opposite else source
    return _v13_guarded_rewrite(_v13_guarded_source_term(semantic[0])) == _v13_guarded_rewrite(_v13_guarded_source_term(semantic[1]))

def _v13_guarded_lean_term(term):
    return term if isinstance(term, str) else f'(CM.op {_v13_guarded_lean_term(term[0])} {_v13_guarded_lean_term(term[1])})'

def _v13_guarded_lean_value(value):
    if value[0] == 'e':
        return 'CM.e'
    if value[0] == 'k':
        return f'(CM.k {_v13_guarded_lean_value(value[1])})'
    return f'(CM.p {_v13_guarded_lean_value(value[1])} {_v13_guarded_lean_value(value[2])})'

def _v13_guarded_lean_ground(term, env):
    return _v13_guarded_lean_value(env[term]) if isinstance(term, str) else f'(CM.op {_v13_guarded_lean_ground(term[0], env)} {_v13_guarded_lean_ground(term[1], env)})'

def _v13_guarded_lean_choice(name, a, b, x, decoded):
    return {'e': '.e', 'a': a, 'b': b, 'x': x, 'ka': f'(.k {a})', 'inner': x, 'kinner': f'(.k {x})', 'pab': f'(.p {a} {b})', 'dec': decoded}[name]

def _v13_guarded_lean_middle(program, opposite):
    same = _v13_guarded_lean_choice(program[1], 'a', 'b', '.e', '.e')
    nested = _v13_guarded_lean_choice(program[2], 'a', 'b', 'x', '.e')
    default = _v13_guarded_lean_choice(program[3], 'a', 'b', '.e', '.e')
    dec_k = _v13_guarded_lean_choice(program[0], '.e', '.e', 'x', '.e')
    right_e = _v13_guarded_lean_choice(program[4], 'a', 'b', '.e', '(dec a)')
    special = _v13_guarded_lean_choice(program[5], 'a', 'b', '.e', '(dec a)')
    normal = _v13_guarded_lean_choice(program[6], 'a', 'b', '.e', '(dec a)')
    instance = 'instance instMagma : Magma CM where\n  op a b := op b a' if opposite else 'instance instMagma : Magma CM where\n  op := op'
    return f'def dec : CM → CM\n  | .e => .e\n  | .k x => {dec_k}\n  | .p a b =>\n      condEq b a {same}\n        (match b with\n        | .p c x => condEq c a {nested} {default}\n        | _ => {default})\n\nlemma dec_p_eq (a b : CM) :\n    dec (.p a b) = condEq b a (.k a)\n      (match b with\n      | .p c x => condEq c a x .e\n      | _ => .e) := rfl\n\nlemma dec_p_p_eq (a c x : CM) :\n    dec (CM.p a (CM.p c x)) =\n      condEq (CM.p c x) a (CM.k a) (condEq c a x CM.e) := rfl\n\ndef op (a b : CM) : CM :=\n  condEq b .e {right_e} (condEq a (.p b b) {special} {normal})\n\n{instance}\n\n'

def _v13_compile_guarded_model(source, target, program, opposite, witness):
    semantic_source = tuple((_v13_opposite_term(t) for t in source)) if opposite else source
    semantic_target = tuple((_v13_opposite_term(t) for t in target)) if opposite else target
    source_names = _v13_guarded_names(source)
    target_names = _v13_guarded_names(target)
    env, left_value, right_value = witness
    apps = ' '.join((_v13_guarded_lean_value(env[name]) for name in target_names))
    source_statement = f"theorem source_instance ({' '.join(source_names)} : CM) :\n    {_v13_guarded_lean_term(semantic_source[0])} = {_v13_guarded_lean_term(semantic_source[1])} := by\n  simp only [triple, op_right_e, decode_twice]\n"
    target_left = _v13_guarded_lean_ground(semantic_target[0], env)
    target_right = _v13_guarded_lean_ground(semantic_target[1], env)
    return _v13_GUARDED_LEAN_HEAD + _v13_guarded_lean_middle(program, opposite) + _v13_GUARDED_LEAN_PROOFS + f'\n\n{source_statement}\nend CM\nend submission\nopen submission\n\ndef submission : Goal := by\n  refine ⟨CM, CM.instMagma, CM.source_instance, ?_⟩\n  intro target\n  have bad := target {apps}\n  change {target_left} = {target_right} at bad\n  exact (show Not ({_v13_guarded_lean_value(left_value)} = {_v13_guarded_lean_value(right_value)}) from by decide) bad\n'

def _v13_guarded_program_model(source, target):
    if not (_v13_guarded_source_closed(source, False) or _v13_guarded_source_closed(source, True)):
        return None
    shallow = _v13_guarded_trees(1) + [_v13_gk(_v13_gk(_v13_GE)), _v13_gp(_v13_GE, _v13_gk(_v13_GE)), _v13_gp(_v13_gk(_v13_GE), _v13_GE)]
    deep = _v13_guarded_trees(2)
    candidates = []
    for ordinal, program in enumerate(_v13_guarded_programs()):
        if time.monotonic() >= _v13_DEADLINE:
            return None
        for opposite in (False, True):
            if _v13_guarded_holds(source, program, shallow, opposite):
                candidates.append((ordinal, program, opposite))
    for _ordinal, program, opposite in candidates:
        if time.monotonic() >= _v13_DEADLINE:
            return None
        if not _v13_guarded_holds(source, program, deep, opposite):
            continue
        if not _v13_guarded_contract(program):
            continue
        if not _v13_guarded_source_closed(source, opposite):
            continue
        witness = _v13_guarded_witness(target, program, shallow, opposite)
        if witness is None:
            continue
        code = _v13_compile_guarded_model(source, target, program, opposite, witness)
        if len(code.encode('utf-8')) <= MAX_FALSE_CERTIFICATE_BYTES:
            return code

def _v13_reset_search_state():
    global _v13_DEADLINE
    global _v13_STRICT_LAST_MODEL
    global _v13_STRICT_LAST_SOURCE_CERT
    global _v13_STRICT_LAST_RULE_POOL
    global _v13_STRICT_LAST_FALLBACKS
    _v13_COMPLETION_CACHE.clear()
    _v13_SELECTION_CACHE.clear()
    _v13_STRICT_FAILURES.clear()
    _v13_STRICT_LAST_MODEL = None
    _v13_STRICT_LAST_SOURCE_CERT = None
    _v13_STRICT_LAST_RULE_POOL = None
    _v13_STRICT_LAST_FALLBACKS = ()
    _v13_DEADLINE = time.monotonic()

def _v13_checked_certificate(code):
    certificate_bytes = len(code.encode("utf-8"))
    if certificate_bytes > MAX_FALSE_CERTIFICATE_BYTES:
        return None, certificate_bytes
    return code, certificate_bytes


_PAPER_HIT = None
_PAPER_GUARDED_ORIENTATION = None
_PAPER_HEARTBEAT_STOP = threading.Event()
_PAPER_HEARTBEAT_THREAD = None


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


_paper_original_guarded_compile = _v13_compile_guarded_model


def _paper_guarded_compile(*args, **kwargs):
    global _PAPER_GUARDED_ORIENTATION
    result = _paper_original_guarded_compile(*args, **kwargs)
    opposite = kwargs.get("opposite", args[3] if len(args) > 3 else False)
    if result:
        _PAPER_GUARDED_ORIENTATION = "dual" if opposite else "direct"
    return result


_v13_compile_guarded_model = _paper_guarded_compile


def _paper_completion_metadata(index=-1, operational=False, priority=False,
                               residual_policy=0, strict_semantic_gate=False,
                               compound_only=False):
    return {
        "subprocedure": "strict_completion",
        "index": index,
        "operational": operational,
        "priority": priority,
        "residual_policy": residual_policy,
        "strict_semantic_gate": strict_semantic_gate,
        "compound_only": compound_only,
    }


def _paper_v13_strict_search(source, target, seconds):
    """Solo v9 v13 queue with only group_word_model removed."""
    global _v13_DEADLINE, _v13_STRICT_LAST_FALLBACKS, _v13_JUDGE_FALLBACKS
    global _PAPER_HIT
    search_end = time.monotonic() + seconds
    mirrored_source = tuple(_v13_opposite_term(term) for term in source)
    mirrored_target = tuple(_v13_opposite_term(term) for term in target)
    orientations = ((source, target, False), (mirrored_source, mirrored_target, True))
    jobs = []
    jobs.append((
        lambda: _v13_guarded_program_model(source, target),
        False,
        20.0,
        {"subprocedure": "guarded_decoder"},
    ))
    for left, right, mirrored in orientations:
        jobs.append((
            lambda left=left, right=right: _v13_strict_completion_candidate(left, right),
            mirrored,
            3.0,
            _paper_completion_metadata(),
        ))
    trace_shapes = [(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (2, 0), (2, 1)]
    trace_shapes += [(index, 0) for index in range(3, 8)]
    for index, depth in trace_shapes:
        for left, right, mirrored in orientations:
            jobs.append((
                lambda left=left, right=right, index=index, depth=depth:
                    _v13_strict_trace_candidate(left, right, index, depth),
                mirrored,
                5.0 if depth else 4.0,
                {
                    "subprocedure": "trace",
                    "trace_index": index,
                    "tableau_depth": depth,
                    "generalized": False,
                },
            ))
        if (index, depth) == (0, 0):
            for left, right, mirrored in orientations:
                jobs.append((
                    lambda left=left, right=right: _v13_strict_completion_candidate(
                        left, right, operational=2, priority=True,
                        residual_policy=-1, strict_semantic_gate=True,
                    ),
                    mirrored,
                    3.5,
                    _paper_completion_metadata(
                        operational=2, priority=True, residual_policy=-1,
                        strict_semantic_gate=True,
                    ),
                ))
            for left, right, mirrored in orientations:
                jobs.append((
                    lambda left=left, right=right: _v13_strict_completion_candidate(
                        left, right, index=0, operational=2, priority=True,
                        residual_policy=-1, strict_semantic_gate=True,
                        compound_only=True,
                    ),
                    mirrored,
                    3.5,
                    _paper_completion_metadata(
                        index=0, operational=2, priority=True,
                        residual_policy=-1, strict_semantic_gate=True,
                        compound_only=True,
                    ),
                ))
    for index in range(4):
        for left, right, mirrored in orientations:
            jobs.append((
                lambda left=left, right=right, index=index:
                    _v13_strict_trace_candidate(left, right, index, generalized=True),
                mirrored,
                3.0,
                {
                    "subprocedure": "trace",
                    "trace_index": index,
                    "tableau_depth": 0,
                    "generalized": True,
                },
            ))
    for left, right, mirrored in orientations:
        for index in range(4):
            jobs.append((
                lambda left=left, right=right, index=index:
                    _v13_strict_completion_candidate(left, right, index),
                mirrored,
                6.0,
                _paper_completion_metadata(index=index),
            ))
    for left, right, mirrored in orientations:
        jobs.append((
            lambda left=left, right=right: _v13_strict_completion_candidate(left, right),
            mirrored,
            30.0,
            _paper_completion_metadata(),
        ))
        jobs.append((
            lambda left=left, right=right: _v13_strict_completion_candidate(
                left, right, operational=2, priority=True,
                residual_policy=-1, strict_semantic_gate=True,
            ),
            mirrored,
            30.0,
            _paper_completion_metadata(
                operational=2, priority=True, residual_policy=-1,
                strict_semantic_gate=True,
            ),
        ))
    # Long, symmetric lane for the highest-ranked source generalization.
    jobs = []
    for left, right, mirrored in orientations:
        jobs.append((
            lambda left=left, right=right:
                _v13_strict_completion_candidate(left, right, index=0),
            mirrored,
            59.0,
            _paper_completion_metadata(index=0),
        ))
    for search, mirrored, budget, metadata in jobs:
        now = time.monotonic()
        if now >= search_end:
            break
        _v13_DEADLINE = min(search_end, now + budget)
        _v13_STRICT_LAST_FALLBACKS = ()
        job_started = time.monotonic()
        try:
            candidate = search()
        except MemoryError:
            _v13_COMPLETION_CACHE.clear()
            _v13_SELECTION_CACHE.clear()
            gc.collect()
            continue
        except Exception:
            continue
        if not candidate:
            continue
        fallbacks = _v13_STRICT_LAST_FALLBACKS
        if mirrored:
            preserve_trace_source_call = bool(
                metadata.get("subprocedure") == "trace"
                and metadata.get("generalized")
            )
            candidate = _v13_opposite_code(
                candidate,
                source,
                preserve_trace_source_call=preserve_trace_source_call,
            )
            fallbacks = tuple(
                _v13_opposite_code(
                    code,
                    source,
                    preserve_trace_source_call=preserve_trace_source_call,
                )
                for code in fallbacks
            )
        _v13_JUDGE_FALLBACKS = tuple(
            code for code in fallbacks if code and code != candidate
        )
        _PAPER_HIT = dict(metadata)
        _PAPER_HIT["orientation"] = (
            _PAPER_GUARDED_ORIENTATION
            if metadata["subprocedure"] == "guarded_decoder"
               and _PAPER_GUARDED_ORIENTATION is not None
            else "dual" if mirrored else "direct"
        )
        _PAPER_HIT["subprocedure_elapsed_seconds"] = round(
            time.monotonic() - job_started, 6
        )
        return candidate
    return None


def _paper_v13_infinite_candidate(source_formula, target_formula, seconds):
    global _v13_JUDGE_FALLBACKS
    _v13_JUDGE_FALLBACKS = ()
    source = _v13_parse_eq(source_formula)
    target = _v13_parse_eq(target_formula)
    order = []
    for term in source + target:
        _v13_variables(term, order)
    alpha = {variable: f"q{index}" for index, variable in enumerate(order)}
    source = tuple(_v13_rename_term(term, alpha) for term in source)
    target = tuple(_v13_rename_term(term, alpha) for term in target)
    _v13_reset_search_state()
    try:
        return _paper_v13_strict_search(source, target, seconds)
    finally:
        _v13_reset_search_state()
        gc.collect()


def _paper_diagnostic(payload):
    print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")), file=sys.stderr, flush=True)


def _paper_judge_message(code, metadata):
    return {
        "call": "judge",
        "verdict": "false",
        "code": code,
        "metadata": metadata,
    }


def main():
    global _PAPER_HIT, _PAPER_GUARDED_ORIENTATION
    _paper_start_heartbeat()
    raw = sys.stdin.readline()
    if not raw:
        return 2
    startup = json.loads(raw)
    problem = startup["problem"]
    _PAPER_HIT = None
    _PAPER_GUARDED_ORIENTATION = None
    started = time.monotonic()
    try:
        candidate = _paper_v13_infinite_candidate(
            problem["equation1"], problem["equation2"], SEARCH_BUDGET_SECONDS
        )
    except Exception as error:
        elapsed_value = time.monotonic() - started
        terminal = {
            "phase": "isolated_search_terminal",
            "search_program": "completion_only",
            "status": "ERROR",
            "error_type": type(error).__name__,
            "error": str(error),
            "elapsed_seconds": round(elapsed_value, 6),
        }
        _paper_diagnostic(terminal)
        _paper_complete_without_candidate(terminal)
    elapsed_value = time.monotonic() - started
    elapsed = round(elapsed_value, 6)
    terminal = {
        "phase": "isolated_search_terminal",
        "search_program": "completion_only",
        "status": "FOUND" if candidate else "NO_MODEL_FOUND",
        "configured_search_seconds": SEARCH_BUDGET_SECONDS,
        "elapsed_seconds": elapsed,
        "hit": _PAPER_HIT,
    }
    _paper_diagnostic(terminal)
    if not candidate:
        _paper_complete_without_candidate(terminal)
    candidate, certificate_bytes = _v13_checked_certificate(candidate)
    if candidate is None:
        terminal["status"] = "FOUND_OVERSIZE_CERTIFICATE"
        terminal["certificate_bytes"] = certificate_bytes
        _paper_diagnostic(terminal)
        _paper_complete_without_candidate(terminal)
    metadata = {
        "experiment_schema": "isolated-infinite-search-v1",
        "search_program": "completion_only",
        "configured_search_seconds": SEARCH_BUDGET_SECONDS,
        "search_elapsed_seconds": elapsed,
        "certificate_bytes": certificate_bytes,
        **(_PAPER_HIT or {}),
    }
    candidates = [candidate]
    candidates.extend(
        code for code in _v13_JUDGE_FALLBACKS
        if isinstance(code, str)
        and code != candidate
        and len(code.encode("utf-8")) <= MAX_FALSE_CERTIFICATE_BYTES
    )
    for index, code in enumerate(candidates):
        attempt_metadata = dict(metadata)
        attempt_metadata["certificate_fallback_index"] = index
        print(json.dumps(
            _paper_judge_message(code, attempt_metadata),
            ensure_ascii=False,
            separators=(",", ":"),
        ), flush=True)
        response_line = sys.stdin.readline()
        if not response_line:
            return 2
        if json.loads(response_line).get("status") == "accepted":
            return 0
    terminal["status"] = "ALL_CANDIDATES_REJECTED"
    _paper_diagnostic(terminal)
    _paper_complete_without_candidate(terminal)


if __name__ == "__main__":
    raise SystemExit(main())
