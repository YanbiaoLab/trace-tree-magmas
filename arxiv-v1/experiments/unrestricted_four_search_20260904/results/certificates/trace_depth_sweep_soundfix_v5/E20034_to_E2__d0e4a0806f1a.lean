import Lean.Elab.Tactic.Omega
import JudgeProblem
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace submission
inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM
deriving DecidableEq
namespace CM
def L : CM → CM | e => e | k _ => e | p a _ => a
def R : CM → CM | e => e | k _ => e | p _ b => b
def U : CM → CM | e => e | k a => a | p _ _ => e
def sz : CM → Nat
  | e => 0
  | k a => sz a + 1
  | p a b => (sz a + 1) + (sz b + 1)
theorem sz_lt_p_left (a b : CM) : sz a < sz (p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))
theorem sz_lt_p_right (a b : CM) : sz b < sz (p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))
mutual
inductive Code : CM → CM → CM → Prop
  | law (x v0 v1 : CM)
 :
      Code (p v0 v0) (p (p v1 (p x x)) v1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 : CM, a = (p q_v0 q_v0) ∧ b = (p (p q_v1 (p q_x q_x)) q_v1) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 => ⟨x, v0, v1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R (L b)))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc)
    omega

noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_hit {{a b o : CM}} (h : Code a b o) : eval a b = o := by
  rw [eval, dif_pos ⟨o, h⟩]
  exact code_unique (Classical.choose_spec ⟨o, h⟩) h
theorem eval_raw {{a b : CM}} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_step (a b : CM) : Step a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rcases h with ⟨o, hc⟩
    rw [eval_hit hc]
    exact Step.hit hc
  · rw [eval_raw h]
    exact Step.raw a b
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => q) ha
  change v0 = (p q_v0 q_v0) at e0
  have e1 := congrArg (fun q => q) hb
  change v0 = (p (p q_v1 (p q_x q_x)) q_v1) at e1
  have cyc : q_v1 = (p q_v1 (p q_x q_x)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p (p q_v1 (p q_x q_x)) q_v1) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_v1 (p q_x q_x)) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v1 (p q_x q_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v1 (p q_x q_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_v1 (p q_x q_x)) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_v1 (p q_x q_x)) := Eq.symm (pst5); pst6)
  have hlt : sz q_v1 < sz (p q_v1 (p q_x q_x)) := sz_lt_p_left q_v1 (p q_x q_x)
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => q) ha
  change x = (p q_v0 q_v0) at e0
  have e1 := congrArg (fun q => q) hb
  change x = (p (p q_v1 (p q_x q_x)) q_v1) at e1
  have cyc : q_v1 = (p q_v1 (p q_x q_x)) := (let peq0 : x = (p q_v0 q_v0) := e0; let peq1 : x = (p (p q_v1 (p q_x q_x)) q_v1) := e1; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_v1 (p q_x q_x)) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v1 (p q_x q_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v1 (p q_x q_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_v1 (p q_x q_x)) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_v1 (p q_x q_x)) := Eq.symm (pst5); pst6)
  have hlt : sz q_v1 < sz (p q_v1 (p q_x q_x)) := sz_lt_p_left q_v1 (p q_x q_x)
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => q) ha
  change v1 = (p q_v0 q_v0) at e0
  have e1 := congrArg (fun q => (L q)) hb
  change x = (p q_v1 (p q_x q_x)) at e1
  have e2 := congrArg (fun q => (R q)) hb
  change x = q_v1 at e2
  have cyc : q_v1 = (p q_v1 (p q_x q_x)) := (let peq1 : x = (p q_v1 (p q_x q_x)) := e1; let peq2 : x = q_v1 := e2; let pst0 : (p q_v1 (p q_x q_x)) = x := Eq.symm (peq1); let pst1 : (p q_v1 (p q_x q_x)) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_v1 (p q_x q_x)) := Eq.symm (pst1); pst2)
  have hlt : sz q_v1 < sz (p q_v1 (p q_x q_x)) := sz_lt_p_left q_v1 (p q_x q_x)
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p v1 (p x x)) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => (L q)) ha
  change v1 = q_v0 at e0
  have e1 := congrArg (fun q => (R q)) ha
  change (p x x) = q_v0 at e1
  have e2 := congrArg (fun q => q) hb
  change v1 = (p (p q_v1 (p q_x q_x)) q_v1) at e2
  have cyc : q_v1 = (p q_v1 (p q_x q_x)) := (let peq0 : v1 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq2 : v1 = (p (p q_v1 (p q_x q_x)) q_v1) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v1 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v1 := Eq.symm (pst1); let pst3 : (p x x) = (p (p q_v1 (p q_x q_x)) q_v1) := Eq.trans (pst2) (peq2); let pst4 : x = (p q_v1 (p q_x q_x)) := congrArg (fun q => L q) (pst3); let pst5 : (p q_v1 (p q_x q_x)) = x := Eq.symm (pst4); let pst6 : x = q_v1 := congrArg (fun q => R q) (pst3); let pst7 : (p q_v1 (p q_x q_x)) = q_v1 := Eq.trans (pst5) (pst6); let pst8 : q_v1 = (p q_v1 (p q_x q_x)) := Eq.symm (pst7); pst8)
  have hlt : sz q_v1 < sz (p q_v1 (p q_x q_x)) := sz_lt_p_left q_v1 (p q_x q_x)
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 v0) (eval (eval v1 (eval x x)) v1)) := by

  change x = (eval (eval v0 v0) (eval (eval v1 (eval x x)) v1))
  have rawEq : (eval (eval v0 v0) (eval (eval v1 (eval x x)) v1)) = (eval (p v0 v0) (p (p v1 (p x x)) v1)) := by
    calc
      (eval (eval v0 v0) (eval (eval v1 (eval x x)) v1)) = (eval (p v0 v0) (eval (eval v1 (eval x x)) v1)) := congrArg (fun q => (eval q (eval (eval v1 (eval x x)) v1))) (eval_raw (nr0 x v0 v1))
      _ = (eval (p v0 v0) (eval (eval v1 (p x x)) v1)) := congrArg (fun q => (eval (p v0 v0) (eval (eval v1 q) v1))) (eval_raw (nr1 x v0 v1))
      _ = (eval (p v0 v0) (eval (p v1 (p x x)) v1)) := congrArg (fun q => (eval (p v0 v0) (eval q v1))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p v0 v0) (p (p v1 (p x x)) v1)) := congrArg (fun q => (eval (p v0 v0) q)) (eval_raw (nr3 x v0 v1))
  exact (eval_hit (Code.law x v0 v1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1
    exact CM.source_holds x v0 v1
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
