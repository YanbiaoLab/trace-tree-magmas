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
      Code (p v0 (p (p x x) v0)) (p v1 v1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 : CM, a = (p q_v0 (p (p q_x q_x) q_v0)) ∧ b = (p q_v1 q_v1) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 => ⟨x, v0, v1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R a)))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_first {a b : CM} : ¬ Step a b a := by
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
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => q) ha
  change x = (p q_v0 (p (p q_x q_x) q_v0)) at e0
  have e1 := congrArg (fun q => q) hb
  change x = (p q_v1 q_v1) at e1
  have cyc : q_v1 = (p (p q_x q_x) q_v1) := (let peq0 : x = (p q_v0 (p (p q_x q_x) q_v0)) := e0; let peq1 : x = (p q_v1 q_v1) := e1; let pst0 : (p q_v0 (p (p q_x q_x) q_v0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) q_v0)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) q_v1) := congrArg (fun q => p (p q_x q_x) q) (pst2); let pst4 : (p (p q_x q_x) q_v1) = (p (p q_x q_x) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_x) q_v0) = q_v1 := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_x) q_v1) = q_v1 := Eq.trans (pst4) (pst5); let pst7 : q_v1 = (p (p q_x q_x) q_v1) := Eq.symm (pst6); pst7)
  have hlt : sz q_v1 < sz (p (p q_x q_x) q_v1) := sz_lt_p_right (p q_x q_x) q_v1
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p x x) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => (L q)) ha
  change x = q_v0 at e0
  have e1 := congrArg (fun q => (R q)) ha
  change x = (p (p q_x q_x) q_v0) at e1
  have e2 := congrArg (fun q => q) hb
  change v0 = (p q_v1 q_v1) at e2
  have cyc : q_v0 = (p (p q_x q_x) q_v0) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p q_x q_x) q_v0) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_x) q_v0) := Eq.trans (pst0) (peq1); pst1)
  have hlt : sz q_v0 < sz (p (p q_x q_x) q_v0) := sz_lt_p_right (p q_x q_x) q_v0
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p (p x x) v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => q) ha
  change v0 = (p q_v0 (p (p q_x q_x) q_v0)) at e0
  have e1 := congrArg (fun q => (L q)) hb
  change (p x x) = q_v1 at e1
  have e2 := congrArg (fun q => (R q)) hb
  change v0 = q_v1 at e2
  have cyc : x = (p (p q_x q_x) x) := (let peq0 : v0 = (p q_v0 (p (p q_x q_x) q_v0)) := e0; let peq1 : (p x x) = q_v1 := e1; let peq2 : v0 = q_v1 := e2; let pst0 : (p q_v0 (p (p q_x q_x) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) q_v0)) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p x x) := Eq.symm (peq1); let pst3 : (p q_v0 (p (p q_x q_x) q_v0)) = (p x x) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = x := congrArg (fun q => L q) (pst3); let pst5 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) x) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst6 : (p (p q_x q_x) x) = (p (p q_x q_x) q_v0) := Eq.symm (pst5); let pst7 : (p (p q_x q_x) q_v0) = x := congrArg (fun q => R q) (pst3); let pst8 : (p (p q_x q_x) x) = x := Eq.trans (pst6) (pst7); let pst9 : x = (p (p q_x q_x) x) := Eq.symm (pst8); pst9)
  have hlt : sz x < sz (p (p q_x q_x) x) := sz_lt_p_right (p q_x q_x) x
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, ha, hb, ho⟩
  have e0 := congrArg (fun q => q) ha
  change v1 = (p q_v0 (p (p q_x q_x) q_v0)) at e0
  have e1 := congrArg (fun q => q) hb
  change v1 = (p q_v1 q_v1) at e1
  have cyc : q_v1 = (p (p q_x q_x) q_v1) := (let peq0 : v1 = (p q_v0 (p (p q_x q_x) q_v0)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p q_v0 (p (p q_x q_x) q_v0)) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) q_v0)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) q_v1) := congrArg (fun q => p (p q_x q_x) q) (pst2); let pst4 : (p (p q_x q_x) q_v1) = (p (p q_x q_x) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_x) q_v0) = q_v1 := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_x) q_v1) = q_v1 := Eq.trans (pst4) (pst5); let pst7 : q_v1 = (p (p q_x q_x) q_v1) := Eq.symm (pst6); pst7)
  have hlt : sz q_v1 < sz (p (p q_x q_x) q_v1) := sz_lt_p_right (p q_x q_x) q_v1
  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 (eval (eval x x) v0)) (eval v1 v1)) := by

  change x = (eval (eval v0 (eval (eval x x) v0)) (eval v1 v1))
  have rawEq : (eval (eval v0 (eval (eval x x) v0)) (eval v1 v1)) = (eval (p v0 (p (p x x) v0)) (p v1 v1)) := by
    calc
      (eval (eval v0 (eval (eval x x) v0)) (eval v1 v1)) = (eval (eval v0 (eval (p x x) v0)) (eval v1 v1)) := congrArg (fun q => (eval (eval v0 (eval q v0)) (eval v1 v1))) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval v0 (p (p x x) v0)) (eval v1 v1)) := congrArg (fun q => (eval (eval v0 q) (eval v1 v1))) (eval_raw (nr1 x v0 v1))
      _ = (eval (p v0 (p (p x x) v0)) (eval v1 v1)) := congrArg (fun q => (eval q (eval v1 v1))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p v0 (p (p x x) v0)) (p v1 v1)) := congrArg (fun q => (eval (p v0 (p (p x x) v0)) q)) (eval_raw (nr3 x v0 v1))
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
