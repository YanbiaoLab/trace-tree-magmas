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
  | law (x v0 v1 H0 : CM)
      (s0 : Step v0 v1 H0) :
      Code (p v0 (p (p (p v0 v0) H0) (p (p x x) x))) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_v1 q_H0 ∧ a = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R (R a))))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz b < sz (p o a) := by
  cases h with
  | raw => simp [sz] <;> omega
  | hit hc =>
    have hb := (code_bounds hc).1
    simp [sz] at hb ⊢ <;> omega

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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p v0 v0) H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change (p v0 v1) = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change (p v0 v1) = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change H0 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change H0 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v0 at e1
    have cyc : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := (let peq0 : x = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v0 at e1
    have cyc : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := (let peq0 : x = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p x x) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => (L q)) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => (R q)) ha
    change x = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) at e1
    have e2 := congrArg (fun q => q) hb
    change x = q_v0 at e2
    have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => (L q)) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => (R q)) ha
    change x = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) at e1
    have e2 := congrArg (fun q => q) hb
    change x = q_v0 at e2
    have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p v0 v0) H0) (p (p x x) x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change (p v0 v0) = q_v0 at e0
      have e1 := congrArg (fun q => (L (R q))) ha
      change v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) at e1
      have e2 := congrArg (fun q => (R (R q))) ha
      change v1 = (p (p q_x q_x) q_x) at e2
      have e3 := congrArg (fun q => q) hb
      change (p (p x x) x) = q_v0 at e3
      have cyc : v0 = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) := e1; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst3); let pst5 : (p q_v0 q_v1) = (p (p v0 v0) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst6 : (p (p (p v0 v0) (p v0 v0)) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (pst5); let pst7 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Eq.trans (pst4) (pst6); let pst8 : v0 = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Eq.trans (peq1) (pst7); pst8)
      have hlt : sz v0 < sz (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change (p v0 v0) = q_v0 at e0
      have e1 := congrArg (fun q => (L (R q))) ha
      change v0 = (p (p q_v0 q_v0) q_H0) at e1
      have e2 := congrArg (fun q => (R (R q))) ha
      change v1 = (p (p q_x q_x) q_x) at e2
      have e3 := congrArg (fun q => q) hb
      change (p (p x x) x) = q_v0 at e3
      have cyc : v0 = (p (p (p v0 v0) (p v0 v0)) q_H0) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : v0 = (p (p q_v0 q_v0) q_H0) := e1; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) q_H0) = (p (p (p v0 v0) (p v0 v0)) q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst5 : v0 = (p (p (p v0 v0) (p v0 v0)) q_H0) := Eq.trans (peq1) (pst4); pst5)
      have hlt : sz v0 < sz (p (p (p v0 v0) (p v0 v0)) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) q_H0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change (p v0 v0) = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change H0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change (p (p x x) x) = q_v0 at e2
      have cyc : x = (p x x) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq2 : (p (p x x) x) = q_v0 := e2; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p (p x x) x) = (p v0 v0) := Eq.trans (peq2) (pst0); let pst2 : x = v0 := congrArg (fun q => R q) (pst1); let pst3 : (p x x) = v0 := congrArg (fun q => L q) (pst1); let pst4 : v0 = (p x x) := Eq.symm (pst3); let pst5 : x = (p x x) := Eq.trans (pst2) (pst4); pst5)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change (p v0 v0) = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change H0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change (p (p x x) x) = q_v0 at e2
      have cyc : x = (p x x) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq2 : (p (p x x) x) = q_v0 := e2; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p (p x x) x) = (p v0 v0) := Eq.trans (peq2) (pst0); let pst2 : x = v0 := congrArg (fun q => R q) (pst1); let pst3 : (p x x) = v0 := congrArg (fun q => L q) (pst1); let pst4 : v0 = (p x x) := Eq.symm (pst3); let pst5 : x = (p x x) := Eq.trans (pst2) (pst4); pst5)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr5 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code v0 (p (p (p v0 v0) H0) (p (p x x) x)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) at e0
      have e1 := congrArg (fun q => q) hb
      change (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := e0; let peq1 : (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p v0 v1)) := congrArg (fun q => p q (p v0 v1)) (pst2); let pst4 : (p v0 v1) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1) := congrArg (fun q => p q v1) (peq0); let pst5 : (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) := congrArg (fun q => p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) q) (pst4); let pst6 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) := Eq.trans (pst3) (pst5); let pst7 : (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := congrArg (fun q => p q (p (p x x) x)) (pst6); let pst8 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) = (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) := Eq.symm (pst7); let pst9 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) = q_v0 := Eq.trans (pst8) (peq1); let pst10 : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := Eq.symm (pst9); pst10)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1))) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v1)) (p (p x x) x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) at e0
      have e1 := congrArg (fun q => q) hb
      change (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := e0; let peq1 : (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p v0 v1)) := congrArg (fun q => p q (p v0 v1)) (pst2); let pst4 : (p v0 v1) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1) := congrArg (fun q => p q v1) (peq0); let pst5 : (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) := congrArg (fun q => p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) q) (pst4); let pst6 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) := Eq.trans (pst3) (pst5); let pst7 : (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := congrArg (fun q => p q (p (p x x) x)) (pst6); let pst8 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) = (p (p (p v0 v0) (p v0 v1)) (p (p x x) x)) := Eq.symm (pst7); let pst9 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) = q_v0 := Eq.trans (pst8) (peq1); let pst10 : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := Eq.symm (pst9); pst10)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1))) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v1)) (p (p x x) x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) at e0
      have e1 := congrArg (fun q => q) hb
      change (p (p (p v0 v0) H0) (p (p x x) x)) = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) := e0; let peq1 : (p (p (p v0 v0) H0) (p (p x x) x)) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) H0) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) := congrArg (fun q => p q H0) (pst2); let pst4 : (p (p (p v0 v0) H0) (p (p x x) x)) = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := congrArg (fun q => p q (p (p x x) x)) (pst3); let pst5 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) = (p (p (p v0 v0) H0) (p (p x x) x)) := Eq.symm (pst4); let pst6 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) = q_v0 := Eq.trans (pst5) (peq1); let pst7 : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := Eq.symm (pst6); pst7)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0)) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p (p q_x q_x) q_x)))) H0) (p (p x x) x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) at e0
      have e1 := congrArg (fun q => q) hb
      change (p (p (p v0 v0) H0) (p (p x x) x)) = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) := e0; let peq1 : (p (p (p v0 v0) H0) (p (p x x) x)) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) H0) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) := congrArg (fun q => p q H0) (pst2); let pst4 : (p (p (p v0 v0) H0) (p (p x x) x)) = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := congrArg (fun q => p q (p (p x x) x)) (pst3); let pst5 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) = (p (p (p v0 v0) H0) (p (p x x) x)) := Eq.symm (pst4); let pst6 : (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) = q_v0 := Eq.trans (pst5) (peq1); let pst7 : q_v0 = (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := Eq.symm (pst6); pst7)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0)) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p (p q_x q_x) q_x)))) H0) (p (p x x) x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 (eval (eval (eval v0 v0) (eval v0 v1)) (eval (eval x x) x))) v0) := by
  let H0 := eval v0 v1
  have e0a : v0 = v0 := by
    change v0 = v0
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step v0 v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v0 v1
  change x = (eval (eval v0 (eval (eval (eval v0 v0) H0) (eval (eval x x) x))) v0)
  have rawEq : (eval (eval v0 (eval (eval (eval v0 v0) H0) (eval (eval x x) x))) v0) = (eval (p v0 (p (p (p v0 v0) H0) (p (p x x) x))) v0) := by
    calc
      (eval (eval v0 (eval (eval (eval v0 v0) H0) (eval (eval x x) x))) v0) = (eval (eval v0 (eval (eval (p v0 v0) H0) (eval (eval x x) x))) v0) := congrArg (fun q => (eval (eval v0 (eval (eval q H0) (eval (eval x x) x))) v0)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval v0 (eval (p (p v0 v0) H0) (eval (eval x x) x))) v0) := congrArg (fun q => (eval (eval v0 (eval q (eval (eval x x) x))) v0)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval v0 (eval (p (p v0 v0) H0) (eval (p x x) x))) v0) := congrArg (fun q => (eval (eval v0 (eval (p (p v0 v0) H0) (eval q x))) v0)) (eval_raw (nr2 x v0 v1))
      _ = (eval (eval v0 (eval (p (p v0 v0) H0) (p (p x x) x))) v0) := congrArg (fun q => (eval (eval v0 (eval (p (p v0 v0) H0) q)) v0)) (eval_raw (nr3 x v0 v1))
      _ = (eval (eval v0 (p (p (p v0 v0) H0) (p (p x x) x))) v0) := congrArg (fun q => (eval (eval v0 q) v0)) (eval_raw (nr4 x v0 v1 H0 s0))
      _ = (eval (p v0 (p (p (p v0 v0) H0) (p (p x x) x))) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr5 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
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
