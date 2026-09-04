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
  | law (x v0 v1 H0 H1 : CM)
      (s0 : Step (p v0 v0) v1 H0)
      (s1 : Step x v0 H1) :
      Code (p (p (p H0 v0) v0) (p H1 x)) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step (p q_v0 q_v0) q_v1 q_H0 ∧ Step q_x q_v0 q_H1 ∧ a = (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
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
theorem code_no_pair_left (v k : CM) :
    ¬ ∃ o, Code (p v k) v o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p (p q_x q_v0) q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := (let peq0 : v = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_H1 q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := (let peq0 : v = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H0 q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p (p q_x q_v0) q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H0 q_v0) q_v0) := (let peq0 : v = (p (p q_H0 q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_H0 q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H0 q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 q_v0) q_v0) := Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H0 q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_H1 q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H0 q_v0) q_v0) := (let peq0 : v = (p (p q_H0 q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_H0 q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H0 q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 q_v0) q_v0) := Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw => exact code_no_pair_left a b
  | hit sh =>
    rintro ⟨u, hk⟩
    have ho := (code_bounds sh).2
    have ha := (code_bounds hk).1
    omega
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) := (let peq0 : v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0)) (sz_lt_p_left (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) := (let peq0 : v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0)) (sz_lt_p_left (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) := (let peq0 : v0 = (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v0)) (sz_lt_p_left (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) := (let peq0 : v0 = (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v0)) (sz_lt_p_left (p (p q_H0 q_v0) q_v0) (p q_H1 q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step (p v0 v0) v1 H0) :
    ¬ ∃ o, Code H0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v1 = (p (p q_x q_v0) q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) q_v1) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_v1) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_v1) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v1 = (p q_H1 q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) q_v1) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_v1) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) q_v1) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_v1) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H0 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v1 = (p (p q_x q_v0) q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_v0 = (p q_H0 q_v0) := (let peq0 : v0 = (p q_H0 q_v0) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p q_H0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_H0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H0 q_v0) := sz_lt_p_right q_H0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H0 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v1 = (p q_H1 q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_v0 = (p q_H0 q_v0) := (let peq0 : v0 = (p q_H0 q_v0) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p q_H0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_H0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H0 q_v0) := sz_lt_p_right q_H0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz (p v0 v0) < sz H0 := by
          have structural : sz (p q_v0 q_v0) < sz (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left (p q_v0 q_v0) q_v1) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0)) (sz_lt_p_left (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x))
          have large_eq : sz (p v0 v0) = sz (p q_v0 q_v0) := congrArg sz (Eq.trans (congrArg (fun q => p q v0) (p1)) (congrArg (fun q => p q_v0 q) (p1)))
          have small_eq : sz H0 = sz (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p (p q_x q_v0) q_x)) := congrArg sz (p0)
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz (p v0 v0) < sz H0 := by
          have structural : sz (p q_v0 q_v0) < sz (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left (p q_v0 q_v0) q_v1) (sz_lt_p_left (p (p q_v0 q_v0) q_v1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0)) (sz_lt_p_left (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x))
          have large_eq : sz (p v0 v0) = sz (p q_v0 q_v0) := congrArg sz (Eq.trans (congrArg (fun q => p q v0) (p1)) (congrArg (fun q => p q_v0 q) (p1)))
          have small_eq : sz H0 = sz (p (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) (p q_H1 q_x)) := congrArg sz (p0)
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p (p (p q_H0 q_v0) q_v0) (p (p q_x q_v0) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p (p (p q_H0 q_v0) q_v0) (p q_H1 q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB qs1hB z0 z1 z2
        omega
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step (p v0 v0) v1 H0) :
    ¬ ∃ o, Code (p H0 v0) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L (L q)))) ha
        change v0 = (p (p q_v0 q_v0) q_v1) at e0
        have e1 := congrArg (fun q => (R (L (L q)))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R (L q))) ha
        change v1 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) ha
        change v0 = (p (p q_x q_v0) q_x) at e3
        have e4 := congrArg (fun q => q) hb
        change v0 = q_v0 at e4
        have cyc : q_v0 = (p (p q_v0 q_v0) q_v1) := (let peq0 : v0 = (p (p q_v0 q_v0) q_v1) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_v0 q_v0) q_v1) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_v1) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_v0 q_v0) q_v1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_v1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L (L q)))) ha
        change v0 = (p (p q_v0 q_v0) q_v1) at e0
        have e1 := congrArg (fun q => (R (L (L q)))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R (L q))) ha
        change v1 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) ha
        change v0 = (p q_H1 q_x) at e3
        have e4 := congrArg (fun q => q) hb
        change v0 = q_v0 at e4
        have cyc : q_v0 = (p (p q_v0 q_v0) q_v1) := (let peq0 : v0 = (p (p q_v0 q_v0) q_v1) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_v0 q_v0) q_v1) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_v1) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_v0 q_v0) q_v1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_v1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L (L q)))) ha
        change v0 = q_H0 at e0
        have e1 := congrArg (fun q => (R (L (L q)))) ha
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R (L q))) ha
        change v1 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) ha
        change v0 = (p (p q_x q_v0) q_x) at e3
        have e4 := congrArg (fun q => q) hb
        change v0 = q_v0 at e4
        have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq0 : v0 = q_H0 := e0; let peq1 : v0 = q_v0 := e1; let peq3 : v0 = (p (p q_x q_v0) q_x) := e3; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = q_v0 := Eq.trans (pst0) (peq1); let pst2 : v0 = q_v0 := Eq.trans (peq0) (pst1); let pst3 : q_v0 = v0 := Eq.symm (pst2); let pst4 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst3) (peq3); pst4)
        have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L (L q)))) (ha)
        change v0 = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L (L q)))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R (L q))) (ha)
        change v1 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_H1 q_x) at p3
        have z3 := congrArg sz p3
        have p4 := hb
        change v0 = q_v0 at p4
        have z4 := congrArg sz p4
        have p5 := ho
        change o = q_x at p5
        have z5 := congrArg sz p5
        simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3 z4 z5
        omega
  | hit s0h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change H0 = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p q_x q_v0) q_x) at e1
        have e2 := congrArg (fun q => q) hb
        change v0 = q_v0 at e2
        have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : v0 = (p (p q_x q_v0) q_x) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = v0 := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H0 = (p (p (p (p q_v0 q_v0) q_v1) q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_H1 q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz (p v0 v0) < sz H0 := by
          have structural : sz (p (p q_H1 q_x) (p q_H1 q_x)) < sz (p (p (p (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) (p q_H1 q_x)) (p q_H1 q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) (sz_lt_p_left (p (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) (p q_H1 q_x))) (sz_lt_p_left (p (p (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) (p q_H1 q_x)) (p q_H1 q_x))
          have large_eq : sz (p v0 v0) = sz (p (p q_H1 q_x) (p q_H1 q_x)) := congrArg sz (Eq.trans (congrArg (fun q => p q v0) (p1)) (congrArg (fun q => p (p q_H1 q_x) q) (p1)))
          have small_eq : sz H0 = sz (p (p (p (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) (p q_H1 q_x)) (p q_H1 q_x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_v1) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (p2.symm) (p1))) (congrArg (fun q => p (p q_H1 q_x) q) (Eq.trans (p2.symm) (p1)))))) (congrArg (fun q => p (p (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) q) (Eq.trans (p2.symm) (p1))))) (congrArg (fun q => p (p (p (p (p q_H1 q_x) (p q_H1 q_x)) q_v1) (p q_H1 q_x)) q) (Eq.trans (p2.symm) (p1)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change H0 = (p (p q_H0 q_v0) q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p q_x q_v0) q_x) at e1
        have e2 := congrArg (fun q => q) hb
        change v0 = q_v0 at e2
        have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : v0 = (p (p q_x q_v0) q_x) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = v0 := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H0 = (p (p q_H0 q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_H1 q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz q_x < sz q_v0 := by
          have structural : sz q_x < sz (p q_H1 q_x) := sz_lt_p_right q_H1 q_x
          have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
          have small_eq : sz q_v0 = sz (p q_H1 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.1).elim
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step x v0 H1) :
    ¬ ∃ o, Code H1 x o := by
  exact step_no_first s1

theorem nr4 (x v0 v1 H0 H1 : CM)
    (s0 : Step (p v0 v0) v1 H0)
    (s1 : Step x v0 H1) :
    ¬ ∃ o, Code (p (p H0 v0) v0) (p H1 x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have s1B := step_bound s1
    have s1N := step_no_first s1
    cases s1 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L (L (L q))))) ha
          change v0 = (p q_v0 q_v0) at e0
          have e1 := congrArg (fun q => (R (L (L (L q))))) ha
          change v0 = q_v1 at e1
          have e2 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e3
          have e4 := congrArg (fun q => (R q)) ha
          change v0 = (p (p q_x q_v0) q_x) at e4
          have e5 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e5
          have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq3 : v0 = q_v0 := e3; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L (L (L q))))) ha
          change v0 = (p q_v0 q_v0) at e0
          have e1 := congrArg (fun q => (R (L (L (L q))))) ha
          change v0 = q_v1 at e1
          have e2 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e3
          have e4 := congrArg (fun q => (R q)) ha
          change v0 = (p q_H1 q_x) at e4
          have e5 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e5
          have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq3 : v0 = q_v0 := e3; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change (p v0 v0) = q_H0 at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = q_v0 at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v0 = (p (p q_x q_v0) q_x) at e3
          have e4 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e4
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq2 : v0 = q_v0 := e2; let peq3 : v0 = (p (p q_x q_v0) q_x) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq2); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq3); pst1)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change (p v0 v0) = q_H0 at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = q_v0 at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v0 = (p q_H1 q_x) at e3
          have e4 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e4
          have cyc : q_H1 = (p x (p q_H1 q_x)) := (let peq2 : v0 = q_v0 := e2; let peq3 : v0 = (p q_H1 q_x) := e3; let peq4 : (p (p x v0) x) = q_v0 := e4; let pst0 : q_v0 = v0 := Eq.symm (peq2); let pst1 : q_v0 = (p q_H1 q_x) := Eq.trans (pst0) (peq3); let pst2 : v0 = (p q_H1 q_x) := Eq.trans (peq2) (pst1); let pst3 : (p x v0) = (p x (p q_H1 q_x)) := congrArg (fun q => p x q) (pst2); let pst4 : (p (p x v0) x) = (p (p x (p q_H1 q_x)) x) := congrArg (fun q => p q x) (pst3); let pst5 : (p (p x (p q_H1 q_x)) x) = (p (p x v0) x) := Eq.symm (pst4); let pst6 : (p (p x (p q_H1 q_x)) x) = q_v0 := Eq.trans (pst5) (peq4); let pst7 : (p (p x (p q_H1 q_x)) x) = (p q_H1 q_x) := Eq.trans (pst6) (pst1); let pst8 : (p x (p q_H1 q_x)) = q_H1 := congrArg (fun q => L q) (pst7); let pst9 : q_H1 = (p x (p q_H1 q_x)) := Eq.symm (pst8); pst9)
          have hlt : sz q_H1 < sz (p x (p q_H1 q_x)) := Nat.lt_trans (sz_lt_p_left q_H1 q_x) (sz_lt_p_right x (p q_H1 q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s1h =>
      have he : q_H0 = (p q_v0 q_v0) := (let peq0 : (p v0 v0) = q_H0 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq3 : v0 = (p q_H1 q_x) := congrArg (fun q => (R q)) (ha); let pst0 : q_H0 = (p v0 v0) := Eq.symm (peq0); let pst1 : q_v0 = v0 := Eq.symm (peq2); let pst2 : q_v0 = (p q_H1 q_x) := Eq.trans (pst1) (peq3); let pst3 : v0 = (p q_H1 q_x) := Eq.trans (peq2) (pst2); let pst4 : (p v0 v0) = (p (p q_H1 q_x) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p q_H1 q_x) := Eq.trans (peq2) (pst2); let pst6 : (p (p q_H1 q_x) v0) = (p (p q_H1 q_x) (p q_H1 q_x)) := congrArg (fun q => p (p q_H1 q_x) q) (pst5); let pst7 : (p v0 v0) = (p (p q_H1 q_x) (p q_H1 q_x)) := Eq.trans (pst4) (pst6); let pst8 : q_H0 = (p (p q_H1 q_x) (p q_H1 q_x)) := Eq.trans (pst0) (pst7); let pst9 : (p q_v0 q_v0) = (p (p q_H1 q_x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst10 : (p (p q_H1 q_x) q_v0) = (p (p q_H1 q_x) (p q_H1 q_x)) := congrArg (fun q => p (p q_H1 q_x) q) (pst2); let pst11 : (p q_v0 q_v0) = (p (p q_H1 q_x) (p q_H1 q_x)) := Eq.trans (pst9) (pst10); let pst12 : (p (p q_H1 q_x) (p q_H1 q_x)) = (p q_v0 q_v0) := Eq.symm (pst11); let pst13 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst8) (pst12); pst13)
      exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have s1B := step_bound s1
    have s1N := step_no_first s1
    cases s1 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change H0 = (p (p (p q_v0 q_v0) q_v1) q_v0) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change v0 = (p (p q_x q_v0) q_x) at e2
          have e3 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e3
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change H0 = (p (p (p q_v0 q_v0) q_v1) q_v0) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change v0 = (p q_H1 q_x) at e2
          have e3 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e3
          have cyc : q_H1 = (p x (p q_H1 q_x)) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_H1 q_x) := e2; let peq3 : (p (p x v0) x) = q_v0 := e3; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_H1 q_x) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_H1 q_x) := Eq.trans (peq1) (pst1); let pst3 : (p x v0) = (p x (p q_H1 q_x)) := congrArg (fun q => p x q) (pst2); let pst4 : (p (p x v0) x) = (p (p x (p q_H1 q_x)) x) := congrArg (fun q => p q x) (pst3); let pst5 : (p (p x (p q_H1 q_x)) x) = (p (p x v0) x) := Eq.symm (pst4); let pst6 : (p (p x (p q_H1 q_x)) x) = q_v0 := Eq.trans (pst5) (peq3); let pst7 : (p (p x (p q_H1 q_x)) x) = (p q_H1 q_x) := Eq.trans (pst6) (pst1); let pst8 : (p x (p q_H1 q_x)) = q_H1 := congrArg (fun q => L q) (pst7); let pst9 : q_H1 = (p x (p q_H1 q_x)) := Eq.symm (pst8); pst9)
          have hlt : sz q_H1 < sz (p x (p q_H1 q_x)) := Nat.lt_trans (sz_lt_p_left q_H1 q_x) (sz_lt_p_right x (p q_H1 q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change H0 = (p q_H0 q_v0) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change v0 = (p (p q_x q_v0) q_x) at e2
          have e3 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e3
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change H0 = (p q_H0 q_v0) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change v0 = (p q_H1 q_x) at e2
          have e3 := congrArg (fun q => q) hb
          change (p (p x v0) x) = q_v0 at e3
          have cyc : q_H1 = (p x (p q_H1 q_x)) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_H1 q_x) := e2; let peq3 : (p (p x v0) x) = q_v0 := e3; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_H1 q_x) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_H1 q_x) := Eq.trans (peq1) (pst1); let pst3 : (p x v0) = (p x (p q_H1 q_x)) := congrArg (fun q => p x q) (pst2); let pst4 : (p (p x v0) x) = (p (p x (p q_H1 q_x)) x) := congrArg (fun q => p q x) (pst3); let pst5 : (p (p x (p q_H1 q_x)) x) = (p (p x v0) x) := Eq.symm (pst4); let pst6 : (p (p x (p q_H1 q_x)) x) = q_v0 := Eq.trans (pst5) (peq3); let pst7 : (p (p x (p q_H1 q_x)) x) = (p q_H1 q_x) := Eq.trans (pst6) (pst1); let pst8 : (p x (p q_H1 q_x)) = q_H1 := congrArg (fun q => L q) (pst7); let pst9 : q_H1 = (p x (p q_H1 q_x)) := Eq.symm (pst8); pst9)
          have hlt : sz q_H1 < sz (p x (p q_H1 q_x)) := Nat.lt_trans (sz_lt_p_left q_H1 q_x) (sz_lt_p_right x (p q_H1 q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change H0 = (p (p (p q_v0 q_v0) q_v1) q_v0) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change v0 = (p (p q_x q_v0) q_x) at e2
          have e3 := congrArg (fun q => q) hb
          change (p H1 x) = q_v0 at e3
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L q))) (ha)
          change H0 = (p (p (p q_v0 q_v0) q_v1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L q))) (ha)
          change v0 = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (ha)
          change v0 = (p q_H1 q_x) at p2
          have z2 := congrArg sz p2
          have p3 := hb
          change (p H1 x) = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have badlt : sz (p v0 v0) < sz H0 := by
            have structural : sz (p (p H1 x) (p H1 x)) < sz (p (p (p (p H1 x) (p H1 x)) q_v1) (p H1 x)) := Nat.lt_trans (sz_lt_p_left (p (p H1 x) (p H1 x)) q_v1) (sz_lt_p_left (p (p (p H1 x) (p H1 x)) q_v1) (p H1 x))
            have large_eq : sz (p v0 v0) = sz (p (p H1 x) (p H1 x)) := congrArg sz (Eq.trans (congrArg (fun q => p q v0) (Eq.trans (p1) (p3.symm))) (congrArg (fun q => p (p H1 x) q) (Eq.trans (p1) (p3.symm))))
            have small_eq : sz H0 = sz (p (p (p (p H1 x) (p H1 x)) q_v1) (p H1 x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_v1) (Eq.trans (congrArg (fun q => p q q_v0) (p3.symm)) (congrArg (fun q => p (p H1 x) q) (p3.symm))))) (congrArg (fun q => p (p (p (p H1 x) (p H1 x)) q_v1) q) (p3.symm))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change H0 = (p q_H0 q_v0) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change v0 = (p (p q_x q_v0) q_x) at e2
          have e3 := congrArg (fun q => q) hb
          change (p H1 x) = q_v0 at e3
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L q))) (ha)
          change H0 = (p q_H0 q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L q))) (ha)
          change v0 = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (ha)
          change v0 = (p q_H1 q_x) at p2
          have z2 := congrArg sz p2
          have p3 := hb
          change (p H1 x) = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have badlt : sz x < sz v0 := by
            have structural : sz x < sz (p H1 x) := sz_lt_p_right H1 x
            have large_eq : sz x = sz x := congrArg sz (rfl)
            have small_eq : sz v0 = sz (p H1 x) := congrArg sz (Eq.trans (p1) (p3.symm))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.1).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval (eval v0 v0) v1) v0) v0) (eval (eval x v0) x)) v0) := by
  let H0 := eval (eval v0 v0) v1
  have e0a : (eval v0 v0) = (p v0 v0) := by
    change (eval v0 v0) = (p v0 v0)
    exact (eval_raw (nr0 x v0 v1))
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step (p v0 v0) v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step (eval v0 v0) v1
  let H1 := eval x v0
  have e1a : x = x := by
    change x = x
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step x v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step x v0
  change x = (eval (eval (eval (eval H0 v0) v0) (eval H1 x)) v0)
  have rawEq : (eval (eval (eval (eval H0 v0) v0) (eval H1 x)) v0) = (eval (p (p (p H0 v0) v0) (p H1 x)) v0) := by
    calc
      (eval (eval (eval (eval H0 v0) v0) (eval H1 x)) v0) = (eval (eval (eval (p H0 v0) v0) (eval H1 x)) v0) := congrArg (fun q => (eval (eval (eval q v0) (eval H1 x)) v0)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval (p (p H0 v0) v0) (eval H1 x)) v0) := congrArg (fun q => (eval (eval q (eval H1 x)) v0)) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval (eval (p (p H0 v0) v0) (p H1 x)) v0) := congrArg (fun q => (eval (eval (p (p H0 v0) v0) q) v0)) (eval_raw (nr3 x v0 v1 H1 s1))
      _ = (eval (p (p (p H0 v0) v0) (p H1 x)) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr4 x v0 v1 H0 H1 s0 s1))
  exact (eval_hit (Code.law x v0 v1 H0 H1 s0 s1)).symm.trans rawEq.symm
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
