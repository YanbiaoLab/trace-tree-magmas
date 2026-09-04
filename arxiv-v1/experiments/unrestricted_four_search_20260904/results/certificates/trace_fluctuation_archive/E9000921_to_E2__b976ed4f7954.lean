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
      (s0 : Step x v1 H0)
      (s1 : Step v0 H0 H1) :
      Code (p (p H1 (p (p x x) v0)) x) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v1 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ a = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R (L a))))
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
      change v = (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_x q_v1)) (sz_lt_p_left (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p q_H1 (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p q_H1 (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H1 (p (p q_x q_x) q_v0)) := Nat.lt_trans (sz_lt_p_right (p q_x q_x) q_v0) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p q_H1 (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p q_H1 (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H1 (p (p q_x q_x) q_v0)) := Nat.lt_trans (sz_lt_p_right (p q_x q_x) q_v0) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))
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
    ¬ ∃ o, Code x x o := by
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
      change x = (p (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) q_x) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_x q_v1)) (sz_lt_p_left (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0))) (sz_lt_p_left (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p q_x q_x) q_v0) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))) (sz_lt_p_left (p q_H1 (p (p q_x q_x) q_v0)) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) q_x) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p (p q_x q_x) q_v0))) (sz_lt_p_left (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p q_x q_x) q_v0) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))) (sz_lt_p_left (p q_H1 (p (p q_x q_x) q_v0)) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p x x) v0 o := by
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
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_x = (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_x < sz (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_v1) (sz_lt_p_right q_v0 (p q_x q_v1))) (sz_lt_p_left (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p q_H1 (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_x = (p q_H1 (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_x < sz (p q_H1 (p (p q_x q_x) q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v0)) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_x = (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_x < sz (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v0)) (sz_lt_p_right (p q_v0 q_H0) (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p q_H1 (p (p q_x q_x) q_v0)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_x = (p q_H1 (p (p q_x q_x) q_v0)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_x < sz (p q_H1 (p (p q_x q_x) q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v0)) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code H1 (p (p x x) v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
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
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H0 = q_x at e1
        have e2 := congrArg (fun q => q) hb
        change (p (p x x) v0) = q_v0 at e2
        have cyc : q_v0 = (p (p x x) (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p (p x x) (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_x q_v1)) (sz_lt_p_left (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0))) (sz_lt_p_right (p x x) (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p q_H1 (p (p q_x q_x) q_v0)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H0 = q_x at e1
        have e2 := congrArg (fun q => q) hb
        change (p (p x x) v0) = q_v0 at e2
        have cyc : q_v0 = (p (p x x) (p q_H1 (p (p q_x q_x) q_v0))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p (p x x) (p q_H1 (p (p q_x q_x) q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p q_x q_x) q_v0) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))) (sz_lt_p_right (p x x) (p q_H1 (p (p q_x q_x) q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H0 = q_x at e1
        have e2 := congrArg (fun q => q) hb
        change (p (p x x) v0) = q_v0 at e2
        have cyc : q_v0 = (p (p x x) (p (p q_v0 q_H0) (p (p q_x q_x) q_v0))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p (p x x) (p (p q_v0 q_H0) (p (p q_x q_x) q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p (p q_x q_x) q_v0))) (sz_lt_p_right (p x x) (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p q_H1 (p (p q_x q_x) q_v0)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H0 = q_x at e1
        have e2 := congrArg (fun q => q) hb
        change (p (p x x) v0) = q_v0 at e2
        have cyc : q_v0 = (p (p x x) (p q_H1 (p (p q_x q_x) q_v0))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p (p x x) (p q_H1 (p (p q_x q_x) q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p q_x q_x) q_v0) (sz_lt_p_right q_H1 (p (p q_x q_x) q_v0))) (sz_lt_p_right (p x x) (p q_H1 (p (p q_x q_x) q_v0)))
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
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) q_x) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p x x) v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB s1B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p x x) v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) q_x) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p x x) v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB s1B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p (p q_H1 (p (p q_x q_x) q_v0)) q_x) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p x x) v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p H1 (p (p x x) v0)) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
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
        change v0 = (p q_v0 (p q_x q_v1)) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = (p (p q_x q_x) q_v0) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change (p (p x x) v0) = q_x at e2
        have e3 := congrArg (fun q => q) hb
        change x = q_v0 at e3
        have cyc : q_x = (p (p x x) (p q_v0 (p q_x q_v1))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
        have hlt : sz q_x < sz (p (p x x) (p q_v0 (p q_x q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_v1) (sz_lt_p_right q_v0 (p q_x q_v1))) (sz_lt_p_right (p x x) (p q_v0 (p q_x q_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change v0 = q_H1 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change H0 = (p (p q_x q_x) q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v0) = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change x = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs1hB s1B qs0B qs1B z0 z1 z2 z3 z4
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0B := step_bound u0s0
        have u0s0N := step_no_first u0s0
        cases u0s0 with
        | raw =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_H0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q (p q_v0 q_H0)) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q (p u0_x u0_v1)) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => R q) (pst19); let pst21 := congrArg (fun q => p u0_x q) (pst20); let pst22 := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 := Eq.trans (pst17) (pst22); let pst24 := Eq.trans (pst12) (pst23); let pst25 := congrArg (fun q => p q q_H0) (pst24); let pst26 := Eq.symm (pst25); let pst27 := congrArg (fun q => R q) (pst10); let pst28 := Eq.trans (pst26) (pst27); let pst29 := Eq.symm (pst28); pst29)
            have hlt : sz u0_x < sz (p (p (p u0_x u0_x) (p u0_x u0_x)) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p u0_x u0_x) u0_v0) q_H0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q (p q_v0 q_H0)) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := congrArg (fun q => p q q_H0) (pst16); let pst18 := Eq.symm (pst17); let pst19 := congrArg (fun q => R q) (pst10); let pst20 := Eq.trans (pst18) (pst19); let pst21 := Eq.symm (pst20); pst21)
            have hlt : sz u0_x < sz (p (p (p u0_x u0_x) u0_v0) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) u0_v0)) (sz_lt_p_left (p (p u0_x u0_x) u0_v0) q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_H0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q (p q_v0 q_H0)) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_H0) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => p (p u0_x u0_x) q) (pst19); let pst21 := Eq.trans (pst17) (pst20); let pst22 := Eq.trans (pst12) (pst21); let pst23 := congrArg (fun q => p q q_H0) (pst22); let pst24 := Eq.symm (pst23); let pst25 := congrArg (fun q => R q) (pst10); let pst26 := Eq.trans (pst24) (pst25); let pst27 := Eq.symm (pst26); pst27)
            have hlt : sz u0_x < sz (p (p (p u0_x u0_x) (p u0_x u0_x)) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p u0_x u0_x) u0_v0) q_H0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q (p q_v0 q_H0)) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := congrArg (fun q => p q q_H0) (pst16); let pst18 := Eq.symm (pst17); let pst19 := congrArg (fun q => R q) (pst10); let pst20 := Eq.trans (pst18) (pst19); let pst21 := Eq.symm (pst20); pst21)
            have hlt : sz u0_x < sz (p (p (p u0_x u0_x) u0_v0) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) u0_v0)) (sz_lt_p_left (p (p u0_x u0_x) u0_v0) q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0B := step_bound u0s0
        have u0s0N := step_no_first u0s0
        cases u0s0 with
        | raw =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          cases u0s1 with
          | raw =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0B := step_bound u1s0
            have u1s0N := step_no_first u1s0
            cases u1s0 with
            | raw =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q (p u0_x u0_v1)) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => R q) (pst19); let pst21 := congrArg (fun q => p u0_x q) (pst20); let pst22 := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 := Eq.trans (pst17) (pst22); let pst24 := Eq.trans (pst12) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq8); let pst27 := congrArg (fun q => L q) (pst26); let pst28 := congrArg (fun q => L q) (pst27); let pst29 := Eq.symm (pst28); let pst30 := congrArg (fun q => R q) (pst27); let pst31 := Eq.trans (pst29) (pst30); let pst32 := congrArg (fun q => L q) (pst31); let pst33 := congrArg (fun q => p q (p u1_x u1_v1)) (pst32); let pst34 := congrArg (fun q => R q) (pst31); let pst35 := Eq.trans (pst34) (pst32); let pst36 := congrArg (fun q => R q) (pst35); let pst37 := congrArg (fun q => p u1_x q) (pst36); let pst38 := congrArg (fun q => p (p u1_x u1_x) q) (pst37); let pst39 := Eq.trans (pst33) (pst38); let pst40 := Eq.trans (pst28) (pst39); let pst41 := congrArg (fun q => p q u0_x) (pst40); let pst42 := congrArg (fun q => p q (p u1_x u1_v1)) (pst32); let pst43 := congrArg (fun q => p u1_x q) (pst36); let pst44 := congrArg (fun q => p (p u1_x u1_x) q) (pst43); let pst45 := Eq.trans (pst42) (pst44); let pst46 := Eq.trans (pst28) (pst45); let pst47 := congrArg (fun q => p (p (p u1_x u1_x) (p u1_x u1_x)) q) (pst46); let pst48 := Eq.trans (pst41) (pst47); let pst49 := Eq.symm (pst48); let pst50 := congrArg (fun q => R q) (pst26); let pst51 := Eq.trans (pst49) (pst50); let pst52 := Eq.symm (pst51); pst52)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) (p u1_x u1_x))) (sz_lt_p_left (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q (p u0_x u0_v1)) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => R q) (pst19); let pst21 := congrArg (fun q => p u0_x q) (pst20); let pst22 := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 := Eq.trans (pst17) (pst22); let pst24 := Eq.trans (pst12) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq8); let pst27 := congrArg (fun q => L q) (pst26); let pst28 := congrArg (fun q => L q) (pst27); let pst29 := Eq.symm (pst28); let pst30 := congrArg (fun q => R q) (pst27); let pst31 := Eq.trans (pst29) (pst30); let pst32 := Eq.trans (pst28) (pst31); let pst33 := congrArg (fun q => p q u0_x) (pst32); let pst34 := Eq.trans (pst28) (pst31); let pst35 := congrArg (fun q => p (p (p u1_x u1_x) u1_v0) q) (pst34); let pst36 := Eq.trans (pst33) (pst35); let pst37 := Eq.symm (pst36); let pst38 := congrArg (fun q => R q) (pst26); let pst39 := Eq.trans (pst37) (pst38); let pst40 := Eq.symm (pst39); pst40)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) u1_v0)) (sz_lt_p_left (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q (p u0_x u0_v1)) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => R q) (pst19); let pst21 := congrArg (fun q => p u0_x q) (pst20); let pst22 := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 := Eq.trans (pst17) (pst22); let pst24 := Eq.trans (pst12) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq8); let pst27 := congrArg (fun q => L q) (pst26); let pst28 := congrArg (fun q => L q) (pst27); let pst29 := Eq.symm (pst28); let pst30 := congrArg (fun q => R q) (pst27); let pst31 := Eq.trans (pst29) (pst30); let pst32 := congrArg (fun q => L q) (pst31); let pst33 := congrArg (fun q => p q u1_H0) (pst32); let pst34 := congrArg (fun q => R q) (pst31); let pst35 := Eq.trans (pst34) (pst32); let pst36 := congrArg (fun q => p (p u1_x u1_x) q) (pst35); let pst37 := Eq.trans (pst33) (pst36); let pst38 := Eq.trans (pst28) (pst37); let pst39 := congrArg (fun q => p q u0_x) (pst38); let pst40 := congrArg (fun q => p q u1_H0) (pst32); let pst41 := congrArg (fun q => p (p u1_x u1_x) q) (pst35); let pst42 := Eq.trans (pst40) (pst41); let pst43 := Eq.trans (pst28) (pst42); let pst44 := congrArg (fun q => p (p (p u1_x u1_x) (p u1_x u1_x)) q) (pst43); let pst45 := Eq.trans (pst39) (pst44); let pst46 := Eq.symm (pst45); let pst47 := congrArg (fun q => R q) (pst26); let pst48 := Eq.trans (pst46) (pst47); let pst49 := Eq.symm (pst48); pst49)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) (p u1_x u1_x))) (sz_lt_p_left (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q (p u0_x u0_v1)) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => R q) (pst19); let pst21 := congrArg (fun q => p u0_x q) (pst20); let pst22 := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 := Eq.trans (pst17) (pst22); let pst24 := Eq.trans (pst12) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq8); let pst27 := congrArg (fun q => L q) (pst26); let pst28 := congrArg (fun q => L q) (pst27); let pst29 := Eq.symm (pst28); let pst30 := congrArg (fun q => R q) (pst27); let pst31 := Eq.trans (pst29) (pst30); let pst32 := Eq.trans (pst28) (pst31); let pst33 := congrArg (fun q => p q u0_x) (pst32); let pst34 := Eq.trans (pst28) (pst31); let pst35 := congrArg (fun q => p (p (p u1_x u1_x) u1_v0) q) (pst34); let pst36 := Eq.trans (pst33) (pst35); let pst37 := Eq.symm (pst36); let pst38 := congrArg (fun q => R q) (pst26); let pst39 := Eq.trans (pst37) (pst38); let pst40 := Eq.symm (pst39); pst40)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) u1_v0)) (sz_lt_p_left (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0B := step_bound u1s0
            have u1s0N := step_no_first u1s0
            cases u1s0 with
            | raw =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u1_x u1_x) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => p q (p u1_x u1_v1)) (pst24); let pst26 := congrArg (fun q => R q) (pst23); let pst27 := Eq.trans (pst26) (pst24); let pst28 := congrArg (fun q => R q) (pst27); let pst29 := congrArg (fun q => p u1_x q) (pst28); let pst30 := congrArg (fun q => p (p u1_x u1_x) q) (pst29); let pst31 := Eq.trans (pst25) (pst30); let pst32 := Eq.trans (pst20) (pst31); let pst33 := Eq.trans (peq7) (pst32); let pst34 := Eq.symm (pst33); let pst35 := Eq.trans (pst34) (peq9); let pst36 := Eq.trans (pst35) (pst24); let pst37 := congrArg (fun q => L q) (pst36); let pst38 := Eq.symm (pst37); pst38)
                have hlt : sz u1_x < sz (p u1_x u1_x) := sz_lt_p_left u1_x u1_x
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p (p u1_x u1_x) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst20) (pst23); let pst25 := Eq.trans (peq7) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (pst26) (peq9); let pst28 := Eq.symm (pst27); pst28)
                have hlt : sz u1_v0 < sz (p (p u1_x u1_x) u1_v0) := sz_lt_p_right (p u1_x u1_x) u1_v0
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u1_x u1_x) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => p q u1_H0) (pst24); let pst26 := congrArg (fun q => R q) (pst23); let pst27 := Eq.trans (pst26) (pst24); let pst28 := congrArg (fun q => p (p u1_x u1_x) q) (pst27); let pst29 := Eq.trans (pst25) (pst28); let pst30 := Eq.trans (pst20) (pst29); let pst31 := Eq.trans (peq7) (pst30); let pst32 := Eq.symm (pst31); let pst33 := Eq.trans (pst32) (peq9); let pst34 := Eq.trans (pst33) (pst24); let pst35 := congrArg (fun q => L q) (pst34); let pst36 := Eq.symm (pst35); pst36)
                have hlt : sz u1_x < sz (p u1_x u1_x) := sz_lt_p_left u1_x u1_x
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p (p u1_x u1_x) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst20) (pst23); let pst25 := Eq.trans (peq7) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (pst26) (peq9); let pst28 := Eq.symm (pst27); pst28)
                have hlt : sz u1_v0 < sz (p (p u1_x u1_x) u1_v0) := sz_lt_p_right (p u1_x u1_x) u1_v0
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          cases u0s1 with
          | raw =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0B := step_bound u1s0
            have u1s0N := step_no_first u1s0
            cases u1s0 with
            | raw =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_H0) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => p (p u0_x u0_x) q) (pst19); let pst21 := Eq.trans (pst17) (pst20); let pst22 := Eq.trans (pst12) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq8); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := congrArg (fun q => L q) (pst25); let pst27 := Eq.symm (pst26); let pst28 := congrArg (fun q => R q) (pst25); let pst29 := Eq.trans (pst27) (pst28); let pst30 := congrArg (fun q => L q) (pst29); let pst31 := congrArg (fun q => p q (p u1_x u1_v1)) (pst30); let pst32 := congrArg (fun q => R q) (pst29); let pst33 := Eq.trans (pst32) (pst30); let pst34 := congrArg (fun q => R q) (pst33); let pst35 := congrArg (fun q => p u1_x q) (pst34); let pst36 := congrArg (fun q => p (p u1_x u1_x) q) (pst35); let pst37 := Eq.trans (pst31) (pst36); let pst38 := Eq.trans (pst26) (pst37); let pst39 := congrArg (fun q => p q u0_x) (pst38); let pst40 := congrArg (fun q => p q (p u1_x u1_v1)) (pst30); let pst41 := congrArg (fun q => p u1_x q) (pst34); let pst42 := congrArg (fun q => p (p u1_x u1_x) q) (pst41); let pst43 := Eq.trans (pst40) (pst42); let pst44 := Eq.trans (pst26) (pst43); let pst45 := congrArg (fun q => p (p (p u1_x u1_x) (p u1_x u1_x)) q) (pst44); let pst46 := Eq.trans (pst39) (pst45); let pst47 := Eq.symm (pst46); let pst48 := congrArg (fun q => R q) (pst24); let pst49 := Eq.trans (pst47) (pst48); let pst50 := Eq.symm (pst49); pst50)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) (p u1_x u1_x))) (sz_lt_p_left (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_H0) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => p (p u0_x u0_x) q) (pst19); let pst21 := Eq.trans (pst17) (pst20); let pst22 := Eq.trans (pst12) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq8); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := congrArg (fun q => L q) (pst25); let pst27 := Eq.symm (pst26); let pst28 := congrArg (fun q => R q) (pst25); let pst29 := Eq.trans (pst27) (pst28); let pst30 := Eq.trans (pst26) (pst29); let pst31 := congrArg (fun q => p q u0_x) (pst30); let pst32 := Eq.trans (pst26) (pst29); let pst33 := congrArg (fun q => p (p (p u1_x u1_x) u1_v0) q) (pst32); let pst34 := Eq.trans (pst31) (pst33); let pst35 := Eq.symm (pst34); let pst36 := congrArg (fun q => R q) (pst24); let pst37 := Eq.trans (pst35) (pst36); let pst38 := Eq.symm (pst37); pst38)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) u1_v0)) (sz_lt_p_left (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_H0) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => p (p u0_x u0_x) q) (pst19); let pst21 := Eq.trans (pst17) (pst20); let pst22 := Eq.trans (pst12) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq8); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := congrArg (fun q => L q) (pst25); let pst27 := Eq.symm (pst26); let pst28 := congrArg (fun q => R q) (pst25); let pst29 := Eq.trans (pst27) (pst28); let pst30 := congrArg (fun q => L q) (pst29); let pst31 := congrArg (fun q => p q u1_H0) (pst30); let pst32 := congrArg (fun q => R q) (pst29); let pst33 := Eq.trans (pst32) (pst30); let pst34 := congrArg (fun q => p (p u1_x u1_x) q) (pst33); let pst35 := Eq.trans (pst31) (pst34); let pst36 := Eq.trans (pst26) (pst35); let pst37 := congrArg (fun q => p q u0_x) (pst36); let pst38 := congrArg (fun q => p q u1_H0) (pst30); let pst39 := congrArg (fun q => p (p u1_x u1_x) q) (pst33); let pst40 := Eq.trans (pst38) (pst39); let pst41 := Eq.trans (pst26) (pst40); let pst42 := congrArg (fun q => p (p (p u1_x u1_x) (p u1_x u1_x)) q) (pst41); let pst43 := Eq.trans (pst37) (pst42); let pst44 := Eq.symm (pst43); let pst45 := congrArg (fun q => R q) (pst24); let pst46 := Eq.trans (pst44) (pst45); let pst47 := Eq.symm (pst46); pst47)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) (p u1_x u1_x))) (sz_lt_p_left (p (p u1_x u1_x) (p u1_x u1_x)) (p (p u1_x u1_x) (p u1_x u1_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_H0) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst18) (pst16); let pst20 := congrArg (fun q => p (p u0_x u0_x) q) (pst19); let pst21 := Eq.trans (pst17) (pst20); let pst22 := Eq.trans (pst12) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq8); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := congrArg (fun q => L q) (pst25); let pst27 := Eq.symm (pst26); let pst28 := congrArg (fun q => R q) (pst25); let pst29 := Eq.trans (pst27) (pst28); let pst30 := Eq.trans (pst26) (pst29); let pst31 := congrArg (fun q => p q u0_x) (pst30); let pst32 := Eq.trans (pst26) (pst29); let pst33 := congrArg (fun q => p (p (p u1_x u1_x) u1_v0) q) (pst32); let pst34 := Eq.trans (pst31) (pst33); let pst35 := Eq.symm (pst34); let pst36 := congrArg (fun q => R q) (pst24); let pst37 := Eq.trans (pst35) (pst36); let pst38 := Eq.symm (pst37); pst38)
                have hlt : sz u1_x < sz (p (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) u1_v0)) (sz_lt_p_left (p (p u1_x u1_x) u1_v0) (p (p u1_x u1_x) u1_v0))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0B := step_bound u1s0
            have u1s0N := step_no_first u1s0
            cases u1s0 with
            | raw =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u1_x u1_x) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => p q (p u1_x u1_v1)) (pst24); let pst26 := congrArg (fun q => R q) (pst23); let pst27 := Eq.trans (pst26) (pst24); let pst28 := congrArg (fun q => R q) (pst27); let pst29 := congrArg (fun q => p u1_x q) (pst28); let pst30 := congrArg (fun q => p (p u1_x u1_x) q) (pst29); let pst31 := Eq.trans (pst25) (pst30); let pst32 := Eq.trans (pst20) (pst31); let pst33 := Eq.trans (peq7) (pst32); let pst34 := Eq.symm (pst33); let pst35 := Eq.trans (pst34) (peq9); let pst36 := Eq.trans (pst35) (pst24); let pst37 := congrArg (fun q => L q) (pst36); let pst38 := Eq.symm (pst37); pst38)
                have hlt : sz u1_x < sz (p u1_x u1_x) := sz_lt_p_left u1_x u1_x
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p (p u1_x u1_x) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst20) (pst23); let pst25 := Eq.trans (peq7) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (pst26) (peq9); let pst28 := Eq.symm (pst27); pst28)
                have hlt : sz u1_v0 < sz (p (p u1_x u1_x) u1_v0) := sz_lt_p_right (p u1_x u1_x) u1_v0
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u1_x u1_x) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => p q u1_H0) (pst24); let pst26 := congrArg (fun q => R q) (pst23); let pst27 := Eq.trans (pst26) (pst24); let pst28 := congrArg (fun q => p (p u1_x u1_x) q) (pst27); let pst29 := Eq.trans (pst25) (pst28); let pst30 := Eq.trans (pst20) (pst29); let pst31 := Eq.trans (peq7) (pst30); let pst32 := Eq.symm (pst31); let pst33 := Eq.trans (pst32) (peq9); let pst34 := Eq.trans (pst33) (pst24); let pst35 := congrArg (fun q => L q) (pst34); let pst36 := Eq.symm (pst35); pst36)
                have hlt : sz u1_x < sz (p u1_x u1_x) := sz_lt_p_left u1_x u1_x
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p (p u1_x u1_x) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := congrArg (fun q => p (p x x) q) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := congrArg (fun q => p q x) (peq3); let pst5 := congrArg (fun q => p q_v0 q) (peq3); let pst6 := Eq.trans (pst4) (pst5); let pst7 := congrArg (fun q => p q q_H1) (pst6); let pst8 := Eq.trans (pst3) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst9) (peq5); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); let pst14 := congrArg (fun q => R q) (pst11); let pst15 := Eq.trans (pst13) (pst14); let pst16 := Eq.trans (pst12) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq8); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst20) (pst23); let pst25 := Eq.trans (peq7) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (pst26) (peq9); let pst28 := Eq.symm (pst27); pst28)
                have hlt : sz u1_v0 < sz (p (p u1_x u1_x) u1_v0) := sz_lt_p_right (p u1_x u1_x) u1_v0
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
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p q_v0 (p q_x q_v1)) (p (p q_x q_x) q_v0)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v0) = q_x at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p q_H1 (p (p q_x q_x) q_v0)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v0) = q_x at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p q_v0 q_H0) (p (p q_x q_x) q_v0)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v0) = q_x at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB s1B qs0B qs1B z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p q_H1 (p (p q_x q_x) q_v0)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v0) = q_x at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 (eval x v1)) (eval (eval x x) v0)) x) v0) := by
  let H0 := eval x v1
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step x v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v1
  let H1 := eval v0 (eval x v1)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval x v1) = H0 := by
    change H0 = H0
    rfl
  have s1 : Step v0 H0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval x v1)
  change x = (eval (eval (eval H1 (eval (eval x x) v0)) x) v0)
  have rawEq : (eval (eval (eval H1 (eval (eval x x) v0)) x) v0) = (eval (p (p H1 (p (p x x) v0)) x) v0) := by
    calc
      (eval (eval (eval H1 (eval (eval x x) v0)) x) v0) = (eval (eval (eval H1 (eval (p x x) v0)) x) v0) := congrArg (fun q => (eval (eval (eval H1 (eval q v0)) x) v0)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval (eval H1 (p (p x x) v0)) x) v0) := congrArg (fun q => (eval (eval (eval H1 q) x) v0)) (eval_raw (nr1 x v0 v1))
      _ = (eval (eval (p H1 (p (p x x) v0)) x) v0) := congrArg (fun q => (eval (eval q x) v0)) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval (p (p H1 (p (p x x) v0)) x) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr3 x v0 v1 H1 s1))
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
