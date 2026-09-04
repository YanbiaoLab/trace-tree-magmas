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
  | law (x v0 v1 H0 H1 H2 : CM)
      (s0 : Step v0 v1 H0)
      (s1 : Step v0 H0 H1)
      (s2 : Step v0 x H2) :
      Code (p (p H1 v0) (p x (p H2 v0))) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 q_H2 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ Step q_v0 q_x q_H2 ∧ a = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 H2 s0 s1 s2 => ⟨x, v0, v1, H0, H1, H2, s0, s1, s2, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, s0, s1, s2, ha, hb, ho⟩
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 (p q_v0 q_v1)) q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p (p q_v0 q_x) q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 (p q_v0 q_v1)) q_v0) := (let peq0 : v = (p (p q_v0 (p q_v0 q_v1)) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 (p q_v0 q_v1)) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v0 q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p q_v0 q_v1)) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_v0 q_v1)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 q_v1)) (sz_lt_p_left (p q_v0 (p q_v0 q_v1)) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 (p q_v0 q_v1)) q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p q_H2 q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 (p q_v0 q_v1)) q_v0) := (let peq0 : v = (p (p q_v0 (p q_v0 q_v1)) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 (p q_v0 q_v1)) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v0 q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p q_v0 q_v1)) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_v0 q_v1)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 q_v1)) (sz_lt_p_left (p q_v0 (p q_v0 q_v1)) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p (p q_v0 q_x) q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v = (p q_H1 q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p q_H1 q_v0) = v := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p q_H2 q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v = (p q_H1 q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p q_H1 q_v0) = v := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 q_H0) q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p (p q_v0 q_x) q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_H0) q_v0) := (let peq0 : v = (p (p q_v0 q_H0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_H0) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 q_H0) q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p q_H2 q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_H0) q_v0) := (let peq0 : v = (p (p q_v0 q_H0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_H0) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p (p q_v0 q_x) q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v = (p q_H1 q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p q_H1 q_v0) = v := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_x (p q_H2 q_v0)) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v = (p q_H1 q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p q_H1 q_v0) = v := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
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
theorem nr0 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code H1 v0 o := by
  exact step_no_first s1

theorem nr1 (x v0 v1 H2 : CM)
    (s2 : Step v0 x H2) :
    ¬ ∃ o, Code H2 v0 o := by
  exact step_no_first s2

theorem nr2 (x v0 v1 H2 : CM)
    (s2 : Step v0 x H2) :
    ¬ ∃ o, Code x (p H2 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s2B := step_bound s2
  have s2N := step_no_first s2
  cases s2 with
  | raw =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := (let peq0 : x = (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 q_v1)) (sz_lt_p_left (p q_v0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0))))) (sz_lt_p_left (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0) := (let peq0 : x = (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 q_v1)) (sz_lt_p_left (p q_v0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0))))) (sz_lt_p_left (p v0 (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := (let peq0 : x = (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))))) (sz_lt_p_left (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := (let peq0 : x = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))))) (sz_lt_p_left (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := (let peq0 : x = (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0))))) (sz_lt_p_left (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0) := (let peq0 : x = (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0))))) (sz_lt_p_left (p v0 (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := (let peq0 : x = (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))))) (sz_lt_p_left (p v0 (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) at e0
          have e1 := congrArg (fun q => q) hb
          change (p (p v0 x) v0) = q_v0 at e1
          have cyc : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := (let peq0 : x = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) := e0; let peq1 : (p (p v0 x) v0) = q_v0 := e1; let pst0 : (p v0 x) = (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p v0 q) (peq0); let pst1 : (p (p v0 x) v0) = (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) = (p (p v0 x) v0) := Eq.symm (pst1); let pst3 : (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := Eq.symm (pst3); pst4)
          have hlt : sz q_v0 < sz (p (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))))) (sz_lt_p_left (p v0 (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0)))) v0)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s2h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_left (p H2 v0) (p (p H2 v0) q_v1))) (sz_lt_p_left (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0))) (sz_lt_p_left (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p (p q_v0 q_x) q_v0))) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (congrArg (fun q => p q (p q_v0 q_v1)) (p1.symm)) (congrArg (fun q => p (p H2 v0) q) (congrArg (fun q => p q q_v1) (p1.symm))))) (congrArg (fun q => p (p (p H2 v0) (p (p H2 v0) q_v1)) q) (p1.symm)))) (congrArg (fun q => p (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) q) (congrArg (fun q => p q_x q) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_x) (p1.symm))) (congrArg (fun q => p (p (p H2 v0) q_x) q) (p1.symm)))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p (p q_v0 (p q_v0 q_v1)) q_v0) (p q_x (p q_H2 q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_left (p H2 v0) (p (p H2 v0) q_v1))) (sz_lt_p_left (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0))) (sz_lt_p_left (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) (p q_x (p q_H2 (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p q_H2 q_v0))) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (congrArg (fun q => p q (p q_v0 q_v1)) (p1.symm)) (congrArg (fun q => p (p H2 v0) q) (congrArg (fun q => p q q_v1) (p1.symm))))) (congrArg (fun q => p (p (p H2 v0) (p (p H2 v0) q_v1)) q) (p1.symm)))) (congrArg (fun q => p (p (p (p H2 v0) (p (p H2 v0) q_v1)) (p H2 v0)) q) (congrArg (fun q => p q_x q) (congrArg (fun q => p q_H2 q) (p1.symm))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs1hB := code_bounds qs1h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p q_H1 (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_right q_H1 (p H2 v0))) (sz_lt_p_left (p q_H1 (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p q_H1 (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p (p q_v0 q_x) q_v0))) (congrArg (fun q => p q_H1 q) (p1.symm))) (congrArg (fun q => p (p q_H1 (p H2 v0)) q) (congrArg (fun q => p q_x q) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_x) (p1.symm))) (congrArg (fun q => p (p (p H2 v0) q_x) q) (p1.symm)))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p q_H1 (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_right q_H1 (p H2 v0))) (sz_lt_p_left (p q_H1 (p H2 v0)) (p q_x (p q_H2 (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p q_H1 (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p q_H2 q_v0))) (congrArg (fun q => p q_H1 q) (p1.symm))) (congrArg (fun q => p (p q_H1 (p H2 v0)) q) (congrArg (fun q => p q_x q) (congrArg (fun q => p q_H2 q) (p1.symm))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p (p q_v0 q_H0) q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p (p (p H2 v0) q_H0) (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_left (p H2 v0) q_H0)) (sz_lt_p_left (p (p H2 v0) q_H0) (p H2 v0))) (sz_lt_p_left (p (p (p H2 v0) q_H0) (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p (p (p H2 v0) q_H0) (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p (p q_v0 q_x) q_v0))) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_H0) (p1.symm))) (congrArg (fun q => p (p (p H2 v0) q_H0) q) (p1.symm)))) (congrArg (fun q => p (p (p (p H2 v0) q_H0) (p H2 v0)) q) (congrArg (fun q => p q_x q) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_x) (p1.symm))) (congrArg (fun q => p (p (p H2 v0) q_x) q) (p1.symm)))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p (p q_v0 q_H0) q_v0) (p q_x (p q_H2 q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p (p (p H2 v0) q_H0) (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_left (p H2 v0) q_H0)) (sz_lt_p_left (p (p H2 v0) q_H0) (p H2 v0))) (sz_lt_p_left (p (p (p H2 v0) q_H0) (p H2 v0)) (p q_x (p q_H2 (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p (p (p H2 v0) q_H0) (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p q_H2 q_v0))) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_H0) (p1.symm))) (congrArg (fun q => p (p (p H2 v0) q_H0) q) (p1.symm)))) (congrArg (fun q => p (p (p (p H2 v0) q_H0) (p H2 v0)) q) (congrArg (fun q => p q_x q) (congrArg (fun q => p q_H2 q) (p1.symm))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p q_H1 q_v0) (p q_x (p (p q_v0 q_x) q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p q_H1 (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_right q_H1 (p H2 v0))) (sz_lt_p_left (p q_H1 (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p q_H1 (p H2 v0)) (p q_x (p (p (p H2 v0) q_x) (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p (p q_v0 q_x) q_v0))) (congrArg (fun q => p q_H1 q) (p1.symm))) (congrArg (fun q => p (p q_H1 (p H2 v0)) q) (congrArg (fun q => p q_x q) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_x) (p1.symm))) (congrArg (fun q => p (p (p H2 v0) q_x) q) (p1.symm)))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change x = (p (p q_H1 q_v0) (p q_x (p q_H2 q_v0))) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p H2 v0) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have badlt : sz v0 < sz x := by
            have structural : sz v0 < sz (p (p q_H1 (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right H2 v0) (sz_lt_p_right q_H1 (p H2 v0))) (sz_lt_p_left (p q_H1 (p H2 v0)) (p q_x (p q_H2 (p H2 v0))))
            have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
            have small_eq : sz x = sz (p (p q_H1 (p H2 v0)) (p q_x (p q_H2 (p H2 v0)))) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q (p q_x (p q_H2 q_v0))) (congrArg (fun q => p q_H1 q) (p1.symm))) (congrArg (fun q => p (p q_H1 (p H2 v0)) q) (congrArg (fun q => p q_x q) (congrArg (fun q => p q_H2 q) (p1.symm))))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
theorem nr3 (x v0 v1 H1 H2 : CM)
    (s1 : Step v0 H0 H1)
    (s2 : Step v0 x H2) :
    ¬ ∃ o, Code (p H1 v0) (p x (p H2 v0)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s1B := step_bound s1
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have s2B := step_bound s2
    have s2N := step_no_first s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 (p q_v0 q_v1)) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_x = (p q_x q_x) := (let peq0 : v0 = (p q_v0 (p q_v0 q_v1)) := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let pst0 : (p q_v0 (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v0 q_v1)) = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p q_v0 q_v1) = (p (p q_v0 q_x) q_v0) := congrArg (fun q => R q) (pst1); let pst6 : (p q_x q_v1) = (p (p q_v0 q_x) q_v0) := Eq.trans (pst4) (pst5); let pst7 : (p q_v0 q_x) = (p q_x q_x) := congrArg (fun q => p q q_x) (pst2); let pst8 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_v0) := congrArg (fun q => p q q_v0) (pst7); let pst9 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) q_x) := congrArg (fun q => p (p q_x q_x) q) (pst2); let pst10 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_x) := Eq.trans (pst8) (pst9); let pst11 : (p q_x q_v1) = (p (p q_x q_x) q_x) := Eq.trans (pst6) (pst10); let pst12 : q_x = (p q_x q_x) := congrArg (fun q => L q) (pst11); pst12)
            have hlt : sz q_x < sz (p q_x q_x) := sz_lt_p_left q_x q_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 (p q_v0 q_v1)) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_H2 = (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) := (let peq0 : v0 = (p q_v0 (p q_v0 q_v1)) := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : (p q_v0 (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v0 q_v1)) = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p q_v0 q_v1) = (p q_H2 q_v0) := congrArg (fun q => R q) (pst1); let pst6 : (p q_x q_v1) = (p q_H2 q_v0) := Eq.trans (pst4) (pst5); let pst7 : (p q_H2 q_v0) = (p q_H2 q_x) := congrArg (fun q => p q_H2 q) (pst2); let pst8 : (p q_x q_v1) = (p q_H2 q_x) := Eq.trans (pst6) (pst7); let pst9 : q_x = q_H2 := congrArg (fun q => L q) (pst8); let pst10 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst11 : (p q_v0 (p q_v0 q_v1)) = (p q_H2 (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst10); let pst12 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst13 : (p q_v0 q_v1) = (p q_H2 q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst14 : q_v1 = q_x := congrArg (fun q => R q) (pst8); let pst15 : q_v1 = q_H2 := Eq.trans (pst14) (pst9); let pst16 : (p q_H2 q_v1) = (p q_H2 q_H2) := congrArg (fun q => p q_H2 q) (pst15); let pst17 : (p q_v0 q_v1) = (p q_H2 q_H2) := Eq.trans (pst13) (pst16); let pst18 : (p q_H2 (p q_v0 q_v1)) = (p q_H2 (p q_H2 q_H2)) := congrArg (fun q => p q_H2 q) (pst17); let pst19 : (p q_v0 (p q_v0 q_v1)) = (p q_H2 (p q_H2 q_H2)) := Eq.trans (pst11) (pst18); let pst20 : v0 = (p q_H2 (p q_H2 q_H2)) := Eq.trans (peq0) (pst19); let pst21 : (p v0 x) = (p (p q_H2 (p q_H2 q_H2)) x) := congrArg (fun q => p q x) (pst20); let pst22 : (p (p v0 x) v0) = (p (p (p q_H2 (p q_H2 q_H2)) x) v0) := congrArg (fun q => p q v0) (pst21); let pst23 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst24 : (p q_v0 (p q_v0 q_v1)) = (p q_H2 (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst23); let pst25 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst26 : (p q_v0 q_v1) = (p q_H2 q_v1) := congrArg (fun q => p q q_v1) (pst25); let pst27 : (p q_H2 q_v1) = (p q_H2 q_H2) := congrArg (fun q => p q_H2 q) (pst15); let pst28 : (p q_v0 q_v1) = (p q_H2 q_H2) := Eq.trans (pst26) (pst27); let pst29 : (p q_H2 (p q_v0 q_v1)) = (p q_H2 (p q_H2 q_H2)) := congrArg (fun q => p q_H2 q) (pst28); let pst30 : (p q_v0 (p q_v0 q_v1)) = (p q_H2 (p q_H2 q_H2)) := Eq.trans (pst24) (pst29); let pst31 : v0 = (p q_H2 (p q_H2 q_H2)) := Eq.trans (peq0) (pst30); let pst32 : (p (p (p q_H2 (p q_H2 q_H2)) x) v0) = (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2))) := congrArg (fun q => p (p (p q_H2 (p q_H2 q_H2)) x) q) (pst31); let pst33 : (p (p v0 x) v0) = (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2))) := Eq.trans (pst22) (pst32); let pst34 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) := congrArg (fun q => p x q) (pst33); let pst35 : (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst34); let pst36 : (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) = q_v0 := Eq.trans (pst35) (peq3); let pst37 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst38 : (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) = q_H2 := Eq.trans (pst36) (pst37); let pst39 : q_H2 = (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) := Eq.symm (pst38); pst39)
            have hlt : sz q_H2 < sz (p x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_H2 (p q_H2 q_H2)) (sz_lt_p_left (p q_H2 (p q_H2 q_H2)) x)) (sz_lt_p_left (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2)))) (sz_lt_p_right x (p (p (p q_H2 (p q_H2 q_H2)) x) (p q_H2 (p q_H2 q_H2))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p v0 x) = (p (p q_x (p (p q_v0 q_x) q_v0)) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (peq0) (pst1); let pst6 : (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p (p (p q_x (p (p q_v0 q_x) q_v0)) x) q) (pst5); let pst7 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := Eq.trans (pst4) (pst6); let pst8 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst7); let pst9 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst8); let pst10 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst9) (peq3); let pst11 : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst10); pst11)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_left (p q_x (p (p q_v0 q_x) q_v0)) x)) (sz_lt_p_left (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p q_H2 q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p v0 x) = (p (p q_x (p q_H2 q_v0)) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p q_x (p q_H2 q_v0)) := Eq.trans (peq0) (pst1); let pst6 : (p (p (p q_x (p q_H2 q_v0)) x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := congrArg (fun q => p (p (p q_x (p q_H2 q_v0)) x) q) (pst5); let pst7 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := Eq.trans (pst4) (pst6); let pst8 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst7); let pst9 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst8); let pst10 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst9) (peq3); let pst11 : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Eq.symm (pst10); pst11)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_left (p q_x (p q_H2 q_v0)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 q_H0) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_x = (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_H0) = (p q_x q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst4 : q_H0 = (p (p q_v0 q_x) q_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p q_v0 q_x) = (p q_x q_x) := congrArg (fun q => p q q_x) (pst2); let pst6 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst7 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) q_x) := congrArg (fun q => p (p q_x q_x) q) (pst2); let pst8 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_x) := Eq.trans (pst6) (pst7); let pst9 : q_H0 = (p (p q_x q_x) q_x) := Eq.trans (pst4) (pst8); let pst10 : (p q_x q_H0) = (p q_x (p (p q_x q_x) q_x)) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p q_v0 q_H0) = (p q_x (p (p q_x q_x) q_x)) := Eq.trans (pst3) (pst10); let pst12 : v0 = (p q_x (p (p q_x q_x) q_x)) := Eq.trans (peq0) (pst11); let pst13 : (p v0 x) = (p (p q_x (p (p q_x q_x) q_x)) x) := congrArg (fun q => p q x) (pst12); let pst14 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_x q_x) q_x)) x) v0) := congrArg (fun q => p q v0) (pst13); let pst15 : (p q_v0 q_H0) = (p q_x q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst16 : (p q_x q_H0) = (p q_x (p (p q_x q_x) q_x)) := congrArg (fun q => p q_x q) (pst9); let pst17 : (p q_v0 q_H0) = (p q_x (p (p q_x q_x) q_x)) := Eq.trans (pst15) (pst16); let pst18 : v0 = (p q_x (p (p q_x q_x) q_x)) := Eq.trans (peq0) (pst17); let pst19 : (p (p (p q_x (p (p q_x q_x) q_x)) x) v0) = (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x))) := congrArg (fun q => p (p (p q_x (p (p q_x q_x) q_x)) x) q) (pst18); let pst20 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x))) := Eq.trans (pst14) (pst19); let pst21 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) := congrArg (fun q => p x q) (pst20); let pst22 : (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst21); let pst23 : (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) = q_v0 := Eq.trans (pst22) (peq3); let pst24 : (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) = q_x := Eq.trans (pst23) (pst2); let pst25 : q_x = (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) := Eq.symm (pst24); pst25)
            have hlt : sz q_x < sz (p x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x (p (p q_x q_x) q_x)) (sz_lt_p_left (p q_x (p (p q_x q_x) q_x)) x)) (sz_lt_p_left (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x)))) (sz_lt_p_right x (p (p (p q_x (p (p q_x q_x) q_x)) x) (p q_x (p (p q_x q_x) q_x))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 q_H0) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_x = (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_H0) = (p q_x q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst4 : q_H0 = (p q_H2 q_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p q_H2 q_v0) = (p q_H2 q_x) := congrArg (fun q => p q_H2 q) (pst2); let pst6 : q_H0 = (p q_H2 q_x) := Eq.trans (pst4) (pst5); let pst7 : (p q_x q_H0) = (p q_x (p q_H2 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p q_v0 q_H0) = (p q_x (p q_H2 q_x)) := Eq.trans (pst3) (pst7); let pst9 : v0 = (p q_x (p q_H2 q_x)) := Eq.trans (peq0) (pst8); let pst10 : (p v0 x) = (p (p q_x (p q_H2 q_x)) x) := congrArg (fun q => p q x) (pst9); let pst11 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_x)) x) v0) := congrArg (fun q => p q v0) (pst10); let pst12 : (p q_v0 q_H0) = (p q_x q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst13 : (p q_x q_H0) = (p q_x (p q_H2 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst14 : (p q_v0 q_H0) = (p q_x (p q_H2 q_x)) := Eq.trans (pst12) (pst13); let pst15 : v0 = (p q_x (p q_H2 q_x)) := Eq.trans (peq0) (pst14); let pst16 : (p (p (p q_x (p q_H2 q_x)) x) v0) = (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x))) := congrArg (fun q => p (p (p q_x (p q_H2 q_x)) x) q) (pst15); let pst17 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x))) := Eq.trans (pst11) (pst16); let pst18 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) := congrArg (fun q => p x q) (pst17); let pst19 : (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst18); let pst20 : (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) = q_v0 := Eq.trans (pst19) (peq3); let pst21 : (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) = q_x := Eq.trans (pst20) (pst2); let pst22 : q_x = (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) := Eq.symm (pst21); pst22)
            have hlt : sz q_x < sz (p x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x (p q_H2 q_x)) (sz_lt_p_left (p q_x (p q_H2 q_x)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_x)) x) (p q_x (p q_H2 q_x))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p v0 x) = (p (p q_x (p (p q_v0 q_x) q_v0)) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (peq0) (pst1); let pst6 : (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p (p (p q_x (p (p q_v0 q_x) q_v0)) x) q) (pst5); let pst7 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := Eq.trans (pst4) (pst6); let pst8 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst7); let pst9 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst8); let pst10 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst9) (peq3); let pst11 : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst10); pst11)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_left (p q_x (p (p q_v0 q_x) q_v0)) x)) (sz_lt_p_left (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p (p v0 x) v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p q_H2 q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p v0 x) = (p (p q_x (p q_H2 q_v0)) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p q_x (p q_H2 q_v0)) := Eq.trans (peq0) (pst1); let pst6 : (p (p (p q_x (p q_H2 q_v0)) x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := congrArg (fun q => p (p (p q_x (p q_H2 q_v0)) x) q) (pst5); let pst7 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := Eq.trans (pst4) (pst6); let pst8 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst7); let pst9 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst8); let pst10 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst9) (peq3); let pst11 : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Eq.symm (pst10); pst11)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_left (p q_x (p q_H2 q_v0)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s2h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 (p q_v0 q_v1)) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_x = (p q_x q_x) := (let peq0 : v0 = (p q_v0 (p q_v0 q_v1)) := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let pst0 : (p q_v0 (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v0 q_v1)) = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p q_v0 q_v1) = (p (p q_v0 q_x) q_v0) := congrArg (fun q => R q) (pst1); let pst6 : (p q_x q_v1) = (p (p q_v0 q_x) q_v0) := Eq.trans (pst4) (pst5); let pst7 : (p q_v0 q_x) = (p q_x q_x) := congrArg (fun q => p q q_x) (pst2); let pst8 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_v0) := congrArg (fun q => p q q_v0) (pst7); let pst9 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) q_x) := congrArg (fun q => p (p q_x q_x) q) (pst2); let pst10 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_x) := Eq.trans (pst8) (pst9); let pst11 : (p q_x q_v1) = (p (p q_x q_x) q_x) := Eq.trans (pst6) (pst10); let pst12 : q_x = (p q_x q_x) := congrArg (fun q => L q) (pst11); pst12)
            have hlt : sz q_x < sz (p q_x q_x) := sz_lt_p_left q_x q_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 (p q_v0 q_v1)) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_H2 = (p x (p H2 (p q_H2 (p q_H2 q_H2)))) := (let peq0 : v0 = (p q_v0 (p q_v0 q_v1)) := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : (p q_v0 (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v0 q_v1)) = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p q_v0 q_v1) = (p q_H2 q_v0) := congrArg (fun q => R q) (pst1); let pst6 : (p q_x q_v1) = (p q_H2 q_v0) := Eq.trans (pst4) (pst5); let pst7 : (p q_H2 q_v0) = (p q_H2 q_x) := congrArg (fun q => p q_H2 q) (pst2); let pst8 : (p q_x q_v1) = (p q_H2 q_x) := Eq.trans (pst6) (pst7); let pst9 : q_x = q_H2 := congrArg (fun q => L q) (pst8); let pst10 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst11 : (p q_v0 (p q_v0 q_v1)) = (p q_H2 (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst10); let pst12 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst13 : (p q_v0 q_v1) = (p q_H2 q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst14 : q_v1 = q_x := congrArg (fun q => R q) (pst8); let pst15 : q_v1 = q_H2 := Eq.trans (pst14) (pst9); let pst16 : (p q_H2 q_v1) = (p q_H2 q_H2) := congrArg (fun q => p q_H2 q) (pst15); let pst17 : (p q_v0 q_v1) = (p q_H2 q_H2) := Eq.trans (pst13) (pst16); let pst18 : (p q_H2 (p q_v0 q_v1)) = (p q_H2 (p q_H2 q_H2)) := congrArg (fun q => p q_H2 q) (pst17); let pst19 : (p q_v0 (p q_v0 q_v1)) = (p q_H2 (p q_H2 q_H2)) := Eq.trans (pst11) (pst18); let pst20 : v0 = (p q_H2 (p q_H2 q_H2)) := Eq.trans (peq0) (pst19); let pst21 : (p H2 v0) = (p H2 (p q_H2 (p q_H2 q_H2))) := congrArg (fun q => p H2 q) (pst20); let pst22 : (p x (p H2 v0)) = (p x (p H2 (p q_H2 (p q_H2 q_H2)))) := congrArg (fun q => p x q) (pst21); let pst23 : (p x (p H2 (p q_H2 (p q_H2 q_H2)))) = (p x (p H2 v0)) := Eq.symm (pst22); let pst24 : (p x (p H2 (p q_H2 (p q_H2 q_H2)))) = q_v0 := Eq.trans (pst23) (peq3); let pst25 : q_v0 = q_H2 := Eq.trans (pst2) (pst9); let pst26 : (p x (p H2 (p q_H2 (p q_H2 q_H2)))) = q_H2 := Eq.trans (pst24) (pst25); let pst27 : q_H2 = (p x (p H2 (p q_H2 (p q_H2 q_H2)))) := Eq.symm (pst26); pst27)
            have hlt : sz q_H2 < sz (p x (p H2 (p q_H2 (p q_H2 q_H2)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_H2 (p q_H2 q_H2)) (sz_lt_p_right H2 (p q_H2 (p q_H2 q_H2)))) (sz_lt_p_right x (p H2 (p q_H2 (p q_H2 q_H2))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p H2 v0) = (p H2 (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p H2 q) (pst2); let pst4 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst4); let pst6 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst5) (peq3); let pst7 : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_right H2 (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p q_H2 q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_v0))) := congrArg (fun q => p H2 q) (pst2); let pst4 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst4); let pst6 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst5) (peq3); let pst7 : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_right H2 (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 q_H0) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_x = (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_H0) = (p q_x q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst4 : q_H0 = (p (p q_v0 q_x) q_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p q_v0 q_x) = (p q_x q_x) := congrArg (fun q => p q q_x) (pst2); let pst6 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst7 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) q_x) := congrArg (fun q => p (p q_x q_x) q) (pst2); let pst8 : (p (p q_v0 q_x) q_v0) = (p (p q_x q_x) q_x) := Eq.trans (pst6) (pst7); let pst9 : q_H0 = (p (p q_x q_x) q_x) := Eq.trans (pst4) (pst8); let pst10 : (p q_x q_H0) = (p q_x (p (p q_x q_x) q_x)) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p q_v0 q_H0) = (p q_x (p (p q_x q_x) q_x)) := Eq.trans (pst3) (pst10); let pst12 : v0 = (p q_x (p (p q_x q_x) q_x)) := Eq.trans (peq0) (pst11); let pst13 : (p H2 v0) = (p H2 (p q_x (p (p q_x q_x) q_x))) := congrArg (fun q => p H2 q) (pst12); let pst14 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) := congrArg (fun q => p x q) (pst13); let pst15 : (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) = (p x (p H2 v0)) := Eq.symm (pst14); let pst16 : (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) = q_v0 := Eq.trans (pst15) (peq3); let pst17 : (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) = q_x := Eq.trans (pst16) (pst2); let pst18 : q_x = (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) := Eq.symm (pst17); pst18)
            have hlt : sz q_x < sz (p x (p H2 (p q_x (p (p q_x q_x) q_x)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x (p (p q_x q_x) q_x)) (sz_lt_p_right H2 (p q_x (p (p q_x q_x) q_x)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_x q_x) q_x))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = (p q_v0 q_H0) at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_x = (p x (p H2 (p q_x (p q_H2 q_x)))) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_H0) = (p q_x q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst4 : q_H0 = (p q_H2 q_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p q_H2 q_v0) = (p q_H2 q_x) := congrArg (fun q => p q_H2 q) (pst2); let pst6 : q_H0 = (p q_H2 q_x) := Eq.trans (pst4) (pst5); let pst7 : (p q_x q_H0) = (p q_x (p q_H2 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p q_v0 q_H0) = (p q_x (p q_H2 q_x)) := Eq.trans (pst3) (pst7); let pst9 : v0 = (p q_x (p q_H2 q_x)) := Eq.trans (peq0) (pst8); let pst10 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_x))) := congrArg (fun q => p H2 q) (pst9); let pst11 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_x)))) := congrArg (fun q => p x q) (pst10); let pst12 : (p x (p H2 (p q_x (p q_H2 q_x)))) = (p x (p H2 v0)) := Eq.symm (pst11); let pst13 : (p x (p H2 (p q_x (p q_H2 q_x)))) = q_v0 := Eq.trans (pst12) (peq3); let pst14 : (p x (p H2 (p q_x (p q_H2 q_x)))) = q_x := Eq.trans (pst13) (pst2); let pst15 : q_x = (p x (p H2 (p q_x (p q_H2 q_x)))) := Eq.symm (pst14); pst15)
            have hlt : sz q_x < sz (p x (p H2 (p q_x (p q_H2 q_x)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x (p q_H2 q_x)) (sz_lt_p_right H2 (p q_x (p q_H2 q_x)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_x))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p H2 v0) = (p H2 (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p H2 q) (pst2); let pst4 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst4); let pst6 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst5) (peq3); let pst7 : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_right H2 (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change v0 = q_H1 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change H0 = q_v0 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e2
            have e3 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e3
            have cyc : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := (let peq0 : v0 = q_H1 := e0; let peq2 : v0 = (p q_x (p q_H2 q_v0)) := e2; let peq3 : (p x (p H2 v0)) = q_v0 := e3; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p q_x (p q_H2 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_x (p q_H2 q_v0)) := Eq.trans (peq0) (pst1); let pst3 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_v0))) := congrArg (fun q => p H2 q) (pst2); let pst4 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst4); let pst6 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst5) (peq3); let pst7 : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_right H2 (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have s2B := step_bound s2
    have s2N := step_no_first s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 (p q_v0 q_v1)) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p (p q_v0 q_x) q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p (p (p q_x (p (p q_v0 q_x) q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_left (p q_x (p (p q_v0 q_x) q_v0)) x)) (sz_lt_p_left (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 (p q_v0 q_v1)) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p q_H2 q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p q_H2 q_v0)) x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := congrArg (fun q => p (p (p q_x (p q_H2 q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_left (p q_x (p q_H2 q_v0)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p (p q_v0 q_x) q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p (p (p q_x (p (p q_v0 q_x) q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_left (p q_x (p (p q_v0 q_x) q_v0)) x)) (sz_lt_p_left (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p q_H2 q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p q_H2 q_v0)) x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := congrArg (fun q => p (p (p q_x (p q_H2 q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_left (p q_x (p q_H2 q_v0)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 q_H0) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p (p q_v0 q_x) q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p (p (p q_x (p (p q_v0 q_x) q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_left (p q_x (p (p q_v0 q_x) q_v0)) x)) (sz_lt_p_left (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 q_H0) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p q_H2 q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p q_H2 q_v0)) x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := congrArg (fun q => p (p (p q_x (p q_H2 q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_left (p q_x (p q_H2 q_v0)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p (p q_v0 q_x) q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p (p (p q_x (p (p q_v0 q_x) q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_left (p q_x (p (p q_v0 q_x) q_v0)) x)) (sz_lt_p_left (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p (p (p q_x (p (p q_v0 q_x) q_v0)) x) (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p (p v0 x) v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p (p v0 x) v0)) = q_v0 := e2; let pst0 : (p v0 x) = (p (p q_x (p q_H2 q_v0)) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) v0) := congrArg (fun q => p q v0) (pst0); let pst2 : (p (p (p q_x (p q_H2 q_v0)) x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := congrArg (fun q => p (p (p q_x (p q_H2 q_v0)) x) q) (peq1); let pst3 : (p (p v0 x) v0) = (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))) := Eq.trans (pst1) (pst2); let pst4 : (p x (p (p v0 x) v0)) = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst3); let pst5 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = (p x (p (p v0 x) v0)) := Eq.symm (pst4); let pst6 : (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst5) (peq2); let pst7 : q_v0 = (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_left (p q_x (p q_H2 q_v0)) x)) (sz_lt_p_left (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p (p (p q_x (p q_H2 q_v0)) x) (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s2h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 (p q_v0 q_v1)) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_right H2 (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 (p q_v0 q_v1)) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_right H2 (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_right H2 (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_right H2 (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 q_H0) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_right H2 (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p (p q_v0 q_H0) q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_right H2 (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p (p q_v0 q_x) q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := (let peq1 : v0 = (p q_x (p (p q_v0 q_x) q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p (p q_v0 q_x) q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p (p q_v0 q_x) q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_v0)) (sz_lt_p_right q_x (p (p q_v0 q_x) q_v0))) (sz_lt_p_right H2 (p q_x (p (p q_v0 q_x) q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p (p q_v0 q_x) q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change H1 = (p q_H1 q_v0) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change v0 = (p q_x (p q_H2 q_v0)) at e1
            have e2 := congrArg (fun q => q) hb
            change (p x (p H2 v0)) = q_v0 at e2
            have cyc : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := (let peq1 : v0 = (p q_x (p q_H2 q_v0)) := e1; let peq2 : (p x (p H2 v0)) = q_v0 := e2; let pst0 : (p H2 v0) = (p H2 (p q_x (p q_H2 q_v0))) := congrArg (fun q => p H2 q) (peq1); let pst1 : (p x (p H2 v0)) = (p x (p H2 (p q_x (p q_H2 q_v0)))) := congrArg (fun q => p x q) (pst0); let pst2 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = (p x (p H2 v0)) := Eq.symm (pst1); let pst3 : (p x (p H2 (p q_x (p q_H2 q_v0)))) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p x (p H2 (p q_x (p q_H2 q_v0)))) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p x (p H2 (p q_x (p q_H2 q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_v0) (sz_lt_p_right q_x (p q_H2 q_v0))) (sz_lt_p_right H2 (p q_x (p q_H2 q_v0)))) (sz_lt_p_right x (p H2 (p q_x (p q_H2 q_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 (eval v0 v1)) v0) (eval x (eval (eval v0 x) v0))) v0) := by
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
  let H1 := eval v0 (eval v0 v1)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval v0 v1) = H0 := by
    change H0 = H0
    rfl
  have s1 : Step v0 H0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval v0 v1)
  let H2 := eval v0 x
  have e2a : v0 = v0 := by
    change v0 = v0
    rfl
  have e2b : x = x := by
    change x = x
    rfl
  have s2 : Step v0 x H2 := by
    rw [← e2a, ← e2b]
    exact eval_step v0 x
  change x = (eval (eval (eval H1 v0) (eval x (eval H2 v0))) v0)
  have rawEq : (eval (eval (eval H1 v0) (eval x (eval H2 v0))) v0) = (eval (p (p H1 v0) (p x (p H2 v0))) v0) := by
    calc
      (eval (eval (eval H1 v0) (eval x (eval H2 v0))) v0) = (eval (eval (p H1 v0) (eval x (eval H2 v0))) v0) := congrArg (fun q => (eval (eval q (eval x (eval H2 v0))) v0)) (eval_raw (nr0 x v0 v1 H1 s1))
      _ = (eval (eval (p H1 v0) (eval x (p H2 v0))) v0) := congrArg (fun q => (eval (eval (p H1 v0) (eval x q)) v0)) (eval_raw (nr1 x v0 v1 H2 s2))
      _ = (eval (eval (p H1 v0) (p x (p H2 v0))) v0) := congrArg (fun q => (eval (eval (p H1 v0) q) v0)) (eval_raw (nr2 x v0 v1 H2 s2))
      _ = (eval (p (p H1 v0) (p x (p H2 v0))) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr3 x v0 v1 H1 H2 s1 s2))
  exact (eval_hit (Code.law x v0 v1 H0 H1 H2 s0 s1 s2)).symm.trans rawEq.symm
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
