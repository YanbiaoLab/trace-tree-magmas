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
  | law (x v0 v1 v2 H0 H1 : CM)
      (s0 : Step v1 v2 H0)
      (s1 : Step v0 H0 H1) :
      Code (p (p (p H1 v0) (p (p x x) v1)) v0) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 : CM, Step q_v1 q_v2 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ a = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 s0 s1 => ⟨x, v0, v1, v2, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R (L a))))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, s0, s1, ha, hb, ho⟩
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : v = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) = v := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v2)) (sz_lt_p_left (p q_v0 (p q_v1 q_v2)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : v = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = v := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : v = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) = v := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : v = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = v := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p (p q_x q_x) q_v1))
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
theorem nr0 (x v0 v1 v2 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code H1 v0 o := by
  exact step_no_first s1

theorem nr1 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) := (let peq0 : x = (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v2)) (sz_lt_p_left (p q_v0 (p q_v1 q_v2)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1))) (sz_lt_p_left (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := (let peq0 : x = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p (p q_x q_x) q_v1))) (sz_lt_p_left (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) := (let peq0 : x = (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1))) (sz_lt_p_left (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := (let peq0 : x = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p (p q_x q_x) q_v1))) (sz_lt_p_left (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code (p x x) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : x = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v2)) (sz_lt_p_left (p q_v0 (p q_v1 q_v2)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : x = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = x := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : x = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := (let peq0 : x = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = x := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) (p (p q_x q_x) q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 v2 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p H1 v0) (p (p x x) v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
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
        change v0 = (p (p q_v0 (p q_v1 q_v2)) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = (p (p q_x q_x) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change (p (p x x) v1) = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 (p q_v1 q_v2)) q_v0) := (let peq0 : v0 = (p (p q_v0 (p q_v1 q_v2)) q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p q_v1 q_v2)) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 q_v2)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v2)) (sz_lt_p_left (p q_v0 (p q_v1 q_v2)) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = (p (p q_x q_x) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change (p (p x x) v1) = q_v0 at e3
        have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v0 = (p q_H1 q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_H1 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p q_v0 q_H0) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = (p (p q_x q_x) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change (p (p x x) v1) = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 q_H0) q_v0) := (let peq0 : v0 = (p (p q_v0 q_H0) q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_H0) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = (p (p q_x q_x) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change (p (p x x) v1) = q_v0 at e3
        have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v0 = (p q_H1 q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_H1 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
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
        change H1 = (p (p (p q_v0 (p q_v1 q_v2)) q_v0) (p (p q_x q_x) q_v1)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change (p (p x x) v1) = q_v0 at p2
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
        change H1 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change (p (p x x) v1) = q_v0 at p2
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
        change H1 = (p (p (p q_v0 q_H0) q_v0) (p (p q_x q_x) q_v1)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change (p (p x x) v1) = q_v0 at p2
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
        change H1 = (p (p q_H1 q_v0) (p (p q_x q_x) q_v1)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change (p (p x x) v1) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
theorem nr4 (x v0 v1 v2 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p (p H1 v0) (p (p x x) v1)) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = (p (p q_x q_x) q_v1) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p (p x x) v1) = q_v0 := congrArg (fun q => (R q)) (ha); let peq4 : v0 = q_v0 := hb; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p (p q_x q_x) q_v1) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p (p q_x q_x) q_v1) := Eq.trans (peq0) (pst1); let pst3 : (p (p q_x q_x) q_v1) = v0 := Eq.symm (pst2); let pst4 : (p (p q_x q_x) q_v1) = q_v0 := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p x x) v1) := Eq.symm (peq3); let pst6 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst4) (pst5); let pst7 : (p q_x q_x) = (p x x) := congrArg (fun q => L q) (pst6); let pst8 : q_x = x := congrArg (fun q => L q) (pst7); let pst9 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst8); let pst10 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst8); let pst11 : (p q_x q_x) = (p x x) := Eq.trans (pst9) (pst10); let pst12 : (p (p q_x q_x) q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst11); let pst13 : q_v1 = v1 := congrArg (fun q => R q) (pst6); let pst14 : (p (p x x) q_v1) = (p (p x x) v1) := congrArg (fun q => p (p x x) q) (pst13); let pst15 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst12) (pst14); let pst16 : q_H1 = (p (p x x) v1) := Eq.trans (pst1) (pst15); let pst17 : (p (p x x) v1) = q_v0 := Eq.symm (pst5); let pst18 : q_H1 = q_v0 := Eq.trans (pst16) (pst17); pst18)
      exact step_ne_first (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = (p (p q_x q_x) q_v1) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p (p x x) v1) = q_v0 := congrArg (fun q => (R q)) (ha); let peq4 : v0 = q_v0 := hb; let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = (p (p q_x q_x) q_v1) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p (p q_x q_x) q_v1) := Eq.trans (peq0) (pst1); let pst3 : (p (p q_x q_x) q_v1) = v0 := Eq.symm (pst2); let pst4 : (p (p q_x q_x) q_v1) = q_v0 := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p x x) v1) := Eq.symm (peq3); let pst6 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst4) (pst5); let pst7 : (p q_x q_x) = (p x x) := congrArg (fun q => L q) (pst6); let pst8 : q_x = x := congrArg (fun q => L q) (pst7); let pst9 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst8); let pst10 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst8); let pst11 : (p q_x q_x) = (p x x) := Eq.trans (pst9) (pst10); let pst12 : (p (p q_x q_x) q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst11); let pst13 : q_v1 = v1 := congrArg (fun q => R q) (pst6); let pst14 : (p (p x x) q_v1) = (p (p x x) v1) := congrArg (fun q => p (p x x) q) (pst13); let pst15 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst12) (pst14); let pst16 : q_H1 = (p (p x x) v1) := Eq.trans (pst1) (pst15); let pst17 : (p (p x x) v1) = q_v0 := Eq.symm (pst5); let pst18 : q_H1 = q_v0 := Eq.trans (pst16) (pst17); pst18)
      exact step_ne_first (by simpa only [he] using qs1)
  | hit s1h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0B := step_bound u0s0
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v1 = (p u0_v1 u0_v2) := (let peq1 : v0 = (p (p q_x q_x) q_v1) := congrArg (fun q => (R (L q))) (ha); let peq2 : (p (p x x) v1) = q_v0 := congrArg (fun q => (R q)) (ha); let peq3 : v0 = q_v0 := hb; let peq5 : v0 = (p (p (p (p u0_v0 (p u0_v1 u0_v2)) u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := u0a; let pst0 : (p (p q_x q_x) q_v1) = v0 := Eq.symm (peq1); let pst1 : (p (p q_x q_x) q_v1) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p x x) v1) := Eq.symm (peq2); let pst3 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst1) (pst2); let pst4 : (p q_x q_x) = (p x x) := congrArg (fun q => L q) (pst3); let pst5 : q_x = x := congrArg (fun q => L q) (pst4); let pst6 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst5); let pst7 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst5); let pst8 : (p q_x q_x) = (p x x) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_x) q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst10 : q_v1 = v1 := congrArg (fun q => R q) (pst3); let pst11 : (p (p x x) q_v1) = (p (p x x) v1) := congrArg (fun q => p (p x x) q) (pst10); let pst12 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst9) (pst11); let pst13 : v0 = (p (p x x) v1) := Eq.trans (peq1) (pst12); let pst14 : (p (p x x) v1) = v0 := Eq.symm (pst13); let pst15 : (p (p x x) v1) = (p (p (p (p u0_v0 (p u0_v1 u0_v2)) u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := Eq.trans (pst14) (peq5); let pst16 : (p x x) = (p (p (p u0_v0 (p u0_v1 u0_v2)) u0_v0) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => L q) (pst15); let pst17 : x = (p (p u0_v0 (p u0_v1 u0_v2)) u0_v0) := congrArg (fun q => L q) (pst16); let pst18 : (p (p u0_v0 (p u0_v1 u0_v2)) u0_v0) = x := Eq.symm (pst17); let pst19 : x = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => R q) (pst16); let pst20 : (p (p u0_v0 (p u0_v1 u0_v2)) u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst18) (pst19); let pst21 : (p u0_v0 (p u0_v1 u0_v2)) = (p u0_x u0_x) := congrArg (fun q => L q) (pst20); let pst22 : u0_v0 = u0_x := congrArg (fun q => L q) (pst21); let pst23 : (p u0_v1 u0_v2) = u0_x := congrArg (fun q => R q) (pst21); let pst24 : u0_x = (p u0_v1 u0_v2) := Eq.symm (pst23); let pst25 : u0_v0 = (p u0_v1 u0_v2) := Eq.trans (pst22) (pst24); let pst26 : (p u0_v1 u0_v2) = u0_v0 := Eq.symm (pst25); let pst27 : u0_v0 = u0_v1 := congrArg (fun q => R q) (pst20); let pst28 : (p u0_v1 u0_v2) = u0_v1 := Eq.trans (pst26) (pst27); let pst29 : u0_v1 = (p u0_v1 u0_v2) := Eq.symm (pst28); pst29)
            have hlt : sz u0_v1 < sz (p u0_v1 u0_v2) := sz_lt_p_left u0_v1 u0_v2
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := (let peq0 : H1 = (p (p q_v0 (p q_v1 q_v2)) q_v0) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p (p q_x q_x) q_v1) := congrArg (fun q => (R (L q))) (ha); let peq2 : (p (p x x) v1) = q_v0 := congrArg (fun q => (R q)) (ha); let peq3 : v0 = q_v0 := hb; let peq5 : v0 = (p (p (p u0s1out u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := u0a; let peq7 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x x) v1) := Eq.symm (peq2); let pst1 : (p (p q_x q_x) q_v1) = v0 := Eq.symm (peq1); let pst2 : (p (p q_x q_x) q_v1) = q_v0 := Eq.trans (pst1) (peq3); let pst3 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst2) (pst0); let pst4 : (p q_x q_x) = (p x x) := congrArg (fun q => L q) (pst3); let pst5 : q_x = x := congrArg (fun q => L q) (pst4); let pst6 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst5); let pst7 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst5); let pst8 : (p q_x q_x) = (p x x) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_x) q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst10 : q_v1 = v1 := congrArg (fun q => R q) (pst3); let pst11 : (p (p x x) q_v1) = (p (p x x) v1) := congrArg (fun q => p (p x x) q) (pst10); let pst12 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst9) (pst11); let pst13 : v0 = (p (p x x) v1) := Eq.trans (peq1) (pst12); let pst14 : (p (p x x) v1) = v0 := Eq.symm (pst13); let pst15 : (p (p x x) v1) = (p (p (p u0s1out u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := Eq.trans (pst14) (peq5); let pst16 : (p x x) = (p (p u0s1out u0_v0) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => L q) (pst15); let pst17 : x = (p u0s1out u0_v0) := congrArg (fun q => L q) (pst16); let pst18 : (p u0s1out u0_v0) = x := Eq.symm (pst17); let pst19 : x = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => R q) (pst16); let pst20 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst18) (pst19); let pst21 : u0s1out = (p u0_x u0_x) := congrArg (fun q => L q) (pst20); let pst22 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst23 : u0_v0 = u0_v1 := congrArg (fun q => R q) (pst20); let pst24 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst25 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst22) (pst24); let pst26 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst25); let pst27 : (p x x) = (p (p (p u0_x u0_x) u0_v1) x) := congrArg (fun q => p q x) (pst26); let pst28 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst29 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst30 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst28) (pst29); let pst31 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst30); let pst32 : (p (p (p u0_x u0_x) u0_v1) x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => p (p (p u0_x u0_x) u0_v1) q) (pst31); let pst33 : (p x x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := Eq.trans (pst27) (pst32); let pst34 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) := congrArg (fun q => p q v1) (pst33); let pst35 : v1 = u0_v0 := congrArg (fun q => R q) (pst15); let pst36 : v1 = u0_v1 := Eq.trans (pst35) (pst23); let pst37 : (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := congrArg (fun q => p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) q) (pst36); let pst38 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst34) (pst37); let pst39 : q_v0 = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst0) (pst38); let pst40 : (p q_v0 (p q_v1 q_v2)) = (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p q_v1 q_v2)) := congrArg (fun q => p q (p q_v1 q_v2)) (pst39); let pst41 : q_v1 = u0_v1 := Eq.trans (pst10) (pst36); let pst42 : (p q_v1 q_v2) = (p u0_v1 q_v2) := congrArg (fun q => p q q_v2) (pst41); let pst43 : (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p q_v1 q_v2)) = (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) := congrArg (fun q => p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) q) (pst42); let pst44 : (p q_v0 (p q_v1 q_v2)) = (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) := Eq.trans (pst40) (pst43); let pst45 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) q_v0) := congrArg (fun q => p q q_v0) (pst44); let pst46 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst47 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst48 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst46) (pst47); let pst49 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst48); let pst50 : (p x x) = (p (p (p u0_x u0_x) u0_v1) x) := congrArg (fun q => p q x) (pst49); let pst51 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst52 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst53 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst51) (pst52); let pst54 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst53); let pst55 : (p (p (p u0_x u0_x) u0_v1) x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => p (p (p u0_x u0_x) u0_v1) q) (pst54); let pst56 : (p x x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := Eq.trans (pst50) (pst55); let pst57 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) := congrArg (fun q => p q v1) (pst56); let pst58 : (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := congrArg (fun q => p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) q) (pst36); let pst59 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst57) (pst58); let pst60 : q_v0 = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst0) (pst59); let pst61 : (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := congrArg (fun q => p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) q) (pst60); let pst62 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Eq.trans (pst45) (pst61); let pst63 : H1 = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Eq.trans (peq0) (pst62); let pst64 : (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) = H1 := Eq.symm (pst63); let pst65 : (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) = u0_x := Eq.trans (pst64) (peq7); let pst66 : u0_x = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Eq.symm (pst65); pst66)
            have hlt : sz u0_x < sz (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) u0_v1)) (sz_lt_p_left (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1))) (sz_lt_p_left (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) (sz_lt_p_left (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2))) (sz_lt_p_left (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v1 = (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) := (let peq0 : H1 = (p (p q_v0 (p q_v1 q_v2)) q_v0) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p (p q_x q_x) q_v1) := congrArg (fun q => (R (L q))) (ha); let peq2 : (p (p x x) v1) = q_v0 := congrArg (fun q => (R q)) (ha); let peq3 : v0 = q_v0 := hb; let peq5 : v0 = (p (p (p (p u0_v0 u0s0out) u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := u0a; let peq7 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x x) v1) := Eq.symm (peq2); let pst1 : (p (p q_x q_x) q_v1) = v0 := Eq.symm (peq1); let pst2 : (p (p q_x q_x) q_v1) = q_v0 := Eq.trans (pst1) (peq3); let pst3 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst2) (pst0); let pst4 : (p q_x q_x) = (p x x) := congrArg (fun q => L q) (pst3); let pst5 : q_x = x := congrArg (fun q => L q) (pst4); let pst6 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst5); let pst7 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst5); let pst8 : (p q_x q_x) = (p x x) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_x) q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst10 : q_v1 = v1 := congrArg (fun q => R q) (pst3); let pst11 : (p (p x x) q_v1) = (p (p x x) v1) := congrArg (fun q => p (p x x) q) (pst10); let pst12 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst9) (pst11); let pst13 : v0 = (p (p x x) v1) := Eq.trans (peq1) (pst12); let pst14 : (p (p x x) v1) = v0 := Eq.symm (pst13); let pst15 : (p (p x x) v1) = (p (p (p (p u0_v0 u0s0out) u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := Eq.trans (pst14) (peq5); let pst16 : (p x x) = (p (p (p u0_v0 u0s0out) u0_v0) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => L q) (pst15); let pst17 : x = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => L q) (pst16); let pst18 : (p (p u0_v0 u0s0out) u0_v0) = x := Eq.symm (pst17); let pst19 : x = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => R q) (pst16); let pst20 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst18) (pst19); let pst21 : (p u0_v0 u0s0out) = (p u0_x u0_x) := congrArg (fun q => L q) (pst20); let pst22 : u0_v0 = u0_x := congrArg (fun q => L q) (pst21); let pst23 : u0_x = u0_v0 := Eq.symm (pst22); let pst24 : u0_v0 = u0_v1 := congrArg (fun q => R q) (pst20); let pst25 : u0_x = u0_v1 := Eq.trans (pst23) (pst24); let pst26 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst27 : (p u0_v0 u0s0out) = (p u0_v1 u0s0out) := congrArg (fun q => p q u0s0out) (pst26); let pst28 : u0s0out = u0_x := congrArg (fun q => R q) (pst21); let pst29 : u0s0out = u0_v1 := Eq.trans (pst28) (pst25); let pst30 : (p u0_v1 u0s0out) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst29); let pst31 : (p u0_v0 u0s0out) = (p u0_v1 u0_v1) := Eq.trans (pst27) (pst30); let pst32 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v0) := congrArg (fun q => p q u0_v0) (pst31); let pst33 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst34 : (p (p u0_v1 u0_v1) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst33); let pst35 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst32) (pst34); let pst36 : x = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst17) (pst35); let pst37 : (p x x) = (p (p (p u0_v1 u0_v1) u0_v1) x) := congrArg (fun q => p q x) (pst36); let pst38 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst39 : (p u0_v0 u0s0out) = (p u0_v1 u0s0out) := congrArg (fun q => p q u0s0out) (pst38); let pst40 : u0s0out = u0_v1 := Eq.trans (pst28) (pst25); let pst41 : (p u0_v1 u0s0out) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst40); let pst42 : (p u0_v0 u0s0out) = (p u0_v1 u0_v1) := Eq.trans (pst39) (pst41); let pst43 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v0) := congrArg (fun q => p q u0_v0) (pst42); let pst44 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst45 : (p (p u0_v1 u0_v1) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst44); let pst46 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst43) (pst45); let pst47 : x = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst17) (pst46); let pst48 : (p (p (p u0_v1 u0_v1) u0_v1) x) = (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) := congrArg (fun q => p (p (p u0_v1 u0_v1) u0_v1) q) (pst47); let pst49 : (p x x) = (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) := Eq.trans (pst37) (pst48); let pst50 : (p (p x x) v1) = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) v1) := congrArg (fun q => p q v1) (pst49); let pst51 : v1 = u0_v0 := congrArg (fun q => R q) (pst15); let pst52 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst53 : v1 = u0_v1 := Eq.trans (pst51) (pst52); let pst54 : (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) v1) = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) := congrArg (fun q => p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) q) (pst53); let pst55 : (p (p x x) v1) = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) := Eq.trans (pst50) (pst54); let pst56 : q_v0 = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) := Eq.trans (pst0) (pst55); let pst57 : (p q_v0 (p q_v1 q_v2)) = (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p q_v1 q_v2)) := congrArg (fun q => p q (p q_v1 q_v2)) (pst56); let pst58 : q_v1 = u0_v1 := Eq.trans (pst10) (pst53); let pst59 : (p q_v1 q_v2) = (p u0_v1 q_v2) := congrArg (fun q => p q q_v2) (pst58); let pst60 : (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p q_v1 q_v2)) = (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) := congrArg (fun q => p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) q) (pst59); let pst61 : (p q_v0 (p q_v1 q_v2)) = (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) := Eq.trans (pst57) (pst60); let pst62 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) q_v0) := congrArg (fun q => p q q_v0) (pst61); let pst63 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst64 : (p u0_v0 u0s0out) = (p u0_v1 u0s0out) := congrArg (fun q => p q u0s0out) (pst63); let pst65 : u0s0out = u0_v1 := Eq.trans (pst28) (pst25); let pst66 : (p u0_v1 u0s0out) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst65); let pst67 : (p u0_v0 u0s0out) = (p u0_v1 u0_v1) := Eq.trans (pst64) (pst66); let pst68 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v0) := congrArg (fun q => p q u0_v0) (pst67); let pst69 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst70 : (p (p u0_v1 u0_v1) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst69); let pst71 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst68) (pst70); let pst72 : x = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst17) (pst71); let pst73 : (p x x) = (p (p (p u0_v1 u0_v1) u0_v1) x) := congrArg (fun q => p q x) (pst72); let pst74 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst75 : (p u0_v0 u0s0out) = (p u0_v1 u0s0out) := congrArg (fun q => p q u0s0out) (pst74); let pst76 : u0s0out = u0_v1 := Eq.trans (pst28) (pst25); let pst77 : (p u0_v1 u0s0out) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst76); let pst78 : (p u0_v0 u0s0out) = (p u0_v1 u0_v1) := Eq.trans (pst75) (pst77); let pst79 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v0) := congrArg (fun q => p q u0_v0) (pst78); let pst80 : u0_v0 = u0_v1 := Eq.trans (pst22) (pst25); let pst81 : (p (p u0_v1 u0_v1) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst80); let pst82 : (p (p u0_v0 u0s0out) u0_v0) = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst79) (pst81); let pst83 : x = (p (p u0_v1 u0_v1) u0_v1) := Eq.trans (pst17) (pst82); let pst84 : (p (p (p u0_v1 u0_v1) u0_v1) x) = (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) := congrArg (fun q => p (p (p u0_v1 u0_v1) u0_v1) q) (pst83); let pst85 : (p x x) = (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) := Eq.trans (pst73) (pst84); let pst86 : (p (p x x) v1) = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) v1) := congrArg (fun q => p q v1) (pst85); let pst87 : (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) v1) = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) := congrArg (fun q => p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) q) (pst53); let pst88 : (p (p x x) v1) = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) := Eq.trans (pst86) (pst87); let pst89 : q_v0 = (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) := Eq.trans (pst0) (pst88); let pst90 : (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) := congrArg (fun q => p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) q) (pst89); let pst91 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) := Eq.trans (pst62) (pst90); let pst92 : H1 = (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) := Eq.trans (peq0) (pst91); let pst93 : (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) = H1 := Eq.symm (pst92); let pst94 : (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) = u0_x := Eq.trans (pst93) (peq7); let pst95 : (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) = u0_v1 := Eq.trans (pst94) (pst25); let pst96 : u0_v1 = (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) := Eq.symm (pst95); pst96)
            have hlt : sz u0_v1 < sz (p (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_left (p u0_v1 u0_v1) u0_v1)) (sz_lt_p_left (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1))) (sz_lt_p_left (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1)) (sz_lt_p_left (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2))) (sz_lt_p_left (p (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_v1 u0_v1) u0_v1) (p (p u0_v1 u0_v1) u0_v1)) u0_v1))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := (let peq0 : H1 = (p (p q_v0 (p q_v1 q_v2)) q_v0) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p (p q_x q_x) q_v1) := congrArg (fun q => (R (L q))) (ha); let peq2 : (p (p x x) v1) = q_v0 := congrArg (fun q => (R q)) (ha); let peq3 : v0 = q_v0 := hb; let peq5 : v0 = (p (p (p u0s1out u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := u0a; let peq7 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x x) v1) := Eq.symm (peq2); let pst1 : (p (p q_x q_x) q_v1) = v0 := Eq.symm (peq1); let pst2 : (p (p q_x q_x) q_v1) = q_v0 := Eq.trans (pst1) (peq3); let pst3 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst2) (pst0); let pst4 : (p q_x q_x) = (p x x) := congrArg (fun q => L q) (pst3); let pst5 : q_x = x := congrArg (fun q => L q) (pst4); let pst6 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst5); let pst7 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst5); let pst8 : (p q_x q_x) = (p x x) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_x) q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst10 : q_v1 = v1 := congrArg (fun q => R q) (pst3); let pst11 : (p (p x x) q_v1) = (p (p x x) v1) := congrArg (fun q => p (p x x) q) (pst10); let pst12 : (p (p q_x q_x) q_v1) = (p (p x x) v1) := Eq.trans (pst9) (pst11); let pst13 : v0 = (p (p x x) v1) := Eq.trans (peq1) (pst12); let pst14 : (p (p x x) v1) = v0 := Eq.symm (pst13); let pst15 : (p (p x x) v1) = (p (p (p u0s1out u0_v0) (p (p u0_x u0_x) u0_v1)) u0_v0) := Eq.trans (pst14) (peq5); let pst16 : (p x x) = (p (p u0s1out u0_v0) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => L q) (pst15); let pst17 : x = (p u0s1out u0_v0) := congrArg (fun q => L q) (pst16); let pst18 : (p u0s1out u0_v0) = x := Eq.symm (pst17); let pst19 : x = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => R q) (pst16); let pst20 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst18) (pst19); let pst21 : u0s1out = (p u0_x u0_x) := congrArg (fun q => L q) (pst20); let pst22 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst23 : u0_v0 = u0_v1 := congrArg (fun q => R q) (pst20); let pst24 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst25 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst22) (pst24); let pst26 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst25); let pst27 : (p x x) = (p (p (p u0_x u0_x) u0_v1) x) := congrArg (fun q => p q x) (pst26); let pst28 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst29 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst30 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst28) (pst29); let pst31 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst30); let pst32 : (p (p (p u0_x u0_x) u0_v1) x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => p (p (p u0_x u0_x) u0_v1) q) (pst31); let pst33 : (p x x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := Eq.trans (pst27) (pst32); let pst34 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) := congrArg (fun q => p q v1) (pst33); let pst35 : v1 = u0_v0 := congrArg (fun q => R q) (pst15); let pst36 : v1 = u0_v1 := Eq.trans (pst35) (pst23); let pst37 : (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := congrArg (fun q => p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) q) (pst36); let pst38 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst34) (pst37); let pst39 : q_v0 = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst0) (pst38); let pst40 : (p q_v0 (p q_v1 q_v2)) = (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p q_v1 q_v2)) := congrArg (fun q => p q (p q_v1 q_v2)) (pst39); let pst41 : q_v1 = u0_v1 := Eq.trans (pst10) (pst36); let pst42 : (p q_v1 q_v2) = (p u0_v1 q_v2) := congrArg (fun q => p q q_v2) (pst41); let pst43 : (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p q_v1 q_v2)) = (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) := congrArg (fun q => p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) q) (pst42); let pst44 : (p q_v0 (p q_v1 q_v2)) = (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) := Eq.trans (pst40) (pst43); let pst45 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) q_v0) := congrArg (fun q => p q q_v0) (pst44); let pst46 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst47 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst48 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst46) (pst47); let pst49 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst48); let pst50 : (p x x) = (p (p (p u0_x u0_x) u0_v1) x) := congrArg (fun q => p q x) (pst49); let pst51 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v0) := congrArg (fun q => p q u0_v0) (pst21); let pst52 : (p (p u0_x u0_x) u0_v0) = (p (p u0_x u0_x) u0_v1) := congrArg (fun q => p (p u0_x u0_x) q) (pst23); let pst53 : (p u0s1out u0_v0) = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst51) (pst52); let pst54 : x = (p (p u0_x u0_x) u0_v1) := Eq.trans (pst17) (pst53); let pst55 : (p (p (p u0_x u0_x) u0_v1) x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := congrArg (fun q => p (p (p u0_x u0_x) u0_v1) q) (pst54); let pst56 : (p x x) = (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) := Eq.trans (pst50) (pst55); let pst57 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) := congrArg (fun q => p q v1) (pst56); let pst58 : (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := congrArg (fun q => p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) q) (pst36); let pst59 : (p (p x x) v1) = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst57) (pst58); let pst60 : q_v0 = (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) := Eq.trans (pst0) (pst59); let pst61 : (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := congrArg (fun q => p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) q) (pst60); let pst62 : (p (p q_v0 (p q_v1 q_v2)) q_v0) = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Eq.trans (pst45) (pst61); let pst63 : H1 = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Eq.trans (peq0) (pst62); let pst64 : (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) = H1 := Eq.symm (pst63); let pst65 : (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) = u0_x := Eq.trans (pst64) (peq7); let pst66 : u0_x = (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Eq.symm (pst65); pst66)
            have hlt : sz u0_x < sz (p (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) u0_v1)) (sz_lt_p_left (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1))) (sz_lt_p_left (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1)) (sz_lt_p_left (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2))) (sz_lt_p_left (p (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1) (p u0_v1 q_v2)) (p (p (p (p u0_x u0_x) u0_v1) (p (p u0_x u0_x) u0_v1)) u0_v1))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = (p (p q_x q_x) q_v1) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v1) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v0 = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB s1B qs0B qs1B z0 z1 z2 z3 z4
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
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p (p q_v0 q_H0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = (p (p q_x q_x) q_v1) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v1) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v0 = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB s1B qs0B qs1B z0 z1 z2 z3 z4
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = (p (p q_x q_x) q_v1) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change (p (p x x) v1) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v0 = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2 z3 z4
        omega
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval (eval (eval (eval v0 (eval v1 v2)) v0) (eval (eval x x) v1)) v0) v0) := by
  let H0 := eval v1 v2
  have e0a : v1 = v1 := by
    change v1 = v1
    rfl
  have e0b : v2 = v2 := by
    change v2 = v2
    rfl
  have s0 : Step v1 v2 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v1 v2
  let H1 := eval v0 (eval v1 v2)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval v1 v2) = H0 := by
    change H0 = H0
    rfl
  have s1 : Step v0 H0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval v1 v2)
  change x = (eval (eval (eval (eval H1 v0) (eval (eval x x) v1)) v0) v0)
  have rawEq : (eval (eval (eval (eval H1 v0) (eval (eval x x) v1)) v0) v0) = (eval (p (p (p H1 v0) (p (p x x) v1)) v0) v0) := by
    calc
      (eval (eval (eval (eval H1 v0) (eval (eval x x) v1)) v0) v0) = (eval (eval (eval (p H1 v0) (eval (eval x x) v1)) v0) v0) := congrArg (fun q => (eval (eval (eval q (eval (eval x x) v1)) v0) v0)) (eval_raw (nr0 x v0 v1 v2 H1 s1))
      _ = (eval (eval (eval (p H1 v0) (eval (p x x) v1)) v0) v0) := congrArg (fun q => (eval (eval (eval (p H1 v0) (eval q v1)) v0) v0)) (eval_raw (nr1 x v0 v1 v2))
      _ = (eval (eval (eval (p H1 v0) (p (p x x) v1)) v0) v0) := congrArg (fun q => (eval (eval (eval (p H1 v0) q) v0) v0)) (eval_raw (nr2 x v0 v1 v2))
      _ = (eval (eval (p (p H1 v0) (p (p x x) v1)) v0) v0) := congrArg (fun q => (eval (eval q v0) v0)) (eval_raw (nr3 x v0 v1 v2 H1 s1))
      _ = (eval (p (p (p H1 v0) (p (p x x) v1)) v0) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr4 x v0 v1 v2 H1 s1))
  exact (eval_hit (Code.law x v0 v1 v2 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1 v2
    exact CM.source_holds x v0 v1 v2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
