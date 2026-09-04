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
      (s0 : Step v0 v1 H0)
      (s1 : Step v0 v1 H1) :
      Code (p v0 (p (p (p v0 v0) H0) (p x x))) H1 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_v0 q_v1 q_H1 ∧ a = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) ∧ b = q_H1 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R (R a)))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
def CodeArg :=
  PSigma fun a : CM => PSigma fun b : CM => PSigma fun o : CM => Code a b o
theorem code_bounds_core (q : CodeArg) : sz q.2.1 < sz q.1 ∧ sz q.2.2.1 < sz q.1 := by
  rcases q with ⟨a, b, o, h⟩
  rcases code_shape h with ⟨x, v0, v1, H0, H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst x
  cases s0 with
  | raw =>
    cases s1 with
    | raw =>
      simp only [getOut, L, R, U, sz] <;> omega
    | hit s1h =>
      have s1hB := code_bounds_core ⟨_, _, _, s1h⟩
      simp only [getOut, L, R, U, sz] at s1hB ⊢ <;> omega
  | hit s0h =>
    have s0hB := code_bounds_core ⟨_, _, _, s0h⟩
    cases s1 with
    | raw =>
      simp only [getOut, L, R, U, sz] at s0hB ⊢ <;> omega
    | hit s1h =>
      have s1hB := code_bounds_core ⟨_, _, _, s1h⟩
      simp only [getOut, L, R, U, sz] at s0hB s1hB ⊢ <;> omega
termination_by sz q.1
decreasing_by
  all_goals try subst a
  all_goals try subst b
  all_goals try subst o
  all_goals simp_all [sz] <;> omega
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a :=
  code_bounds_core ⟨a, b, o, h⟩
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
    have he : q_H1 = q_v0 := (let peq0 : v = q_v0 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_H1 := hb; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq2); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
    exact step_ne_first (by simpa only [he] using qs1)
  | hit qs0h =>
    have he : q_H1 = q_v0 := (let peq0 : v = q_v0 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_H1 := hb; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq2); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
    exact step_ne_first (by simpa only [he] using qs1)
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
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v1) at e1
      have cyc : q_v1 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) := e0; let peq1 : v0 = (p q_v0 q_v1) := e1; let pst0 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) = (p q_v0 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : q_v1 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_right (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_H1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) < sz (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) := hx
      exact (Nat.lt_irrefl _ selflt).elim
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = (p q_v0 q_v1) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) < sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) := hx
      exact (Nat.lt_irrefl _ selflt).elim
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_H1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) < sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) := hx
      exact (Nat.lt_irrefl _ selflt).elim
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p v0 v0) H0 o := by
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
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v1 = q_v1 at e3
        have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => q) hb
        change (p v0 v1) = q_H1 at e2
        have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v1 = q_v1 at e3
        have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => q) hb
        change (p v0 v1) = q_H1 at e2
        have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))
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
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => q) hb
        change H0 = (p q_v0 q_v1) at e2
        have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => q) hb
        change H0 = q_H1 at e2
        have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => q) hb
        change H0 = (p q_v0 q_v1) at e2
        have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at e1
        have e2 := congrArg (fun q => q) hb
        change H0 = q_H1 at e2
        have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Eq.trans (pst0) (peq1); pst1)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
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
      change x = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 q_v1) at e1
      have cyc : q_v1 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : x = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) := e0; let peq1 : x = (p q_v0 q_v1) := e1; let pst0 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) = (p q_v0 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : q_v1 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_right (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change x = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change x = q_H1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) < sz (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) := hx
      exact (Nat.lt_irrefl _ selflt).elim
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change x = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change x = (p q_v0 q_v1) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) < sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) := hx
      exact (Nat.lt_irrefl _ selflt).elim
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change x = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change x = q_H1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) < sz (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) := hx
      exact (Nat.lt_irrefl _ selflt).elim
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p v0 v0) H0) (p x x) o := by
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
        have e0 := congrArg (fun q => (L q)) ha
        change (p v0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L (R q))) ha
        change v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) at e1
        have e2 := congrArg (fun q => (R (R q))) ha
        change v1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e3
        have e4 := congrArg (fun q => (R q)) hb
        change x = q_v1 at e4
        have cyc : v0 = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) := e1; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst3); let pst5 : (p q_v0 q_v1) = (p (p v0 v0) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst6 : (p (p (p v0 v0) (p v0 v0)) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (pst5); let pst7 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Eq.trans (pst4) (pst6); let pst8 : v0 = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Eq.trans (peq1) (pst7); pst8)
        have hlt : sz v0 < sz (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change (p v0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L (R q))) ha
        change v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) at e1
        have e2 := congrArg (fun q => (R (R q))) ha
        change v1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change (p x x) = q_H1 at e3
        have cyc : v0 = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) := e1; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst3); let pst5 : (p q_v0 q_v1) = (p (p v0 v0) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst6 : (p (p (p v0 v0) (p v0 v0)) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (pst5); let pst7 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Eq.trans (pst4) (pst6); let pst8 : v0 = (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Eq.trans (peq1) (pst7); pst8)
        have hlt : sz v0 < sz (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change (p v0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L (R q))) ha
        change v0 = (p (p q_v0 q_v0) q_H0) at e1
        have e2 := congrArg (fun q => (R (R q))) ha
        change v1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e3
        have e4 := congrArg (fun q => (R q)) hb
        change x = q_v1 at e4
        have cyc : v0 = (p (p (p v0 v0) (p v0 v0)) q_H0) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : v0 = (p (p q_v0 q_v0) q_H0) := e1; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) q_H0) = (p (p (p v0 v0) (p v0 v0)) q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst5 : v0 = (p (p (p v0 v0) (p v0 v0)) q_H0) := Eq.trans (peq1) (pst4); pst5)
        have hlt : sz v0 < sz (p (p (p v0 v0) (p v0 v0)) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) q_H0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change (p v0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L (R q))) ha
        change v0 = (p (p q_v0 q_v0) q_H0) at e1
        have e2 := congrArg (fun q => (R (R q))) ha
        change v1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change (p x x) = q_H1 at e3
        have cyc : v0 = (p (p (p v0 v0) (p v0 v0)) q_H0) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : v0 = (p (p q_v0 q_v0) q_H0) := e1; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) q_H0) = (p (p (p v0 v0) (p v0 v0)) q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst5 : v0 = (p (p (p v0 v0) (p v0 v0)) q_H0) := Eq.trans (peq1) (pst4); pst5)
        have hlt : sz v0 < sz (p (p (p v0 v0) (p v0 v0)) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) q_H0)
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
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L q)) (hb)
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R q)) (hb)
        change x = q_v1 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz v0 < sz H0 := by
          have structural : sz v0 < sz (p (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) (p v0 v0))) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) (p (p v0 v0) (p v0 v0)))) (sz_lt_p_left (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) (p v0 v0))) (p q_x q_x))
          have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
          have small_eq : sz H0 = sz (p (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) (p v0 v0))) (p q_x q_x)) := congrArg sz (Eq.trans (p1) (congrArg (fun q => p q (p q_x q_x)) (Eq.trans (congrArg (fun q => p q (p q_v0 q_v1)) (Eq.trans (congrArg (fun q => p q q_v0) (p0.symm)) (congrArg (fun q => p (p v0 v0) q) (p0.symm)))) (congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (Eq.trans (congrArg (fun q => p q q_v1) (p0.symm)) (congrArg (fun q => p (p v0 v0) q) (Eq.trans (p3.symm) (Eq.trans (p2) (p0.symm)))))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change (p x x) = q_H1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H0 := by
          have structural : sz v0 < sz (p (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1))) (sz_lt_p_left (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) (p q_x q_x))
          have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
          have small_eq : sz H0 = sz (p (p (p (p v0 v0) (p v0 v0)) (p (p v0 v0) q_v1)) (p q_x q_x)) := congrArg sz (Eq.trans (p1) (congrArg (fun q => p q (p q_x q_x)) (Eq.trans (congrArg (fun q => p q (p q_v0 q_v1)) (Eq.trans (congrArg (fun q => p q q_v0) (p0.symm)) (congrArg (fun q => p (p v0 v0) q) (p0.symm)))) (congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (congrArg (fun q => p q q_v1) (p0.symm))))))
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
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L q)) (hb)
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R q)) (hb)
        change x = q_v1 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have hx := qs0hB.1
        rw [Eq.trans (p3.symm) (Eq.trans (p2) (p0.symm)), p0.symm] at hx
        have selflt : sz (p v0 v0) < sz (p v0 v0) := hx
        exact (Nat.lt_irrefl _ selflt).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change (p x x) = q_H1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H0 := by
          have structural : sz v0 < sz (p (p (p (p v0 v0) (p v0 v0)) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) q_H0)) (sz_lt_p_left (p (p (p v0 v0) (p v0 v0)) q_H0) (p q_x q_x))
          have large_eq : sz v0 = sz v0 := congrArg sz (rfl)
          have small_eq : sz H0 = sz (p (p (p (p v0 v0) (p v0 v0)) q_H0) (p q_x q_x)) := congrArg sz (Eq.trans (p1) (congrArg (fun q => p q (p q_x q_x)) (congrArg (fun q => p q q_H0) (Eq.trans (congrArg (fun q => p q q_v0) (p0.symm)) (congrArg (fun q => p (p v0 v0) q) (p0.symm))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code v0 (p (p (p v0 v0) H0) (p x x)) o := by
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
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p (p v0 v0) (p v0 v1)) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change (p x x) = q_v1 at e2
        have cyc : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) := e0; let peq1 : (p (p v0 v0) (p v0 v1)) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p v0 v1)) := congrArg (fun q => p q (p v0 v1)) (pst2); let pst4 : (p v0 v1) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1) := congrArg (fun q => p q v1) (peq0); let pst5 : (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) := congrArg (fun q => p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) q) (pst4); let pst6 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) := Eq.trans (pst3) (pst5); let pst7 : (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) = (p (p v0 v0) (p v0 v1)) := Eq.symm (pst6); let pst8 : (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) = q_v0 := Eq.trans (pst7) (peq1); let pst9 : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) := Eq.symm (pst8); pst9)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p (p v0 v0) (p v0 v1)) (p x x)) = q_H1 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz q_v0 < sz q_H1 := by
          have structural : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) (p x x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1))) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) (p x x))
          have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
          have small_eq : sz q_H1 = sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v1)) (p x x)) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p q (p x x)) (Eq.trans (congrArg (fun q => p q (p v0 v1)) (Eq.trans (congrArg (fun q => p q v0) (p0)) (congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) q) (p0)))) (congrArg (fun q => p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) q) (congrArg (fun q => p q v1) (p0))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p (p v0 v0) (p v0 v1)) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change (p x x) = q_v1 at e2
        have cyc : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) := e0; let peq1 : (p (p v0 v0) (p v0 v1)) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p v0 v1)) := congrArg (fun q => p q (p v0 v1)) (pst2); let pst4 : (p v0 v1) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1) := congrArg (fun q => p q v1) (peq0); let pst5 : (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) := congrArg (fun q => p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) q) (pst4); let pst6 : (p (p v0 v0) (p v0 v1)) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) := Eq.trans (pst3) (pst5); let pst7 : (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) = (p (p v0 v0) (p v0 v1)) := Eq.symm (pst6); let pst8 : (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) = q_v0 := Eq.trans (pst7) (peq1); let pst9 : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) := Eq.symm (pst8); pst9)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p (p v0 v0) (p v0 v1)) (p x x)) = q_H1 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz q_v0 < sz q_H1 := by
          have structural : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) (p x x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1))) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) (p x x))
          have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
          have small_eq : sz q_H1 = sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v1)) (p x x)) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p q (p x x)) (Eq.trans (congrArg (fun q => p q (p v0 v1)) (Eq.trans (congrArg (fun q => p q v0) (p0)) (congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) q) (p0)))) (congrArg (fun q => p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) q) (congrArg (fun q => p q v1) (p0))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.2).elim
  | hit s0h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p (p v0 v0) H0) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change (p x x) = q_v1 at e2
        have cyc : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) := e0; let peq1 : (p (p v0 v0) H0) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) H0) = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) := congrArg (fun q => p q H0) (pst2); let pst4 : (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) = (p (p v0 v0) H0) := Eq.symm (pst3); let pst5 : (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) = q_v0 := Eq.trans (pst4) (peq1); let pst6 : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) := Eq.symm (pst5); pst6)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p (p v0 v0) H0) (p x x)) = q_H1 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz q_v0 < sz q_H1 := by
          have structural : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) (p x x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0)) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) (p x x))
          have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
          have small_eq : sz q_H1 = sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)))) H0) (p x x)) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p q (p x x)) (congrArg (fun q => p q H0) (Eq.trans (congrArg (fun q => p q v0) (p0)) (congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) q) (p0))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p (p v0 v0) H0) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change (p x x) = q_v1 at e2
        have cyc : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) := (let peq0 : v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) := e0; let peq1 : (p (p v0 v0) H0) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) := congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) H0) = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) := congrArg (fun q => p q H0) (pst2); let pst4 : (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) = (p (p v0 v0) H0) := Eq.symm (pst3); let pst5 : (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) = q_v0 := Eq.trans (pst4) (peq1); let pst6 : q_v0 = (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) := Eq.symm (pst5); pst6)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p (p (p v0 v0) H0) (p x x)) = q_H1 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz q_v0 < sz q_H1 := by
          have structural : sz q_v0 < sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) (p x x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))))) (sz_lt_p_left (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0)) (sz_lt_p_left (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) (p x x))
          have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
          have small_eq : sz q_H1 = sz (p (p (p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)))) H0) (p x x)) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p q (p x x)) (congrArg (fun q => p q H0) (Eq.trans (congrArg (fun q => p q v0) (p0)) (congrArg (fun q => p (p q_v0 (p (p (p q_v0 q_v0) q_H0) (p q_x q_x))) q) (p0))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.2).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 (eval (eval (eval v0 v0) (eval v0 v1)) (eval x x))) (eval v0 v1)) := by
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
  let H1 := eval v0 v1
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : v1 = v1 := by
    change v1 = v1
    rfl
  have s1 : Step v0 v1 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 v1
  change x = (eval (eval v0 (eval (eval (eval v0 v0) H0) (eval x x))) H1)
  have rawEq : (eval (eval v0 (eval (eval (eval v0 v0) H0) (eval x x))) H1) = (eval (p v0 (p (p (p v0 v0) H0) (p x x))) H1) := by
    calc
      (eval (eval v0 (eval (eval (eval v0 v0) H0) (eval x x))) H1) = (eval (eval v0 (eval (eval (p v0 v0) H0) (eval x x))) H1) := congrArg (fun q => (eval (eval v0 (eval (eval q H0) (eval x x))) H1)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval v0 (eval (p (p v0 v0) H0) (eval x x))) H1) := congrArg (fun q => (eval (eval v0 (eval q (eval x x))) H1)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval v0 (eval (p (p v0 v0) H0) (p x x))) H1) := congrArg (fun q => (eval (eval v0 (eval (p (p v0 v0) H0) q)) H1)) (eval_raw (nr2 x v0 v1))
      _ = (eval (eval v0 (p (p (p v0 v0) H0) (p x x))) H1) := congrArg (fun q => (eval (eval v0 q) H1)) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval (p v0 (p (p (p v0 v0) H0) (p x x))) H1) := congrArg (fun q => (eval q H1)) (eval_raw (nr4 x v0 v1 H0 s0))
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
