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
      (s1 : Step v0 H0 H1) :
      Code (p H1 (p (p v0 v0) x)) (p v0 v0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ a = (p q_H1 (p (p q_v0 q_v0) q_x)) ∧ b = (p q_v0 q_v0) ∧ o = q_x := by
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
      change v = (p q_v0 (p q_v0 q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p (p q_v0 q_v0) q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p q_v0 q_v1) := (let peq0 : v = (p q_v0 (p q_v0 q_v1)) := e0; let peq2 : v = (p q_v0 q_v0) := e2; let pst0 : (p q_v0 (p q_v0 q_v1)) = v := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v0 q_v1)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : (p q_v0 q_v1) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p q_v0 q_v1) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_v1) := sz_lt_p_left q_v0 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := congrArg (fun q => (L q)) (ha)
      change v = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change k = (p (p q_v0 q_v0) q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v = (p q_v0 q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := congrArg (fun q => (L q)) (ha)
      change v = (p q_v0 q_H0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change k = (p (p q_v0 q_v0) q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v = (p q_v0 q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs0B qs1B z0 z1 z2 z3
      omega
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := congrArg (fun q => (L q)) (ha)
      change v = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change k = (p (p q_v0 q_v0) q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v = (p q_v0 q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
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
      change v0 = (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p q_v0 (p q_v0 q_v1)) := (let peq0 : v0 = (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 (p q_v0 q_v1)) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 (p q_v0 q_v1)) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 (p q_v0 q_v1)) := sz_lt_p_left q_v0 (p q_v0 q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p q_H1 (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v0) q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p (p q_v0 q_v0) q_x) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p q_v0 q_H0) := (let peq0 : v0 = (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_H0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_H0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_H0) := sz_lt_p_left q_v0 q_H0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p q_H1 (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v0) q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p (p q_v0 q_v0) q_x) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p v0 v0) x o := by
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
      change v0 = (p q_v0 (p q_v0 q_v1)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p (p q_v0 q_v0) q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change x = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p q_v0 (p q_v0 q_v1)) := e0; let peq1 : v0 = (p (p q_v0 q_v0) q_x) := e1; let pst0 : (p q_v0 (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v0 q_v1)) = (p (p q_v0 q_v0) q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := congrArg (fun q => (L q)) (ha)
      change v0 = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = (p (p q_v0 q_v0) q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change x = (p q_v0 q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p q_v0 q_H0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p (p q_v0 q_v0) q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change x = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq1 : v0 = (p (p q_v0 q_v0) q_x) := e1; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p (p q_v0 q_v0) q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := congrArg (fun q => (L q)) (ha)
      change v0 = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = (p (p q_v0 q_v0) q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change x = (p q_v0 q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code H1 (p (p v0 v0) x) o := by
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
        change v0 = (p q_v0 (p q_v0 q_v1)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H0 = (p (p q_v0 q_v0) q_x) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change (p v0 v0) = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) := (let peq0 : v0 = (p q_v0 (p q_v0 q_v1)) := e0; let peq2 : (p v0 v0) = q_v0 := e2; let pst0 : (p v0 v0) = (p (p q_v0 (p q_v0 q_v1)) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p q_v0 q_v1)) v0) = (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) := congrArg (fun q => p (p q_v0 (p q_v0 q_v1)) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) := Eq.trans (pst0) (pst1); let pst3 : (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 q_v1)) (sz_lt_p_left (p q_v0 (p q_v0 q_v1)) (p q_v0 (p q_v0 q_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change v0 = q_H1 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H0 = (p (p q_v0 q_v0) q_x) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L q)) (hb)
        change (p v0 v0) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R q)) (hb)
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
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p q_v0 q_H0) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H0 = (p (p q_v0 q_v0) q_x) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change (p v0 v0) = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 q_H0) (p q_v0 q_H0)) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq2 : (p v0 v0) = q_v0 := e2; let pst0 : (p v0 v0) = (p (p q_v0 q_H0) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 q_H0) v0) = (p (p q_v0 q_H0) (p q_v0 q_H0)) := congrArg (fun q => p (p q_v0 q_H0) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 q_H0) (p q_v0 q_H0)) := Eq.trans (pst0) (pst1); let pst3 : (p (p q_v0 q_H0) (p q_v0 q_H0)) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p (p q_v0 q_H0) (p q_v0 q_H0)) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p (p q_v0 q_H0) (p q_v0 q_H0)) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p (p q_v0 q_H0) (p q_v0 q_H0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p q_v0 q_H0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
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
            have cyc : u0_v0 = (p u0_v0 u0_v0) := (let peq0 : v0 = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : (p v0 v0) = q_v0 := congrArg (fun q => (L q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_v0 u0_v1)) (p (p u0_v0 u0_v0) u0_x)) := u0a; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst5); let pst7 : (p q_H1 q_H1) = (p (p u0_v0 (p u0_v0 u0_v1)) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst6) (peq5); let pst8 : q_H1 = (p u0_v0 (p u0_v0 u0_v1)) := congrArg (fun q => L q) (pst7); let pst9 : (p u0_v0 (p u0_v0 u0_v1)) = q_H1 := Eq.symm (pst8); let pst10 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : (p u0_v0 (p u0_v0 u0_v1)) = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst9) (pst10); let pst12 : u0_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst11); pst12)
            have hlt : sz u0_v0 < sz (p u0_v0 u0_v0) := sz_lt_p_left u0_v0 u0_v0
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have u0s1hB := code_bounds u0s1h
            have s1B := s1B
            have qs0B := qs0B
            have qs1B := qs1B
            have u0s0B := u0s0B
            have u0s1B := u0s1B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = q_H1 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p (p q_v0 q_v0) q_x) at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L q)) (hb)
            change (p v0 v0) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R q)) (hb)
            change x = q_v0 at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have p5 := u0a
            change q_v0 = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) at p5
            have z5 := congrArg sz p5
            have p6 := u0b
            change q_v1 = (p u0_v0 u0_v0) at p6
            have z6 := congrArg sz p6
            have p7 := u0o
            change q_H0 = u0_x at p7
            have z7 := congrArg sz p7
            simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB u0s1hB s1B qs0B qs1B u0s0B u0s1B z0 z1 z2 z3 z4 z5 z6 z7
            omega
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p u0_v0 u0_v0) := (let peq0 : v0 = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : (p v0 v0) = q_v0 := congrArg (fun q => (L q)) (hb); let peq5 : q_v0 = (p (p u0_v0 u0s0out) (p (p u0_v0 u0_v0) u0_x)) := u0a; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst5); let pst7 : (p q_H1 q_H1) = (p (p u0_v0 u0s0out) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst6) (peq5); let pst8 : q_H1 = (p u0_v0 u0s0out) := congrArg (fun q => L q) (pst7); let pst9 : (p u0_v0 u0s0out) = q_H1 := Eq.symm (pst8); let pst10 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : (p u0_v0 u0s0out) = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst9) (pst10); let pst12 : u0_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst11); pst12)
            have hlt : sz u0_v0 < sz (p u0_v0 u0_v0) := sz_lt_p_left u0_v0 u0_v0
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0B := step_bound u1s0
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u0_v0 = (p u0_v0 u0_v0) := (let peq0 : v0 = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : (p v0 v0) = q_v0 := congrArg (fun q => (L q)) (hb); let peq5 : q_v0 = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := u0a; let peq8 : q_v0 = (p (p u1_v0 (p u1_v0 u1_v1)) (p (p u1_v0 u1_v0) u1_x)) := u1a; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst5); let pst7 : (p q_H1 q_H1) = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst6) (peq5); let pst8 : q_H1 = u0s1out := congrArg (fun q => L q) (pst7); let pst9 : u0s1out = q_H1 := Eq.symm (pst8); let pst10 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0s1out = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst9) (pst10); let pst12 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst13 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) q_H1) := congrArg (fun q => p q q_H1) (pst12); let pst14 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p u0_v0 u0_v0) u0_x) q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := congrArg (fun q => p (p (p u0_v0 u0_v0) u0_x) q) (pst14); let pst16 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst13) (pst15); let pst17 : q_v0 = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst5) (pst16); let pst18 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = q_v0 := Eq.symm (pst17); let pst19 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = (p (p u1_v0 (p u1_v0 u1_v1)) (p (p u1_v0 u1_v0) u1_x)) := Eq.trans (pst18) (peq8); let pst20 : (p (p u0_v0 u0_v0) u0_x) = (p u1_v0 (p u1_v0 u1_v1)) := congrArg (fun q => L q) (pst19); let pst21 : u0_x = (p u1_v0 u1_v1) := congrArg (fun q => R q) (pst20); let pst22 : (p u0_v0 u0_v0) = u1_v0 := congrArg (fun q => L q) (pst20); let pst23 : u1_v0 = (p u0_v0 u0_v0) := Eq.symm (pst22); let pst24 : (p u1_v0 u1_v1) = (p (p u0_v0 u0_v0) u1_v1) := congrArg (fun q => p q u1_v1) (pst23); let pst25 : u0_x = (p (p u0_v0 u0_v0) u1_v1) := Eq.trans (pst21) (pst24); let pst26 : (p (p u0_v0 u0_v0) u0_x) = (p (p u0_v0 u0_v0) (p (p u0_v0 u0_v0) u1_v1)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst25); let pst27 : (p (p u0_v0 u0_v0) (p (p u0_v0 u0_v0) u1_v1)) = (p (p u0_v0 u0_v0) u0_x) := Eq.symm (pst26); let pst28 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) u1_x) := congrArg (fun q => R q) (pst19); let pst29 : (p (p u0_v0 u0_v0) (p (p u0_v0 u0_v0) u1_v1)) = (p (p u1_v0 u1_v0) u1_x) := Eq.trans (pst27) (pst28); let pst30 : (p u1_v0 u1_v0) = (p (p u0_v0 u0_v0) u1_v0) := congrArg (fun q => p q u1_v0) (pst23); let pst31 : (p (p u0_v0 u0_v0) u1_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst23); let pst32 : (p u1_v0 u1_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := Eq.trans (pst30) (pst31); let pst33 : (p (p u1_v0 u1_v0) u1_x) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) u1_x) := congrArg (fun q => p q u1_x) (pst32); let pst34 : (p (p u0_v0 u0_v0) (p (p u0_v0 u0_v0) u1_v1)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) u1_x) := Eq.trans (pst29) (pst33); let pst35 : (p u0_v0 u0_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => L q) (pst34); let pst36 : u0_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst35); pst36)
                have hlt : sz u0_v0 < sz (p u0_v0 u0_v0) := sz_lt_p_left u0_v0 u0_v0
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p u1_v0 u1_v0) := (let peq0 : v0 = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : (p v0 v0) = q_v0 := congrArg (fun q => (L q)) (hb); let peq5 : q_v0 = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := u0a; let peq7 : q_H0 = u0_x := u0o; let peq8 : q_v0 = (p u1s1out (p (p u1_v0 u1_v0) u1_x)) := u1a; let peq9 : q_H0 = (p u1_v0 u1_v0) := u1b; let peq10 : q_H1 = u1_x := u1o; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst5); let pst7 : (p q_H1 q_H1) = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst6) (peq5); let pst8 : q_H1 = u0s1out := congrArg (fun q => L q) (pst7); let pst9 : u0s1out = q_H1 := Eq.symm (pst8); let pst10 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0s1out = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst9) (pst10); let pst12 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst13 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) q_H1) := congrArg (fun q => p q q_H1) (pst12); let pst14 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p u0_v0 u0_v0) u0_x) q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := congrArg (fun q => p (p (p u0_v0 u0_v0) u0_x) q) (pst14); let pst16 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst13) (pst15); let pst17 : q_v0 = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst5) (pst16); let pst18 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = q_v0 := Eq.symm (pst17); let pst19 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = (p u1s1out (p (p u1_v0 u1_v0) u1_x)) := Eq.trans (pst18) (peq8); let pst20 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) u1_x) := congrArg (fun q => R q) (pst19); let pst21 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => L q) (pst20); let pst22 : u0_v0 = u1_v0 := congrArg (fun q => L q) (pst21); let pst23 : (p u0_v0 u0_v0) = (p u1_v0 u0_v0) := congrArg (fun q => p q u0_v0) (pst22); let pst24 : (p u1_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (pst22); let pst25 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := Eq.trans (pst23) (pst24); let pst26 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) u0_x) := congrArg (fun q => p q u0_x) (pst25); let pst27 : u0_x = u1_x := congrArg (fun q => R q) (pst20); let pst28 : q_H0 = u1_x := Eq.trans (peq7) (pst27); let pst29 : u1_x = q_H0 := Eq.symm (pst28); let pst30 : u1_x = (p u1_v0 u1_v0) := Eq.trans (pst29) (peq9); let pst31 : u0_x = (p u1_v0 u1_v0) := Eq.trans (pst27) (pst30); let pst32 : (p (p u1_v0 u1_v0) u0_x) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst31); let pst33 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst26) (pst32); let pst34 : u0s1out = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst11) (pst33); let pst35 : q_H1 = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst8) (pst34); let pst36 : (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) = q_H1 := Eq.symm (pst35); let pst37 : (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) = u1_x := Eq.trans (pst36) (peq10); let pst38 : (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) = (p u1_v0 u1_v0) := Eq.trans (pst37) (pst30); let pst39 : (p u1_v0 u1_v0) = u1_v0 := congrArg (fun q => L q) (pst38); let pst40 : u1_v0 = (p u1_v0 u1_v0) := Eq.symm (pst39); pst40)
                have hlt : sz u1_v0 < sz (p u1_v0 u1_v0) := sz_lt_p_left u1_v0 u1_v0
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1B := step_bound u1s1
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u0_v0 = (p u0_v0 u0_v0) := (let peq0 : v0 = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : (p v0 v0) = q_v0 := congrArg (fun q => (L q)) (hb); let peq5 : q_v0 = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := u0a; let peq8 : q_v0 = (p (p u1_v0 u1s0out) (p (p u1_v0 u1_v0) u1_x)) := u1a; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst5); let pst7 : (p q_H1 q_H1) = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst6) (peq5); let pst8 : q_H1 = u0s1out := congrArg (fun q => L q) (pst7); let pst9 : u0s1out = q_H1 := Eq.symm (pst8); let pst10 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0s1out = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst9) (pst10); let pst12 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst13 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) q_H1) := congrArg (fun q => p q q_H1) (pst12); let pst14 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p u0_v0 u0_v0) u0_x) q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := congrArg (fun q => p (p (p u0_v0 u0_v0) u0_x) q) (pst14); let pst16 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst13) (pst15); let pst17 : q_v0 = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst5) (pst16); let pst18 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = q_v0 := Eq.symm (pst17); let pst19 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = (p (p u1_v0 u1s0out) (p (p u1_v0 u1_v0) u1_x)) := Eq.trans (pst18) (peq8); let pst20 : (p (p u0_v0 u0_v0) u0_x) = (p u1_v0 u1s0out) := congrArg (fun q => L q) (pst19); let pst21 : u0_x = u1s0out := congrArg (fun q => R q) (pst20); let pst22 : (p (p u0_v0 u0_v0) u0_x) = (p (p u0_v0 u0_v0) u1s0out) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst21); let pst23 : (p (p u0_v0 u0_v0) u1s0out) = (p (p u0_v0 u0_v0) u0_x) := Eq.symm (pst22); let pst24 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) u1_x) := congrArg (fun q => R q) (pst19); let pst25 : (p (p u0_v0 u0_v0) u1s0out) = (p (p u1_v0 u1_v0) u1_x) := Eq.trans (pst23) (pst24); let pst26 : (p u0_v0 u0_v0) = u1_v0 := congrArg (fun q => L q) (pst20); let pst27 : u1_v0 = (p u0_v0 u0_v0) := Eq.symm (pst26); let pst28 : (p u1_v0 u1_v0) = (p (p u0_v0 u0_v0) u1_v0) := congrArg (fun q => p q u1_v0) (pst27); let pst29 : (p (p u0_v0 u0_v0) u1_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst27); let pst30 : (p u1_v0 u1_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := Eq.trans (pst28) (pst29); let pst31 : (p (p u1_v0 u1_v0) u1_x) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) u1_x) := congrArg (fun q => p q u1_x) (pst30); let pst32 : (p (p u0_v0 u0_v0) u1s0out) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) u1_x) := Eq.trans (pst25) (pst31); let pst33 : (p u0_v0 u0_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => L q) (pst32); let pst34 : u0_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst33); pst34)
                have hlt : sz u0_v0 < sz (p u0_v0 u0_v0) := sz_lt_p_left u0_v0 u0_v0
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p u1_v0 u1_v0) := (let peq0 : v0 = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : (p v0 v0) = q_v0 := congrArg (fun q => (L q)) (hb); let peq5 : q_v0 = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := u0a; let peq7 : q_H0 = u0_x := u0o; let peq8 : q_v0 = (p u1s1out (p (p u1_v0 u1_v0) u1_x)) := u1a; let peq9 : q_H0 = (p u1_v0 u1_v0) := u1b; let peq10 : q_H1 = u1_x := u1o; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst5); let pst7 : (p q_H1 q_H1) = (p u0s1out (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst6) (peq5); let pst8 : q_H1 = u0s1out := congrArg (fun q => L q) (pst7); let pst9 : u0s1out = q_H1 := Eq.symm (pst8); let pst10 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0s1out = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst9) (pst10); let pst12 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst13 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) q_H1) := congrArg (fun q => p q q_H1) (pst12); let pst14 : q_H1 = (p (p u0_v0 u0_v0) u0_x) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p u0_v0 u0_v0) u0_x) q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := congrArg (fun q => p (p (p u0_v0 u0_v0) u0_x) q) (pst14); let pst16 : (p q_H1 q_H1) = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst13) (pst15); let pst17 : q_v0 = (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) := Eq.trans (pst5) (pst16); let pst18 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = q_v0 := Eq.symm (pst17); let pst19 : (p (p (p u0_v0 u0_v0) u0_x) (p (p u0_v0 u0_v0) u0_x)) = (p u1s1out (p (p u1_v0 u1_v0) u1_x)) := Eq.trans (pst18) (peq8); let pst20 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) u1_x) := congrArg (fun q => R q) (pst19); let pst21 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => L q) (pst20); let pst22 : u0_v0 = u1_v0 := congrArg (fun q => L q) (pst21); let pst23 : (p u0_v0 u0_v0) = (p u1_v0 u0_v0) := congrArg (fun q => p q u0_v0) (pst22); let pst24 : (p u1_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (pst22); let pst25 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := Eq.trans (pst23) (pst24); let pst26 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) u0_x) := congrArg (fun q => p q u0_x) (pst25); let pst27 : u0_x = u1_x := congrArg (fun q => R q) (pst20); let pst28 : q_H0 = u1_x := Eq.trans (peq7) (pst27); let pst29 : u1_x = q_H0 := Eq.symm (pst28); let pst30 : u1_x = (p u1_v0 u1_v0) := Eq.trans (pst29) (peq9); let pst31 : u0_x = (p u1_v0 u1_v0) := Eq.trans (pst27) (pst30); let pst32 : (p (p u1_v0 u1_v0) u0_x) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst31); let pst33 : (p (p u0_v0 u0_v0) u0_x) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst26) (pst32); let pst34 : u0s1out = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst11) (pst33); let pst35 : q_H1 = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst8) (pst34); let pst36 : (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) = q_H1 := Eq.symm (pst35); let pst37 : (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) = u1_x := Eq.trans (pst36) (peq10); let pst38 : (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) = (p u1_v0 u1_v0) := Eq.trans (pst37) (pst30); let pst39 : (p u1_v0 u1_v0) = u1_v0 := congrArg (fun q => L q) (pst38); let pst40 : u1_v0 = (p u1_v0 u1_v0) := Eq.symm (pst39); pst40)
                have hlt : sz u1_v0 < sz (p u1_v0 u1_v0) := sz_lt_p_left u1_v0 u1_v0
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
        change H1 = (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p v0 v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
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
        have p0 := ha
        change H1 = (p q_H1 (p (p q_v0 q_v0) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p v0 v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
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
        have p0 := ha
        change H1 = (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p v0 v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
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
        have p0 := ha
        change H1 = (p q_H1 (p (p q_v0 q_v0) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p v0 v0) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change x = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
theorem nr3 (x v0 v1 : CM)
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
      change v0 = (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p q_v0 (p q_v0 q_v1)) := (let peq0 : v0 = (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v0 q_v1)) (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 (p q_v0 q_v1)) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 (p q_v0 q_v1)) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 (p q_v0 q_v1)) := sz_lt_p_left q_v0 (p q_v0 q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p q_H1 (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v0) q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p (p q_v0 q_v0) q_x) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p q_v0 q_H0) := (let peq0 : v0 = (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_H0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_H0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_H0) := sz_lt_p_left q_v0 q_H0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 q_v0) at e1
      have cyc : q_v0 = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p q_H1 (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = (p q_v0 q_v0) := e1; let pst0 : (p q_H1 (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 (p (p q_v0 q_v0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v0) q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p (p q_v0 q_v0) q_x) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 (eval v0 v1)) (eval (eval v0 v0) x)) (eval v0 v0)) := by
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
  change x = (eval (eval H1 (eval (eval v0 v0) x)) (eval v0 v0))
  have rawEq : (eval (eval H1 (eval (eval v0 v0) x)) (eval v0 v0)) = (eval (p H1 (p (p v0 v0) x)) (p v0 v0)) := by
    calc
      (eval (eval H1 (eval (eval v0 v0) x)) (eval v0 v0)) = (eval (eval H1 (eval (p v0 v0) x)) (eval v0 v0)) := congrArg (fun q => (eval (eval H1 (eval q x)) (eval v0 v0))) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval H1 (p (p v0 v0) x)) (eval v0 v0)) := congrArg (fun q => (eval (eval H1 q) (eval v0 v0))) (eval_raw (nr1 x v0 v1))
      _ = (eval (p H1 (p (p v0 v0) x)) (eval v0 v0)) := congrArg (fun q => (eval q (eval v0 v0))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval (p H1 (p (p v0 v0) x)) (p v0 v0)) := congrArg (fun q => (eval (p H1 (p (p v0 v0) x)) q)) (eval_raw (nr3 x v0 v1))
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
