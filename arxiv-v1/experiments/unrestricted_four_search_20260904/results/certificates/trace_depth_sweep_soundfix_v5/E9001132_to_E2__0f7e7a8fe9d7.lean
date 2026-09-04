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
      (s0 : Step v1 v0 H0)
      (s1 : Step v0 H0 H1)
      (s2 : Step x v0 H2) :
      Code (p (p H1 (p H2 x)) (p v0 v0)) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 q_H2 : CM, Step q_v1 q_v0 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ Step q_x q_v0 q_H2 ∧ a = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 H2 s0 s1 s2 => ⟨x, v0, v1, H0, H1, H2, s0, s1, s2, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (R (L a)))
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
        change v = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) := (let peq0 : v = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) := (let peq0 : v = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p q_H1 (p (p q_x q_v0) q_x)) := (let peq0 : v = (p q_H1 (p (p q_x q_v0) q_x)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p q_H1 (p (p q_x q_v0) q_x)) = v := Eq.symm (peq0); let pst1 : (p q_H1 (p (p q_x q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 (p (p q_x q_v0) q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 (p (p q_x q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_right q_H1 (p (p q_x q_v0) q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have qs2hB := code_bounds qs2h
        have qs0B := qs0B
        have qs1B := qs1B
        have qs2B := qs2B
        have p0 := congrArg (fun q => (L q)) (ha)
        change v = (p q_H1 (p q_H2 q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change k = (p q_v0 q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB qs1hB qs2hB qs0B qs1B qs2B z0 z1 z2 z3
        omega
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) := (let peq0 : v = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p (p q_x q_v0) q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 q_H0) (p q_H2 q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_H0) (p q_H2 q_x)) := (let peq0 : v = (p (p q_v0 q_H0) (p q_H2 q_x)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) (p q_H2 q_x)) = v := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) (p q_H2 q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) (p q_H2 q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_H0) (p q_H2 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p q_H2 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change v = q_v0 at e2
        have cyc : q_v0 = (p q_H1 (p (p q_x q_v0) q_x)) := (let peq0 : v = (p q_H1 (p (p q_x q_v0) q_x)) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p q_H1 (p (p q_x q_v0) q_x)) = v := Eq.symm (peq0); let pst1 : (p q_H1 (p (p q_x q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_H1 (p (p q_x q_v0) q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_H1 (p (p q_x q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_right q_H1 (p (p q_x q_v0) q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have qs2hB := code_bounds qs2h
        have qs0B := qs0B
        have qs1B := qs1B
        have qs2B := qs2B
        have p0 := congrArg (fun q => (L q)) (ha)
        change v = (p q_H1 (p q_H2 q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change k = (p q_v0 q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs2hB qs0B qs1B qs2B z0 z1 z2 z3
        omega
theorem code_no_pair_right (v k : CM) :
    ¬ ∃ o, Code (p v k) k o := by
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
        change v = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 (p q_H2 q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p (p q_v0 q_H0) (p q_H2 q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 (p (p q_x q_v0) q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v = (p q_H1 (p q_H2 q_x)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change k = (p q_v0 q_v0) at e1
        have e2 := congrArg (fun q => q) hb
        change k = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : k = (p q_v0 q_v0) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p q_v0 q_v0) = k := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
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
theorem step_no_output {a b o : CM} (st : Step a b o) :
    ¬ ∃ k, Code (p o a) k b := by
  rintro ⟨k, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have stB := step_bound st
  have stN := step_no_first st
  cases st with
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
          change a = (p q_v0 (p q_v1 q_v0)) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change b = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => (R q)) ha
          change a = (p q_v0 q_v0) at e2
          have e3 := congrArg (fun q => q) hb
          change k = q_v0 at e3
          have cyc : q_v0 = (p q_v1 q_v0) := (let peq0 : a = (p q_v0 (p q_v1 q_v0)) := e0; let peq2 : a = (p q_v0 q_v0) := e2; let pst0 : (p q_v0 (p q_v1 q_v0)) = a := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 q_v0)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : (p q_v1 q_v0) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p q_v1 q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p q_v1 q_v0) := sz_lt_p_right q_v1 q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change a = (p q_v0 (p q_v1 q_v0)) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change b = (p q_H2 q_x) at e1
          have e2 := congrArg (fun q => (R q)) ha
          change a = (p q_v0 q_v0) at e2
          have e3 := congrArg (fun q => q) hb
          change k = q_v0 at e3
          have cyc : q_v0 = (p q_v1 q_v0) := (let peq0 : a = (p q_v0 (p q_v1 q_v0)) := e0; let peq2 : a = (p q_v0 q_v0) := e2; let pst0 : (p q_v0 (p q_v1 q_v0)) = a := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 q_v0)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : (p q_v1 q_v0) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p q_v1 q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p q_v1 q_v0) := sz_lt_p_right q_v1 q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have cyc : q_x = (p (p q_x q_v0) q_x) := (let peq1 : b = (p (p q_x q_v0) q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : b = q_x := ho; let pst0 : (p (p q_x q_v0) q_x) = b := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_x := Eq.trans (pst0) (peq4); let pst2 : q_x = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have cyc : q_x = (p q_H2 q_x) := (let peq1 : b = (p q_H2 q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : b = q_x := ho; let pst0 : (p q_H2 q_x) = b := Eq.symm (peq1); let pst1 : (p q_H2 q_x) = q_x := Eq.trans (pst0) (peq4); let pst2 : q_x = (p q_H2 q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p q_H2 q_x) := sz_lt_p_right q_H2 q_x
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
          have cyc : q_x = (p (p q_x q_v0) q_x) := (let peq1 : b = (p (p q_x q_v0) q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : b = q_x := ho; let pst0 : (p (p q_x q_v0) q_x) = b := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_x := Eq.trans (pst0) (peq4); let pst2 : q_x = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have cyc : q_x = (p q_H2 q_x) := (let peq1 : b = (p q_H2 q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : b = q_x := ho; let pst0 : (p q_H2 q_x) = b := Eq.symm (peq1); let pst1 : (p q_H2 q_x) = q_x := Eq.trans (pst0) (peq4); let pst2 : q_x = (p q_H2 q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p q_H2 q_x) := sz_lt_p_right q_H2 q_x
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have cyc : q_x = (p (p q_x q_v0) q_x) := (let peq1 : b = (p (p q_x q_v0) q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : b = q_x := ho; let pst0 : (p (p q_x q_v0) q_x) = b := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_x := Eq.trans (pst0) (peq4); let pst2 : q_x = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have cyc : q_x = (p q_H2 q_x) := (let peq1 : b = (p q_H2 q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : b = q_x := ho; let pst0 : (p q_H2 q_x) = b := Eq.symm (peq1); let pst1 : (p q_H2 q_x) = q_x := Eq.trans (pst0) (peq4); let pst2 : q_x = (p q_H2 q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p q_H2 q_x) := sz_lt_p_right q_H2 q_x
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit sth =>
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
          have sthB := code_bounds sth
          have stB := stB
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := congrArg (fun q => (L q)) (ha)
          change o = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change a = (p q_v0 q_v0) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change b = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB sthB stB qs0B qs1B qs2B z0 z1 z2 z3
          omega
        | hit qs2h =>
          have hcB := code_bounds hc
          have sthB := code_bounds sth
          have qs2hB := code_bounds qs2h
          have stB := stB
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := congrArg (fun q => (L q)) (ha)
          change o = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change a = (p q_v0 q_v0) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change b = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB sthB qs2hB stB qs0B qs1B qs2B z0 z1 z2 z3
          omega
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have sthB := code_bounds sth
          have qs1hB := code_bounds qs1h
          have stB := stB
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := congrArg (fun q => (L q)) (ha)
          change o = (p q_H1 (p (p q_x q_v0) q_x)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change a = (p q_v0 q_v0) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change b = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB sthB qs1hB stB qs0B qs1B qs2B z0 z1 z2 z3
          omega
        | hit qs2h =>
          have hcB := code_bounds hc
          have sthB := code_bounds sth
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have stB := stB
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := congrArg (fun q => (L q)) (ha)
          change o = (p q_H1 (p q_H2 q_x)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change a = (p q_v0 q_v0) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change b = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB sthB qs1hB qs2hB stB qs0B qs1B qs2B z0 z1 z2 z3
          omega
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
          have sthB := code_bounds sth
          have qs0hB := code_bounds qs0h
          have stB := stB
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := congrArg (fun q => (L q)) (ha)
          change o = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change a = (p q_v0 q_v0) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change b = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB sthB qs0hB stB qs0B qs1B qs2B z0 z1 z2 z3
          omega
        | hit qs2h =>
          have hcB := code_bounds hc
          have sthB := code_bounds sth
          have qs0hB := code_bounds qs0h
          have qs2hB := code_bounds qs2h
          have stB := stB
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := congrArg (fun q => (L q)) (ha)
          change o = (p (p q_v0 q_H0) (p q_H2 q_x)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change a = (p q_v0 q_v0) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change b = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB sthB qs0hB qs2hB stB qs0B qs1B qs2B z0 z1 z2 z3
          omega
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0_H2, u0s0, u0s1, u0s2, u0a, u0b, u0o⟩
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
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 (p u0_v1 u0_v0)) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 (p u0_v1 u0_v0)) := sz_lt_p_left u0_v0 (p u0_v1 u0_v0)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 (p u0_v1 u0_v0)) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 (p u0_v1 u0_v0)) := sz_lt_p_left u0_v0 (p u0_v1 u0_v0)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p (p u0_x u0_v0) u0_x) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0s1out (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p (p u0_x u0_v0) u0_x) = u0_v0 := congrArg (fun q => R q) (pst5); let pst7 : u0_v0 = (p (p u0_x u0_v0) u0_x) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p (p u0_x u0_v0) u0_x) := Nat.lt_trans (sz_lt_p_right u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_x = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := (let peq0 : o = (p q_H1 (p (p q_x q_v0) q_x)) := congrArg (fun q => (L q)) (ha); let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq3 : b = q_x := ho; let peq4 : a = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : b = u0_v0 := u0b; let peq6 : o = u0_x := u0o; let pst0 : q_x = b := Eq.symm (peq3); let pst1 : q_x = u0_v0 := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst3 : (p q_v0 q_v0) = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = (p u0s1out (p u0s2out u0_x)) := congrArg (fun q => L q) (pst3); let pst5 : (p u0s1out (p u0s2out u0_x)) = q_v0 := Eq.symm (pst4); let pst6 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst3); let pst7 : (p u0s1out (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : (p u0s2out u0_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst9 : u0_v0 = (p u0s2out u0_x) := Eq.symm (pst8); let pst10 : q_x = (p u0s2out u0_x) := Eq.trans (pst1) (pst9); let pst11 : (p q_x q_v0) = (p (p u0s2out u0_x) q_v0) := congrArg (fun q => p q q_v0) (pst10); let pst12 : u0s1out = u0_v0 := congrArg (fun q => L q) (pst7); let pst13 : u0s1out = (p u0s2out u0_x) := Eq.trans (pst12) (pst9); let pst14 : (p u0s1out (p u0s2out u0_x)) = (p (p u0s2out u0_x) (p u0s2out u0_x)) := congrArg (fun q => p q (p u0s2out u0_x)) (pst13); let pst15 : q_v0 = (p (p u0s2out u0_x) (p u0s2out u0_x)) := Eq.trans (pst4) (pst14); let pst16 : (p (p u0s2out u0_x) q_v0) = (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) := congrArg (fun q => p (p u0s2out u0_x) q) (pst15); let pst17 : (p q_x q_v0) = (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) := Eq.trans (pst11) (pst16); let pst18 : (p (p q_x q_v0) q_x) = (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) q_x) := congrArg (fun q => p q q_x) (pst17); let pst19 : (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) q_x) = (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x)) := congrArg (fun q => p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) q) (pst10); let pst20 : (p (p q_x q_v0) q_x) = (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x)) := Eq.trans (pst18) (pst19); let pst21 : (p q_H1 (p (p q_x q_v0) q_x)) = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := congrArg (fun q => p q_H1 q) (pst20); let pst22 : o = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := Eq.trans (peq0) (pst21); let pst23 : (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) = o := Eq.symm (pst22); let pst24 : (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) = u0_x := Eq.trans (pst23) (peq6); let pst25 : u0_x = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := Eq.symm (pst24); pst25)
                have hlt : sz u0_x < sz (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_left (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x)))) (sz_lt_p_left (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) (sz_lt_p_right q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            let u0s1out := u0_H1
            cases u0s1 with
            | raw =>
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p u0_v0 u0s0out) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 u0s0out) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 u0s0out) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 u0s0out) := sz_lt_p_left u0_v0 u0s0out
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_v0 = (p u0_v0 u0s0out) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 u0s0out) (p u0s2out u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 u0s0out) (p u0s2out u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 u0s0out) (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 u0s0out) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 u0s0out) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 u0s0out) := sz_lt_p_left u0_v0 u0s0out
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p (p u0_x u0_v0) u0_x) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0s1out (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p (p u0_x u0_v0) u0_x) = u0_v0 := congrArg (fun q => R q) (pst5); let pst7 : u0_v0 = (p (p u0_x u0_v0) u0_x) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p (p u0_x u0_v0) u0_x) := Nat.lt_trans (sz_lt_p_right u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_x = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := (let peq0 : o = (p q_H1 (p (p q_x q_v0) q_x)) := congrArg (fun q => (L q)) (ha); let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq3 : b = q_x := ho; let peq4 : a = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : b = u0_v0 := u0b; let peq6 : o = u0_x := u0o; let pst0 : q_x = b := Eq.symm (peq3); let pst1 : q_x = u0_v0 := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst3 : (p q_v0 q_v0) = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = (p u0s1out (p u0s2out u0_x)) := congrArg (fun q => L q) (pst3); let pst5 : (p u0s1out (p u0s2out u0_x)) = q_v0 := Eq.symm (pst4); let pst6 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst3); let pst7 : (p u0s1out (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : (p u0s2out u0_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst9 : u0_v0 = (p u0s2out u0_x) := Eq.symm (pst8); let pst10 : q_x = (p u0s2out u0_x) := Eq.trans (pst1) (pst9); let pst11 : (p q_x q_v0) = (p (p u0s2out u0_x) q_v0) := congrArg (fun q => p q q_v0) (pst10); let pst12 : u0s1out = u0_v0 := congrArg (fun q => L q) (pst7); let pst13 : u0s1out = (p u0s2out u0_x) := Eq.trans (pst12) (pst9); let pst14 : (p u0s1out (p u0s2out u0_x)) = (p (p u0s2out u0_x) (p u0s2out u0_x)) := congrArg (fun q => p q (p u0s2out u0_x)) (pst13); let pst15 : q_v0 = (p (p u0s2out u0_x) (p u0s2out u0_x)) := Eq.trans (pst4) (pst14); let pst16 : (p (p u0s2out u0_x) q_v0) = (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) := congrArg (fun q => p (p u0s2out u0_x) q) (pst15); let pst17 : (p q_x q_v0) = (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) := Eq.trans (pst11) (pst16); let pst18 : (p (p q_x q_v0) q_x) = (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) q_x) := congrArg (fun q => p q q_x) (pst17); let pst19 : (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) q_x) = (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x)) := congrArg (fun q => p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) q) (pst10); let pst20 : (p (p q_x q_v0) q_x) = (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x)) := Eq.trans (pst18) (pst19); let pst21 : (p q_H1 (p (p q_x q_v0) q_x)) = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := congrArg (fun q => p q_H1 q) (pst20); let pst22 : o = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := Eq.trans (peq0) (pst21); let pst23 : (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) = o := Eq.symm (pst22); let pst24 : (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) = u0_x := Eq.trans (pst23) (peq6); let pst25 : u0_x = (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := Eq.symm (pst24); pst25)
                have hlt : sz u0_x < sz (p q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_left (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x)))) (sz_lt_p_left (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x))) (sz_lt_p_right q_H1 (p (p (p u0s2out u0_x) (p (p u0s2out u0_x) (p u0s2out u0_x))) (p u0s2out u0_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0_H2, u0s0, u0s1, u0s2, u0a, u0b, u0o⟩
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
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 (p u0_v1 u0_v0)) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 (p u0_v1 u0_v0)) := sz_lt_p_left u0_v0 (p u0_v1 u0_v0)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 (p u0_v1 u0_v0)) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 (p u0_v1 u0_v0)) := sz_lt_p_left u0_v0 (p u0_v1 u0_v0)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p (p u0_x u0_v0) u0_x) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0s1out (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p (p u0_x u0_v0) u0_x) = u0_v0 := congrArg (fun q => R q) (pst5); let pst7 : u0_v0 = (p (p u0_x u0_v0) u0_x) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p (p u0_x u0_v0) u0_x) := Nat.lt_trans (sz_lt_p_right u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_x = (p q_H1 (p q_H2 (p u0s2out u0_x))) := (let peq0 : o = (p q_H1 (p q_H2 q_x)) := congrArg (fun q => (L q)) (ha); let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq3 : b = q_x := ho; let peq4 : a = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : b = u0_v0 := u0b; let peq6 : o = u0_x := u0o; let pst0 : q_x = b := Eq.symm (peq3); let pst1 : q_x = u0_v0 := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst3 : (p q_v0 q_v0) = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = (p u0s1out (p u0s2out u0_x)) := congrArg (fun q => L q) (pst3); let pst5 : (p u0s1out (p u0s2out u0_x)) = q_v0 := Eq.symm (pst4); let pst6 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst3); let pst7 : (p u0s1out (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : (p u0s2out u0_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst9 : u0_v0 = (p u0s2out u0_x) := Eq.symm (pst8); let pst10 : q_x = (p u0s2out u0_x) := Eq.trans (pst1) (pst9); let pst11 : (p q_H2 q_x) = (p q_H2 (p u0s2out u0_x)) := congrArg (fun q => p q_H2 q) (pst10); let pst12 : (p q_H1 (p q_H2 q_x)) = (p q_H1 (p q_H2 (p u0s2out u0_x))) := congrArg (fun q => p q_H1 q) (pst11); let pst13 : o = (p q_H1 (p q_H2 (p u0s2out u0_x))) := Eq.trans (peq0) (pst12); let pst14 : (p q_H1 (p q_H2 (p u0s2out u0_x))) = o := Eq.symm (pst13); let pst15 : (p q_H1 (p q_H2 (p u0s2out u0_x))) = u0_x := Eq.trans (pst14) (peq6); let pst16 : u0_x = (p q_H1 (p q_H2 (p u0s2out u0_x))) := Eq.symm (pst15); pst16)
                have hlt : sz u0_x < sz (p q_H1 (p q_H2 (p u0s2out u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right q_H2 (p u0s2out u0_x))) (sz_lt_p_right q_H1 (p q_H2 (p u0s2out u0_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            let u0s1out := u0_H1
            cases u0s1 with
            | raw =>
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p u0_v0 u0s0out) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 u0s0out) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 u0s0out) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 u0s0out) := sz_lt_p_left u0_v0 u0s0out
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_v0 = (p u0_v0 u0s0out) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p u0_v0 u0s0out) (p u0s2out u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p u0_v0 u0s0out) (p u0s2out u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p (p u0_v0 u0s0out) (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p u0_v0 u0s0out) = u0_v0 := congrArg (fun q => L q) (pst5); let pst7 : u0_v0 = (p u0_v0 u0s0out) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p u0_v0 u0s0out) := sz_lt_p_left u0_v0 u0s0out
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have u0s2B := step_bound u0s2
              have u0s2N := step_no_first u0s2
              let u0s2out := u0_H2
              cases u0s2 with
              | raw =>
                have cyc : u0_v0 = (p (p u0_x u0_v0) u0_x) := (let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq4 : a = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let pst0 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst1 : (p q_v0 q_v0) = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0s1out (p (p u0_x u0_v0) u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst5 : (p u0s1out (p (p u0_x u0_v0) u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst3) (pst4); let pst6 : (p (p u0_x u0_v0) u0_x) = u0_v0 := congrArg (fun q => R q) (pst5); let pst7 : u0_v0 = (p (p u0_x u0_v0) u0_x) := Eq.symm (pst6); pst7)
                have hlt : sz u0_v0 < sz (p (p u0_x u0_v0) u0_x) := Nat.lt_trans (sz_lt_p_right u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s2h =>
                have cyc : u0_x = (p q_H1 (p q_H2 (p u0s2out u0_x))) := (let peq0 : o = (p q_H1 (p q_H2 q_x)) := congrArg (fun q => (L q)) (ha); let peq1 : a = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq3 : b = q_x := ho; let peq4 : a = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : b = u0_v0 := u0b; let peq6 : o = u0_x := u0o; let pst0 : q_x = b := Eq.symm (peq3); let pst1 : q_x = u0_v0 := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 q_v0) = a := Eq.symm (peq1); let pst3 : (p q_v0 q_v0) = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = (p u0s1out (p u0s2out u0_x)) := congrArg (fun q => L q) (pst3); let pst5 : (p u0s1out (p u0s2out u0_x)) = q_v0 := Eq.symm (pst4); let pst6 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst3); let pst7 : (p u0s1out (p u0s2out u0_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : (p u0s2out u0_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst9 : u0_v0 = (p u0s2out u0_x) := Eq.symm (pst8); let pst10 : q_x = (p u0s2out u0_x) := Eq.trans (pst1) (pst9); let pst11 : (p q_H2 q_x) = (p q_H2 (p u0s2out u0_x)) := congrArg (fun q => p q_H2 q) (pst10); let pst12 : (p q_H1 (p q_H2 q_x)) = (p q_H1 (p q_H2 (p u0s2out u0_x))) := congrArg (fun q => p q_H1 q) (pst11); let pst13 : o = (p q_H1 (p q_H2 (p u0s2out u0_x))) := Eq.trans (peq0) (pst12); let pst14 : (p q_H1 (p q_H2 (p u0s2out u0_x))) = o := Eq.symm (pst13); let pst15 : (p q_H1 (p q_H2 (p u0s2out u0_x))) = u0_x := Eq.trans (pst14) (peq6); let pst16 : u0_x = (p q_H1 (p q_H2 (p u0s2out u0_x))) := Eq.symm (pst15); pst16)
                have hlt : sz u0_x < sz (p q_H1 (p q_H2 (p u0s2out u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right q_H2 (p u0s2out u0_x))) (sz_lt_p_right q_H1 (p q_H2 (p u0s2out u0_x)))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H2 : CM)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code H2 x o := by
  exact step_no_first s2

theorem nr1 (x v0 v1 H1 H2 : CM)
    (s1 : Step v0 H0 H1)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code H1 (p H2 x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s1B := step_bound s1
  have s1N := step_no_first s1
  have s1O := step_no_output s1
  cases s1 with
  | raw =>
    have s2B := step_bound s2
    have s2N := step_no_first s2
    have s2O := step_no_output s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      have qs0O := step_no_output qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change v0 = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change H0 = (p q_v0 q_v0) at e1
            have e2 := congrArg (fun q => q) hb
            change (p (p x v0) x) = q_v0 at e2
            have cyc : q_v0 = (p (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x) := (let peq0 : v0 = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) := e0; let peq2 : (p (p x v0) x) = q_v0 := e2; let pst0 : (p x v0) = (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) x) = (p (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x) := congrArg (fun q => p q x) (pst0); let pst2 : (p (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x) = (p (p x v0) x) := Eq.symm (pst1); let pst3 : (p (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) (sz_lt_p_right x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)))) (sz_lt_p_left (p x (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change v0 = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change H0 = (p q_v0 q_v0) at e1
            have e2 := congrArg (fun q => q) hb
            change (p (p x v0) x) = q_v0 at e2
            have cyc : q_v0 = (p (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x) := (let peq0 : v0 = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) := e0; let peq2 : (p (p x v0) x) = q_v0 := e2; let pst0 : (p x v0) = (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) x) = (p (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x) := congrArg (fun q => p q x) (pst0); let pst2 : (p (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x) = (p (p x v0) x) := Eq.symm (pst1); let pst3 : (p (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) (sz_lt_p_right x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)))) (sz_lt_p_left (p x (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change v0 = (p q_H1 (p (p q_x q_v0) q_x)) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change H0 = (p q_v0 q_v0) at e1
            have e2 := congrArg (fun q => q) hb
            change (p (p x v0) x) = q_v0 at e2
            have cyc : q_v0 = (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := (let peq0 : v0 = (p q_H1 (p (p q_x q_v0) q_x)) := e0; let peq2 : (p (p x v0) x) = q_v0 := e2; let pst0 : (p x v0) = (p x (p q_H1 (p (p q_x q_v0) q_x))) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) x) = (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := congrArg (fun q => p q x) (pst0); let pst2 : (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) = (p (p x v0) x) := Eq.symm (pst1); let pst3 : (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_right q_H1 (p (p q_x q_v0) q_x))) (sz_lt_p_right x (p q_H1 (p (p q_x q_v0) q_x)))) (sz_lt_p_left (p x (p q_H1 (p (p q_x q_v0) q_x))) x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have hcB := code_bounds hc
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p q_H1 (p q_H2 q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p (p x v0) x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change v0 = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change H0 = (p q_v0 q_v0) at e1
            have e2 := congrArg (fun q => q) hb
            change (p (p x v0) x) = q_v0 at e2
            have cyc : q_v0 = (p (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x) := (let peq0 : v0 = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) := e0; let peq2 : (p (p x v0) x) = q_v0 := e2; let pst0 : (p x v0) = (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) x) = (p (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x) := congrArg (fun q => p q x) (pst0); let pst2 : (p (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x) = (p (p x v0) x) := Eq.symm (pst1); let pst3 : (p (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p (p q_x q_v0) q_x))) (sz_lt_p_right x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)))) (sz_lt_p_left (p x (p (p q_v0 q_H0) (p (p q_x q_v0) q_x))) x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => (L q)) ha
            change v0 = (p (p q_v0 q_H0) (p q_H2 q_x)) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change H0 = (p q_v0 q_v0) at e1
            have e2 := congrArg (fun q => q) hb
            change (p (p x v0) x) = q_v0 at e2
            have cyc : q_v0 = (p (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x) := (let peq0 : v0 = (p (p q_v0 q_H0) (p q_H2 q_x)) := e0; let peq2 : (p (p x v0) x) = q_v0 := e2; let pst0 : (p x v0) = (p x (p (p q_v0 q_H0) (p q_H2 q_x))) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) x) = (p (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x) := congrArg (fun q => p q x) (pst0); let pst2 : (p (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x) = (p (p x v0) x) := Eq.symm (pst1); let pst3 : (p (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p q_H2 q_x))) (sz_lt_p_right x (p (p q_v0 q_H0) (p q_H2 q_x)))) (sz_lt_p_left (p x (p (p q_v0 q_H0) (p q_H2 q_x))) x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => (L q)) ha
            change v0 = (p q_H1 (p (p q_x q_v0) q_x)) at e0
            have e1 := congrArg (fun q => (R q)) ha
            change H0 = (p q_v0 q_v0) at e1
            have e2 := congrArg (fun q => q) hb
            change (p (p x v0) x) = q_v0 at e2
            have cyc : q_v0 = (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := (let peq0 : v0 = (p q_H1 (p (p q_x q_v0) q_x)) := e0; let peq2 : (p (p x v0) x) = q_v0 := e2; let pst0 : (p x v0) = (p x (p q_H1 (p (p q_x q_v0) q_x))) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) x) = (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := congrArg (fun q => p q x) (pst0); let pst2 : (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) = (p (p x v0) x) := Eq.symm (pst1); let pst3 : (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := Eq.symm (pst3); pst4)
            have hlt : sz q_v0 < sz (p (p x (p q_H1 (p (p q_x q_v0) q_x))) x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_right q_H1 (p (p q_x q_v0) q_x))) (sz_lt_p_right x (p q_H1 (p (p q_x q_v0) q_x)))) (sz_lt_p_left (p x (p q_H1 (p (p q_x q_v0) q_x))) x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p q_H1 (p q_H2 q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p (p x v0) x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
    | hit s2h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      have qs0O := step_no_output qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p q_H1 (p (p q_x q_v0) q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs1hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p q_H1 (p q_H2 q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs0hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p (p q_v0 q_H0) (p q_H2 q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs0hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p q_H1 (p (p q_x q_v0) q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs0hB qs1hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := congrArg (fun q => (L q)) (ha)
            change v0 = (p q_H1 (p q_H2 q_x)) at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change H0 = (p q_v0 q_v0) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change (p H2 x) = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB s2hB qs0hB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2 z3
            omega
  | hit s1h =>
    have s2B := step_bound s2
    have s2N := step_no_first s2
    have s2O := step_no_output s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      have qs0O := step_no_output qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p (p x v0) x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0_H2, u0s0, u0s1, u0s2, u0a, u0b, u0o⟩
            have u0s0B := step_bound u0s0
            have u0s0N := step_no_first u0s0
            have u0s0O := step_no_output u0s0
            let u0s0out := u0_H0
            cases u0s0 with
            | raw =>
              have u0s1B := step_bound u0s1
              have u0s1N := step_no_first u0s1
              have u0s1O := step_no_output u0s1
              let u0s1out := u0_H1
              cases u0s1 with
              | raw =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x))) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s1h =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right u0s1out (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right u0s1out (p u0s2out u0_x))) (sz_lt_p_left (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s0h =>
              have u0s1B := step_bound u0s1
              have u0s1N := step_no_first u0s1
              have u0s1O := step_no_output u0s1
              let u0s1out := u0_H1
              cases u0s1 with
              | raw =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right (p u0_v0 u0s0out) (p u0s2out u0_x))) (sz_lt_p_left (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s1h =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right u0s1out (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst4) (pst9); let pst11 : (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) = (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) := congrArg (fun q => p q (p q_H2 q_x)) (pst10); let pst12 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst11); let pst13 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst14 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst13); let pst15 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst14); let pst16 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst15); let pst17 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst18 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst17); let pst19 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst18); let pst20 : (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst19); let pst21 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst16) (pst20); let pst22 : (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) q) (pst21); let pst23 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (pst12) (pst22); let pst24 : H1 = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst23); let pst25 : (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst24); let pst26 : (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst25) (peq5); let pst27 : u0_x = (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst26); pst27)
                  have hlt : sz u0_x < sz (p (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right u0s1out (p u0s2out u0_x))) (sz_lt_p_left (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))) (sz_lt_p_left (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x))) (sz_lt_p_left (p (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p q_v1 (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p (p x v0) x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p (p x v0) x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have qs0hB := code_bounds qs0h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p (p x v0) x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p (p x v0) x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p (p x v0) x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0_H2, u0s0, u0s1, u0s2, u0a, u0b, u0o⟩
            have u0s0B := step_bound u0s0
            have u0s0N := step_no_first u0s0
            have u0s0O := step_no_output u0s0
            let u0s0out := u0_H0
            cases u0s0 with
            | raw =>
              have u0s1B := step_bound u0s1
              have u0s1N := step_no_first u0s1
              have u0s1O := step_no_output u0s1
              let u0s1out := u0_H1
              cases u0s1 with
              | raw =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x))) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 (p u0_v1 u0_v0)) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s1h =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right u0s1out (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right u0s1out (p u0s2out u0_x))) (sz_lt_p_left (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s0h =>
              have u0s1B := step_bound u0s1
              have u0s1N := step_no_first u0s1
              have u0s1O := step_no_output u0s1
              let u0s1out := u0_H1
              cases u0s1 with
              | raw =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right (p u0_v0 u0s0out) (p u0s2out u0_x))) (sz_lt_p_left (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p (p u0_v0 u0s0out) (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u0s1h =>
                have u0s2B := step_bound u0s2
                have u0s2N := step_no_first u0s2
                have u0s2O := step_no_output u0s2
                let u0s2out := u0_H2
                cases u0s2 with
                | raw =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_v0) (sz_lt_p_left (p u0_x u0_v0) u0_x)) (sz_lt_p_right u0s1out (p (p u0_x u0_v0) u0_x))) (sz_lt_p_left (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p (p u0_x u0_v0) u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u0s2h =>
                  have cyc : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := (let peq0 : H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := ha; let peq1 : (p (p x v0) x) = q_v0 := hb; let peq3 : v0 = (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)) := u0a; let peq5 : H1 = u0_x := u0o; let pst0 : q_v0 = (p (p x v0) x) := Eq.symm (peq1); let pst1 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst2 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst1); let pst3 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p x v0) = (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) := congrArg (fun q => p x q) (peq3); let pst6 : (p (p x v0) x) = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := congrArg (fun q => p q x) (pst5); let pst7 : q_v0 = (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) := Eq.trans (pst0) (pst6); let pst8 : (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := congrArg (fun q => p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) := Eq.trans (pst4) (pst8); let pst10 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := congrArg (fun q => p (p q_H1 (p q_H2 q_x)) q) (pst9); let pst11 : H1 = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.trans (peq0) (pst10); let pst12 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = H1 := Eq.symm (pst11); let pst13 : (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) = u0_x := Eq.trans (pst12) (peq5); let pst14 : u0_x = (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Eq.symm (pst13); pst14)
                  have hlt : sz u0_x < sz (p (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0s2out u0_x) (sz_lt_p_right u0s1out (p u0s2out u0_x))) (sz_lt_p_left (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) (sz_lt_p_right x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0)))) (sz_lt_p_left (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)) (sz_lt_p_left (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x))) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x) (p (p x (p (p u0s1out (p u0s2out u0_x)) (p u0_v0 u0_v0))) x)))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s2h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      have qs0O := step_no_output qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs1hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        have qs1O := step_no_output qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs0hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs0hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
        | hit qs1h =>
          have qs2B := step_bound qs2
          have qs2N := step_no_first qs2
          have qs2O := step_no_output qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs0hB qs1hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change H1 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) at p0
            have z0 := congrArg sz p0
            have p1 := hb
            change (p H2 x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := ho
            change o = q_x at p2
            have z2 := congrArg sz p2
            simp only [getOut, L, R, U, sz] at hcB s1hB s2hB qs0hB qs1hB qs2hB s1B s2B qs0B qs1B qs2B z0 z1 z2
            omega
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  have qs0O := step_no_output qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    have qs1O := step_no_output qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      have qs2N := step_no_first qs2
      have qs2O := step_no_output qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x))) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v0)) (p (p q_x q_v0) q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x))) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v0)) (p q_H2 q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      have qs2N := step_no_first qs2
      have qs2O := step_no_output qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_right q_H1 (p (p q_x q_v0) q_x))) (sz_lt_p_left (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    have qs1O := step_no_output qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      have qs2N := step_no_first qs2
      have qs2O := step_no_output qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p (p q_x q_v0) q_x))) (sz_lt_p_left (p (p q_v0 q_H0) (p (p q_x q_v0) q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p q_H2 q_x))) (sz_lt_p_left (p (p q_v0 q_H0) (p q_H2 q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      have qs2N := step_no_first qs2
      have qs2O := step_no_output qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_right q_H1 (p (p q_x q_v0) q_x))) (sz_lt_p_left (p q_H1 (p (p q_x q_v0) q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) at e0
        have e1 := congrArg (fun q => q) hb
        change v0 = q_v0 at e1
        have cyc : q_v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p q_H1 (p q_H2 q_x)) (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H1 H2 : CM)
    (s1 : Step v0 H0 H1)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code (p H1 (p H2 x)) (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s1B := step_bound s1
  have s1N := step_no_first s1
  have s1O := step_no_output s1
  cases s1 with
  | raw =>
    have he : H2 = x := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L q))) (ha); let peq2 : H2 = q_v0 := congrArg (fun q => (L (R q))) (ha); let peq3 : x = q_v0 := congrArg (fun q => (R (R q))) (ha); let peq4 : (p v0 v0) = q_v0 := hb; let pst0 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq0); let pst2 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst0) (pst1); let pst3 : (p q_H1 q_H1) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p q_H1 q_H1) = q_v0 := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p q_H1 q_H1) := Eq.symm (pst4); let pst6 : H2 = (p q_H1 q_H1) := Eq.trans (peq2) (pst5); let pst7 : x = (p q_H1 q_H1) := Eq.trans (peq3) (pst5); let pst8 : (p q_H1 q_H1) = x := Eq.symm (pst7); let pst9 : H2 = x := Eq.trans (pst6) (pst8); pst9)
    exact step_ne_first (by simpa only [he] using s2)
  | hit s1h =>
    have he : H2 = x := (let peq1 : H2 = q_v0 := congrArg (fun q => (L (R q))) (ha); let peq2 : x = q_v0 := congrArg (fun q => (R (R q))) (ha); let peq3 : (p v0 v0) = q_v0 := hb; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq3); let pst1 : H2 = (p v0 v0) := Eq.trans (peq1) (pst0); let pst2 : x = (p v0 v0) := Eq.trans (peq2) (pst0); let pst3 : (p v0 v0) = x := Eq.symm (pst2); let pst4 : H2 = x := Eq.trans (pst1) (pst3); pst4)
    exact step_ne_first (by simpa only [he] using s2)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 (eval v1 v0)) (eval (eval x v0) x)) (eval v0 v0)) v0) := by
  let H0 := eval v1 v0
  have e0a : v1 = v1 := by
    change v1 = v1
    rfl
  have e0b : v0 = v0 := by
    change v0 = v0
    rfl
  have s0 : Step v1 v0 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v1 v0
  let H1 := eval v0 (eval v1 v0)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval v1 v0) = H0 := by
    change H0 = H0
    rfl
  have s1 : Step v0 H0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval v1 v0)
  let H2 := eval x v0
  have e2a : x = x := by
    change x = x
    rfl
  have e2b : v0 = v0 := by
    change v0 = v0
    rfl
  have s2 : Step x v0 H2 := by
    rw [← e2a, ← e2b]
    exact eval_step x v0
  change x = (eval (eval (eval H1 (eval H2 x)) (eval v0 v0)) v0)
  have rawEq : (eval (eval (eval H1 (eval H2 x)) (eval v0 v0)) v0) = (eval (p (p H1 (p H2 x)) (p v0 v0)) v0) := by
    calc
      (eval (eval (eval H1 (eval H2 x)) (eval v0 v0)) v0) = (eval (eval (eval H1 (p H2 x)) (eval v0 v0)) v0) := congrArg (fun q => (eval (eval (eval H1 q) (eval v0 v0)) v0)) (eval_raw (nr0 x v0 v1 H2 s2))
      _ = (eval (eval (p H1 (p H2 x)) (eval v0 v0)) v0) := congrArg (fun q => (eval (eval q (eval v0 v0)) v0)) (eval_raw (nr1 x v0 v1 H1 H2 s1 s2))
      _ = (eval (eval (p H1 (p H2 x)) (p v0 v0)) v0) := congrArg (fun q => (eval (eval (p H1 (p H2 x)) q) v0)) (eval_raw (nr2 x v0 v1))
      _ = (eval (p (p H1 (p H2 x)) (p v0 v0)) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr3 x v0 v1 H1 H2 s1 s2))
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
