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
  | law (x v0 v1 v2 H0 H1 H2 H3 : CM)
      (s0 : Step v1 v0 H0)
      (s1 : Step H0 v2 H1)
      (s2 : Step v0 H1 H2)
      (s3 : Step x v0 H3) :
      Code (p H2 (p H3 x)) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 q_H2 q_H3 : CM, Step q_v1 q_v0 q_H0 ∧ Step q_H0 q_v2 q_H1 ∧ Step q_v0 q_H1 q_H2 ∧ Step q_x q_v0 q_H3 ∧ a = (p q_H2 (p q_H3 q_x)) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 H2 H3 s0 s1 s2 s3 => ⟨x, v0, v1, v2, H0, H1, H2, H3, s0, s1, s2, s3, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
def CodeArg := (a : CM) ×' (b : CM) ×' (o : CM) ×' Code a b o
def StepArg := (a : CM) ×' (b : CM) ×' (o : CM) ×' Step a b o
mutual
theorem code_bounds_core (q : CodeArg) :
    sz q.2.1 < sz q.1 ∧ sz q.2.2.1 < sz q.1 := by
  rcases q with ⟨a, b, o, h⟩
  rcases code_shape h with ⟨x, v0, v1, v2, H0, H1, H2, H3, s0, s1, s2, s3, ha, hb, ho⟩
  subst a
  subst b
  subst x
  exact ⟨Nat.lt_trans (step_bound_core ⟨_, _, _, s3⟩) (sz_lt_p_right H2 (p H3 o)), Nat.lt_trans (sz_lt_p_right H3 o) (sz_lt_p_right H2 (p H3 o))⟩
termination_by sz q.1
decreasing_by simp_all [sz] <;> omega
theorem step_bound_core (q : StepArg) :
    sz q.2.1 < sz (p q.2.2.1 q.1) := by
  rcases q with ⟨a, b, o, h⟩
  cases h with
  | raw => simp only [sz] <;> omega
  | hit hc => exact Nat.lt_trans ((code_bounds_core ⟨_, _, _, hc⟩).1) (sz_lt_p_right o a)
termination_by sz (p q.2.2.1 q.1)
decreasing_by simp_all only [sz] <;> omega
end
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a :=
  code_bounds_core ⟨a, b, o, h⟩
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz b < sz (p o a) :=
  step_bound_core ⟨a, b, o, h⟩
theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
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
theorem code_no_pair_left (v k : CM) :
    ¬ ∃ o, Code (p v k) v o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have he : q_H2 = q_v0 := (let peq0 : v = q_H2 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H2 = v := Eq.symm (peq0); let pst1 : q_H2 = q_v0 := Eq.trans (pst0) (peq2); pst1)
      exact step_ne_first (by simpa only [he] using qs2)
    | hit qs1h =>
      have he : q_H2 = q_v0 := (let peq0 : v = q_H2 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H2 = v := Eq.symm (peq0); let pst1 : q_H2 = q_v0 := Eq.trans (pst0) (peq2); pst1)
      exact step_ne_first (by simpa only [he] using qs2)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have he : q_H2 = q_v0 := (let peq0 : v = q_H2 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H2 = v := Eq.symm (peq0); let pst1 : q_H2 = q_v0 := Eq.trans (pst0) (peq2); pst1)
      exact step_ne_first (by simpa only [he] using qs2)
    | hit qs1h =>
      have he : q_H2 = q_v0 := (let peq0 : v = q_H2 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H2 = v := Eq.symm (peq0); let pst1 : q_H2 = q_v0 := Eq.trans (pst0) (peq2); pst1)
      exact step_ne_first (by simpa only [he] using qs2)
theorem code_no_pair_right (v k : CM) :
    ¬ ∃ o, Code (p v k) k o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = (p q_v0 (p (p q_v1 q_v0) q_v2)) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = (p q_v0 (p (p q_v1 q_v0) q_v2)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = q_H2 at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = q_H2 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_v0 < sz (p (p q_v1 q_v0) q_v2) := by
            have structural : sz (p q_H3 q_x) < sz (p (p q_v1 (p q_H3 q_x)) q_v2) := Nat.lt_trans (sz_lt_p_right q_v1 (p q_H3 q_x)) (sz_lt_p_left (p q_v1 (p q_H3 q_x)) q_v2)
            have large_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            have small_eq : sz (p (p q_v1 q_v0) q_v2) = sz (p (p q_v1 (p q_H3 q_x)) q_v2) := congrArg sz (congrArg (fun q => p q q_v2) (congrArg (fun q => p q_v1 q) (Eq.trans (p2.symm) (p1))))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs2hB.1).elim
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = (p q_v0 q_H1) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs1hB := code_bounds qs1h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = (p q_v0 q_H1) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = q_H2 at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = q_H2 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = (p q_v0 (p q_H0 q_v2)) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = (p q_v0 (p q_H0 q_v2)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = q_H2 at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = q_H2 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = (p q_v0 q_H1) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = (p q_v0 q_H1) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v = q_H2 at e0
          have e1 := congrArg (fun q => (R q)) ha
          change k = (p (p q_x q_v0) q_x) at e1
          have e2 := congrArg (fun q => q) hb
          change k = q_v0 at e2
          have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq1 : k = (p (p q_x q_v0) q_x) := e1; let peq2 : k = q_v0 := e2; let pst0 : (p (p q_x q_v0) q_x) = k := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_x q_v0) q_x) := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have qs3B := qs3B
          have p0 := congrArg (fun q => (L q)) (ha)
          change v = q_H2 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change k = (p q_H3 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change k = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          have badlt : sz q_x < sz q_v0 := by
            have structural : sz q_x < sz (p q_H3 q_x) := sz_lt_p_right q_H3 q_x
            have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
            have small_eq : sz q_v0 = sz (p q_H3 q_x) := congrArg sz (Eq.trans (p2.symm) (p1))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs3hB.1).elim
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
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
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change a = q_v0 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change b = (p (p q_v1 q_v0) q_v2) at e1
            have e2 := congrArg (fun q => (R q)) ha
            change a = (p (p q_x q_v0) q_x) at e2
            have e3 := congrArg (fun q => q) hb
            change k = q_v0 at e3
            have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq0 : a = q_v0 := e0; let peq2 : a = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = a := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
            have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs3h =>
            have cyc : q_x = (p (p q_v1 (p q_H3 q_x)) q_v2) := (let peq0 : a = q_v0 := congrArg (fun q => (L (L q))) (ha); let peq1 : b = (p (p q_v1 q_v0) q_v2) := congrArg (fun q => (R (L q))) (ha); let peq2 : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha); let peq4 : b = q_x := ho; let pst0 : q_v0 = a := Eq.symm (peq0); let pst1 : q_v0 = (p q_H3 q_x) := Eq.trans (pst0) (peq2); let pst2 : (p q_v1 q_v0) = (p q_v1 (p q_H3 q_x)) := congrArg (fun q => p q_v1 q) (pst1); let pst3 : (p (p q_v1 q_v0) q_v2) = (p (p q_v1 (p q_H3 q_x)) q_v2) := congrArg (fun q => p q q_v2) (pst2); let pst4 : b = (p (p q_v1 (p q_H3 q_x)) q_v2) := Eq.trans (peq1) (pst3); let pst5 : (p (p q_v1 (p q_H3 q_x)) q_v2) = b := Eq.symm (pst4); let pst6 : (p (p q_v1 (p q_H3 q_x)) q_v2) = q_x := Eq.trans (pst5) (peq4); let pst7 : q_x = (p (p q_v1 (p q_H3 q_x)) q_v2) := Eq.symm (pst6); pst7)
            have hlt : sz q_x < sz (p (p q_v1 (p q_H3 q_x)) q_v2) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H3 q_x) (sz_lt_p_right q_v1 (p q_H3 q_x))) (sz_lt_p_left (p q_v1 (p q_H3 q_x)) q_v2)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have hcB := code_bounds hc
            have qs2hB := code_bounds qs2h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p (p q_x q_v0) q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            have badlt : sz q_v0 < sz (p (p q_v1 q_v0) q_v2) := by
              have structural : sz q_v0 < sz (p (p q_v1 q_v0) q_v2) := Nat.lt_trans (sz_lt_p_right q_v1 q_v0) (sz_lt_p_left (p q_v1 q_v0) q_v2)
              have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have small_eq : sz (p (p q_v1 q_v0) q_v2) = sz (p (p q_v1 q_v0) q_v2) := congrArg sz (rfl)
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs2hB.1).elim
          | hit qs3h =>
            have hcB := code_bounds hc
            have qs2hB := code_bounds qs2h
            have qs3hB := code_bounds qs3h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p q_H3 q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            have badlt : sz q_v0 < sz (p (p q_v1 q_v0) q_v2) := by
              have structural : sz q_v0 < sz (p (p q_v1 q_v0) q_v2) := Nat.lt_trans (sz_lt_p_right q_v1 q_v0) (sz_lt_p_left (p q_v1 q_v0) q_v2)
              have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have small_eq : sz (p (p q_v1 q_v0) q_v2) = sz (p (p q_v1 q_v0) q_v2) := congrArg sz (rfl)
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs2hB.1).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change a = q_v0 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change b = q_H1 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change a = (p (p q_x q_v0) q_x) at e2
            have e3 := congrArg (fun q => q) hb
            change k = q_v0 at e3
            have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq0 : a = q_v0 := e0; let peq2 : a = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = a := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
            have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs3h =>
            have epa : (p (p a b) a) = (p (p (p q_H3 q_x) q_x) (p q_H3 q_x)) := Eq.trans (congrArg (fun q => p q a) (Eq.trans (congrArg (fun q => p q b) (Eq.trans (congrArg (fun q => (L (L q))) (ha)) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha))))) (congrArg (fun q => p (p q_H3 q_x) q) (Eq.trans (congrArg (fun q => (R (L q))) (ha)) (Eq.trans (Eq.symm (congrArg (fun q => (R (L q))) (ha))) (ho)))))) (congrArg (fun q => p (p (p q_H3 q_x) q_x) q) (Eq.trans (congrArg (fun q => (L (L q))) (ha)) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha)))))
            have epb : k = (p q_H3 q_x) := Eq.trans (hb) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha)))
            apply code_no_pair_right (p (p q_H3 q_x) q_x) (p q_H3 q_x)
            exact ⟨_, by simpa only [epa, epb] using hc⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have hcB := code_bounds hc
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p (p q_x q_v0) q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            have badlt : sz q_v0 < sz q_H2 := by
              have structural : sz q_v0 < sz (p (p (p q_x q_v0) q_x) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_left (p (p q_x q_v0) q_x) q_x)
              have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have small_eq : sz q_H2 = sz (p (p (p q_x q_v0) q_x) q_x) := congrArg sz (Eq.trans (p0.symm) (Eq.trans (congrArg (fun q => p q b) (p1)) (congrArg (fun q => p (p (p q_x q_v0) q_x) q) (ho))))
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs2hB.2).elim
          | hit qs3h =>
            have hcB := code_bounds hc
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have qs3hB := code_bounds qs3h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p q_H3 q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB qs1hB qs2hB qs3hB z0 z1 z2 z3
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
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change a = q_v0 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change b = (p q_H0 q_v2) at e1
            have e2 := congrArg (fun q => (R q)) ha
            change a = (p (p q_x q_v0) q_x) at e2
            have e3 := congrArg (fun q => q) hb
            change k = q_v0 at e3
            have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq0 : a = q_v0 := e0; let peq2 : a = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = a := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
            have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs3h =>
            have epa : (p (p a b) a) = (p (p (p q_H3 (p q_H0 q_v2)) (p q_H0 q_v2)) (p q_H3 (p q_H0 q_v2))) := Eq.trans (congrArg (fun q => p q a) (Eq.trans (congrArg (fun q => p q b) (Eq.trans (congrArg (fun q => (L (L q))) (ha)) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha))) (congrArg (fun q => p q_H3 q) (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => (R (L q))) (ha))) (ho))))))) (congrArg (fun q => p (p q_H3 (p q_H0 q_v2)) q) (congrArg (fun q => (R (L q))) (ha))))) (congrArg (fun q => p (p (p q_H3 (p q_H0 q_v2)) (p q_H0 q_v2)) q) (Eq.trans (congrArg (fun q => (L (L q))) (ha)) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha))) (congrArg (fun q => p q_H3 q) (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => (R (L q))) (ha))) (ho)))))))
            have epb : k = (p q_H3 (p q_H0 q_v2)) := Eq.trans (Eq.trans (hb) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha)))) (congrArg (fun q => p q_H3 q) (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => (R (L q))) (ha))) (ho))))
            apply code_no_pair_right (p (p q_H3 (p q_H0 q_v2)) (p q_H0 q_v2)) (p q_H3 (p q_H0 q_v2))
            exact ⟨_, by simpa only [epa, epb] using hc⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p (p q_x q_v0) q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            have badlt : sz q_v0 < sz q_H2 := by
              have structural : sz q_v0 < sz (p (p (p q_x q_v0) q_x) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_left (p (p q_x q_v0) q_x) q_x)
              have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have small_eq : sz q_H2 = sz (p (p (p q_x q_v0) q_x) q_x) := congrArg sz (Eq.trans (p0.symm) (Eq.trans (congrArg (fun q => p q b) (p1)) (congrArg (fun q => p (p (p q_x q_v0) q_x) q) (ho))))
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs2hB.2).elim
          | hit qs3h =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have qs3hB := code_bounds qs3h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p q_H3 q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB qs0hB qs2hB qs3hB z0 z1 z2 z3
            omega
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have e0 := congrArg (fun q => (L (L q))) ha
            change a = q_v0 at e0
            have e1 := congrArg (fun q => (R (L q))) ha
            change b = q_H1 at e1
            have e2 := congrArg (fun q => (R q)) ha
            change a = (p (p q_x q_v0) q_x) at e2
            have e3 := congrArg (fun q => q) hb
            change k = q_v0 at e3
            have cyc : q_v0 = (p (p q_x q_v0) q_x) := (let peq0 : a = q_v0 := e0; let peq2 : a = (p (p q_x q_v0) q_x) := e2; let pst0 : q_v0 = a := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) q_x) := Eq.trans (pst0) (peq2); pst1)
            have hlt : sz q_v0 < sz (p (p q_x q_v0) q_x) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs3h =>
            have epa : (p (p a b) a) = (p (p (p q_H3 q_x) q_x) (p q_H3 q_x)) := Eq.trans (congrArg (fun q => p q a) (Eq.trans (congrArg (fun q => p q b) (Eq.trans (congrArg (fun q => (L (L q))) (ha)) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha))))) (congrArg (fun q => p (p q_H3 q_x) q) (Eq.trans (congrArg (fun q => (R (L q))) (ha)) (Eq.trans (Eq.symm (congrArg (fun q => (R (L q))) (ha))) (ho)))))) (congrArg (fun q => p (p (p q_H3 q_x) q_x) q) (Eq.trans (congrArg (fun q => (L (L q))) (ha)) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha)))))
            have epb : k = (p q_H3 q_x) := Eq.trans (hb) (Eq.trans (Eq.symm (congrArg (fun q => (L (L q))) (ha))) (congrArg (fun q => (R q)) (ha)))
            apply code_no_pair_right (p (p q_H3 q_x) q_x) (p q_H3 q_x)
            exact ⟨_, by simpa only [epa, epb] using hc⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p (p q_x q_v0) q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            have badlt : sz q_v0 < sz q_H2 := by
              have structural : sz q_v0 < sz (p (p (p q_x q_v0) q_x) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_left (p (p q_x q_v0) q_x) q_x)
              have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have small_eq : sz q_H2 = sz (p (p (p q_x q_v0) q_x) q_x) := congrArg sz (Eq.trans (p0.symm) (Eq.trans (congrArg (fun q => p q b) (p1)) (congrArg (fun q => p (p (p q_x q_v0) q_x) q) (ho))))
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs2hB.2).elim
          | hit qs3h =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have qs3hB := code_bounds qs3h
            have stB := stB
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have qs3B := qs3B
            have p0 := congrArg (fun q => (L q)) (ha)
            change (p a b) = q_H2 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (R q)) (ha)
            change a = (p q_H3 q_x) at p1
            have z1 := congrArg sz p1
            have p2 := hb
            change k = q_v0 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change b = q_x at p3
            have z3 := congrArg sz p3
            simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs2hB qs3hB z0 z1 z2 z3
            omega
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
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
      | hit qs1h =>
        have qs2B := step_bound qs2
        have qs2N := step_no_first qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
        | hit qs2h =>
          have qs3B := step_bound qs3
          have qs3N := step_no_first qs3
          cases qs3 with
          | raw =>
            have epa : a = (p (p q_x q_v0) q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right (p q_x q_v0) q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
          | hit qs3h =>
            have epa : a = (p q_H3 q_x) := congrArg (fun q => (R q)) (ha)
            have epb : b = q_x := ho
            apply code_no_pair_right q_H3 q_x
            exact ⟨_, by simpa only [epa, epb] using sth⟩
theorem nr0 (x v0 v1 v2 H3 : CM)
    (s3 : Step x v0 H3) :
    ¬ ∃ o, Code H3 x o := by
  exact step_no_first s3

theorem nr1 (x v0 v1 v2 H2 H3 : CM)
    (s2 : Step v0 H1 H2)
    (s3 : Step x v0 H3) :
    ¬ ∃ o, Code H2 (p H3 x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  have s3B := step_bound s3
  have s3O := step_no_output s3
  cases s2 with
  | raw =>
    cases qs2 with
    | raw =>
      have he : v0 = (p (p H3 x) q_H1) := (let peq0 : v0 = (p q_v0 q_H1) := congrArg (fun q => (L q)) (ha); let peq2 : (p H3 x) = q_v0 := hb; let pst0 : q_v0 = (p H3 x) := Eq.symm (peq2); let pst1 : (p q_v0 q_H1) = (p (p H3 x) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst2 : v0 = (p (p H3 x) q_H1) := Eq.trans (peq0) (pst1); pst2)
      have hs := congrArg sz he
      simp only [getOut, L, R, U, sz] at s3B hs
      omega
    | hit qs2h =>
      have ein : q_v0 = (p H3 x) := (let peq2 : (p H3 x) = q_v0 := hb; let pst0 : q_v0 = (p H3 x) := Eq.symm (peq2); pst0)
      have eout : q_H2 = v0 := (let peq0 : v0 = q_H2 := congrArg (fun q => (L q)) (ha); let pst0 : q_H2 = v0 := Eq.symm (peq0); pst0)
      apply s3O
      refine ⟨q_H1, ?_⟩
      simpa only [ein, eout] using qs2h
  | hit s2h =>
    have hu := (code_bounds s2h).2
    have hk := (code_bounds hc).1
    omega
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval (eval v0 (eval (eval v1 v0) v2)) (eval (eval x v0) x)) v0) := by
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
  let H1 := eval (eval v1 v0) v2
  have e1a : (eval v1 v0) = H0 := by
    change H0 = H0
    rfl
  have e1b : v2 = v2 := by
    change v2 = v2
    rfl
  have s1 : Step H0 v2 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v1 v0) v2
  let H2 := eval v0 (eval (eval v1 v0) v2)
  have e2a : v0 = v0 := by
    change v0 = v0
    rfl
  have e2b : (eval (eval v1 v0) v2) = H1 := by
    change H1 = H1
    rfl
  have s2 : Step v0 H1 H2 := by
    rw [← e2a, ← e2b]
    exact eval_step v0 (eval (eval v1 v0) v2)
  let H3 := eval x v0
  have e3a : x = x := by
    change x = x
    rfl
  have e3b : v0 = v0 := by
    change v0 = v0
    rfl
  have s3 : Step x v0 H3 := by
    rw [← e3a, ← e3b]
    exact eval_step x v0
  change x = (eval (eval H2 (eval H3 x)) v0)
  have rawEq : (eval (eval H2 (eval H3 x)) v0) = (eval (p H2 (p H3 x)) v0) := by
    calc
      (eval (eval H2 (eval H3 x)) v0) = (eval (eval H2 (p H3 x)) v0) := congrArg (fun q => (eval (eval H2 q) v0)) (eval_raw (nr0 x v0 v1 v2 H3 s3))
      _ = (eval (p H2 (p H3 x)) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr1 x v0 v1 v2 H2 H3 s2 s3))
  exact (eval_hit (Code.law x v0 v1 v2 H0 H1 H2 H3 s0 s1 s2 s3)).symm.trans rawEq.symm
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
