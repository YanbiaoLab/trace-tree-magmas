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
      (s1 : Step H0 v1 H1) :
      Code H1 (p x (p v1 (p v1 v1))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_H0 q_v1 q_H1 ∧ a = q_H1 ∧ b = (p q_x (p q_v1 (p q_v1 q_v1))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L b)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
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
theorem code_no_pair_left (v k : CM) :
    ¬ ∃ o, Code (p v k) v o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p q_v0 q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_x (p q_v1 (p q_v1 q_v1))) at e2
      have cyc : q_v1 = (p q_v1 (p q_v1 q_v1)) := (let peq0 : v = (p q_v0 q_v1) := e0; let peq2 : v = (p q_x (p q_v1 (p q_v1 q_v1))) := e2; let pst0 : (p q_v0 q_v1) = v := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x (p q_v1 (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_v1 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); pst2)
      have hlt : sz q_v1 < sz (p q_v1 (p q_v1 q_v1)) := sz_lt_p_left q_v1 (p q_v1 q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change (p v k) = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v = (p q_x (p q_v1 (p q_v1 q_v1))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have badlt : sz q_v1 < sz q_H1 := by
        have structural : sz q_v1 < sz (p (p q_x (p q_v1 (p q_v1 q_v1))) k) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 (p q_v1 q_v1)) (sz_lt_p_right q_x (p q_v1 (p q_v1 q_v1)))) (sz_lt_p_left (p q_x (p q_v1 (p q_v1 q_v1))) k)
        have large_eq : sz q_v1 = sz q_v1 := congrArg sz (rfl)
        have small_eq : sz q_H1 = sz (p (p q_x (p q_v1 (p q_v1 q_v1))) k) := congrArg sz (Eq.trans (p0.symm) (congrArg (fun q => p q k) (p1)))
        exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB).elim
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have p0 := congrArg (fun q => (L q)) (ha)
      change v = q_H0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change k = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v = (p q_x (p q_v1 (p q_v1 q_v1))) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3
      omega
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change (p v k) = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v = (p q_x (p q_v1 (p q_v1 q_v1))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have badlt : sz q_v1 < sz q_H1 := by
        have structural : sz q_v1 < sz (p (p q_x (p q_v1 (p q_v1 q_v1))) k) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 (p q_v1 q_v1)) (sz_lt_p_right q_x (p q_v1 (p q_v1 q_v1)))) (sz_lt_p_left (p q_x (p q_v1 (p q_v1 q_v1))) k)
        have large_eq : sz q_v1 = sz q_v1 := congrArg sz (rfl)
        have small_eq : sz q_H1 = sz (p (p q_x (p q_v1 (p q_v1 q_v1))) k) := congrArg sz (Eq.trans (p0.symm) (congrArg (fun q => p q k) (p1)))
        exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
      exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB).elim
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p q_v0 q_v1) q_v1) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_x (p q_v1 (p q_v1 q_v1))) at e1
      have cyc : q_v1 = (p q_v1 (p q_v1 q_v1)) := (let peq0 : v1 = (p (p q_v0 q_v1) q_v1) := e0; let peq1 : v1 = (p q_x (p q_v1 (p q_v1 q_v1))) := e1; let pst0 : (p (p q_v0 q_v1) q_v1) = v1 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v1) q_v1) = (p q_x (p q_v1 (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p q_v1 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); pst2)
      have hlt : sz q_v1 < sz (p q_v1 (p q_v1 q_v1)) := sz_lt_p_left q_v1 (p q_v1 q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change v1 = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v1 = (p q_x (p q_v1 (p q_v1 q_v1))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB qs1hB z0 z1 z2
      omega
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p q_H0 q_v1) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_x (p q_v1 (p q_v1 q_v1))) at e1
      have cyc : q_v1 = (p q_v1 (p q_v1 q_v1)) := (let peq0 : v1 = (p q_H0 q_v1) := e0; let peq1 : v1 = (p q_x (p q_v1 (p q_v1 q_v1))) := e1; let pst0 : (p q_H0 q_v1) = v1 := Eq.symm (peq0); let pst1 : (p q_H0 q_v1) = (p q_x (p q_v1 (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p q_v1 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); pst2)
      have hlt : sz q_v1 < sz (p q_v1 (p q_v1 q_v1)) := sz_lt_p_left q_v1 (p q_v1 q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change v1 = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v1 = (p q_x (p q_v1 (p q_v1 q_v1))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2
      omega
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 (p v1 v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p q_v0 q_v1) q_v1) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v1 (p q_v1 q_v1)) at e2
      have cyc : q_v1 = (p q_v0 q_v1) := (let peq0 : v1 = (p (p q_v0 q_v1) q_v1) := e0; let peq2 : v1 = (p q_v1 (p q_v1 q_v1)) := e2; let pst0 : (p (p q_v0 q_v1) q_v1) = v1 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v1) q_v1) = (p q_v1 (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : (p q_v0 q_v1) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p q_v0 q_v1) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p q_v0 q_v1) := sz_lt_p_right q_v0 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change v1 = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change v1 = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change v1 = (p q_v1 (p q_v1 q_v1)) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs1hB z0 z1 z2 z3
      omega
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p q_H0 q_v1) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v1 (p q_v1 q_v1)) at e2
      have cyc : q_v1 = (p q_v1 q_v1) := (let peq0 : v1 = (p q_H0 q_v1) := e0; let peq2 : v1 = (p q_v1 (p q_v1 q_v1)) := e2; let pst0 : (p q_H0 q_v1) = v1 := Eq.symm (peq0); let pst1 : (p q_H0 q_v1) = (p q_v1 (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_v1 q_v1) := congrArg (fun q => R q) (pst1); pst2)
      have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change v1 = q_H1 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change v1 = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change v1 = (p q_v1 (p q_v1 q_v1)) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3
      omega
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x (p v1 (p v1 v1)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_v0 q_v1) q_v1) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = q_v1 at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p q_v1 q_v1) at e3
      have cyc : q_v1 = (p q_v1 q_v1) := (let peq1 : v1 = q_x := e1; let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p q_v1 q_v1) := e3; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = q_v1 := Eq.trans (pst0) (peq2); let pst2 : v1 = q_v1 := Eq.trans (peq1) (pst1); let pst3 : q_v1 = v1 := Eq.symm (pst2); let pst4 : q_v1 = (p q_v1 q_v1) := Eq.trans (pst3) (peq3); pst4)
      have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_H1 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = q_v1 at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p q_v1 q_v1) at e3
      have cyc : q_v1 = (p q_v1 q_v1) := (let peq1 : v1 = q_x := e1; let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p q_v1 q_v1) := e3; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = q_v1 := Eq.trans (pst0) (peq2); let pst2 : v1 = q_v1 := Eq.trans (peq1) (pst1); let pst3 : q_v1 = v1 := Eq.symm (pst2); let pst4 : q_v1 = (p q_v1 q_v1) := Eq.trans (pst3) (peq3); pst4)
      have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_H0 q_v1) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = q_v1 at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p q_v1 q_v1) at e3
      have cyc : q_v1 = (p q_v1 q_v1) := (let peq1 : v1 = q_x := e1; let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p q_v1 q_v1) := e3; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = q_v1 := Eq.trans (pst0) (peq2); let pst2 : v1 = q_v1 := Eq.trans (peq1) (pst1); let pst3 : q_v1 = v1 := Eq.symm (pst2); let pst4 : q_v1 = (p q_v1 q_v1) := Eq.trans (pst3) (peq3); pst4)
      have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_H1 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = q_v1 at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p q_v1 q_v1) at e3
      have cyc : q_v1 = (p q_v1 q_v1) := (let peq1 : v1 = q_x := e1; let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p q_v1 q_v1) := e3; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = q_v1 := Eq.trans (pst0) (peq2); let pst2 : v1 = q_v1 := Eq.trans (peq1) (pst1); let pst3 : q_v1 = v1 := Eq.symm (pst2); let pst4 : q_v1 = (p q_v1 q_v1) := Eq.trans (pst3) (peq3); pst4)
      have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 v1) v1) (eval x (eval v1 (eval v1 v1)))) := by
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
  let H1 := eval (eval v0 v1) v1
  have e1a : (eval v0 v1) = H0 := by
    change H0 = H0
    rfl
  have e1b : v1 = v1 := by
    change v1 = v1
    rfl
  have s1 : Step H0 v1 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v0 v1) v1
  change x = (eval H1 (eval x (eval v1 (eval v1 v1))))
  have rawEq : (eval H1 (eval x (eval v1 (eval v1 v1)))) = (eval H1 (p x (p v1 (p v1 v1)))) := by
    calc
      (eval H1 (eval x (eval v1 (eval v1 v1)))) = (eval H1 (eval x (eval v1 (p v1 v1)))) := congrArg (fun q => (eval H1 (eval x (eval v1 q)))) (eval_raw (nr0 x v0 v1))
      _ = (eval H1 (eval x (p v1 (p v1 v1)))) := congrArg (fun q => (eval H1 (eval x q))) (eval_raw (nr1 x v0 v1))
      _ = (eval H1 (p x (p v1 (p v1 v1)))) := congrArg (fun q => (eval H1 q)) (eval_raw (nr2 x v0 v1))
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
