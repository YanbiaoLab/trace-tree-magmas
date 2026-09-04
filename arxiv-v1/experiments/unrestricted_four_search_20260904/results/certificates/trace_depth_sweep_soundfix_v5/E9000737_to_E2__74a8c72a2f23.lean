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
      (s0 : Step v1 v2 H0)
      (s1 : Step v0 H0 H1)
      (s2 : Step H1 v1 H2)
      (s3 : Step H2 v2 H3) :
      Code H3 (p x (p v2 (p v2 v2))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 q_H2 q_H3 : CM, Step q_v1 q_v2 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ Step q_H1 q_v1 q_H2 ∧ Step q_H2 q_v2 q_H3 ∧ a = q_H3 ∧ b = (p q_x (p q_v2 (p q_v2 q_v2))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 H2 H3 s0 s1 s2 s3 => ⟨x, v0, v1, v2, H0, H1, H2, H3, s0, s1, s2, s3, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L b)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, s0, s1, s2, s3, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code v2 v2 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs3hB z0 z1 z2
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs2hB qs3hB z0 z1 z2
          omega
    | hit qs1h =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p q_H1 q_v1) q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p (p q_H1 q_v1) q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p (p q_H1 q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v1) q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs1hB := code_bounds qs1h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs1hB qs3hB z0 z1 z2
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs1hB qs2hB qs3hB z0 z1 z2
          omega
  | hit qs0h =>
    cases qs1 with
    | raw =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p (p q_v0 q_H0) q_v1) q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p (p (p q_v0 q_H0) q_v1) q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p (p (p q_v0 q_H0) q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v1) q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs3hB z0 z1 z2
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs2hB qs3hB z0 z1 z2
          omega
    | hit qs1h =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p q_H1 q_v1) q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p (p q_H1 q_v1) q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p (p q_H1 q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v1) q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs3hB z0 z1 z2
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => q) hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at e1
          have cyc : q_v2 = (p q_v2 (p q_v2 q_v2)) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq1 : v2 = (p q_x (p q_v2 (p q_v2 q_v2))) := e1; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_x (p q_v2 (p q_v2 q_v2))) := Eq.trans (pst0) (peq1); let pst2 : q_v2 = (p q_v2 (p q_v2 q_v2)) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 (p q_v2 q_v2)) := sz_lt_p_left q_v2 (p q_v2 q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change v2 = (p q_x (p q_v2 (p q_v2 q_v2))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs2hB qs3hB z0 z1 z2
          omega
theorem nr1 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code v2 (p v2 v2) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_v2 = (p (p q_v0 (p q_v1 q_v2)) q_v1) := (let peq0 : v2 = (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : (p (p q_v0 (p q_v1 q_v2)) q_v1) = q_v2 := congrArg (fun q => L q) (pst1); let pst3 : q_v2 = (p (p q_v0 (p q_v1 q_v2)) q_v1) := Eq.symm (pst2); pst3)
          have hlt : sz q_v2 < sz (p (p q_v0 (p q_v1 q_v2)) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v1 q_v2) (sz_lt_p_right q_v0 (p q_v1 q_v2))) (sz_lt_p_left (p q_v0 (p q_v1 q_v2)) q_v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs3hB z0 z1 z2 z3
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs2hB qs3hB z0 z1 z2 z3
          omega
    | hit qs1h =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p q_H1 q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_H1 = (p q_H1 q_v1) := (let peq0 : v2 = (p (p q_H1 q_v1) q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p (p q_H1 q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v1) q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : (p q_H1 q_v1) = q_v2 := congrArg (fun q => L q) (pst1); let pst3 : q_v2 = (p q_H1 q_v1) := Eq.symm (pst2); let pst4 : (p q_H1 q_v1) = q_v2 := Eq.symm (pst3); let pst5 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); let pst6 : (p q_H1 q_v1) = (p q_v2 q_v2) := Eq.trans (pst4) (pst5); let pst7 : (p q_v2 q_v2) = (p (p q_H1 q_v1) q_v2) := congrArg (fun q => p q q_v2) (pst3); let pst8 : (p (p q_H1 q_v1) q_v2) = (p (p q_H1 q_v1) (p q_H1 q_v1)) := congrArg (fun q => p (p q_H1 q_v1) q) (pst3); let pst9 : (p q_v2 q_v2) = (p (p q_H1 q_v1) (p q_H1 q_v1)) := Eq.trans (pst7) (pst8); let pst10 : (p q_H1 q_v1) = (p (p q_H1 q_v1) (p q_H1 q_v1)) := Eq.trans (pst6) (pst9); let pst11 : q_H1 = (p q_H1 q_v1) := congrArg (fun q => L q) (pst10); pst11)
          have hlt : sz q_H1 < sz (p q_H1 q_v1) := sz_lt_p_left q_H1 q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs1hB := code_bounds qs1h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs1hB qs3hB z0 z1 z2 z3
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs1hB qs2hB qs3hB z0 z1 z2 z3
          omega
  | hit qs0h =>
    cases qs1 with
    | raw =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p (p q_v0 q_H0) q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_v0 = (p q_v0 q_H0) := (let peq0 : v2 = (p (p (p q_v0 q_H0) q_v1) q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p (p (p q_v0 q_H0) q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v1) q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : (p (p q_v0 q_H0) q_v1) = q_v2 := congrArg (fun q => L q) (pst1); let pst3 : q_v2 = (p (p q_v0 q_H0) q_v1) := Eq.symm (pst2); let pst4 : (p (p q_v0 q_H0) q_v1) = q_v2 := Eq.symm (pst3); let pst5 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_v0 q_H0) q_v1) = (p q_v2 q_v2) := Eq.trans (pst4) (pst5); let pst7 : (p q_v2 q_v2) = (p (p (p q_v0 q_H0) q_v1) q_v2) := congrArg (fun q => p q q_v2) (pst3); let pst8 : (p (p (p q_v0 q_H0) q_v1) q_v2) = (p (p (p q_v0 q_H0) q_v1) (p (p q_v0 q_H0) q_v1)) := congrArg (fun q => p (p (p q_v0 q_H0) q_v1) q) (pst3); let pst9 : (p q_v2 q_v2) = (p (p (p q_v0 q_H0) q_v1) (p (p q_v0 q_H0) q_v1)) := Eq.trans (pst7) (pst8); let pst10 : (p (p q_v0 q_H0) q_v1) = (p (p (p q_v0 q_H0) q_v1) (p (p q_v0 q_H0) q_v1)) := Eq.trans (pst6) (pst9); let pst11 : (p q_v0 q_H0) = (p (p q_v0 q_H0) q_v1) := congrArg (fun q => L q) (pst10); let pst12 : q_v0 = (p q_v0 q_H0) := congrArg (fun q => L q) (pst11); pst12)
          have hlt : sz q_v0 < sz (p q_v0 q_H0) := sz_lt_p_left q_v0 q_H0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs3hB z0 z1 z2 z3
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs2hB qs3hB z0 z1 z2 z3
          omega
    | hit qs1h =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p (p q_H1 q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_H1 = (p q_H1 q_v1) := (let peq0 : v2 = (p (p q_H1 q_v1) q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p (p q_H1 q_v1) q_v2) = v2 := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v1) q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : (p q_H1 q_v1) = q_v2 := congrArg (fun q => L q) (pst1); let pst3 : q_v2 = (p q_H1 q_v1) := Eq.symm (pst2); let pst4 : (p q_H1 q_v1) = q_v2 := Eq.symm (pst3); let pst5 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); let pst6 : (p q_H1 q_v1) = (p q_v2 q_v2) := Eq.trans (pst4) (pst5); let pst7 : (p q_v2 q_v2) = (p (p q_H1 q_v1) q_v2) := congrArg (fun q => p q q_v2) (pst3); let pst8 : (p (p q_H1 q_v1) q_v2) = (p (p q_H1 q_v1) (p q_H1 q_v1)) := congrArg (fun q => p (p q_H1 q_v1) q) (pst3); let pst9 : (p q_v2 q_v2) = (p (p q_H1 q_v1) (p q_H1 q_v1)) := Eq.trans (pst7) (pst8); let pst10 : (p q_H1 q_v1) = (p (p q_H1 q_v1) (p q_H1 q_v1)) := Eq.trans (pst6) (pst9); let pst11 : q_H1 = (p q_H1 q_v1) := congrArg (fun q => L q) (pst10); pst11)
          have hlt : sz q_H1 < sz (p q_H1 q_v1) := sz_lt_p_left q_H1 q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs3hB z0 z1 z2 z3
          omega
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v2 = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v2 = (p q_v2 (p q_v2 q_v2)) at e2
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq0 : v2 = (p q_H2 q_v2) := e0; let peq2 : v2 = (p q_v2 (p q_v2 q_v2)) := e2; let pst0 : (p q_H2 q_v2) = v2 := Eq.symm (peq0); let pst1 : (p q_H2 q_v2) = (p q_v2 (p q_v2 q_v2)) := Eq.trans (pst0) (peq2); let pst2 : q_v2 = (p q_v2 q_v2) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have qs3hB := code_bounds qs3h
          have p0 := ha
          change v2 = q_H3 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v2 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change v2 = (p q_v2 (p q_v2 q_v2)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs2hB qs3hB z0 z1 z2 z3
          omega
theorem nr2 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code x (p v2 (p v2 v2)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p (p q_v0 (p q_v1 q_v2)) q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p q_H1 q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p (p q_v0 q_H0) q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      cases qs2 with
      | raw =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p (p q_H1 q_v1) q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        cases qs3 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change x = (p q_H2 q_v2) at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have e0 := congrArg (fun q => q) ha
          change x = q_H3 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v2 = q_x at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v2 = q_v2 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v2 = (p q_v2 q_v2) at e3
          have cyc : q_v2 = (p q_v2 q_v2) := (let peq1 : v2 = q_x := e1; let peq2 : v2 = q_v2 := e2; let peq3 : v2 = (p q_v2 q_v2) := e3; let pst0 : q_x = v2 := Eq.symm (peq1); let pst1 : q_x = q_v2 := Eq.trans (pst0) (peq2); let pst2 : v2 = q_v2 := Eq.trans (peq1) (pst1); let pst3 : q_v2 = v2 := Eq.symm (pst2); let pst4 : q_v2 = (p q_v2 q_v2) := Eq.trans (pst3) (peq3); pst4)
          have hlt : sz q_v2 < sz (p q_v2 q_v2) := sz_lt_p_left q_v2 q_v2
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval (eval (eval v0 (eval v1 v2)) v1) v2) (eval x (eval v2 (eval v2 v2)))) := by
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
  let H2 := eval (eval v0 (eval v1 v2)) v1
  have e2a : (eval v0 (eval v1 v2)) = H1 := by
    change H1 = H1
    rfl
  have e2b : v1 = v1 := by
    change v1 = v1
    rfl
  have s2 : Step H1 v1 H2 := by
    rw [← e2a, ← e2b]
    exact eval_step (eval v0 (eval v1 v2)) v1
  let H3 := eval (eval (eval v0 (eval v1 v2)) v1) v2
  have e3a : (eval (eval v0 (eval v1 v2)) v1) = H2 := by
    change H2 = H2
    rfl
  have e3b : v2 = v2 := by
    change v2 = v2
    rfl
  have s3 : Step H2 v2 H3 := by
    rw [← e3a, ← e3b]
    exact eval_step (eval (eval v0 (eval v1 v2)) v1) v2
  change x = (eval H3 (eval x (eval v2 (eval v2 v2))))
  have rawEq : (eval H3 (eval x (eval v2 (eval v2 v2)))) = (eval H3 (p x (p v2 (p v2 v2)))) := by
    calc
      (eval H3 (eval x (eval v2 (eval v2 v2)))) = (eval H3 (eval x (eval v2 (p v2 v2)))) := congrArg (fun q => (eval H3 (eval x (eval v2 q)))) (eval_raw (nr0 x v0 v1 v2))
      _ = (eval H3 (eval x (p v2 (p v2 v2)))) := congrArg (fun q => (eval H3 (eval x q))) (eval_raw (nr1 x v0 v1 v2))
      _ = (eval H3 (p x (p v2 (p v2 v2)))) := congrArg (fun q => (eval H3 q)) (eval_raw (nr2 x v0 v1 v2))
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
