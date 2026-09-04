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
  | law (x v0 v1 H0 : CM)
      (s0 : Step v0 v1 H0) :
      Code (p (p (p (p H0 v0) v1) (p x x)) v1) v1 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_v1 q_H0 ∧ a = (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) ∧ b = q_v1 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R (L a)))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code H0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v1 = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v1 at e2
      have cyc : q_v1 = (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) := (let peq0 : v0 = (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v1)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v1 = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v1 at e2
      have cyc : q_v1 = (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) := (let peq0 : v0 = (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_v0) q_v1) (sz_lt_p_left (p (p q_H0 q_v0) q_v1) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change H0 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB s0hB s0B qs0B z0 z1 z2
      omega
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change H0 = (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2
      omega
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p H0 v0) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p (p (p q_v0 q_v1) q_v0) q_v1) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v1 = (p q_x q_x) at e1
      have e2 := congrArg (fun q => (R q)) ha
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => q) hb
      change v1 = q_v1 at e3
      have cyc : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v1) := (let peq0 : v0 = (p (p (p q_v0 q_v1) q_v0) q_v1) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_v0 q_v1) q_v0) q_v1) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) q_v1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v1) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p q_v0 q_v1) q_v0) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p (p q_H0 q_v0) q_v1) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v1 = (p q_x q_x) at e1
      have e2 := congrArg (fun q => (R q)) ha
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => q) hb
      change v1 = q_v1 at e3
      have cyc : q_v1 = (p (p q_H0 q_v0) q_v1) := (let peq0 : v0 = (p (p q_H0 q_v0) q_v1) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p q_H0 q_v0) q_v1) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) q_v1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p q_H0 q_v0) q_v1) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p q_H0 q_v0) q_v1) := sz_lt_p_right (p q_H0 q_v0) q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L q)) (ha)
      change H0 = (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v1 = q_v1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB s0hB s0B qs0B z0 z1 z2 z3
      omega
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L q)) (ha)
      change H0 = (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v1 = q_v1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2 z3
      omega
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v1 at e1
    have cyc : q_v1 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) := (let peq0 : x = (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) := e0; let peq1 : x = q_v1 := e1; let pst0 : (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) = x := Eq.symm (peq0); let pst1 : (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) = q_v1 := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) := Eq.symm (pst1); pst2)
    have hlt : sz q_v1 < sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v1)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x))) (sz_lt_p_left (p (p (p (p q_v0 q_v1) q_v0) q_v1) (p q_x q_x)) q_v1)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v1 at e1
    have cyc : q_v1 = (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) := (let peq0 : x = (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) := e0; let peq1 : x = q_v1 := e1; let pst0 : (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) = q_v1 := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) := Eq.symm (pst1); pst2)
    have hlt : sz q_v1 < sz (p (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p q_H0 q_v0) q_v1) (sz_lt_p_left (p (p q_H0 q_v0) q_v1) (p q_x q_x))) (sz_lt_p_left (p (p (p q_H0 q_v0) q_v1) (p q_x q_x)) q_v1)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p H0 v0) v1) (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_v0 := (let peq0 : v0 = (p q_H0 q_v0) := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let pst0 : (p q_H0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 q_v0) = (p q_x q_x) := Eq.trans (pst0) (peq2); let pst2 : q_H0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst4 : q_x = q_v0 := Eq.symm (pst3); let pst5 : q_H0 = q_v0 := Eq.trans (pst2) (pst4); pst5)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v1 = (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := (let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq5 : v0 = (p (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := u0a; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_x) = (p (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := Eq.trans (pst0) (peq5); let pst2 : q_x = (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) = q_x := Eq.symm (pst2); let pst4 : q_x = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0_v0 u0_v1) (sz_lt_p_left (p u0_v0 u0_v1) u0_v0)) (sz_lt_p_left (p (p u0_v0 u0_v1) u0_v0) u0_v1)) (sz_lt_p_left (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v1 = (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := (let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq5 : v0 = (p (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := u0a; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_x) = (p (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := Eq.trans (pst0) (peq5); let pst2 : q_x = (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) = q_x := Eq.symm (pst2); let pst4 : q_x = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := Nat.lt_trans (sz_lt_p_right (p u0s0out u0_v0) u0_v1) (sz_lt_p_left (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v1 = (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := (let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq5 : v0 = (p (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := u0a; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_x) = (p (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := Eq.trans (pst0) (peq5); let pst2 : q_x = (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) = q_x := Eq.symm (pst2); let pst4 : q_x = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0_v0 u0_v1) (sz_lt_p_left (p u0_v0 u0_v1) u0_v0)) (sz_lt_p_left (p (p u0_v0 u0_v1) u0_v0) u0_v1)) (sz_lt_p_left (p (p (p u0_v0 u0_v1) u0_v0) u0_v1) (p u0_x u0_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v1 = (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := (let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq5 : v0 = (p (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := u0a; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_x) = (p (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) u0_v1) := Eq.trans (pst0) (peq5); let pst2 : q_x = (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) = q_x := Eq.symm (pst2); let pst4 : q_x = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x)) := Nat.lt_trans (sz_lt_p_right (p u0s0out u0_v0) u0_v1) (sz_lt_p_left (p (p u0s0out u0_v0) u0_v1) (p u0_x u0_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p (p H0 v0) v1) (p x x)) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_v0 := (let peq0 : v0 = q_H0 := congrArg (fun q => (L (L (L (L q))))) (ha); let peq1 : v1 = q_v0 := congrArg (fun q => (R (L (L (L q))))) (ha); let peq2 : v0 = q_v1 := congrArg (fun q => (R (L (L q)))) (ha); let peq3 : v1 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq4 : (p x x) = q_v1 := congrArg (fun q => (R q)) (ha); let peq5 : v1 = q_v1 := hb; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p x x) := Eq.symm (peq4); let pst3 : q_H0 = (p x x) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = v1 := Eq.symm (peq1); let pst5 : q_v0 = (p q_x q_x) := Eq.trans (pst4) (peq3); let pst6 : v1 = (p q_x q_x) := Eq.trans (peq1) (pst5); let pst7 : (p q_x q_x) = v1 := Eq.symm (pst6); let pst8 : (p q_x q_x) = q_v1 := Eq.trans (pst7) (peq5); let pst9 : (p q_x q_x) = (p x x) := Eq.trans (pst8) (pst2); let pst10 : q_x = x := congrArg (fun q => L q) (pst9); let pst11 : (p q_x q_x) = (p x q_x) := congrArg (fun q => p q q_x) (pst10); let pst12 : (p x q_x) = (p x x) := congrArg (fun q => p x q) (pst10); let pst13 : (p q_x q_x) = (p x x) := Eq.trans (pst11) (pst12); let pst14 : q_v0 = (p x x) := Eq.trans (pst5) (pst13); let pst15 : (p x x) = q_v0 := Eq.symm (pst14); let pst16 : q_H0 = q_v0 := Eq.trans (pst3) (pst15); pst16)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L (L (L q)))) (ha)
      change H0 = (p (p q_v0 q_v1) q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L (L q)))) (ha)
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R (L q))) (ha)
      change v1 = (p q_x q_x) at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R q)) (ha)
      change (p x x) = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := hb
      change v1 = q_v1 at p4
      have z4 := congrArg sz p4
      have p5 := ho
      change o = q_x at p5
      have z5 := congrArg sz p5
      simp only [getOut, L, R, U, sz] at hcB s0hB s0B qs0B z0 z1 z2 z3 z4 z5
      omega
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L (L (L q)))) (ha)
      change H0 = (p q_H0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L (L q)))) (ha)
      change v0 = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R (L q))) (ha)
      change v1 = (p q_x q_x) at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R q)) (ha)
      change (p x x) = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := hb
      change v1 = q_v1 at p4
      have z4 := congrArg sz p4
      have p5 := ho
      change o = q_x at p5
      have z5 := congrArg sz p5
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2 z3 z4 z5
      omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval (eval v0 v1) v0) v1) (eval x x)) v1) v1) := by
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
  change x = (eval (eval (eval (eval (eval H0 v0) v1) (eval x x)) v1) v1)
  have rawEq : (eval (eval (eval (eval (eval H0 v0) v1) (eval x x)) v1) v1) = (eval (p (p (p (p H0 v0) v1) (p x x)) v1) v1) := by
    calc
      (eval (eval (eval (eval (eval H0 v0) v1) (eval x x)) v1) v1) = (eval (eval (eval (eval (p H0 v0) v1) (eval x x)) v1) v1) := congrArg (fun q => (eval (eval (eval (eval q v1) (eval x x)) v1) v1)) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval (eval (eval (p (p H0 v0) v1) (eval x x)) v1) v1) := congrArg (fun q => (eval (eval (eval q (eval x x)) v1) v1)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval (eval (p (p H0 v0) v1) (p x x)) v1) v1) := congrArg (fun q => (eval (eval (eval (p (p H0 v0) v1) q) v1) v1)) (eval_raw (nr2 x v0 v1))
      _ = (eval (eval (p (p (p H0 v0) v1) (p x x)) v1) v1) := congrArg (fun q => (eval (eval q v1) v1)) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval (p (p (p (p H0 v0) v1) (p x x)) v1) v1) := congrArg (fun q => (eval q v1)) (eval_raw (nr4 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
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
