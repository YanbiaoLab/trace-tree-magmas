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
  | law (x v0 v1 v2 H0 : CM)
      (s0 : Step v0 v1 H0) :
      Code (p (p (p H0 v0) (p (p x x) v2)) (p v0 v0)) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 : CM, Step q_v0 q_v1 q_H0 ∧ a = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 s0 => ⟨x, v0, v1, v2, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R (L a))))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, s0, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 v2 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code H0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v1 = (p q_v0 q_v0) at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) := (let peq0 : v0 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v1 = (p q_v0 q_v0) at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) := (let peq0 : v0 = (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) := Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p (p q_x q_x) q_v2))
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
      change H0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_v0 at p1
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
      change H0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v0 = q_v0 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2
      omega
theorem nr1 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v0 at e1
    have cyc : q_v0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := (let peq0 : x = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2))) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := (let peq0 : x = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p (p q_x q_x) q_v2))) (sz_lt_p_left (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code (p x x) v2 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => (L q)) ha
    change x = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) at e0
    have e1 := congrArg (fun q => (R q)) ha
    change x = (p q_v0 q_v0) at e1
    have e2 := congrArg (fun q => q) hb
    change v2 = q_v0 at e2
    have cyc : q_v0 = (p (p q_v0 q_v1) q_v0) := (let peq0 : x = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) := e0; let peq1 : x = (p q_v0 q_v0) := e1; let pst0 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v1) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p q_v0 q_v1) q_v0) := Eq.symm (pst2); pst3)
    have hlt : sz q_v0 < sz (p (p q_v0 q_v1) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => (L q)) ha
    change x = (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) at e0
    have e1 := congrArg (fun q => (R q)) ha
    change x = (p q_v0 q_v0) at e1
    have e2 := congrArg (fun q => q) hb
    change v2 = q_v0 at e2
    have cyc : q_v0 = (p q_H0 q_v0) := (let peq0 : x = (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) := e0; let peq1 : x = (p q_v0 q_v0) := e1; let pst0 : (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) = x := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_H0 q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_H0 q_v0) := Eq.symm (pst2); pst3)
    have hlt : sz q_v0 < sz (p q_H0 q_v0) := sz_lt_p_right q_H0 q_v0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 v2 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p H0 v0) (p (p x x) v2) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_v0 := (let peq0 : v0 = (p q_H0 q_v0) := congrArg (fun q => (L (L q))) (ha); let peq2 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq3 : (p (p x x) v2) = q_v0 := hb; let pst0 : (p q_H0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 q_v0) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_H0 = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p x x) v2) := Eq.symm (peq3); let pst4 : q_H0 = (p (p x x) v2) := Eq.trans (pst2) (pst3); let pst5 : (p (p x x) v2) = q_v0 := Eq.symm (pst3); let pst6 : q_H0 = q_v0 := Eq.trans (pst4) (pst5); pst6)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L q)) (ha)
      change H0 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change v0 = (p q_v0 q_v0) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change (p (p x x) v2) = q_v0 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB s0hB s0B qs0B z0 z1 z2 z3
      omega
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p u0_v0 u0_v1) := (let peq1 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq2 : (p (p x x) v2) = q_v0 := hb; let peq4 : v0 = (p (p (p (p u0_v0 u0_v1) u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := u0a; let pst0 : q_v0 = (p (p x x) v2) := Eq.symm (peq2); let pst1 : (p q_v0 q_v0) = (p (p (p x x) v2) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p (p x x) v2) q_v0) = (p (p (p x x) v2) (p (p x x) v2)) := congrArg (fun q => p (p (p x x) v2) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p (p x x) v2) (p (p x x) v2)) := Eq.trans (pst1) (pst2); let pst4 : v0 = (p (p (p x x) v2) (p (p x x) v2)) := Eq.trans (peq1) (pst3); let pst5 : (p (p (p x x) v2) (p (p x x) v2)) = v0 := Eq.symm (pst4); let pst6 : (p (p (p x x) v2) (p (p x x) v2)) = (p (p (p (p u0_v0 u0_v1) u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := Eq.trans (pst5) (peq4); let pst7 : (p (p x x) v2) = (p (p (p u0_v0 u0_v1) u0_v0) (p (p u0_x u0_x) u0_v2)) := congrArg (fun q => L q) (pst6); let pst8 : (p x x) = (p (p u0_v0 u0_v1) u0_v0) := congrArg (fun q => L q) (pst7); let pst9 : x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst8); let pst10 : (p u0_v0 u0_v1) = x := Eq.symm (pst9); let pst11 : x = u0_v0 := congrArg (fun q => R q) (pst8); let pst12 : (p u0_v0 u0_v1) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p u0_v0 u0_v1) := Eq.symm (pst12); pst13)
        have hlt : sz u0_v0 < sz (p u0_v0 u0_v1) := sz_lt_p_left u0_v0 u0_v1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p u0_v0 u0_v0) := (let peq1 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (ha); let peq2 : (p (p x x) v2) = q_v0 := hb; let peq4 : v0 = (p (p (p u0s0out u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := u0a; let pst0 : q_v0 = (p (p x x) v2) := Eq.symm (peq2); let pst1 : (p q_v0 q_v0) = (p (p (p x x) v2) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p (p x x) v2) q_v0) = (p (p (p x x) v2) (p (p x x) v2)) := congrArg (fun q => p (p (p x x) v2) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p (p x x) v2) (p (p x x) v2)) := Eq.trans (pst1) (pst2); let pst4 : v0 = (p (p (p x x) v2) (p (p x x) v2)) := Eq.trans (peq1) (pst3); let pst5 : (p (p (p x x) v2) (p (p x x) v2)) = v0 := Eq.symm (pst4); let pst6 : (p (p (p x x) v2) (p (p x x) v2)) = (p (p (p u0s0out u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := Eq.trans (pst5) (peq4); let pst7 : (p (p x x) v2) = (p (p u0s0out u0_v0) (p (p u0_x u0_x) u0_v2)) := congrArg (fun q => L q) (pst6); let pst8 : (p x x) = (p u0s0out u0_v0) := congrArg (fun q => L q) (pst7); let pst9 : x = u0s0out := congrArg (fun q => L q) (pst8); let pst10 : u0s0out = x := Eq.symm (pst9); let pst11 : x = u0_v0 := congrArg (fun q => R q) (pst8); let pst12 : u0s0out = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : x = u0_v0 := Eq.trans (pst9) (pst12); let pst14 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (pst13); let pst15 : x = u0_v0 := Eq.trans (pst9) (pst12); let pst16 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst15); let pst17 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst14) (pst16); let pst18 : (p (p x x) v2) = (p (p u0_v0 u0_v0) v2) := congrArg (fun q => p q v2) (pst17); let pst19 : v2 = (p (p u0_x u0_x) u0_v2) := congrArg (fun q => R q) (pst7); let pst20 : (p (p u0_v0 u0_v0) v2) = (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst19); let pst21 : (p (p x x) v2) = (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) := Eq.trans (pst18) (pst20); let pst22 : (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) = (p (p x x) v2) := Eq.symm (pst21); let pst23 : (p (p x x) v2) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst6); let pst24 : (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) = (p u0_v0 u0_v0) := Eq.trans (pst22) (pst23); let pst25 : (p u0_v0 u0_v0) = u0_v0 := congrArg (fun q => L q) (pst24); let pst26 : u0_v0 = (p u0_v0 u0_v0) := Eq.symm (pst25); pst26)
        have hlt : sz u0_v0 < sz (p u0_v0 u0_v0) := sz_lt_p_left u0_v0 u0_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2))) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := (let peq0 : v0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p (p q_x q_x) q_v2))) (sz_lt_p_left (p (p q_H0 q_v0) (p (p q_x q_x) q_v2)) (p q_v0 q_v0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr5 (x v0 v1 v2 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p H0 v0) (p (p x x) v2)) (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L (L q)))) ha
      change v0 = (p q_v0 q_v1) at e0
      have e1 := congrArg (fun q => (R (L (L q)))) ha
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (R (L q))) ha
      change v0 = (p (p q_x q_x) q_v2) at e2
      have e3 := congrArg (fun q => (L (R q))) ha
      change (p x x) = q_v0 at e3
      have e4 := congrArg (fun q => (R (R q))) ha
      change v2 = q_v0 at e4
      have e5 := congrArg (fun q => q) hb
      change (p v0 v0) = q_v0 at e5
      have cyc : q_x = (p (p q_x q_x) q_v2) := (let peq0 : v0 = (p q_v0 q_v1) := e0; let peq2 : v0 = (p (p q_x q_x) q_v2) := e2; let peq5 : (p v0 v0) = q_v0 := e5; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p (p q_x q_x) q_v2) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x q_x) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p (p q_x q_x) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_v2 := congrArg (fun q => R q) (pst1); let pst5 : (p (p q_x q_x) q_v1) = (p (p q_x q_x) q_v2) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst6 : (p q_v0 q_v1) = (p (p q_x q_x) q_v2) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p (p q_x q_x) q_v2) := Eq.trans (peq0) (pst6); let pst8 : (p v0 v0) = (p (p (p q_x q_x) q_v2) v0) := congrArg (fun q => p q v0) (pst7); let pst9 : (p q_v0 q_v1) = (p (p q_x q_x) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst10 : (p (p q_x q_x) q_v1) = (p (p q_x q_x) q_v2) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst11 : (p q_v0 q_v1) = (p (p q_x q_x) q_v2) := Eq.trans (pst9) (pst10); let pst12 : v0 = (p (p q_x q_x) q_v2) := Eq.trans (peq0) (pst11); let pst13 : (p (p (p q_x q_x) q_v2) v0) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := congrArg (fun q => p (p (p q_x q_x) q_v2) q) (pst12); let pst14 : (p v0 v0) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst8) (pst13); let pst15 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p v0 v0) := Eq.symm (pst14); let pst16 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = q_v0 := Eq.trans (pst15) (peq5); let pst17 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p q_x q_x) := Eq.trans (pst16) (pst2); let pst18 : (p (p q_x q_x) q_v2) = q_x := congrArg (fun q => L q) (pst17); let pst19 : q_x = (p (p q_x q_x) q_v2) := Eq.symm (pst18); pst19)
      have hlt : sz q_x < sz (p (p q_x q_x) q_v2) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v2)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p u0_v0 u0_v1) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = (p (p q_x q_x) q_v2) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p x x) = q_v0 := congrArg (fun q => (L (R q))) (ha); let peq5 : (p v0 v0) = q_v0 := hb; let peq7 : q_v0 = (p (p (p (p u0_v0 u0_v1) u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := u0a; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : q_H0 = v0 := Eq.symm (peq0); let pst2 : q_H0 = (p (p q_x q_x) q_v2) := Eq.trans (pst1) (peq2); let pst3 : v0 = (p (p q_x q_x) q_v2) := Eq.trans (peq0) (pst2); let pst4 : (p v0 v0) = (p (p (p q_x q_x) q_v2) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p (p q_x q_x) q_v2) := Eq.trans (peq0) (pst2); let pst6 : (p (p (p q_x q_x) q_v2) v0) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := congrArg (fun q => p (p (p q_x q_x) q_v2) q) (pst5); let pst7 : (p v0 v0) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst4) (pst6); let pst8 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p v0 v0) := Eq.symm (pst7); let pst9 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = q_v0 := Eq.trans (pst8) (peq5); let pst10 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p x x) := Eq.trans (pst9) (pst0); let pst11 : (p (p q_x q_x) q_v2) = x := congrArg (fun q => L q) (pst10); let pst12 : x = (p (p q_x q_x) q_v2) := Eq.symm (pst11); let pst13 : (p x x) = (p (p (p q_x q_x) q_v2) x) := congrArg (fun q => p q x) (pst12); let pst14 : (p (p (p q_x q_x) q_v2) x) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := congrArg (fun q => p (p (p q_x q_x) q_v2) q) (pst12); let pst15 : (p x x) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst13) (pst14); let pst16 : q_v0 = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst0) (pst15); let pst17 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = q_v0 := Eq.symm (pst16); let pst18 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p (p (p (p u0_v0 u0_v1) u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := Eq.trans (pst17) (peq7); let pst19 : (p (p q_x q_x) q_v2) = (p (p (p u0_v0 u0_v1) u0_v0) (p (p u0_x u0_x) u0_v2)) := congrArg (fun q => L q) (pst18); let pst20 : (p q_x q_x) = (p (p u0_v0 u0_v1) u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst20); let pst22 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst21); let pst23 : q_x = u0_v0 := congrArg (fun q => R q) (pst20); let pst24 : (p u0_v0 u0_v1) = u0_v0 := Eq.trans (pst22) (pst23); let pst25 : u0_v0 = (p u0_v0 u0_v1) := Eq.symm (pst24); pst25)
        have hlt : sz u0_v0 < sz (p u0_v0 u0_v1) := sz_lt_p_left u0_v0 u0_v1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p u0_v0 u0_v0) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = (p (p q_x q_x) q_v2) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p x x) = q_v0 := congrArg (fun q => (L (R q))) (ha); let peq5 : (p v0 v0) = q_v0 := hb; let peq7 : q_v0 = (p (p (p u0s0out u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := u0a; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : q_H0 = v0 := Eq.symm (peq0); let pst2 : q_H0 = (p (p q_x q_x) q_v2) := Eq.trans (pst1) (peq2); let pst3 : v0 = (p (p q_x q_x) q_v2) := Eq.trans (peq0) (pst2); let pst4 : (p v0 v0) = (p (p (p q_x q_x) q_v2) v0) := congrArg (fun q => p q v0) (pst3); let pst5 : v0 = (p (p q_x q_x) q_v2) := Eq.trans (peq0) (pst2); let pst6 : (p (p (p q_x q_x) q_v2) v0) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := congrArg (fun q => p (p (p q_x q_x) q_v2) q) (pst5); let pst7 : (p v0 v0) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst4) (pst6); let pst8 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p v0 v0) := Eq.symm (pst7); let pst9 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = q_v0 := Eq.trans (pst8) (peq5); let pst10 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p x x) := Eq.trans (pst9) (pst0); let pst11 : (p (p q_x q_x) q_v2) = x := congrArg (fun q => L q) (pst10); let pst12 : x = (p (p q_x q_x) q_v2) := Eq.symm (pst11); let pst13 : (p x x) = (p (p (p q_x q_x) q_v2) x) := congrArg (fun q => p q x) (pst12); let pst14 : (p (p (p q_x q_x) q_v2) x) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := congrArg (fun q => p (p (p q_x q_x) q_v2) q) (pst12); let pst15 : (p x x) = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst13) (pst14); let pst16 : q_v0 = (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) := Eq.trans (pst0) (pst15); let pst17 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = q_v0 := Eq.symm (pst16); let pst18 : (p (p (p q_x q_x) q_v2) (p (p q_x q_x) q_v2)) = (p (p (p u0s0out u0_v0) (p (p u0_x u0_x) u0_v2)) (p u0_v0 u0_v0)) := Eq.trans (pst17) (peq7); let pst19 : (p (p q_x q_x) q_v2) = (p (p u0s0out u0_v0) (p (p u0_x u0_x) u0_v2)) := congrArg (fun q => L q) (pst18); let pst20 : (p q_x q_x) = (p u0s0out u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : q_x = u0s0out := congrArg (fun q => L q) (pst20); let pst22 : u0s0out = q_x := Eq.symm (pst21); let pst23 : q_x = u0_v0 := congrArg (fun q => R q) (pst20); let pst24 : u0s0out = u0_v0 := Eq.trans (pst22) (pst23); let pst25 : q_x = u0_v0 := Eq.trans (pst21) (pst24); let pst26 : (p q_x q_x) = (p u0_v0 q_x) := congrArg (fun q => p q q_x) (pst25); let pst27 : q_x = u0_v0 := Eq.trans (pst21) (pst24); let pst28 : (p u0_v0 q_x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst27); let pst29 : (p q_x q_x) = (p u0_v0 u0_v0) := Eq.trans (pst26) (pst28); let pst30 : (p (p q_x q_x) q_v2) = (p (p u0_v0 u0_v0) q_v2) := congrArg (fun q => p q q_v2) (pst29); let pst31 : q_v2 = (p (p u0_x u0_x) u0_v2) := congrArg (fun q => R q) (pst19); let pst32 : (p (p u0_v0 u0_v0) q_v2) = (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst31); let pst33 : (p (p q_x q_x) q_v2) = (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) := Eq.trans (pst30) (pst32); let pst34 : (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) = (p (p q_x q_x) q_v2) := Eq.symm (pst33); let pst35 : (p (p q_x q_x) q_v2) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst18); let pst36 : (p (p u0_v0 u0_v0) (p (p u0_x u0_x) u0_v2)) = (p u0_v0 u0_v0) := Eq.trans (pst34) (pst35); let pst37 : (p u0_v0 u0_v0) = u0_v0 := congrArg (fun q => L q) (pst36); let pst38 : u0_v0 = (p u0_v0 u0_v0) := Eq.symm (pst37); pst38)
        have hlt : sz u0_v0 < sz (p u0_v0 u0_v0) := sz_lt_p_left u0_v0 u0_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change H0 = (p (p q_v0 q_v1) q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = (p (p q_x q_x) q_v2) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (ha)
      change (p x x) = q_v0 at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (ha)
      change v2 = q_v0 at p3
      have z3 := congrArg sz p3
      have p4 := hb
      change (p v0 v0) = q_v0 at p4
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
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change H0 = (p q_H0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = (p (p q_x q_x) q_v2) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (ha)
      change (p x x) = q_v0 at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (ha)
      change v2 = q_v0 at p3
      have z3 := congrArg sz p3
      have p4 := hb
      change (p v0 v0) = q_v0 at p4
      have z4 := congrArg sz p4
      have p5 := ho
      change o = q_x at p5
      have z5 := congrArg sz p5
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2 z3 z4 z5
      omega
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval (eval (eval (eval v0 v1) v0) (eval (eval x x) v2)) (eval v0 v0)) v0) := by
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
  change x = (eval (eval (eval (eval H0 v0) (eval (eval x x) v2)) (eval v0 v0)) v0)
  have rawEq : (eval (eval (eval (eval H0 v0) (eval (eval x x) v2)) (eval v0 v0)) v0) = (eval (p (p (p H0 v0) (p (p x x) v2)) (p v0 v0)) v0) := by
    calc
      (eval (eval (eval (eval H0 v0) (eval (eval x x) v2)) (eval v0 v0)) v0) = (eval (eval (eval (p H0 v0) (eval (eval x x) v2)) (eval v0 v0)) v0) := congrArg (fun q => (eval (eval (eval q (eval (eval x x) v2)) (eval v0 v0)) v0)) (eval_raw (nr0 x v0 v1 v2 H0 s0))
      _ = (eval (eval (eval (p H0 v0) (eval (p x x) v2)) (eval v0 v0)) v0) := congrArg (fun q => (eval (eval (eval (p H0 v0) (eval q v2)) (eval v0 v0)) v0)) (eval_raw (nr1 x v0 v1 v2))
      _ = (eval (eval (eval (p H0 v0) (p (p x x) v2)) (eval v0 v0)) v0) := congrArg (fun q => (eval (eval (eval (p H0 v0) q) (eval v0 v0)) v0)) (eval_raw (nr2 x v0 v1 v2))
      _ = (eval (eval (p (p H0 v0) (p (p x x) v2)) (eval v0 v0)) v0) := congrArg (fun q => (eval (eval q (eval v0 v0)) v0)) (eval_raw (nr3 x v0 v1 v2 H0 s0))
      _ = (eval (eval (p (p H0 v0) (p (p x x) v2)) (p v0 v0)) v0) := congrArg (fun q => (eval (eval (p (p H0 v0) (p (p x x) v2)) q) v0)) (eval_raw (nr4 x v0 v1 v2))
      _ = (eval (p (p (p H0 v0) (p (p x x) v2)) (p v0 v0)) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr5 x v0 v1 v2 H0 s0))
  exact (eval_hit (Code.law x v0 v1 v2 H0 s0)).symm.trans rawEq.symm
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
