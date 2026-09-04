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
      (s0 : Step v0 x H0)
      (s1 : Step v1 v0 H1) :
      Code v0 (p (p x H0) (p v0 H1)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_x q_H0 ∧ Step q_v1 q_v0 q_H1 ∧ a = q_v0 ∧ b = (p (p q_x q_H0) (p q_v0 q_H1)) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L b))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz a < sz (p o b) := by
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
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_x (p q_v0 q_x)) (p q_v0 (p q_v1 q_v0))) at e1
      have cyc : v = (p (p q_x (p (p v k) q_x)) (p (p v k) (p q_v1 (p v k)))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_x (p q_v0 q_x)) (p q_v0 (p q_v1 q_v0))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p v k) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p v k) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : (p (p q_x (p q_v0 q_x)) (p q_v0 (p q_v1 q_v0))) = (p (p q_x (p (p v k) q_x)) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p v k) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst0); let pst5 : (p q_v1 q_v0) = (p q_v1 (p v k)) := congrArg (fun q => p q_v1 q) (pst0); let pst6 : (p (p v k) (p q_v1 q_v0)) = (p (p v k) (p q_v1 (p v k))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_v1 q_v0)) = (p (p v k) (p q_v1 (p v k))) := Eq.trans (pst4) (pst6); let pst8 : (p (p q_x (p (p v k) q_x)) (p q_v0 (p q_v1 q_v0))) = (p (p q_x (p (p v k) q_x)) (p (p v k) (p q_v1 (p v k)))) := congrArg (fun q => p (p q_x (p (p v k) q_x)) q) (pst7); let pst9 : (p (p q_x (p q_v0 q_x)) (p q_v0 (p q_v1 q_v0))) = (p (p q_x (p (p v k) q_x)) (p (p v k) (p q_v1 (p v k)))) := Eq.trans (pst3) (pst8); let pst10 : v = (p (p q_x (p (p v k) q_x)) (p (p v k) (p q_v1 (p v k)))) := Eq.trans (peq1) (pst9); pst10)
      have hlt : sz v < sz (p (p q_x (p (p v k) q_x)) (p (p v k) (p q_v1 (p v k)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_x)) (sz_lt_p_right q_x (p (p v k) q_x))) (sz_lt_p_left (p q_x (p (p v k) q_x)) (p (p v k) (p q_v1 (p v k))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_x (p q_v0 q_x)) (p q_v0 q_H1)) at e1
      have cyc : v = (p (p q_x (p (p v k) q_x)) (p (p v k) q_H1)) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_x (p q_v0 q_x)) (p q_v0 q_H1)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p v k) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p v k) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : (p (p q_x (p q_v0 q_x)) (p q_v0 q_H1)) = (p (p q_x (p (p v k) q_x)) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (pst2); let pst4 : (p q_v0 q_H1) = (p (p v k) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst5 : (p (p q_x (p (p v k) q_x)) (p q_v0 q_H1)) = (p (p q_x (p (p v k) q_x)) (p (p v k) q_H1)) := congrArg (fun q => p (p q_x (p (p v k) q_x)) q) (pst4); let pst6 : (p (p q_x (p q_v0 q_x)) (p q_v0 q_H1)) = (p (p q_x (p (p v k) q_x)) (p (p v k) q_H1)) := Eq.trans (pst3) (pst5); let pst7 : v = (p (p q_x (p (p v k) q_x)) (p (p v k) q_H1)) := Eq.trans (peq1) (pst6); pst7)
      have hlt : sz v < sz (p (p q_x (p (p v k) q_x)) (p (p v k) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_x)) (sz_lt_p_right q_x (p (p v k) q_x))) (sz_lt_p_left (p q_x (p (p v k) q_x)) (p (p v k) q_H1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_x q_H0) (p q_v0 (p q_v1 q_v0))) at e1
      have cyc : v = (p (p q_x q_H0) (p (p v k) (p q_v1 (p v k)))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_x q_H0) (p q_v0 (p q_v1 q_v0))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 q_v0)) = (p (p v k) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst0); let pst2 : (p q_v1 q_v0) = (p q_v1 (p v k)) := congrArg (fun q => p q_v1 q) (pst0); let pst3 : (p (p v k) (p q_v1 q_v0)) = (p (p v k) (p q_v1 (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p v k) (p q_v1 (p v k))) := Eq.trans (pst1) (pst3); let pst5 : (p (p q_x q_H0) (p q_v0 (p q_v1 q_v0))) = (p (p q_x q_H0) (p (p v k) (p q_v1 (p v k)))) := congrArg (fun q => p (p q_x q_H0) q) (pst4); let pst6 : v = (p (p q_x q_H0) (p (p v k) (p q_v1 (p v k)))) := Eq.trans (peq1) (pst5); pst6)
      have hlt : sz v < sz (p (p q_x q_H0) (p (p v k) (p q_v1 (p v k)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_v1 (p v k)))) (sz_lt_p_right (p q_x q_H0) (p (p v k) (p q_v1 (p v k))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_x q_H0) (p q_v0 q_H1)) at e1
      have cyc : v = (p (p q_x q_H0) (p (p v k) q_H1)) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_x q_H0) (p q_v0 q_H1)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = (p (p v k) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst2 : (p (p q_x q_H0) (p q_v0 q_H1)) = (p (p q_x q_H0) (p (p v k) q_H1)) := congrArg (fun q => p (p q_x q_H0) q) (pst1); let pst3 : v = (p (p q_x q_H0) (p (p v k) q_H1)) := Eq.trans (peq1) (pst2); pst3)
      have hlt : sz v < sz (p (p q_x q_H0) (p (p v k) q_H1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H1)) (sz_lt_p_right (p q_x q_H0) (p (p v k) q_H1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code x H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p q_x (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 (p q_v1 q_v0)) at e2
        have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v0 (p q_v1 q_v0)) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p q_x (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 q_H1) at e2
        have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v0 q_H1) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_H1) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p q_x q_H0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 (p q_v1 q_v0)) at e2
        have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v0 (p q_v1 q_v0)) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p q_x q_H0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 q_H1) at e2
        have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v0 q_H1) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_H1) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p q_x (p q_v0 q_x)) (p q_v0 (p q_v1 q_v0))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s0hB s0B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p q_x (p q_v0 q_x)) (p q_v0 q_H1)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s0hB qs1hB s0B qs0B qs1B z0 z1 z2
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p q_x q_H0) (p q_v0 (p q_v1 q_v0))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p q_x q_H0) (p q_v0 q_H1)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B qs0B qs1B z0 z1 z2
        omega
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step v1 v0 H1) :
    ¬ ∃ o, Code v0 H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p q_x (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 (p q_v1 q_v0)) at e2
        have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v0 (p q_v1 q_v0)) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p q_x (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 q_H1) at e2
        have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v0 q_H1) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_H1) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p q_x q_H0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 (p q_v1 q_v0)) at e2
        have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v0 (p q_v1 q_v0)) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p q_x q_H0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 q_H1) at e2
        have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v0 q_H1) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_H1) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x (p q_v0 q_x)) (p q_v0 (p q_v1 q_v0))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB s1B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x (p q_v0 q_x)) (p q_v0 q_H1)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x q_H0) (p q_v0 (p q_v1 q_v0))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB s1B qs0B qs1B z0 z1 z2
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
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x q_H0) (p q_v0 q_H1)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
theorem nr2 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 x H0)
    (s1 : Step v1 v0 H1) :
    ¬ ∃ o, Code (p x H0) (p v0 H1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have s1B := step_bound s1
    cases s1 with
    | raw =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p q_x (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_v1 q_v0) at e3
          have cyc : v0 = (p q_x (p (p x (p v0 x)) q_x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p x (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p x (p v0 x)) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : v0 = (p q_x (p (p x (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p q_x (p (p x (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right x (p v0 x))) (sz_lt_p_left (p x (p v0 x)) q_x)) (sz_lt_p_right q_x (p (p x (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p q_x (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = q_H1 at e3
          have cyc : v0 = (p q_x (p (p x (p v0 x)) q_x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p x (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p x (p v0 x)) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : v0 = (p q_x (p (p x (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p q_x (p (p x (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right x (p v0 x))) (sz_lt_p_left (p x (p v0 x)) q_x)) (sz_lt_p_right q_x (p (p x (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p q_x q_H0) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_v1 q_v0) at e3
          have cyc : q_H0 = (p x (p (p q_v1 q_H0) x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p q_x q_H0) := e1; let peq3 : v0 = (p q_v1 q_v0) := e3; let pst0 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_H0) = (p q_v1 q_v0) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst3 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst4 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst3); let pst5 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst2) (pst4); let pst6 : (p q_v1 q_v0) = (p q_v1 (p x (p (p q_x q_H0) x))) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p q_x q_H0) = (p q_v1 (p x (p (p q_x q_H0) x))) := Eq.trans (pst1) (pst6); let pst8 : q_H0 = (p x (p (p q_x q_H0) x)) := congrArg (fun q => R q) (pst7); let pst9 : q_x = q_v1 := congrArg (fun q => L q) (pst7); let pst10 : (p q_x q_H0) = (p q_v1 q_H0) := congrArg (fun q => p q q_H0) (pst9); let pst11 : (p (p q_x q_H0) x) = (p (p q_v1 q_H0) x) := congrArg (fun q => p q x) (pst10); let pst12 : (p x (p (p q_x q_H0) x)) = (p x (p (p q_v1 q_H0) x)) := congrArg (fun q => p x q) (pst11); let pst13 : q_H0 = (p x (p (p q_v1 q_H0) x)) := Eq.trans (pst8) (pst12); pst13)
          have hlt : sz q_H0 < sz (p x (p (p q_v1 q_H0) x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v1 q_H0) (sz_lt_p_left (p q_v1 q_H0) x)) (sz_lt_p_right x (p (p q_v1 q_H0) x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x (p v0 x)) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = q_H1 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
    | hit s1h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p q_x (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (R q)) hb
          change H1 = (p q_v0 (p q_v1 q_v0)) at e2
          have cyc : v0 = (p q_x (p (p x (p v0 x)) q_x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p x (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p x (p v0 x)) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : v0 = (p q_x (p (p x (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p q_x (p (p x (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right x (p v0 x))) (sz_lt_p_left (p x (p v0 x)) q_x)) (sz_lt_p_right q_x (p (p x (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p q_x (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (R q)) hb
          change H1 = (p q_v0 q_H1) at e2
          have cyc : v0 = (p q_x (p (p x (p v0 x)) q_x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p x (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p x (p v0 x)) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : v0 = (p q_x (p (p x (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p q_x (p (p x (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right x (p v0 x))) (sz_lt_p_left (p x (p v0 x)) q_x)) (sz_lt_p_right q_x (p (p x (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          let u0s0out := u0_H0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            let u0s1out := u0_H1
            cases u0s1 with
            | raw =>
              have cyc : u0_x = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) := (let peq0 : (p x (p v0 x)) = q_v0 := ha; let peq1 : v0 = (p q_x q_H0) := congrArg (fun q => (L q)) (hb); let peq2 : H1 = (p q_v0 (p q_v1 q_v0)) := congrArg (fun q => (R q)) (hb); let peq5 : v0 = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) := u0b; let peq6 : H1 = u0_x := u0o; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst2 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst1); let pst3 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst6 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst5); let pst7 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p x (p (p q_x q_H0) x))) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p (p x (p (p q_x q_H0) x)) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (pst4) (pst9); let pst11 : H1 = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (peq2) (pst10); let pst12 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst13 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst12) (peq5); let pst14 : q_x = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => L q) (pst13); let pst15 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst16 : q_H0 = (p u0_v0 (p u0_v1 u0_v0)) := congrArg (fun q => R q) (pst13); let pst17 : (p (p u0_x (p u0_v0 u0_x)) q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) := congrArg (fun q => p (p u0_x (p u0_v0 u0_x)) q) (pst16); let pst18 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst15) (pst17); let pst19 : (p (p q_x q_H0) x) = (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x) := congrArg (fun q => p q x) (pst18); let pst20 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) := congrArg (fun q => p x q) (pst19); let pst21 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p q (p q_v1 (p x (p (p q_x q_H0) x)))) (pst20); let pst22 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst23 : (p (p u0_x (p u0_v0 u0_x)) q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) := congrArg (fun q => p (p u0_x (p u0_v0 u0_x)) q) (pst16); let pst24 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst22) (pst23); let pst25 : (p (p q_x q_H0) x) = (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x) := congrArg (fun q => p q x) (pst24); let pst26 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) := congrArg (fun q => p x q) (pst25); let pst27 : (p q_v1 (p x (p (p q_x q_H0) x))) = (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x))) := congrArg (fun q => p q_v1 q) (pst26); let pst28 : (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) := congrArg (fun q => p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) q) (pst27); let pst29 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Eq.trans (pst21) (pst28); let pst30 : H1 = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Eq.trans (pst11) (pst29); let pst31 : (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) = H1 := Eq.symm (pst30); let pst32 : (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) = u0_x := Eq.trans (pst31) (peq6); let pst33 : u0_x = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Eq.symm (pst32); pst33)
              have hlt : sz u0_x < sz (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v0 u0_x)) (sz_lt_p_left (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0)))) (sz_lt_p_left (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (sz_lt_p_right x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x))) (sz_lt_p_left (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 (p u0_v1 u0_v0))) x))))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_x = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) := (let peq0 : (p x (p v0 x)) = q_v0 := ha; let peq1 : v0 = (p q_x q_H0) := congrArg (fun q => (L q)) (hb); let peq2 : H1 = (p q_v0 (p q_v1 q_v0)) := congrArg (fun q => (R q)) (hb); let peq5 : v0 = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) := u0b; let peq6 : H1 = u0_x := u0o; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst2 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst1); let pst3 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst6 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst5); let pst7 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p x (p (p q_x q_H0) x))) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p (p x (p (p q_x q_H0) x)) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (pst4) (pst9); let pst11 : H1 = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (peq2) (pst10); let pst12 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst13 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) := Eq.trans (pst12) (peq5); let pst14 : q_x = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => L q) (pst13); let pst15 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst16 : q_H0 = (p u0_v0 u0s1out) := congrArg (fun q => R q) (pst13); let pst17 : (p (p u0_x (p u0_v0 u0_x)) q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) := congrArg (fun q => p (p u0_x (p u0_v0 u0_x)) q) (pst16); let pst18 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) := Eq.trans (pst15) (pst17); let pst19 : (p (p q_x q_H0) x) = (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x) := congrArg (fun q => p q x) (pst18); let pst20 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) := congrArg (fun q => p x q) (pst19); let pst21 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p q (p q_v1 (p x (p (p q_x q_H0) x)))) (pst20); let pst22 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst23 : (p (p u0_x (p u0_v0 u0_x)) q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) := congrArg (fun q => p (p u0_x (p u0_v0 u0_x)) q) (pst16); let pst24 : (p q_x q_H0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) := Eq.trans (pst22) (pst23); let pst25 : (p (p q_x q_H0) x) = (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x) := congrArg (fun q => p q x) (pst24); let pst26 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) := congrArg (fun q => p x q) (pst25); let pst27 : (p q_v1 (p x (p (p q_x q_H0) x))) = (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x))) := congrArg (fun q => p q_v1 q) (pst26); let pst28 : (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) := congrArg (fun q => p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) q) (pst27); let pst29 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) := Eq.trans (pst21) (pst28); let pst30 : H1 = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) := Eq.trans (pst11) (pst29); let pst31 : (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) = H1 := Eq.symm (pst30); let pst32 : (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) = u0_x := Eq.trans (pst31) (peq6); let pst33 : u0_x = (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) := Eq.symm (pst32); pst33)
              have hlt : sz u0_x < sz (p (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v0 u0_x)) (sz_lt_p_left (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out))) (sz_lt_p_left (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (sz_lt_p_right x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x))) (sz_lt_p_left (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x (p u0_v0 u0_x)) (p u0_v0 u0s1out)) x))))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            let u0s1out := u0_H1
            cases u0s1 with
            | raw =>
              have cyc : u0_x = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) := (let peq0 : (p x (p v0 x)) = q_v0 := ha; let peq1 : v0 = (p q_x q_H0) := congrArg (fun q => (L q)) (hb); let peq2 : H1 = (p q_v0 (p q_v1 q_v0)) := congrArg (fun q => (R q)) (hb); let peq5 : v0 = (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) := u0b; let peq6 : H1 = u0_x := u0o; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst2 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst1); let pst3 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst6 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst5); let pst7 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p x (p (p q_x q_H0) x))) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p (p x (p (p q_x q_H0) x)) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (pst4) (pst9); let pst11 : H1 = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (peq2) (pst10); let pst12 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst13 : (p q_x q_H0) = (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst12) (peq5); let pst14 : q_x = (p u0_x u0s0out) := congrArg (fun q => L q) (pst13); let pst15 : (p q_x q_H0) = (p (p u0_x u0s0out) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst16 : q_H0 = (p u0_v0 (p u0_v1 u0_v0)) := congrArg (fun q => R q) (pst13); let pst17 : (p (p u0_x u0s0out) q_H0) = (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) := congrArg (fun q => p (p u0_x u0s0out) q) (pst16); let pst18 : (p q_x q_H0) = (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst15) (pst17); let pst19 : (p (p q_x q_H0) x) = (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x) := congrArg (fun q => p q x) (pst18); let pst20 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) := congrArg (fun q => p x q) (pst19); let pst21 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p q (p q_v1 (p x (p (p q_x q_H0) x)))) (pst20); let pst22 : (p q_x q_H0) = (p (p u0_x u0s0out) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst23 : (p (p u0_x u0s0out) q_H0) = (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) := congrArg (fun q => p (p u0_x u0s0out) q) (pst16); let pst24 : (p q_x q_H0) = (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst22) (pst23); let pst25 : (p (p q_x q_H0) x) = (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x) := congrArg (fun q => p q x) (pst24); let pst26 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) := congrArg (fun q => p x q) (pst25); let pst27 : (p q_v1 (p x (p (p q_x q_H0) x))) = (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x))) := congrArg (fun q => p q_v1 q) (pst26); let pst28 : (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) := congrArg (fun q => p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) q) (pst27); let pst29 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Eq.trans (pst21) (pst28); let pst30 : H1 = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Eq.trans (pst11) (pst29); let pst31 : (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) = H1 := Eq.symm (pst30); let pst32 : (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) = u0_x := Eq.trans (pst31) (peq6); let pst33 : u0_x = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Eq.symm (pst32); pst33)
              have hlt : sz u0_x < sz (p (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s0out) (sz_lt_p_left (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0)))) (sz_lt_p_left (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (sz_lt_p_right x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x))) (sz_lt_p_left (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 (p u0_v1 u0_v0))) x))))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_x = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) := (let peq0 : (p x (p v0 x)) = q_v0 := ha; let peq1 : v0 = (p q_x q_H0) := congrArg (fun q => (L q)) (hb); let peq2 : H1 = (p q_v0 (p q_v1 q_v0)) := congrArg (fun q => (R q)) (hb); let peq5 : v0 = (p (p u0_x u0s0out) (p u0_v0 u0s1out)) := u0b; let peq6 : H1 = u0_x := u0o; let pst0 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst1 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst2 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst1); let pst3 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst2); let pst4 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst3); let pst5 : (p v0 x) = (p (p q_x q_H0) x) := congrArg (fun q => p q x) (peq1); let pst6 : (p x (p v0 x)) = (p x (p (p q_x q_H0) x)) := congrArg (fun q => p x q) (pst5); let pst7 : q_v0 = (p x (p (p q_x q_H0) x)) := Eq.trans (pst0) (pst6); let pst8 : (p q_v1 q_v0) = (p q_v1 (p x (p (p q_x q_H0) x))) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p x (p (p q_x q_H0) x)) (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p (p x (p (p q_x q_H0) x)) q) (pst8); let pst10 : (p q_v0 (p q_v1 q_v0)) = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (pst4) (pst9); let pst11 : H1 = (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := Eq.trans (peq2) (pst10); let pst12 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst13 : (p q_x q_H0) = (p (p u0_x u0s0out) (p u0_v0 u0s1out)) := Eq.trans (pst12) (peq5); let pst14 : q_x = (p u0_x u0s0out) := congrArg (fun q => L q) (pst13); let pst15 : (p q_x q_H0) = (p (p u0_x u0s0out) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst16 : q_H0 = (p u0_v0 u0s1out) := congrArg (fun q => R q) (pst13); let pst17 : (p (p u0_x u0s0out) q_H0) = (p (p u0_x u0s0out) (p u0_v0 u0s1out)) := congrArg (fun q => p (p u0_x u0s0out) q) (pst16); let pst18 : (p q_x q_H0) = (p (p u0_x u0s0out) (p u0_v0 u0s1out)) := Eq.trans (pst15) (pst17); let pst19 : (p (p q_x q_H0) x) = (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x) := congrArg (fun q => p q x) (pst18); let pst20 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) := congrArg (fun q => p x q) (pst19); let pst21 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) := congrArg (fun q => p q (p q_v1 (p x (p (p q_x q_H0) x)))) (pst20); let pst22 : (p q_x q_H0) = (p (p u0_x u0s0out) q_H0) := congrArg (fun q => p q q_H0) (pst14); let pst23 : (p (p u0_x u0s0out) q_H0) = (p (p u0_x u0s0out) (p u0_v0 u0s1out)) := congrArg (fun q => p (p u0_x u0s0out) q) (pst16); let pst24 : (p q_x q_H0) = (p (p u0_x u0s0out) (p u0_v0 u0s1out)) := Eq.trans (pst22) (pst23); let pst25 : (p (p q_x q_H0) x) = (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x) := congrArg (fun q => p q x) (pst24); let pst26 : (p x (p (p q_x q_H0) x)) = (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) := congrArg (fun q => p x q) (pst25); let pst27 : (p q_v1 (p x (p (p q_x q_H0) x))) = (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x))) := congrArg (fun q => p q_v1 q) (pst26); let pst28 : (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) := congrArg (fun q => p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) q) (pst27); let pst29 : (p (p x (p (p q_x q_H0) x)) (p q_v1 (p x (p (p q_x q_H0) x)))) = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) := Eq.trans (pst21) (pst28); let pst30 : H1 = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) := Eq.trans (pst11) (pst29); let pst31 : (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) = H1 := Eq.symm (pst30); let pst32 : (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) = u0_x := Eq.trans (pst31) (peq6); let pst33 : u0_x = (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) := Eq.symm (pst32); pst33)
              have hlt : sz u0_x < sz (p (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s0out) (sz_lt_p_left (p u0_x u0s0out) (p u0_v0 u0s1out))) (sz_lt_p_left (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (sz_lt_p_right x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x))) (sz_lt_p_left (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x)) (p q_v1 (p x (p (p (p u0_x u0s0out) (p u0_v0 u0s1out)) x))))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have hcB := code_bounds hc
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x (p v0 x)) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change H1 = (p q_v0 q_H1) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
  | hit s0h =>
    have s1B := step_bound s1
    cases s1 with
    | raw =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x H0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p q_x (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_v1 q_v0) at e3
          have cyc : x = (p x H0) := (let peq0 : (p x H0) = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let peq3 : v0 = (p q_v1 q_v0) := e3; let pst0 : q_v0 = (p x H0) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p x H0) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p q_x (p q_v0 q_x)) = (p q_x (p (p x H0) q_x)) := congrArg (fun q => p q_x q) (pst1); let pst3 : v0 = (p q_x (p (p x H0) q_x)) := Eq.trans (peq1) (pst2); let pst4 : (p q_x (p (p x H0) q_x)) = v0 := Eq.symm (pst3); let pst5 : (p q_x (p (p x H0) q_x)) = (p q_v1 q_v0) := Eq.trans (pst4) (peq3); let pst6 : (p q_v1 q_v0) = (p q_v1 (p x H0)) := congrArg (fun q => p q_v1 q) (pst0); let pst7 : (p q_x (p (p x H0) q_x)) = (p q_v1 (p x H0)) := Eq.trans (pst5) (pst6); let pst8 : q_x = q_v1 := congrArg (fun q => L q) (pst7); let pst9 : (p (p x H0) q_x) = (p (p x H0) q_v1) := congrArg (fun q => p (p x H0) q) (pst8); let pst10 : (p (p x H0) q_v1) = (p (p x H0) q_x) := Eq.symm (pst9); let pst11 : (p (p x H0) q_x) = (p x H0) := congrArg (fun q => R q) (pst7); let pst12 : (p (p x H0) q_v1) = (p x H0) := Eq.trans (pst10) (pst11); let pst13 : (p x H0) = x := congrArg (fun q => L q) (pst12); let pst14 : x = (p x H0) := Eq.symm (pst13); pst14)
          have hlt : sz x < sz (p x H0) := sz_lt_p_left x H0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x (p q_v0 q_x)) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = q_H1 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have qs0hB := code_bounds qs0h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = (p q_v1 q_v0) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = q_H1 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
    | hit s1h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x (p q_v0 q_x)) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change H1 = (p q_v0 (p q_v1 q_v0)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x (p q_v0 q_x)) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change H1 = (p q_v0 q_H1) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change H1 = (p q_v0 (p q_v1 q_v0)) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p q_x q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (hb)
          change H1 = (p q_v0 q_H1) at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval (eval x (eval v0 x)) (eval v0 (eval v1 v0)))) := by
  let H0 := eval v0 x
  have e0a : v0 = v0 := by
    change v0 = v0
    rfl
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step v0 x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v0 x
  let H1 := eval v1 v0
  have e1a : v1 = v1 := by
    change v1 = v1
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step v1 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v1 v0
  change x = (eval v0 (eval (eval x H0) (eval v0 H1)))
  have rawEq : (eval v0 (eval (eval x H0) (eval v0 H1))) = (eval v0 (p (p x H0) (p v0 H1))) := by
    calc
      (eval v0 (eval (eval x H0) (eval v0 H1))) = (eval v0 (eval (p x H0) (eval v0 H1))) := congrArg (fun q => (eval v0 (eval q (eval v0 H1)))) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval v0 (eval (p x H0) (p v0 H1))) := congrArg (fun q => (eval v0 (eval (p x H0) q))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval v0 (p (p x H0) (p v0 H1))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr2 x v0 v1 H0 H1 s0 s1))
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
