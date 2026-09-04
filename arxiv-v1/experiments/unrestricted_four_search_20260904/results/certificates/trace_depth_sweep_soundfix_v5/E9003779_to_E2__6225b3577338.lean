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
      (s0 : Step x v1 H0) :
      Code v0 (p x (p v0 (p (p v1 H0) (p v1 v1)))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_x q_v1 q_H0 ∧ a = q_v0 ∧ b = (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L b)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code v1 H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change x = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) at e2
      have cyc : q_v0 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := (let peq0 : v1 = q_v0 := e0; let peq2 : v1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := e2; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := sz_lt_p_left q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v1 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change x = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) at e2
      have cyc : q_v0 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := (let peq0 : v1 = q_v0 := e0; let peq2 : v1 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := e2; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := sz_lt_p_left q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))
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
      change v1 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))) at p1
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
      change v1 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2
      omega
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))) at e1
    have cyc : q_v0 = (p q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))) := (let peq0 : v1 = q_v0 := e0; let peq1 : v1 = (p q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))) := e1; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) (sz_lt_p_right q_x (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) at e1
    have cyc : q_v0 = (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) := (let peq0 : v1 = q_v0 := e0; let peq1 : v1 = (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) := e1; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) (sz_lt_p_right q_x (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code (p v1 H0) (p v1 v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v1 (p x v1)) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) at e2
      have cyc : q_x = (p (p q_x (p x q_x)) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := (let peq0 : (p v1 (p x v1)) = q_v0 := e0; let peq1 : v1 = q_x := e1; let peq2 : v1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := e2; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p v1 (p x v1)) := Eq.symm (peq0); let pst3 : (p v1 (p x v1)) = (p q_x (p x v1)) := congrArg (fun q => p q (p x v1)) (peq1); let pst4 : (p x v1) = (p x q_x) := congrArg (fun q => p x q) (peq1); let pst5 : (p q_x (p x v1)) = (p q_x (p x q_x)) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p v1 (p x v1)) = (p q_x (p x q_x)) := Eq.trans (pst3) (pst5); let pst7 : q_v0 = (p q_x (p x q_x)) := Eq.trans (pst2) (pst6); let pst8 : (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) = (p (p q_x (p x q_x)) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) (pst7); let pst9 : q_x = (p (p q_x (p x q_x)) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Eq.trans (pst1) (pst8); pst9)
      have hlt : sz q_x < sz (p (p q_x (p x q_x)) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Nat.lt_trans (sz_lt_p_left q_x (p x q_x)) (sz_lt_p_left (p q_x (p x q_x)) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p v1 (p x v1)) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) at e2
      have cyc : q_x = (p (p q_x (p x q_x)) (p (p q_v1 q_H0) (p q_v1 q_v1))) := (let peq0 : (p v1 (p x v1)) = q_v0 := e0; let peq1 : v1 = q_x := e1; let peq2 : v1 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := e2; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p v1 (p x v1)) := Eq.symm (peq0); let pst3 : (p v1 (p x v1)) = (p q_x (p x v1)) := congrArg (fun q => p q (p x v1)) (peq1); let pst4 : (p x v1) = (p x q_x) := congrArg (fun q => p x q) (peq1); let pst5 : (p q_x (p x v1)) = (p q_x (p x q_x)) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p v1 (p x v1)) = (p q_x (p x q_x)) := Eq.trans (pst3) (pst5); let pst7 : q_v0 = (p q_x (p x q_x)) := Eq.trans (pst2) (pst6); let pst8 : (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) = (p (p q_x (p x q_x)) (p (p q_v1 q_H0) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_v1 q_H0) (p q_v1 q_v1))) (pst7); let pst9 : q_x = (p (p q_x (p x q_x)) (p (p q_v1 q_H0) (p q_v1 q_v1))) := Eq.trans (pst1) (pst8); pst9)
      have hlt : sz q_x < sz (p (p q_x (p x q_x)) (p (p q_v1 q_H0) (p q_v1 q_v1))) := Nat.lt_trans (sz_lt_p_left q_x (p x q_x)) (sz_lt_p_left (p q_x (p x q_x)) (p (p q_v1 q_H0) (p q_v1 q_v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v1 H0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) at e2
      have cyc : q_x = (p (p q_x H0) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := (let peq0 : (p v1 H0) = q_v0 := e0; let peq1 : v1 = q_x := e1; let peq2 : v1 = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := e2; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p v1 H0) := Eq.symm (peq0); let pst3 : (p v1 H0) = (p q_x H0) := congrArg (fun q => p q H0) (peq1); let pst4 : q_v0 = (p q_x H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) = (p (p q_x H0) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) (pst4); let pst6 : q_x = (p (p q_x H0) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Eq.trans (pst1) (pst5); pst6)
      have hlt : sz q_x < sz (p (p q_x H0) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1))) := Nat.lt_trans (sz_lt_p_left q_x H0) (sz_lt_p_left (p q_x H0) (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p v1 H0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) at e2
      have cyc : q_x = (p (p q_x H0) (p (p q_v1 q_H0) (p q_v1 q_v1))) := (let peq0 : (p v1 H0) = q_v0 := e0; let peq1 : v1 = q_x := e1; let peq2 : v1 = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := e2; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p v1 H0) := Eq.symm (peq0); let pst3 : (p v1 H0) = (p q_x H0) := congrArg (fun q => p q H0) (peq1); let pst4 : q_v0 = (p q_x H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 (p (p q_v1 q_H0) (p q_v1 q_v1))) = (p (p q_x H0) (p (p q_v1 q_H0) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_v1 q_H0) (p q_v1 q_v1))) (pst4); let pst6 : q_x = (p (p q_x H0) (p (p q_v1 q_H0) (p q_v1 q_v1))) := Eq.trans (pst1) (pst5); pst6)
      have hlt : sz q_x < sz (p (p q_x H0) (p (p q_v1 q_H0) (p q_v1 q_v1))) := Nat.lt_trans (sz_lt_p_left q_x H0) (sz_lt_p_left (p q_x H0) (p (p q_v1 q_H0) (p q_v1 q_v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code v0 (p (p v1 H0) (p v1 v1)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p v1 (p x v1)) = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = q_v0 at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) at e3
      have cyc : q_v0 = (p (p q_v1 (p (p q_v0 (p x q_v0)) q_v1)) (p q_v1 q_v1)) := (let peq1 : (p v1 (p x v1)) = q_x := e1; let peq2 : v1 = q_v0 := e2; let peq3 : v1 = (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) := e3; let pst0 : q_v0 = v1 := Eq.symm (peq2); let pst1 : q_v0 = (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) := Eq.trans (pst0) (peq3); let pst2 : q_x = (p v1 (p x v1)) := Eq.symm (peq1); let pst3 : (p v1 (p x v1)) = (p q_v0 (p x v1)) := congrArg (fun q => p q (p x v1)) (peq2); let pst4 : (p x v1) = (p x q_v0) := congrArg (fun q => p x q) (peq2); let pst5 : (p q_v0 (p x v1)) = (p q_v0 (p x q_v0)) := congrArg (fun q => p q_v0 q) (pst4); let pst6 : (p v1 (p x v1)) = (p q_v0 (p x q_v0)) := Eq.trans (pst3) (pst5); let pst7 : q_x = (p q_v0 (p x q_v0)) := Eq.trans (pst2) (pst6); let pst8 : (p q_x q_v1) = (p (p q_v0 (p x q_v0)) q_v1) := congrArg (fun q => p q q_v1) (pst7); let pst9 : (p q_v1 (p q_x q_v1)) = (p q_v1 (p (p q_v0 (p x q_v0)) q_v1)) := congrArg (fun q => p q_v1 q) (pst8); let pst10 : (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) = (p (p q_v1 (p (p q_v0 (p x q_v0)) q_v1)) (p q_v1 q_v1)) := congrArg (fun q => p q (p q_v1 q_v1)) (pst9); let pst11 : q_v0 = (p (p q_v1 (p (p q_v0 (p x q_v0)) q_v1)) (p q_v1 q_v1)) := Eq.trans (pst1) (pst10); pst11)
      have hlt : sz q_v0 < sz (p (p q_v1 (p (p q_v0 (p x q_v0)) q_v1)) (p q_v1 q_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p x q_v0)) (sz_lt_p_left (p q_v0 (p x q_v0)) q_v1)) (sz_lt_p_right q_v1 (p (p q_v0 (p x q_v0)) q_v1))) (sz_lt_p_left (p q_v1 (p (p q_v0 (p x q_v0)) q_v1)) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : q_v1 = (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) := (let peq1 : (p v1 (p x v1)) = q_x := congrArg (fun q => (L q)) (hb); let peq2 : v1 = q_v0 := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := congrArg (fun q => (R (R q))) (hb); let peq5 : q_x = u0_v0 := u0a; let peq6 : q_v1 = (p u0_x (p u0_v0 (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) := u0b; let pst0 : q_x = (p v1 (p x v1)) := Eq.symm (peq1); let pst1 : q_v0 = v1 := Eq.symm (peq2); let pst2 : q_v0 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := Eq.trans (pst1) (peq3); let pst3 : v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := Eq.trans (peq2) (pst2); let pst4 : (p v1 (p x v1)) = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x v1)) := congrArg (fun q => p q (p x v1)) (pst3); let pst5 : v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := Eq.trans (peq2) (pst2); let pst6 : (p x v1) = (p x (p (p q_v1 q_H0) (p q_v1 q_v1))) := congrArg (fun q => p x q) (pst5); let pst7 : (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x v1)) = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := congrArg (fun q => p (p (p q_v1 q_H0) (p q_v1 q_v1)) q) (pst6); let pst8 : (p v1 (p x v1)) = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.trans (pst4) (pst7); let pst9 : q_x = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.trans (pst0) (pst8); let pst10 : (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) = q_x := Eq.symm (pst9); let pst11 : (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) = u0_v0 := Eq.trans (pst10) (peq5); let pst12 : u0_v0 = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.symm (pst11); let pst13 : (p u0_v0 (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1))) = (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1))) := congrArg (fun q => p q (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1))) (pst12); let pst14 : (p u0_x (p u0_v0 (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) = (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) := congrArg (fun q => p u0_x q) (pst13); let pst15 : q_v1 = (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) := Eq.trans (peq6) (pst14); pst15)
        have hlt : sz q_v1 < sz (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_H0) (sz_lt_p_left (p q_v1 q_H0) (p q_v1 q_v1))) (sz_lt_p_left (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1))))) (sz_lt_p_left (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1)))) (sz_lt_p_right u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 (p u0_x u0_v1)) (p u0_v1 u0_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : q_v1 = (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) := (let peq1 : (p v1 (p x v1)) = q_x := congrArg (fun q => (L q)) (hb); let peq2 : v1 = q_v0 := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := congrArg (fun q => (R (R q))) (hb); let peq5 : q_x = u0_v0 := u0a; let peq6 : q_v1 = (p u0_x (p u0_v0 (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) := u0b; let pst0 : q_x = (p v1 (p x v1)) := Eq.symm (peq1); let pst1 : q_v0 = v1 := Eq.symm (peq2); let pst2 : q_v0 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := Eq.trans (pst1) (peq3); let pst3 : v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := Eq.trans (peq2) (pst2); let pst4 : (p v1 (p x v1)) = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x v1)) := congrArg (fun q => p q (p x v1)) (pst3); let pst5 : v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) := Eq.trans (peq2) (pst2); let pst6 : (p x v1) = (p x (p (p q_v1 q_H0) (p q_v1 q_v1))) := congrArg (fun q => p x q) (pst5); let pst7 : (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x v1)) = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := congrArg (fun q => p (p (p q_v1 q_H0) (p q_v1 q_v1)) q) (pst6); let pst8 : (p v1 (p x v1)) = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.trans (pst4) (pst7); let pst9 : q_x = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.trans (pst0) (pst8); let pst10 : (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) = q_x := Eq.symm (pst9); let pst11 : (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) = u0_v0 := Eq.trans (pst10) (peq5); let pst12 : u0_v0 = (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) := Eq.symm (pst11); let pst13 : (p u0_v0 (p (p u0_v1 u0s0out) (p u0_v1 u0_v1))) = (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1))) := congrArg (fun q => p q (p (p u0_v1 u0s0out) (p u0_v1 u0_v1))) (pst12); let pst14 : (p u0_x (p u0_v0 (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) = (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) := congrArg (fun q => p u0_x q) (pst13); let pst15 : q_v1 = (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) := Eq.trans (peq6) (pst14); pst15)
        have hlt : sz q_v1 < sz (p u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_H0) (sz_lt_p_left (p q_v1 q_H0) (p q_v1 q_v1))) (sz_lt_p_left (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1))))) (sz_lt_p_left (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1)))) (sz_lt_p_right u0_x (p (p (p (p q_v1 q_H0) (p q_v1 q_v1)) (p x (p (p q_v1 q_H0) (p q_v1 q_v1)))) (p (p u0_v1 u0s0out) (p u0_v1 u0_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p v1 H0) = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = q_v0 at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) at e3
      have cyc : q_v0 = (p (p q_v1 (p (p q_v0 H0) q_v1)) (p q_v1 q_v1)) := (let peq1 : (p v1 H0) = q_x := e1; let peq2 : v1 = q_v0 := e2; let peq3 : v1 = (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) := e3; let pst0 : q_v0 = v1 := Eq.symm (peq2); let pst1 : q_v0 = (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) := Eq.trans (pst0) (peq3); let pst2 : q_x = (p v1 H0) := Eq.symm (peq1); let pst3 : (p v1 H0) = (p q_v0 H0) := congrArg (fun q => p q H0) (peq2); let pst4 : q_x = (p q_v0 H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_x q_v1) = (p (p q_v0 H0) q_v1) := congrArg (fun q => p q q_v1) (pst4); let pst6 : (p q_v1 (p q_x q_v1)) = (p q_v1 (p (p q_v0 H0) q_v1)) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p (p q_v1 (p q_x q_v1)) (p q_v1 q_v1)) = (p (p q_v1 (p (p q_v0 H0) q_v1)) (p q_v1 q_v1)) := congrArg (fun q => p q (p q_v1 q_v1)) (pst6); let pst8 : q_v0 = (p (p q_v1 (p (p q_v0 H0) q_v1)) (p q_v1 q_v1)) := Eq.trans (pst1) (pst7); pst8)
      have hlt : sz q_v0 < sz (p (p q_v1 (p (p q_v0 H0) q_v1)) (p q_v1 q_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 H0) (sz_lt_p_left (p q_v0 H0) q_v1)) (sz_lt_p_right q_v1 (p (p q_v0 H0) q_v1))) (sz_lt_p_left (p q_v1 (p (p q_v0 H0) q_v1)) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change v0 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change (p v1 H0) = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (hb)
      change v1 = q_v0 at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (hb)
      change v1 = (p (p q_v1 q_H0) (p q_v1 q_v1)) at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B qs0B z0 z1 z2 z3 z4
      omega
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code x (p v0 (p (p v1 H0) (p v1 v1))) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change (p v1 (p x v1)) = q_v0 at e2
      have e3 := congrArg (fun q => (L (R (R q)))) hb
      change v1 = (p q_v1 (p q_x q_v1)) at e3
      have e4 := congrArg (fun q => (R (R (R q)))) hb
      change v1 = (p q_v1 q_v1) at e4
      have cyc : q_v0 = (p v1 (p q_v0 v1)) := (let peq0 : x = q_v0 := e0; let peq2 : (p v1 (p x v1)) = q_v0 := e2; let pst0 : (p x v1) = (p q_v0 v1) := congrArg (fun q => p q v1) (peq0); let pst1 : (p v1 (p x v1)) = (p v1 (p q_v0 v1)) := congrArg (fun q => p v1 q) (pst0); let pst2 : (p v1 (p q_v0 v1)) = (p v1 (p x v1)) := Eq.symm (pst1); let pst3 : (p v1 (p q_v0 v1)) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p v1 (p q_v0 v1)) := Eq.symm (pst3); pst4)
      have hlt : sz q_v0 < sz (p v1 (p q_v0 v1)) := Nat.lt_trans (sz_lt_p_left q_v0 v1) (sz_lt_p_right v1 (p q_v0 v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change (p v1 (p x v1)) = q_v0 at e2
      have e3 := congrArg (fun q => (L (R (R q)))) hb
      change v1 = (p q_v1 q_H0) at e3
      have e4 := congrArg (fun q => (R (R (R q)))) hb
      change v1 = (p q_v1 q_v1) at e4
      have cyc : q_v0 = (p v1 (p q_v0 v1)) := (let peq0 : x = q_v0 := e0; let peq2 : (p v1 (p x v1)) = q_v0 := e2; let pst0 : (p x v1) = (p q_v0 v1) := congrArg (fun q => p q v1) (peq0); let pst1 : (p v1 (p x v1)) = (p v1 (p q_v0 v1)) := congrArg (fun q => p v1 q) (pst0); let pst2 : (p v1 (p q_v0 v1)) = (p v1 (p x v1)) := Eq.symm (pst1); let pst3 : (p v1 (p q_v0 v1)) = q_v0 := Eq.trans (pst2) (peq2); let pst4 : q_v0 = (p v1 (p q_v0 v1)) := Eq.symm (pst3); pst4)
      have hlt : sz q_v0 < sz (p v1 (p q_v0 v1)) := Nat.lt_trans (sz_lt_p_left q_v0 v1) (sz_lt_p_right v1 (p q_v0 v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have he : q_H0 = q_v1 := (let peq3 : v1 = (p q_v1 q_H0) := congrArg (fun q => (L (R (R q)))) (hb); let peq4 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : (p q_v1 q_H0) = v1 := Eq.symm (peq3); let pst1 : (p q_v1 q_H0) = (p q_v1 q_v1) := Eq.trans (pst0) (peq4); let pst2 : q_H0 = q_v1 := congrArg (fun q => R q) (pst1); pst2)
    exact step_ne_second (by simpa only [he] using qs0)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval x (eval v0 (eval (eval v1 (eval x v1)) (eval v1 v1))))) := by
  let H0 := eval x v1
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step x v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v1
  change x = (eval v0 (eval x (eval v0 (eval (eval v1 H0) (eval v1 v1)))))
  have rawEq : (eval v0 (eval x (eval v0 (eval (eval v1 H0) (eval v1 v1))))) = (eval v0 (p x (p v0 (p (p v1 H0) (p v1 v1))))) := by
    calc
      (eval v0 (eval x (eval v0 (eval (eval v1 H0) (eval v1 v1))))) = (eval v0 (eval x (eval v0 (eval (p v1 H0) (eval v1 v1))))) := congrArg (fun q => (eval v0 (eval x (eval v0 (eval q (eval v1 v1)))))) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval v0 (eval x (eval v0 (eval (p v1 H0) (p v1 v1))))) := congrArg (fun q => (eval v0 (eval x (eval v0 (eval (p v1 H0) q))))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval x (eval v0 (p (p v1 H0) (p v1 v1))))) := congrArg (fun q => (eval v0 (eval x (eval v0 q)))) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval v0 (eval x (p v0 (p (p v1 H0) (p v1 v1))))) := congrArg (fun q => (eval v0 (eval x q))) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval v0 (p x (p v0 (p (p v1 H0) (p v1 v1))))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr4 x v0 v1 H0 s0))
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
