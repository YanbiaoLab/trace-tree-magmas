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
      (s0 : Step x v0 H0) :
      Code v0 (p v0 (p (p H0 (p v1 (p x x))) v0)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_x q_v0 q_H0 ∧ a = q_v0 ∧ b = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R (R (L (R b)))))
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) at e1
    have cyc : q_v0 = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := sz_lt_p_left q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) at e1
    have cyc : q_v0 = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := sz_lt_p_left q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change x = q_v0 at e1
    have e2 := congrArg (fun q => (R q)) hb
    change x = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) at e2
    have cyc : q_v0 = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : x = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) := e2; let pst0 : q_v0 = x := Eq.symm (peq1); let pst1 : q_v0 = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) := Eq.trans (pst0) (peq2); pst1)
    have hlt : sz q_v0 < sz (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_v1 (p q_x q_x)))) (sz_lt_p_left (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change x = q_v0 at e1
    have e2 := congrArg (fun q => (R q)) hb
    change x = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) at e2
    have cyc : q_v0 = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : x = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) := e2; let pst0 : q_v0 = x := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) := Eq.trans (pst0) (peq2); pst1)
    have hlt : sz q_v0 < sz (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) := sz_lt_p_right (p q_H0 (p q_v1 (p q_x q_x))) q_v0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step x v0 H0) :
    ¬ ∃ o, Code H0 (p v1 (p x x)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x v0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change x = (p (p q_x q_v0) (p q_v1 (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change x = q_v0 at e3
      have cyc : x = (p (p q_x (p x v0)) (p q_v1 (p q_x q_x))) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : x = (p (p q_x q_v0) (p q_v1 (p q_x q_x))) := e2; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = (p (p q_x (p x v0)) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst1); let pst3 : x = (p (p q_x (p x v0)) (p q_v1 (p q_x q_x))) := Eq.trans (peq2) (pst2); pst3)
      have hlt : sz x < sz (p (p q_x (p x v0)) (p q_v1 (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x v0) (sz_lt_p_right q_x (p x v0))) (sz_lt_p_left (p q_x (p x v0)) (p q_v1 (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x v0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change x = (p q_H0 (p q_v1 (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change x = q_v0 at e3
      have cyc : q_H0 = (p q_H0 (p q_v1 (p q_x q_x))) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : x = (p q_H0 (p q_v1 (p q_x q_x))) := e2; let peq3 : x = q_v0 := e3; let pst0 : (p q_H0 (p q_v1 (p q_x q_x))) = x := Eq.symm (peq2); let pst1 : (p q_H0 (p q_v1 (p q_x q_x))) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x v0) := Eq.symm (peq0); let pst3 : (p x v0) = (p (p q_H0 (p q_v1 (p q_x q_x))) v0) := congrArg (fun q => p q v0) (peq2); let pst4 : q_v0 = (p (p q_H0 (p q_v1 (p q_x q_x))) v0) := Eq.trans (pst2) (pst3); let pst5 : (p q_H0 (p q_v1 (p q_x q_x))) = (p (p q_H0 (p q_v1 (p q_x q_x))) v0) := Eq.trans (pst1) (pst4); let pst6 : q_H0 = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => L q) (pst5); pst6)
      have hlt : sz q_H0 < sz (p q_H0 (p q_v1 (p q_x q_x))) := sz_lt_p_left q_H0 (p q_v1 (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change H0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change x = (p (p q_x q_v0) (p q_v1 (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change x = q_v0 at e3
      have cyc : q_v0 = (p (p q_x q_v0) (p q_v1 (p q_x q_x))) := (let peq2 : x = (p (p q_x q_v0) (p q_v1 (p q_x q_x))) := e2; let peq3 : x = q_v0 := e3; let pst0 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = x := Eq.symm (peq2); let pst1 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p q_x q_v0) (p q_v1 (p q_x q_x))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_x q_v0) (p q_v1 (p q_x q_x))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_v1 (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1s0, u1a, u1b, u1o⟩
        have u1s0B := step_bound u1s0
        let u1s0out := u1_H0
        cases u1s0 with
        | raw =>
          have cyc : u1_v0 = (p u1_v0 u1_v0) := (let peq2 : x = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => (L (R q))) (hb); let peq3 : x = q_v0 := congrArg (fun q => (R (R q))) (hb); let peq8 : q_x = u1_v0 := u1a; let peq9 : q_v0 = (p u1_v0 (p (p (p u1_x u1_v0) (p u1_v1 (p u1_x u1_x))) u1_v0)) := u1b; let pst0 : (p q_H0 (p q_v1 (p q_x q_x))) = x := Eq.symm (peq2); let pst1 : (p q_H0 (p q_v1 (p q_x q_x))) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_H0 (p q_v1 (p q_x q_x))) := Eq.symm (pst1); let pst3 : (p q_x q_x) = (p u1_v0 q_x) := congrArg (fun q => p q q_x) (peq8); let pst4 : (p u1_v0 q_x) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (peq8); let pst5 : (p q_x q_x) = (p u1_v0 u1_v0) := Eq.trans (pst3) (pst4); let pst6 : (p q_v1 (p q_x q_x)) = (p q_v1 (p u1_v0 u1_v0)) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p q_H0 (p q_v1 (p q_x q_x))) = (p q_H0 (p q_v1 (p u1_v0 u1_v0))) := congrArg (fun q => p q_H0 q) (pst6); let pst8 : q_v0 = (p q_H0 (p q_v1 (p u1_v0 u1_v0))) := Eq.trans (pst2) (pst7); let pst9 : (p q_H0 (p q_v1 (p u1_v0 u1_v0))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H0 (p q_v1 (p u1_v0 u1_v0))) = (p u1_v0 (p (p (p u1_x u1_v0) (p u1_v1 (p u1_x u1_x))) u1_v0)) := Eq.trans (pst9) (peq9); let pst11 : (p q_v1 (p u1_v0 u1_v0)) = (p (p (p u1_x u1_v0) (p u1_v1 (p u1_x u1_x))) u1_v0) := congrArg (fun q => R q) (pst10); let pst12 : (p u1_v0 u1_v0) = u1_v0 := congrArg (fun q => R q) (pst11); let pst13 : u1_v0 = (p u1_v0 u1_v0) := Eq.symm (pst12); pst13)
          have hlt : sz u1_v0 < sz (p u1_v0 u1_v0) := sz_lt_p_left u1_v0 u1_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u1s0h =>
          have cyc : u1_v0 = (p u1_v0 u1_v0) := (let peq2 : x = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => (L (R q))) (hb); let peq3 : x = q_v0 := congrArg (fun q => (R (R q))) (hb); let peq8 : q_x = u1_v0 := u1a; let peq9 : q_v0 = (p u1_v0 (p (p u1s0out (p u1_v1 (p u1_x u1_x))) u1_v0)) := u1b; let pst0 : (p q_H0 (p q_v1 (p q_x q_x))) = x := Eq.symm (peq2); let pst1 : (p q_H0 (p q_v1 (p q_x q_x))) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_H0 (p q_v1 (p q_x q_x))) := Eq.symm (pst1); let pst3 : (p q_x q_x) = (p u1_v0 q_x) := congrArg (fun q => p q q_x) (peq8); let pst4 : (p u1_v0 q_x) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (peq8); let pst5 : (p q_x q_x) = (p u1_v0 u1_v0) := Eq.trans (pst3) (pst4); let pst6 : (p q_v1 (p q_x q_x)) = (p q_v1 (p u1_v0 u1_v0)) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p q_H0 (p q_v1 (p q_x q_x))) = (p q_H0 (p q_v1 (p u1_v0 u1_v0))) := congrArg (fun q => p q_H0 q) (pst6); let pst8 : q_v0 = (p q_H0 (p q_v1 (p u1_v0 u1_v0))) := Eq.trans (pst2) (pst7); let pst9 : (p q_H0 (p q_v1 (p u1_v0 u1_v0))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H0 (p q_v1 (p u1_v0 u1_v0))) = (p u1_v0 (p (p u1s0out (p u1_v1 (p u1_x u1_x))) u1_v0)) := Eq.trans (pst9) (peq9); let pst11 : (p q_v1 (p u1_v0 u1_v0)) = (p (p u1s0out (p u1_v1 (p u1_x u1_x))) u1_v0) := congrArg (fun q => R q) (pst10); let pst12 : (p u1_v0 u1_v0) = u1_v0 := congrArg (fun q => R q) (pst11); let pst13 : u1_v0 = (p u1_v0 u1_v0) := Eq.symm (pst12); pst13)
          have hlt : sz u1_v0 < sz (p u1_v0 u1_v0) := sz_lt_p_left u1_v0 u1_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have u0s0hB := code_bounds u0s0h
        have s0B := s0B
        have qs0B := qs0B
        have u0s0B := u0s0B
        have p0 := ha
        change H0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change x = (p q_H0 (p q_v1 (p q_x q_x))) at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change x = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have p5 := u0a
        change x = u0_v0 at p5
        have z5 := congrArg sz p5
        have p6 := u0b
        change v0 = (p u0_v0 (p (p u0s0out (p u0_v1 (p u0_x u0_x))) u0_v0)) at p6
        have z6 := congrArg sz p6
        have p7 := u0o
        change H0 = u0_x at p7
        have z7 := congrArg sz p7
        simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB u0s0hB s0B qs0B u0s0B z0 z1 z2 z3 z4 z5 z6 z7
        omega
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step x v0 H0) :
    ¬ ∃ o, Code (p H0 (p v1 (p x x))) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p (p x v0) (p v1 (p x x))) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) at e1
      have cyc : v0 = (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := (let peq0 : (p (p x v0) (p v1 (p x x))) = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := e1; let pst0 : q_v0 = (p (p x v0) (p v1 (p x x))) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := congrArg (fun q => p q (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) (pst0); let pst2 : (p q_x q_v0) = (p q_x (p (p x v0) (p v1 (p x x)))) := congrArg (fun q => p q_x q) (pst0); let pst3 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst2); let pst4 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x)))) := congrArg (fun q => p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q) (pst0); let pst6 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x)))) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := congrArg (fun q => p (p (p x v0) (p v1 (p x x))) q) (pst6); let pst8 : (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := Eq.trans (pst1) (pst7); let pst9 : v0 = (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v0 < sz (p (p (p x v0) (p v1 (p x x))) (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x v0) (sz_lt_p_left (p x v0) (p v1 (p x x)))) (sz_lt_p_left (p (p x v0) (p v1 (p x x))) (p (p (p q_x (p (p x v0) (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p (p x v0) (p v1 (p x x))) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) at e1
      have cyc : v0 = (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := (let peq0 : (p (p x v0) (p v1 (p x x))) = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := e1; let pst0 : q_v0 = (p (p x v0) (p v1 (p x x))) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := congrArg (fun q => p q (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) (pst0); let pst2 : (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst0); let pst3 : (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := congrArg (fun q => p (p (p x v0) (p v1 (p x x))) q) (pst2); let pst4 : (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := Eq.trans (pst1) (pst3); let pst5 : v0 = (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := Eq.trans (peq1) (pst4); pst5)
      have hlt : sz v0 < sz (p (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x v0) (sz_lt_p_left (p x v0) (p v1 (p x x)))) (sz_lt_p_left (p (p x v0) (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p (p x v0) (p v1 (p x x)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := (let peq0 : (p H0 (p v1 (p x x))) = q_v0 := ha; let peq1 : v0 = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := hb; let peq3 : x = u0_v0 := u0a; let peq4 : v0 = (p u0_v0 (p (p (p u0_x u0_v0) (p u0_v1 (p u0_x u0_x))) u0_v0)) := u0b; let pst0 : q_v0 = (p H0 (p v1 (p x x))) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := congrArg (fun q => p q (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) (pst0); let pst2 : (p q_x q_v0) = (p q_x (p H0 (p v1 (p x x)))) := congrArg (fun q => p q_x q) (pst0); let pst3 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst2); let pst4 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q) (pst0); let pst6 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := Eq.trans (pst4) (pst5); let pst7 : (p (p H0 (p v1 (p x x))) (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p (p H0 (p v1 (p x x))) q) (pst6); let pst8 : (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (pst1) (pst7); let pst9 : v0 = (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (peq1) (pst8); let pst10 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst11 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst12 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst10) (pst11); let pst13 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst12); let pst14 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst13); let pst15 : (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p q (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) (pst14); let pst16 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst17 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst18 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst16) (pst17); let pst19 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst18); let pst20 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst19); let pst21 : (p q_x (p H0 (p v1 (p x x)))) = (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) := congrArg (fun q => p q_x q) (pst20); let pst22 : (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) = (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst21); let pst23 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p q (p H0 (p v1 (p x x)))) (pst22); let pst24 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst25 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst26 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst24) (pst25); let pst27 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst26); let pst28 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst27); let pst29 : (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) q) (pst28); let pst30 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0)))) := Eq.trans (pst23) (pst29); let pst31 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := congrArg (fun q => p (p H0 (p v1 (p u0_v0 u0_v0))) q) (pst30); let pst32 : (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst15) (pst31); let pst33 : v0 = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst9) (pst32); let pst34 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = v0 := Eq.symm (pst33); let pst35 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = (p u0_v0 (p (p (p u0_x u0_v0) (p u0_v1 (p u0_x u0_x))) u0_v0)) := Eq.trans (pst34) (peq4); let pst36 : (p H0 (p v1 (p u0_v0 u0_v0))) = u0_v0 := congrArg (fun q => L q) (pst35); let pst37 : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := Eq.symm (pst36); pst37)
        have hlt : sz u0_v0 < sz (p H0 (p v1 (p u0_v0 u0_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right v1 (p u0_v0 u0_v0))) (sz_lt_p_right H0 (p v1 (p u0_v0 u0_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := (let peq0 : (p H0 (p v1 (p x x))) = q_v0 := ha; let peq1 : v0 = (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := hb; let peq3 : x = u0_v0 := u0a; let peq4 : v0 = (p u0_v0 (p (p u0s0out (p u0_v1 (p u0_x u0_x))) u0_v0)) := u0b; let pst0 : q_v0 = (p H0 (p v1 (p x x))) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) := congrArg (fun q => p q (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) (pst0); let pst2 : (p q_x q_v0) = (p q_x (p H0 (p v1 (p x x)))) := congrArg (fun q => p q_x q) (pst0); let pst3 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst2); let pst4 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q) (pst0); let pst6 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := Eq.trans (pst4) (pst5); let pst7 : (p (p H0 (p v1 (p x x))) (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p (p H0 (p v1 (p x x))) q) (pst6); let pst8 : (p q_v0 (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (pst1) (pst7); let pst9 : v0 = (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (peq1) (pst8); let pst10 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst11 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst12 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst10) (pst11); let pst13 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst12); let pst14 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst13); let pst15 : (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p q (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) (pst14); let pst16 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst17 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst18 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst16) (pst17); let pst19 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst18); let pst20 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst19); let pst21 : (p q_x (p H0 (p v1 (p x x)))) = (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) := congrArg (fun q => p q_x q) (pst20); let pst22 : (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) = (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst21); let pst23 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p q (p H0 (p v1 (p x x)))) (pst22); let pst24 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst25 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst26 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst24) (pst25); let pst27 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst26); let pst28 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst27); let pst29 : (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) q) (pst28); let pst30 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0)))) := Eq.trans (pst23) (pst29); let pst31 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := congrArg (fun q => p (p H0 (p v1 (p u0_v0 u0_v0))) q) (pst30); let pst32 : (p (p H0 (p v1 (p x x))) (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst15) (pst31); let pst33 : v0 = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst9) (pst32); let pst34 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = v0 := Eq.symm (pst33); let pst35 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p (p q_x (p H0 (p v1 (p u0_v0 u0_v0)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = (p u0_v0 (p (p u0s0out (p u0_v1 (p u0_x u0_x))) u0_v0)) := Eq.trans (pst34) (peq4); let pst36 : (p H0 (p v1 (p u0_v0 u0_v0))) = u0_v0 := congrArg (fun q => L q) (pst35); let pst37 : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := Eq.symm (pst36); pst37)
        have hlt : sz u0_v0 < sz (p H0 (p v1 (p u0_v0 u0_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right v1 (p u0_v0 u0_v0))) (sz_lt_p_right H0 (p v1 (p u0_v0 u0_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := (let peq0 : (p H0 (p v1 (p x x))) = q_v0 := ha; let peq1 : v0 = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := hb; let peq3 : x = u0_v0 := u0a; let peq4 : v0 = (p u0_v0 (p (p (p u0_x u0_v0) (p u0_v1 (p u0_x u0_x))) u0_v0)) := u0b; let pst0 : q_v0 = (p H0 (p v1 (p x x))) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := congrArg (fun q => p q (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) (pst0); let pst2 : (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst0); let pst3 : (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p (p H0 (p v1 (p x x))) q) (pst2); let pst4 : (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (pst1) (pst3); let pst5 : v0 = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (peq1) (pst4); let pst6 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst7 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst8 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst6) (pst7); let pst9 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst8); let pst10 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst9); let pst11 : (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p q (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) (pst10); let pst12 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst13 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst14 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst12) (pst13); let pst15 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst14); let pst16 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst15); let pst17 : (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst16); let pst18 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := congrArg (fun q => p (p H0 (p v1 (p u0_v0 u0_v0))) q) (pst17); let pst19 : (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst11) (pst18); let pst20 : v0 = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst5) (pst19); let pst21 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = v0 := Eq.symm (pst20); let pst22 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = (p u0_v0 (p (p (p u0_x u0_v0) (p u0_v1 (p u0_x u0_x))) u0_v0)) := Eq.trans (pst21) (peq4); let pst23 : (p H0 (p v1 (p u0_v0 u0_v0))) = u0_v0 := congrArg (fun q => L q) (pst22); let pst24 : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := Eq.symm (pst23); pst24)
        have hlt : sz u0_v0 < sz (p H0 (p v1 (p u0_v0 u0_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right v1 (p u0_v0 u0_v0))) (sz_lt_p_right H0 (p v1 (p u0_v0 u0_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := (let peq0 : (p H0 (p v1 (p x x))) = q_v0 := ha; let peq1 : v0 = (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := hb; let peq3 : x = u0_v0 := u0a; let peq4 : v0 = (p u0_v0 (p (p u0s0out (p u0_v1 (p u0_x u0_x))) u0_v0)) := u0b; let pst0 : q_v0 = (p H0 (p v1 (p x x))) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) := congrArg (fun q => p q (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) (pst0); let pst2 : (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst0); let pst3 : (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p (p H0 (p v1 (p x x))) q) (pst2); let pst4 : (p q_v0 (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0)) = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (pst1) (pst3); let pst5 : v0 = (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := Eq.trans (peq1) (pst4); let pst6 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst7 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst8 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst6) (pst7); let pst9 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst8); let pst10 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst9); let pst11 : (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) := congrArg (fun q => p q (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) (pst10); let pst12 : (p x x) = (p u0_v0 x) := congrArg (fun q => p q x) (peq3); let pst13 : (p u0_v0 x) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (peq3); let pst14 : (p x x) = (p u0_v0 u0_v0) := Eq.trans (pst12) (pst13); let pst15 : (p v1 (p x x)) = (p v1 (p u0_v0 u0_v0)) := congrArg (fun q => p v1 q) (pst14); let pst16 : (p H0 (p v1 (p x x))) = (p H0 (p v1 (p u0_v0 u0_v0))) := congrArg (fun q => p H0 q) (pst15); let pst17 : (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst16); let pst18 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := congrArg (fun q => p (p H0 (p v1 (p u0_v0 u0_v0))) q) (pst17); let pst19 : (p (p H0 (p v1 (p x x))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x))))) = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst11) (pst18); let pst20 : v0 = (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) := Eq.trans (pst5) (pst19); let pst21 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = v0 := Eq.symm (pst20); let pst22 : (p (p H0 (p v1 (p u0_v0 u0_v0))) (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p u0_v0 u0_v0))))) = (p u0_v0 (p (p u0s0out (p u0_v1 (p u0_x u0_x))) u0_v0)) := Eq.trans (pst21) (peq4); let pst23 : (p H0 (p v1 (p u0_v0 u0_v0))) = u0_v0 := congrArg (fun q => L q) (pst22); let pst24 : u0_v0 = (p H0 (p v1 (p u0_v0 u0_v0))) := Eq.symm (pst23); pst24)
        have hlt : sz u0_v0 < sz (p H0 (p v1 (p u0_v0 u0_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right v1 (p u0_v0 u0_v0))) (sz_lt_p_right H0 (p v1 (p u0_v0 u0_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step x v0 H0) :
    ¬ ∃ o, Code v0 (p (p H0 (p v1 (p x x))) v0) o := by
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
      change (p (p x v0) (p v1 (p x x))) = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) at e2
      have cyc : q_v0 = (p (p x q_v0) (p v1 (p x x))) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p (p x v0) (p v1 (p x x))) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) (p v1 (p x x))) = (p (p x q_v0) (p v1 (p x x))) := congrArg (fun q => p q (p v1 (p x x))) (pst0); let pst2 : (p (p x q_v0) (p v1 (p x x))) = (p (p x v0) (p v1 (p x x))) := Eq.symm (pst1); let pst3 : (p (p x q_v0) (p v1 (p x x))) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p x q_v0) (p v1 (p x x))) := Eq.symm (pst3); pst4)
      have hlt : sz q_v0 < sz (p (p x q_v0) (p v1 (p x x))) := Nat.lt_trans (sz_lt_p_right x q_v0) (sz_lt_p_left (p x q_v0) (p v1 (p x x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p (p x v0) (p v1 (p x x))) = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) at e2
      have cyc : q_v0 = (p (p x q_v0) (p v1 (p x x))) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p (p x v0) (p v1 (p x x))) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p (p x v0) (p v1 (p x x))) = (p (p x q_v0) (p v1 (p x x))) := congrArg (fun q => p q (p v1 (p x x))) (pst0); let pst2 : (p (p x q_v0) (p v1 (p x x))) = (p (p x v0) (p v1 (p x x))) := Eq.symm (pst1); let pst3 : (p (p x q_v0) (p v1 (p x x))) = q_v0 := Eq.trans (pst2) (peq1); let pst4 : q_v0 = (p (p x q_v0) (p v1 (p x x))) := Eq.symm (pst3); pst4)
      have hlt : sz q_v0 < sz (p (p x q_v0) (p v1 (p x x))) := Nat.lt_trans (sz_lt_p_right x q_v0) (sz_lt_p_left (p x q_v0) (p v1 (p x x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p H0 (p v1 (p x x))) = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) at e2
      have cyc : H0 = (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p H0 (p v1 (p x x))) = q_v0 := e1; let peq2 : v0 = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) := e2; let pst0 : q_v0 = (p H0 (p v1 (p x x))) := Eq.symm (peq1); let pst1 : v0 = (p H0 (p v1 (p x x))) := Eq.trans (peq0) (pst0); let pst2 : (p H0 (p v1 (p x x))) = v0 := Eq.symm (pst1); let pst3 : (p H0 (p v1 (p x x))) = (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) := Eq.trans (pst2) (peq2); let pst4 : (p q_x q_v0) = (p q_x (p H0 (p v1 (p x x)))) := congrArg (fun q => p q_x q) (pst0); let pst5 : (p (p q_x q_v0) (p q_v1 (p q_x q_x))) = (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => p q (p q_v1 (p q_x q_x))) (pst4); let pst6 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst7 : (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) q) (pst0); let pst8 : (p (p (p q_x q_v0) (p q_v1 (p q_x q_x))) q_v0) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := Eq.trans (pst6) (pst7); let pst9 : (p H0 (p v1 (p x x))) = (p (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := Eq.trans (pst3) (pst8); let pst10 : H0 = (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := congrArg (fun q => L q) (pst9); pst10)
      have hlt : sz H0 < sz (p (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left H0 (p v1 (p x x))) (sz_lt_p_right q_x (p H0 (p v1 (p x x))))) (sz_lt_p_left (p q_x (p H0 (p v1 (p x x)))) (p q_v1 (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p H0 (p v1 (p x x))) = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) at e2
      have cyc : q_H0 = (p q_H0 (p q_v1 (p q_x q_x))) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p H0 (p v1 (p x x))) = q_v0 := e1; let peq2 : v0 = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) := e2; let pst0 : q_v0 = (p H0 (p v1 (p x x))) := Eq.symm (peq1); let pst1 : v0 = (p H0 (p v1 (p x x))) := Eq.trans (peq0) (pst0); let pst2 : (p H0 (p v1 (p x x))) = v0 := Eq.symm (pst1); let pst3 : (p H0 (p v1 (p x x))) = (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) := Eq.trans (pst2) (peq2); let pst4 : (p (p q_H0 (p q_v1 (p q_x q_x))) q_v0) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst0); let pst5 : (p H0 (p v1 (p x x))) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p H0 (p v1 (p x x)))) := Eq.trans (pst3) (pst4); let pst6 : (p v1 (p x x)) = (p H0 (p v1 (p x x))) := congrArg (fun q => R q) (pst5); let pst7 : H0 = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => L q) (pst5); let pst8 : (p H0 (p v1 (p x x))) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p v1 (p x x))) := congrArg (fun q => p q (p v1 (p x x))) (pst7); let pst9 : (p v1 (p x x)) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p v1 (p x x))) := Eq.trans (pst6) (pst8); let pst10 : (p x x) = (p v1 (p x x)) := congrArg (fun q => R q) (pst9); let pst11 : v1 = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => L q) (pst9); let pst12 : (p v1 (p x x)) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p x x)) := congrArg (fun q => p q (p x x)) (pst11); let pst13 : (p x x) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p x x)) := Eq.trans (pst10) (pst12); let pst14 : x = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => L q) (pst13); let pst15 : (p q_H0 (p q_v1 (p q_x q_x))) = x := Eq.symm (pst14); let pst16 : x = (p x x) := congrArg (fun q => R q) (pst13); let pst17 : (p q_H0 (p q_v1 (p q_x q_x))) = (p x x) := Eq.trans (pst15) (pst16); let pst18 : (p x x) = (p (p q_H0 (p q_v1 (p q_x q_x))) x) := congrArg (fun q => p q x) (pst14); let pst19 : (p (p q_H0 (p q_v1 (p q_x q_x))) x) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p q_H0 (p q_v1 (p q_x q_x)))) := congrArg (fun q => p (p q_H0 (p q_v1 (p q_x q_x))) q) (pst14); let pst20 : (p x x) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p q_H0 (p q_v1 (p q_x q_x)))) := Eq.trans (pst18) (pst19); let pst21 : (p q_H0 (p q_v1 (p q_x q_x))) = (p (p q_H0 (p q_v1 (p q_x q_x))) (p q_H0 (p q_v1 (p q_x q_x)))) := Eq.trans (pst17) (pst20); let pst22 : q_H0 = (p q_H0 (p q_v1 (p q_x q_x))) := congrArg (fun q => L q) (pst21); pst22)
      have hlt : sz q_H0 < sz (p q_H0 (p q_v1 (p q_x q_x))) := sz_lt_p_left q_H0 (p q_v1 (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval (eval x v0) (eval v1 (eval x x))) v0))) := by
  let H0 := eval x v0
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v0 = v0 := by
    change v0 = v0
    rfl
  have s0 : Step x v0 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v0
  change x = (eval v0 (eval v0 (eval (eval H0 (eval v1 (eval x x))) v0)))
  have rawEq : (eval v0 (eval v0 (eval (eval H0 (eval v1 (eval x x))) v0))) = (eval v0 (p v0 (p (p H0 (p v1 (p x x))) v0))) := by
    calc
      (eval v0 (eval v0 (eval (eval H0 (eval v1 (eval x x))) v0))) = (eval v0 (eval v0 (eval (eval H0 (eval v1 (p x x))) v0))) := congrArg (fun q => (eval v0 (eval v0 (eval (eval H0 (eval v1 q)) v0)))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval v0 (eval (eval H0 (p v1 (p x x))) v0))) := congrArg (fun q => (eval v0 (eval v0 (eval (eval H0 q) v0)))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval v0 (eval (p H0 (p v1 (p x x))) v0))) := congrArg (fun q => (eval v0 (eval v0 (eval q v0)))) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval v0 (eval v0 (p (p H0 (p v1 (p x x))) v0))) := congrArg (fun q => (eval v0 (eval v0 q))) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval v0 (p v0 (p (p H0 (p v1 (p x x))) v0))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr4 x v0 v1 H0 s0))
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
