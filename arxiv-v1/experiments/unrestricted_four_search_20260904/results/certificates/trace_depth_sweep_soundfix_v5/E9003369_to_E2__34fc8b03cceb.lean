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
      (s0 : Step x v0 H0)
      (s1 : Step (p v1 v1) v0 H1) :
      Code v0 (p H0 (p x (p v0 H1))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v0 q_H0 ∧ Step (p q_v1 q_v1) q_v0 q_H1 ∧ a = q_v0 ∧ b = (p q_H0 (p q_x (p q_v0 q_H1))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R b))
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
      change v = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) at e1
      have cyc : v = (p (p q_x (p v k)) (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst2 : (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) = (p (p q_x (p v k)) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := congrArg (fun q => p q (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) (pst1); let pst3 : (p q_v0 (p (p q_v1 q_v1) q_v0)) = (p (p v k) (p (p q_v1 q_v1) q_v0)) := congrArg (fun q => p q (p (p q_v1 q_v1) q_v0)) (pst0); let pst4 : (p (p q_v1 q_v1) q_v0) = (p (p q_v1 q_v1) (p v k)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst0); let pst5 : (p (p v k) (p (p q_v1 q_v1) q_v0)) = (p (p v k) (p (p q_v1 q_v1) (p v k))) := congrArg (fun q => p (p v k) q) (pst4); let pst6 : (p q_v0 (p (p q_v1 q_v1) q_v0)) = (p (p v k) (p (p q_v1 q_v1) (p v k))) := Eq.trans (pst3) (pst5); let pst7 : (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) = (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k)))) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p (p q_x (p v k)) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) = (p (p q_x (p v k)) (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := congrArg (fun q => p (p q_x (p v k)) q) (pst7); let pst9 : (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) = (p (p q_x (p v k)) (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := Eq.trans (pst2) (pst8); let pst10 : v = (p (p q_x (p v k)) (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := Eq.trans (peq1) (pst9); pst10)
      have hlt : sz v < sz (p (p q_x (p v k)) (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_right q_x (p v k))) (sz_lt_p_left (p q_x (p v k)) (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) at e1
      have cyc : v = (p (p q_x (p v k)) (p q_x (p (p v k) q_H1))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst2 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = (p (p q_x (p v k)) (p q_x (p q_v0 q_H1))) := congrArg (fun q => p q (p q_x (p q_v0 q_H1))) (pst1); let pst3 : (p q_v0 q_H1) = (p (p v k) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst4 : (p q_x (p q_v0 q_H1)) = (p q_x (p (p v k) q_H1)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p q_x (p v k)) (p q_x (p q_v0 q_H1))) = (p (p q_x (p v k)) (p q_x (p (p v k) q_H1))) := congrArg (fun q => p (p q_x (p v k)) q) (pst4); let pst6 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = (p (p q_x (p v k)) (p q_x (p (p v k) q_H1))) := Eq.trans (pst2) (pst5); let pst7 : v = (p (p q_x (p v k)) (p q_x (p (p v k) q_H1))) := Eq.trans (peq1) (pst6); pst7)
      have hlt : sz v < sz (p (p q_x (p v k)) (p q_x (p (p v k) q_H1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_right q_x (p v k))) (sz_lt_p_left (p q_x (p v k)) (p q_x (p (p v k) q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) at e1
      have cyc : v = (p q_H0 (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_v1 q_v1) q_v0)) = (p (p v k) (p (p q_v1 q_v1) q_v0)) := congrArg (fun q => p q (p (p q_v1 q_v1) q_v0)) (pst0); let pst2 : (p (p q_v1 q_v1) q_v0) = (p (p q_v1 q_v1) (p v k)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst0); let pst3 : (p (p v k) (p (p q_v1 q_v1) q_v0)) = (p (p v k) (p (p q_v1 q_v1) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_v1 q_v1) q_v0)) = (p (p v k) (p (p q_v1 q_v1) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) = (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k)))) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) = (p q_H0 (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := congrArg (fun q => p q_H0 q) (pst5); let pst7 : v = (p q_H0 (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := Eq.trans (peq1) (pst6); pst7)
      have hlt : sz v < sz (p q_H0 (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_v1 q_v1) (p v k)))) (sz_lt_p_right q_x (p (p v k) (p (p q_v1 q_v1) (p v k))))) (sz_lt_p_right q_H0 (p q_x (p (p v k) (p (p q_v1 q_v1) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_H0 (p q_x (p q_v0 q_H1))) at e1
      have cyc : v = (p q_H0 (p q_x (p (p v k) q_H1))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_H0 (p q_x (p q_v0 q_H1))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = (p (p v k) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst2 : (p q_x (p q_v0 q_H1)) = (p q_x (p (p v k) q_H1)) := congrArg (fun q => p q_x q) (pst1); let pst3 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p q_H0 (p q_x (p (p v k) q_H1))) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : v = (p q_H0 (p q_x (p (p v k) q_H1))) := Eq.trans (peq1) (pst3); pst4)
      have hlt : sz v < sz (p q_H0 (p q_x (p (p v k) q_H1))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H1)) (sz_lt_p_right q_x (p (p v k) q_H1))) (sz_lt_p_right q_H0 (p q_x (p (p v k) q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) at e1
      have cyc : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := (let peq0 : v1 = q_v0 := e0; let peq1 : v1 = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := e1; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v1 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) at e1
      have cyc : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := (let peq0 : v1 = q_v0 := e0; let peq1 : v1 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := e1; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_x (p q_v0 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) at e1
      have cyc : q_v0 = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := (let peq0 : v1 = q_v0 := e0; let peq1 : v1 = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := e1; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v1 q_v1) q_v0)) (sz_lt_p_right q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) (sz_lt_p_right q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v1 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_H0 (p q_x (p q_v0 q_H1))) at e1
      have cyc : q_v0 = (p q_H0 (p q_x (p q_v0 q_H1))) := (let peq0 : v1 = q_v0 := e0; let peq1 : v1 = (p q_H0 (p q_x (p q_v0 q_H1))) := e1; let pst0 : q_v0 = v1 := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 (p q_x (p q_v0 q_H1))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_H0 (p q_x (p q_v0 q_H1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H1) (sz_lt_p_right q_x (p q_v0 q_H1))) (sz_lt_p_right q_H0 (p q_x (p q_v0 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step (p v1 v1) v0 H1) :
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
        have e1 := congrArg (fun q => (L (L q))) hb
        change v1 = q_x at e1
        have e2 := congrArg (fun q => (R (L q))) hb
        change v1 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) at e3
        have cyc : q_v0 = (p q_v0 (p q_v0 (p (p q_v1 q_v1) q_v0))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v1 = q_x := e1; let peq2 : v1 = q_v0 := e2; let peq3 : v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) := Eq.trans (pst0) (peq3); let pst2 : q_x = v1 := Eq.symm (peq1); let pst3 : q_x = q_v0 := Eq.trans (pst2) (peq2); let pst4 : (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) = (p q_v0 (p q_v0 (p (p q_v1 q_v1) q_v0))) := congrArg (fun q => p q (p q_v0 (p (p q_v1 q_v1) q_v0))) (pst3); let pst5 : q_v0 = (p q_v0 (p q_v0 (p (p q_v1 q_v1) q_v0))) := Eq.trans (pst1) (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v0 (p (p q_v1 q_v1) q_v0))) := sz_lt_p_left q_v0 (p q_v0 (p (p q_v1 q_v1) q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L (L q))) hb
        change v1 = q_x at e1
        have e2 := congrArg (fun q => (R (L q))) hb
        change v1 = q_v0 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 q_H1)) at e3
        have cyc : q_v0 = (p q_v0 (p q_v0 q_H1)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v1 = q_x := e1; let peq2 : v1 = q_v0 := e2; let peq3 : v0 = (p q_x (p q_v0 q_H1)) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 q_H1)) := Eq.trans (pst0) (peq3); let pst2 : q_x = v1 := Eq.symm (peq1); let pst3 : q_x = q_v0 := Eq.trans (pst2) (peq2); let pst4 : (p q_x (p q_v0 q_H1)) = (p q_v0 (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (pst3); let pst5 : q_v0 = (p q_v0 (p q_v0 q_H1)) := Eq.trans (pst1) (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v0 q_H1)) := sz_lt_p_left q_v0 (p q_v0 q_H1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p v1 v1) = q_H0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) at e2
        have cyc : q_v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v1 q_v1) q_v0)) (sz_lt_p_right q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p v1 v1) = q_H0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 q_H1)) at e2
        have cyc : q_v0 = (p q_x (p q_v0 q_H1)) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p q_v0 q_H1)) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 q_H1)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_x (p q_v0 q_H1)) := Nat.lt_trans (sz_lt_p_left q_v0 q_H1) (sz_lt_p_right q_x (p q_v0 q_H1))
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
        change H1 = (p (p q_x q_v0) (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) at p1
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
        change H1 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) at p1
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
        change H1 = (p q_H0 (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0)))) at p1
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
        change H1 = (p q_H0 (p q_x (p q_v0 q_H1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step (p v1 v1) v0 H1) :
    ¬ ∃ o, Code x (p v0 H1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := (let peq1 : v0 = (p q_x q_v0) := congrArg (fun q => (L q)) (hb); let peq2 : (p v1 v1) = q_x := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p q_v0 q_H1) := congrArg (fun q => (R (R q))) (hb); let pst0 : q_x = (p v1 v1) := Eq.symm (peq2); let pst1 : (p q_x q_v0) = (p (p v1 v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : v0 = (p (p v1 v1) q_v0) := Eq.trans (peq1) (pst1); let pst3 : (p (p v1 v1) q_v0) = v0 := Eq.symm (pst2); let pst4 : (p (p v1 v1) q_v0) = (p q_v0 q_H1) := Eq.trans (pst3) (peq3); let pst5 : (p v1 v1) = q_v0 := congrArg (fun q => L q) (pst4); let pst6 : q_v0 = (p v1 v1) := Eq.symm (pst5); let pst7 : (p v1 v1) = q_v0 := Eq.symm (pst6); let pst8 : q_v0 = q_H1 := congrArg (fun q => R q) (pst4); let pst9 : (p v1 v1) = q_H1 := Eq.trans (pst7) (pst8); let pst10 : q_H1 = (p v1 v1) := Eq.symm (pst9); let pst11 : (p v1 v1) = q_v0 := Eq.symm (pst6); let pst12 : q_H1 = q_v0 := Eq.trans (pst10) (pst11); pst12)
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change (p v1 v1) = q_x at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change v0 = (p q_v0 (p (p q_v1 q_v1) q_v0)) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs0hB s1B qs0B qs1B z0 z1 z2 z3 z4
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change (p v1 v1) = q_x at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change v0 = (p q_v0 q_H1) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2 z3 z4
        omega
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
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = (p q_x q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) at p2
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
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = (p q_x q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB s1B qs0B qs1B z0 z1 z2 z3
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
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 (p (p q_v1 q_v1) q_v0))) at p2
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
        change x = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
theorem nr3 (x v0 v1 H0 H1 : CM)
    (s0 : Step x v0 H0)
    (s1 : Step (p v1 v1) v0 H1) :
    ¬ ∃ o, Code H0 (p x (p v0 H1)) o := by
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
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = (p q_x q_v0) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_x at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change (p v1 v1) = q_v0 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p (p q_v1 q_v1) q_v0) at e4
          have cyc : x = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq1 : x = (p q_x q_v0) := e1; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : x = (p q_x (p x v0)) := Eq.trans (peq1) (pst1); pst2)
          have hlt : sz x < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_left x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = (p q_x q_v0) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_x at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change (p v1 v1) = q_v0 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = q_H1 at e4
          have cyc : x = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq1 : x = (p q_x q_v0) := e1; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : x = (p q_x (p x v0)) := Eq.trans (peq1) (pst1); pst2)
          have hlt : sz x < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_left x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_H0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_x at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change (p v1 v1) = q_v0 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p (p q_v1 q_v1) q_v0) at e4
          have cyc : q_x = (p (p q_v1 q_v1) (p q_x q_x)) := (let peq0 : (p x v0) = q_v0 := e0; let peq1 : x = q_H0 := e1; let peq2 : v0 = q_x := e2; let peq3 : (p v1 v1) = q_v0 := e3; let peq4 : v0 = (p (p q_v1 q_v1) q_v0) := e4; let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = (p (p q_v1 q_v1) q_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p x v0) := Eq.symm (peq0); let pst3 : (p x v0) = (p q_H0 v0) := congrArg (fun q => p q v0) (peq1); let pst4 : (p q_H0 v0) = (p q_H0 q_x) := congrArg (fun q => p q_H0 q) (peq2); let pst5 : (p x v0) = (p q_H0 q_x) := Eq.trans (pst3) (pst4); let pst6 : q_v0 = (p q_H0 q_x) := Eq.trans (pst2) (pst5); let pst7 : (p v1 v1) = (p q_H0 q_x) := Eq.trans (peq3) (pst6); let pst8 : v1 = q_H0 := congrArg (fun q => L q) (pst7); let pst9 : q_H0 = v1 := Eq.symm (pst8); let pst10 : v1 = q_x := congrArg (fun q => R q) (pst7); let pst11 : q_H0 = q_x := Eq.trans (pst9) (pst10); let pst12 : x = q_x := Eq.trans (peq1) (pst11); let pst13 : (p x v0) = (p q_x v0) := congrArg (fun q => p q v0) (pst12); let pst14 : (p q_x v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (peq2); let pst15 : (p x v0) = (p q_x q_x) := Eq.trans (pst13) (pst14); let pst16 : q_v0 = (p q_x q_x) := Eq.trans (pst2) (pst15); let pst17 : (p (p q_v1 q_v1) q_v0) = (p (p q_v1 q_v1) (p q_x q_x)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst16); let pst18 : q_x = (p (p q_v1 q_v1) (p q_x q_x)) := Eq.trans (pst1) (pst17); pst18)
          have hlt : sz q_x < sz (p (p q_v1 q_v1) (p q_x q_x)) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right (p q_v1 q_v1) (p q_x q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          let u0s0out := u0_H0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            let u0s1out := u0_H1
            cases u0s1 with
            | raw =>
              have cyc : u0_v0 = (p u0_x u0_v0) := (let peq0 : (p x v0) = q_v0 := ha; let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq3 : (p v1 v1) = q_v0 := congrArg (fun q => (L (R (R q)))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let peq6 : q_x = u0_v0 := u0a; let peq7 : q_v0 = (p (p u0_x u0_v0) (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0)))) := u0b; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p x v0) = (p q_H0 v0) := congrArg (fun q => p q v0) (peq1); let pst2 : (p q_H0 v0) = (p q_H0 q_x) := congrArg (fun q => p q_H0 q) (peq2); let pst3 : (p x v0) = (p q_H0 q_x) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H0 q_x) := Eq.trans (pst0) (pst3); let pst5 : (p v1 v1) = (p q_H0 q_x) := Eq.trans (peq3) (pst4); let pst6 : v1 = q_H0 := congrArg (fun q => L q) (pst5); let pst7 : q_H0 = v1 := Eq.symm (pst6); let pst8 : v1 = q_x := congrArg (fun q => R q) (pst5); let pst9 : q_H0 = q_x := Eq.trans (pst7) (pst8); let pst10 : q_x = v0 := Eq.symm (peq2); let pst11 : q_x = q_H1 := Eq.trans (pst10) (peq4); let pst12 : q_H1 = q_x := Eq.symm (pst11); let pst13 : q_H1 = u0_v0 := Eq.trans (pst12) (peq6); let pst14 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst15 : q_H0 = u0_v0 := Eq.trans (pst9) (pst14); let pst16 : x = u0_v0 := Eq.trans (peq1) (pst15); let pst17 : (p x v0) = (p u0_v0 v0) := congrArg (fun q => p q v0) (pst16); let pst18 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst19 : v0 = u0_v0 := Eq.trans (peq2) (pst18); let pst20 : (p u0_v0 v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : (p x v0) = (p u0_v0 u0_v0) := Eq.trans (pst17) (pst20); let pst22 : q_v0 = (p u0_v0 u0_v0) := Eq.trans (pst0) (pst21); let pst23 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst22); let pst24 : (p u0_v0 u0_v0) = (p (p u0_x u0_v0) (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0)))) := Eq.trans (pst23) (peq7); let pst25 : u0_v0 = (p u0_x u0_v0) := congrArg (fun q => L q) (pst24); pst25)
              have hlt : sz u0_v0 < sz (p u0_x u0_v0) := sz_lt_p_right u0_x u0_v0
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_v0 = (p u0_x u0_v0) := (let peq0 : (p x v0) = q_v0 := ha; let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq3 : (p v1 v1) = q_v0 := congrArg (fun q => (L (R (R q)))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let peq6 : q_x = u0_v0 := u0a; let peq7 : q_v0 = (p (p u0_x u0_v0) (p u0_x (p u0_v0 u0s1out))) := u0b; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p x v0) = (p q_H0 v0) := congrArg (fun q => p q v0) (peq1); let pst2 : (p q_H0 v0) = (p q_H0 q_x) := congrArg (fun q => p q_H0 q) (peq2); let pst3 : (p x v0) = (p q_H0 q_x) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H0 q_x) := Eq.trans (pst0) (pst3); let pst5 : (p v1 v1) = (p q_H0 q_x) := Eq.trans (peq3) (pst4); let pst6 : v1 = q_H0 := congrArg (fun q => L q) (pst5); let pst7 : q_H0 = v1 := Eq.symm (pst6); let pst8 : v1 = q_x := congrArg (fun q => R q) (pst5); let pst9 : q_H0 = q_x := Eq.trans (pst7) (pst8); let pst10 : q_x = v0 := Eq.symm (peq2); let pst11 : q_x = q_H1 := Eq.trans (pst10) (peq4); let pst12 : q_H1 = q_x := Eq.symm (pst11); let pst13 : q_H1 = u0_v0 := Eq.trans (pst12) (peq6); let pst14 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst15 : q_H0 = u0_v0 := Eq.trans (pst9) (pst14); let pst16 : x = u0_v0 := Eq.trans (peq1) (pst15); let pst17 : (p x v0) = (p u0_v0 v0) := congrArg (fun q => p q v0) (pst16); let pst18 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst19 : v0 = u0_v0 := Eq.trans (peq2) (pst18); let pst20 : (p u0_v0 v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : (p x v0) = (p u0_v0 u0_v0) := Eq.trans (pst17) (pst20); let pst22 : q_v0 = (p u0_v0 u0_v0) := Eq.trans (pst0) (pst21); let pst23 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst22); let pst24 : (p u0_v0 u0_v0) = (p (p u0_x u0_v0) (p u0_x (p u0_v0 u0s1out))) := Eq.trans (pst23) (peq7); let pst25 : u0_v0 = (p u0_x u0_v0) := congrArg (fun q => L q) (pst24); pst25)
              have hlt : sz u0_v0 < sz (p u0_x u0_v0) := sz_lt_p_right u0_x u0_v0
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            let u0s1out := u0_H1
            cases u0s1 with
            | raw =>
              have cyc : u0s0out = (p u0_x (p u0s0out (p (p u0_v1 u0_v1) u0s0out))) := (let peq0 : (p x v0) = q_v0 := ha; let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq3 : (p v1 v1) = q_v0 := congrArg (fun q => (L (R (R q)))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let peq6 : q_x = u0_v0 := u0a; let peq7 : q_v0 = (p u0s0out (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0)))) := u0b; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p x v0) = (p q_H0 v0) := congrArg (fun q => p q v0) (peq1); let pst2 : (p q_H0 v0) = (p q_H0 q_x) := congrArg (fun q => p q_H0 q) (peq2); let pst3 : (p x v0) = (p q_H0 q_x) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H0 q_x) := Eq.trans (pst0) (pst3); let pst5 : (p v1 v1) = (p q_H0 q_x) := Eq.trans (peq3) (pst4); let pst6 : v1 = q_H0 := congrArg (fun q => L q) (pst5); let pst7 : q_H0 = v1 := Eq.symm (pst6); let pst8 : v1 = q_x := congrArg (fun q => R q) (pst5); let pst9 : q_H0 = q_x := Eq.trans (pst7) (pst8); let pst10 : q_x = v0 := Eq.symm (peq2); let pst11 : q_x = q_H1 := Eq.trans (pst10) (peq4); let pst12 : q_H1 = q_x := Eq.symm (pst11); let pst13 : q_H1 = u0_v0 := Eq.trans (pst12) (peq6); let pst14 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst15 : q_H0 = u0_v0 := Eq.trans (pst9) (pst14); let pst16 : x = u0_v0 := Eq.trans (peq1) (pst15); let pst17 : (p x v0) = (p u0_v0 v0) := congrArg (fun q => p q v0) (pst16); let pst18 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst19 : v0 = u0_v0 := Eq.trans (peq2) (pst18); let pst20 : (p u0_v0 v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : (p x v0) = (p u0_v0 u0_v0) := Eq.trans (pst17) (pst20); let pst22 : q_v0 = (p u0_v0 u0_v0) := Eq.trans (pst0) (pst21); let pst23 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst22); let pst24 : (p u0_v0 u0_v0) = (p u0s0out (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0)))) := Eq.trans (pst23) (peq7); let pst25 : u0_v0 = u0s0out := congrArg (fun q => L q) (pst24); let pst26 : u0s0out = u0_v0 := Eq.symm (pst25); let pst27 : u0_v0 = (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0))) := congrArg (fun q => R q) (pst24); let pst28 : u0s0out = (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0))) := Eq.trans (pst26) (pst27); let pst29 : (p u0_v0 (p (p u0_v1 u0_v1) u0_v0)) = (p u0s0out (p (p u0_v1 u0_v1) u0_v0)) := congrArg (fun q => p q (p (p u0_v1 u0_v1) u0_v0)) (pst25); let pst30 : (p (p u0_v1 u0_v1) u0_v0) = (p (p u0_v1 u0_v1) u0s0out) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst25); let pst31 : (p u0s0out (p (p u0_v1 u0_v1) u0_v0)) = (p u0s0out (p (p u0_v1 u0_v1) u0s0out)) := congrArg (fun q => p u0s0out q) (pst30); let pst32 : (p u0_v0 (p (p u0_v1 u0_v1) u0_v0)) = (p u0s0out (p (p u0_v1 u0_v1) u0s0out)) := Eq.trans (pst29) (pst31); let pst33 : (p u0_x (p u0_v0 (p (p u0_v1 u0_v1) u0_v0))) = (p u0_x (p u0s0out (p (p u0_v1 u0_v1) u0s0out))) := congrArg (fun q => p u0_x q) (pst32); let pst34 : u0s0out = (p u0_x (p u0s0out (p (p u0_v1 u0_v1) u0s0out))) := Eq.trans (pst28) (pst33); pst34)
              have hlt : sz u0s0out < sz (p u0_x (p u0s0out (p (p u0_v1 u0_v1) u0s0out))) := Nat.lt_trans (sz_lt_p_left u0s0out (p (p u0_v1 u0_v1) u0s0out)) (sz_lt_p_right u0_x (p u0s0out (p (p u0_v1 u0_v1) u0s0out)))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0s0out = (p u0_x (p u0s0out u0s1out)) := (let peq0 : (p x v0) = q_v0 := ha; let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq3 : (p v1 v1) = q_v0 := congrArg (fun q => (L (R (R q)))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let peq6 : q_x = u0_v0 := u0a; let peq7 : q_v0 = (p u0s0out (p u0_x (p u0_v0 u0s1out))) := u0b; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p x v0) = (p q_H0 v0) := congrArg (fun q => p q v0) (peq1); let pst2 : (p q_H0 v0) = (p q_H0 q_x) := congrArg (fun q => p q_H0 q) (peq2); let pst3 : (p x v0) = (p q_H0 q_x) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H0 q_x) := Eq.trans (pst0) (pst3); let pst5 : (p v1 v1) = (p q_H0 q_x) := Eq.trans (peq3) (pst4); let pst6 : v1 = q_H0 := congrArg (fun q => L q) (pst5); let pst7 : q_H0 = v1 := Eq.symm (pst6); let pst8 : v1 = q_x := congrArg (fun q => R q) (pst5); let pst9 : q_H0 = q_x := Eq.trans (pst7) (pst8); let pst10 : q_x = v0 := Eq.symm (peq2); let pst11 : q_x = q_H1 := Eq.trans (pst10) (peq4); let pst12 : q_H1 = q_x := Eq.symm (pst11); let pst13 : q_H1 = u0_v0 := Eq.trans (pst12) (peq6); let pst14 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst15 : q_H0 = u0_v0 := Eq.trans (pst9) (pst14); let pst16 : x = u0_v0 := Eq.trans (peq1) (pst15); let pst17 : (p x v0) = (p u0_v0 v0) := congrArg (fun q => p q v0) (pst16); let pst18 : q_x = u0_v0 := Eq.trans (pst11) (pst13); let pst19 : v0 = u0_v0 := Eq.trans (peq2) (pst18); let pst20 : (p u0_v0 v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : (p x v0) = (p u0_v0 u0_v0) := Eq.trans (pst17) (pst20); let pst22 : q_v0 = (p u0_v0 u0_v0) := Eq.trans (pst0) (pst21); let pst23 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst22); let pst24 : (p u0_v0 u0_v0) = (p u0s0out (p u0_x (p u0_v0 u0s1out))) := Eq.trans (pst23) (peq7); let pst25 : u0_v0 = u0s0out := congrArg (fun q => L q) (pst24); let pst26 : u0s0out = u0_v0 := Eq.symm (pst25); let pst27 : u0_v0 = (p u0_x (p u0_v0 u0s1out)) := congrArg (fun q => R q) (pst24); let pst28 : u0s0out = (p u0_x (p u0_v0 u0s1out)) := Eq.trans (pst26) (pst27); let pst29 : (p u0_v0 u0s1out) = (p u0s0out u0s1out) := congrArg (fun q => p q u0s1out) (pst25); let pst30 : (p u0_x (p u0_v0 u0s1out)) = (p u0_x (p u0s0out u0s1out)) := congrArg (fun q => p u0_x q) (pst29); let pst31 : u0s0out = (p u0_x (p u0s0out u0s1out)) := Eq.trans (pst28) (pst30); pst31)
              have hlt : sz u0s0out < sz (p u0_x (p u0s0out u0s1out)) := Nat.lt_trans (sz_lt_p_left u0s0out u0s1out) (sz_lt_p_right u0_x (p u0s0out u0s1out))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s1h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = (p q_x q_v0) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_x at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change H1 = (p q_v0 (p (p q_v1 q_v1) q_v0)) at e3
          have cyc : x = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq1 : x = (p q_x q_v0) := e1; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : x = (p q_x (p x v0)) := Eq.trans (peq1) (pst1); pst2)
          have hlt : sz x < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_left x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = (p q_x q_v0) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_x at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change H1 = (p q_v0 q_H1) at e3
          have cyc : x = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq1 : x = (p q_x q_v0) := e1; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : x = (p q_x (p x v0)) := Eq.trans (peq1) (pst1); pst2)
          have hlt : sz x < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_left x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have hcB := code_bounds hc
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change (p x v0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change x = q_H0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v0 (p (p q_v1 q_v1) q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
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
          change (p x v0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change x = q_H0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v0 q_H1) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
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
          have epa : x = (p (p (p q_v1 q_v1) (p v1 v1)) (p v1 v1)) := Eq.trans (congrArg (fun q => (L q)) (hb)) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L (R q))) (hb))) (congrArg (fun q => (R (R (R q)))) (hb))) (congrArg (fun q => p (p q_v1 q_v1) q) (Eq.symm (congrArg (fun q => (L (R (R q)))) (hb)))))) (congrArg (fun q => p (p (p q_v1 q_v1) (p v1 v1)) q) (Eq.symm (congrArg (fun q => (L (R (R q)))) (hb)))))
          have epb : v0 = (p (p q_v1 q_v1) (p v1 v1)) := Eq.trans (congrArg (fun q => (L (R q))) (hb)) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L (R q))) (hb))) (congrArg (fun q => (R (R (R q)))) (hb))) (congrArg (fun q => p (p q_v1 q_v1) q) (Eq.symm (congrArg (fun q => (L (R (R q)))) (hb)))))
          apply code_no_pair_left (p (p q_v1 q_v1) (p v1 v1)) (p v1 v1)
          exact ⟨_, by simpa only [epa, epb] using s0h⟩
        | hit qs1h =>
          have epa : x = (p q_H1 (p v1 v1)) := Eq.trans (congrArg (fun q => (L q)) (hb)) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (Eq.symm (congrArg (fun q => (L (R q))) (hb))) (congrArg (fun q => (R (R (R q)))) (hb)))) (congrArg (fun q => p q_H1 q) (Eq.symm (congrArg (fun q => (L (R (R q)))) (hb)))))
          have epb : v0 = q_H1 := Eq.trans (congrArg (fun q => (L (R q))) (hb)) (Eq.trans (Eq.symm (congrArg (fun q => (L (R q))) (hb))) (congrArg (fun q => (R (R (R q)))) (hb)))
          apply code_no_pair_left q_H1 (p v1 v1)
          exact ⟨_, by simpa only [epa, epb] using s0h⟩
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
          change H0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change x = q_H0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (L (R (R q)))) (hb)
          change (p v1 v1) = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := congrArg (fun q => (R (R (R q)))) (hb)
          change v0 = (p (p q_v1 q_v1) q_v0) at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4 z5
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
          change H0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change x = q_H0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (L (R (R q)))) (hb)
          change (p v1 v1) = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := congrArg (fun q => (R (R (R q)))) (hb)
          change v0 = q_H1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4 z5
          omega
    | hit s1h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have epa : x = (p q_x q_v0) := congrArg (fun q => (L q)) (hb)
          have epb : v0 = q_x := congrArg (fun q => (L (R q))) (hb)
          apply code_no_pair_left q_x q_v0
          exact ⟨_, by simpa only [epa, epb] using s0h⟩
        | hit qs1h =>
          have epa : x = (p q_x q_v0) := congrArg (fun q => (L q)) (hb)
          have epb : v0 = q_x := congrArg (fun q => (L (R q))) (hb)
          apply code_no_pair_left q_x q_v0
          exact ⟨_, by simpa only [epa, epb] using s0h⟩
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
          change H0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change x = q_H0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v0 (p (p q_v1 q_v1) q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
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
          change H0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change x = q_H0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v0 q_H1) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval (eval x v0) (eval x (eval v0 (eval (eval v1 v1) v0))))) := by
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
  let H1 := eval (eval v1 v1) v0
  have e1a : (eval v1 v1) = (p v1 v1) := by
    change (eval v1 v1) = (p v1 v1)
    exact (eval_raw (nr0 x v0 v1))
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step (p v1 v1) v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v1 v1) v0
  change x = (eval v0 (eval H0 (eval x (eval v0 H1))))
  have rawEq : (eval v0 (eval H0 (eval x (eval v0 H1)))) = (eval v0 (p H0 (p x (p v0 H1)))) := by
    calc
      (eval v0 (eval H0 (eval x (eval v0 H1)))) = (eval v0 (eval H0 (eval x (p v0 H1)))) := congrArg (fun q => (eval v0 (eval H0 (eval x q)))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval v0 (eval H0 (p x (p v0 H1)))) := congrArg (fun q => (eval v0 (eval H0 q))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval v0 (p H0 (p x (p v0 H1)))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H0 H1 s0 s1))
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
