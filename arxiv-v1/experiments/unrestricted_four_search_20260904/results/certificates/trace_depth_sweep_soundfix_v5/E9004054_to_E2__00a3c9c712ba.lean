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
      (s1 : Step H0 x H1) :
      Code v0 (p v0 (p x (p H1 (p v0 v0)))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_H0 q_x q_H1 ∧ a = q_v0 ∧ b = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) ∧ o = q_x := by
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
      change v = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) = (p (p v k) (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v1) = (p (p v k) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst3 : (p (p q_v0 q_v1) q_x) = (p (p (p v k) q_v1) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)) = (p (p (p (p v k) q_v1) q_x) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst3); let pst5 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst6 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst7 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst5) (pst6); let pst8 : (p (p (p (p v k) q_v1) q_x) (p q_v0 q_v0)) = (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))) := congrArg (fun q => p (p (p (p v k) q_v1) q_x) q) (pst7); let pst9 : (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)) = (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))) := Eq.trans (pst4) (pst8); let pst10 : (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) = (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k)))) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p (p v k) (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) = (p (p v k) (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst10); let pst12 : (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) = (p (p v k) (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))))) := Eq.trans (pst1) (pst11); let pst13 : v = (p (p v k) (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))))) := Eq.trans (peq1) (pst12); pst13)
      have hlt : sz v < sz (p (p v k) (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p (p (p v k) q_v1) q_x) (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_x (p q_H1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_x (p q_H1 (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p v k) (p v k))) := congrArg (fun q => p q_H1 q) (pst4); let pst6 : (p q_x (p q_H1 (p q_v0 q_v0))) = (p q_x (p q_H1 (p (p v k) (p v k)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p v k) (p q_x (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p q_H1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p q_x (p (p q_H0 q_x) (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) = (p (p v k) (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p (p q_H0 q_x) (p q_v0 q_v0)) = (p (p q_H0 q_x) (p (p v k) (p v k))) := congrArg (fun q => p (p q_H0 q_x) q) (pst4); let pst6 : (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) = (p q_x (p (p q_H0 q_x) (p (p v k) (p v k)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p v k) (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) = (p (p v k) (p q_x (p (p q_H0 q_x) (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) = (p (p v k) (p q_x (p (p q_H0 q_x) (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p q_x (p (p q_H0 q_x) (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p q_x (p (p q_H0 q_x) (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p q_H0 q_x) (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_x (p q_H1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_x (p q_H1 (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p v k) (p v k))) := congrArg (fun q => p q_H1 q) (pst4); let pst6 : (p q_x (p q_H1 (p q_v0 q_v0))) = (p q_x (p q_H1 (p (p v k) (p v k)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p v k) (p q_x (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p q_x (p q_H1 (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p q_H1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p q_x (p (p q_H0 q_x) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p q_x (p q_H1 (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step H0 x H1) :
    ¬ ∃ o, Code H1 (p v0 v0) o := by
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
        change (p H0 x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) at e2
        have cyc : x = (p (p (p (p q_x x) q_v1) q_x) (p (p q_x x) (p q_x x))) := (let peq0 : (p H0 x) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p H0 x) := Eq.symm (peq0); let pst1 : v0 = (p H0 x) := Eq.trans (peq1) (pst0); let pst2 : (p H0 x) = v0 := Eq.symm (pst1); let pst3 : (p H0 x) = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v1) = (p (p H0 x) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst5 : (p (p q_v0 q_v1) q_x) = (p (p (p H0 x) q_v1) q_x) := congrArg (fun q => p q q_x) (pst4); let pst6 : (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)) = (p (p (p (p H0 x) q_v1) q_x) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst5); let pst7 : (p q_v0 q_v0) = (p (p H0 x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst8 : (p (p H0 x) q_v0) = (p (p H0 x) (p H0 x)) := congrArg (fun q => p (p H0 x) q) (pst0); let pst9 : (p q_v0 q_v0) = (p (p H0 x) (p H0 x)) := Eq.trans (pst7) (pst8); let pst10 : (p (p (p (p H0 x) q_v1) q_x) (p q_v0 q_v0)) = (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x))) := congrArg (fun q => p (p (p (p H0 x) q_v1) q_x) q) (pst9); let pst11 : (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)) = (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x))) := Eq.trans (pst6) (pst10); let pst12 : (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) = (p q_x (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x)))) := congrArg (fun q => p q_x q) (pst11); let pst13 : (p H0 x) = (p q_x (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x)))) := Eq.trans (pst3) (pst12); let pst14 : x = (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x))) := congrArg (fun q => R q) (pst13); let pst15 : H0 = q_x := congrArg (fun q => L q) (pst13); let pst16 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst15); let pst17 : (p (p H0 x) q_v1) = (p (p q_x x) q_v1) := congrArg (fun q => p q q_v1) (pst16); let pst18 : (p (p (p H0 x) q_v1) q_x) = (p (p (p q_x x) q_v1) q_x) := congrArg (fun q => p q q_x) (pst17); let pst19 : (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x))) = (p (p (p (p q_x x) q_v1) q_x) (p (p H0 x) (p H0 x))) := congrArg (fun q => p q (p (p H0 x) (p H0 x))) (pst18); let pst20 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst15); let pst21 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p H0 x)) := congrArg (fun q => p q (p H0 x)) (pst20); let pst22 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst15); let pst23 : (p (p q_x x) (p H0 x)) = (p (p q_x x) (p q_x x)) := congrArg (fun q => p (p q_x x) q) (pst22); let pst24 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p q_x x)) := Eq.trans (pst21) (pst23); let pst25 : (p (p (p (p q_x x) q_v1) q_x) (p (p H0 x) (p H0 x))) = (p (p (p (p q_x x) q_v1) q_x) (p (p q_x x) (p q_x x))) := congrArg (fun q => p (p (p (p q_x x) q_v1) q_x) q) (pst24); let pst26 : (p (p (p (p H0 x) q_v1) q_x) (p (p H0 x) (p H0 x))) = (p (p (p (p q_x x) q_v1) q_x) (p (p q_x x) (p q_x x))) := Eq.trans (pst19) (pst25); let pst27 : x = (p (p (p (p q_x x) q_v1) q_x) (p (p q_x x) (p q_x x))) := Eq.trans (pst14) (pst26); pst27)
        have hlt : sz x < sz (p (p (p (p q_x x) q_v1) q_x) (p (p q_x x) (p q_x x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x x) (sz_lt_p_left (p q_x x) q_v1)) (sz_lt_p_left (p (p q_x x) q_v1) q_x)) (sz_lt_p_left (p (p (p q_x x) q_v1) q_x) (p (p q_x x) (p q_x x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p H0 x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : x = (p q_H1 (p (p q_x x) (p q_x x))) := (let peq0 : (p H0 x) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p H0 x) := Eq.symm (peq0); let pst1 : v0 = (p H0 x) := Eq.trans (peq1) (pst0); let pst2 : (p H0 x) = v0 := Eq.symm (pst1); let pst3 : (p H0 x) = (p q_x (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p H0 x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p H0 x) q_v0) = (p (p H0 x) (p H0 x)) := congrArg (fun q => p (p H0 x) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p H0 x) (p H0 x)) := Eq.trans (pst4) (pst5); let pst7 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p H0 x) (p H0 x))) := congrArg (fun q => p q_H1 q) (pst6); let pst8 : (p q_x (p q_H1 (p q_v0 q_v0))) = (p q_x (p q_H1 (p (p H0 x) (p H0 x)))) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p H0 x) = (p q_x (p q_H1 (p (p H0 x) (p H0 x)))) := Eq.trans (pst3) (pst8); let pst10 : x = (p q_H1 (p (p H0 x) (p H0 x))) := congrArg (fun q => R q) (pst9); let pst11 : H0 = q_x := congrArg (fun q => L q) (pst9); let pst12 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst11); let pst13 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p H0 x)) := congrArg (fun q => p q (p H0 x)) (pst12); let pst14 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst11); let pst15 : (p (p q_x x) (p H0 x)) = (p (p q_x x) (p q_x x)) := congrArg (fun q => p (p q_x x) q) (pst14); let pst16 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p q_x x)) := Eq.trans (pst13) (pst15); let pst17 : (p q_H1 (p (p H0 x) (p H0 x))) = (p q_H1 (p (p q_x x) (p q_x x))) := congrArg (fun q => p q_H1 q) (pst16); let pst18 : x = (p q_H1 (p (p q_x x) (p q_x x))) := Eq.trans (pst10) (pst17); pst18)
        have hlt : sz x < sz (p q_H1 (p (p q_x x) (p q_x x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x x) (sz_lt_p_left (p q_x x) (p q_x x))) (sz_lt_p_right q_H1 (p (p q_x x) (p q_x x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p H0 x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) at e2
        have cyc : x = (p (p q_H0 q_x) (p (p q_x x) (p q_x x))) := (let peq0 : (p H0 x) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p H0 x) := Eq.symm (peq0); let pst1 : v0 = (p H0 x) := Eq.trans (peq1) (pst0); let pst2 : (p H0 x) = v0 := Eq.symm (pst1); let pst3 : (p H0 x) = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p H0 x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p H0 x) q_v0) = (p (p H0 x) (p H0 x)) := congrArg (fun q => p (p H0 x) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p H0 x) (p H0 x)) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_H0 q_x) (p q_v0 q_v0)) = (p (p q_H0 q_x) (p (p H0 x) (p H0 x))) := congrArg (fun q => p (p q_H0 q_x) q) (pst6); let pst8 : (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) = (p q_x (p (p q_H0 q_x) (p (p H0 x) (p H0 x)))) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p H0 x) = (p q_x (p (p q_H0 q_x) (p (p H0 x) (p H0 x)))) := Eq.trans (pst3) (pst8); let pst10 : x = (p (p q_H0 q_x) (p (p H0 x) (p H0 x))) := congrArg (fun q => R q) (pst9); let pst11 : H0 = q_x := congrArg (fun q => L q) (pst9); let pst12 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst11); let pst13 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p H0 x)) := congrArg (fun q => p q (p H0 x)) (pst12); let pst14 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst11); let pst15 : (p (p q_x x) (p H0 x)) = (p (p q_x x) (p q_x x)) := congrArg (fun q => p (p q_x x) q) (pst14); let pst16 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p q_x x)) := Eq.trans (pst13) (pst15); let pst17 : (p (p q_H0 q_x) (p (p H0 x) (p H0 x))) = (p (p q_H0 q_x) (p (p q_x x) (p q_x x))) := congrArg (fun q => p (p q_H0 q_x) q) (pst16); let pst18 : x = (p (p q_H0 q_x) (p (p q_x x) (p q_x x))) := Eq.trans (pst10) (pst17); pst18)
        have hlt : sz x < sz (p (p q_H0 q_x) (p (p q_x x) (p q_x x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x x) (sz_lt_p_left (p q_x x) (p q_x x))) (sz_lt_p_right (p q_H0 q_x) (p (p q_x x) (p q_x x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p H0 x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : x = (p q_H1 (p (p q_x x) (p q_x x))) := (let peq0 : (p H0 x) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p H0 x) := Eq.symm (peq0); let pst1 : v0 = (p H0 x) := Eq.trans (peq1) (pst0); let pst2 : (p H0 x) = v0 := Eq.symm (pst1); let pst3 : (p H0 x) = (p q_x (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p H0 x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p H0 x) q_v0) = (p (p H0 x) (p H0 x)) := congrArg (fun q => p (p H0 x) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p H0 x) (p H0 x)) := Eq.trans (pst4) (pst5); let pst7 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p H0 x) (p H0 x))) := congrArg (fun q => p q_H1 q) (pst6); let pst8 : (p q_x (p q_H1 (p q_v0 q_v0))) = (p q_x (p q_H1 (p (p H0 x) (p H0 x)))) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p H0 x) = (p q_x (p q_H1 (p (p H0 x) (p H0 x)))) := Eq.trans (pst3) (pst8); let pst10 : x = (p q_H1 (p (p H0 x) (p H0 x))) := congrArg (fun q => R q) (pst9); let pst11 : H0 = q_x := congrArg (fun q => L q) (pst9); let pst12 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst11); let pst13 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p H0 x)) := congrArg (fun q => p q (p H0 x)) (pst12); let pst14 : (p H0 x) = (p q_x x) := congrArg (fun q => p q x) (pst11); let pst15 : (p (p q_x x) (p H0 x)) = (p (p q_x x) (p q_x x)) := congrArg (fun q => p (p q_x x) q) (pst14); let pst16 : (p (p H0 x) (p H0 x)) = (p (p q_x x) (p q_x x)) := Eq.trans (pst13) (pst15); let pst17 : (p q_H1 (p (p H0 x) (p H0 x))) = (p q_H1 (p (p q_x x) (p q_x x))) := congrArg (fun q => p q_H1 q) (pst16); let pst18 : x = (p q_H1 (p (p q_x x) (p q_x x))) := Eq.trans (pst10) (pst17); pst18)
        have hlt : sz x < sz (p q_H1 (p (p q_x x) (p q_x x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x x) (sz_lt_p_left (p q_x x) (p q_x x))) (sz_lt_p_right q_H1 (p (p q_x x) (p q_x x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_x)) (sz_lt_p_left (p (p q_v0 q_v1) q_x) (p q_v0 q_v0))) (sz_lt_p_right q_x (p (p (p q_v0 q_v1) q_x) (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_x (p q_H1 (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_H1 (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_H1 (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_x (p (p q_H0 q_x) (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p q_H0 q_x) (p q_v0 q_v0))) (sz_lt_p_right q_x (p (p q_H0 q_x) (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_x (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_x (p q_H1 (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_H1 (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_H1 (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step H0 x H1) :
    ¬ ∃ o, Code x (p H1 (p v0 v0)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have he : H1 = x := (let peq0 : x = q_v0 := ha; let peq1 : H1 = q_v0 := congrArg (fun q => (L q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : H1 = x := Eq.trans (peq1) (pst0); pst1)
  exact step_ne_second (by simpa only [he] using s1)
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step H0 x H1) :
    ¬ ∃ o, Code v0 (p x (p H1 (p v0 v0))) o := by
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
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change (p H0 x) = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p (p q_v0 q_v1) q_x) at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_v0 = (p (p q_v0 q_v1) (p H0 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq1 : x = q_v0 := e1; let peq2 : (p H0 x) = q_x := e2; let peq3 : v0 = (p (p q_v0 q_v1) q_x) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 q_v1) q_x) := Eq.trans (pst0) (peq3); let pst2 : (p H0 x) = (p H0 q_v0) := congrArg (fun q => p H0 q) (peq1); let pst3 : (p H0 q_v0) = (p H0 x) := Eq.symm (pst2); let pst4 : (p H0 q_v0) = q_x := Eq.trans (pst3) (peq2); let pst5 : q_x = (p H0 q_v0) := Eq.symm (pst4); let pst6 : (p (p q_v0 q_v1) q_x) = (p (p q_v0 q_v1) (p H0 q_v0)) := congrArg (fun q => p (p q_v0 q_v1) q) (pst5); let pst7 : q_v0 = (p (p q_v0 q_v1) (p H0 q_v0)) := Eq.trans (pst1) (pst6); pst7)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v1) (p H0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) (p H0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change (p H0 x) = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = q_H1 at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = q_H1 := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
        have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change (p H0 x) = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p q_H0 q_x) at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_v0 = (p q_H0 (p H0 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq1 : x = q_v0 := e1; let peq2 : (p H0 x) = q_x := e2; let peq3 : v0 = (p q_H0 q_x) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 q_x) := Eq.trans (pst0) (peq3); let pst2 : (p H0 x) = (p H0 q_v0) := congrArg (fun q => p H0 q) (peq1); let pst3 : (p H0 q_v0) = (p H0 x) := Eq.symm (pst2); let pst4 : (p H0 q_v0) = q_x := Eq.trans (pst3) (peq2); let pst5 : q_x = (p H0 q_v0) := Eq.symm (pst4); let pst6 : (p q_H0 q_x) = (p q_H0 (p H0 q_v0)) := congrArg (fun q => p q_H0 q) (pst5); let pst7 : q_v0 = (p q_H0 (p H0 q_v0)) := Eq.trans (pst1) (pst6); pst7)
        have hlt : sz q_v0 < sz (p q_H0 (p H0 q_v0)) := Nat.lt_trans (sz_lt_p_right H0 q_v0) (sz_lt_p_right q_H0 (p H0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change (p H0 x) = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = q_H1 at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = q_H1 := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
        have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p (p q_v0 q_v1) q_x) at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_v0 = (p (p q_v0 q_v1) q_x) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p (p q_v0 q_v1) q_x) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 q_v1) q_x) := Eq.trans (pst0) (peq3); pst1)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v1) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = q_H1 at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = q_H1 := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
        have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p q_H0 q_x) at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_H0 = (p q_H0 q_x) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p q_H0 q_x) := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 q_x) := Eq.trans (pst0) (peq3); let pst2 : v0 = (p q_H0 q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_H0 q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_H0 q_x) = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p (p q_H0 q_x) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p (p q_H0 q_x) q_v0) = (p (p q_H0 q_x) (p q_H0 q_x)) := congrArg (fun q => p (p q_H0 q_x) q) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_H0 q_x) (p q_H0 q_x)) := Eq.trans (pst5) (pst6); let pst8 : (p q_H0 q_x) = (p (p q_H0 q_x) (p q_H0 q_x)) := Eq.trans (pst4) (pst7); let pst9 : q_H0 = (p q_H0 q_x) := congrArg (fun q => L q) (pst8); pst9)
        have hlt : sz q_H0 < sz (p q_H0 q_x) := sz_lt_p_left q_H0 q_x
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = q_x at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = q_H1 at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = q_H1 := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
        have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval x (eval (eval (eval v0 v1) x) (eval v0 v0))))) := by
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
  let H1 := eval (eval v0 v1) x
  have e1a : (eval v0 v1) = H0 := by
    change H0 = H0
    rfl
  have e1b : x = x := by
    change x = x
    rfl
  have s1 : Step H0 x H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v0 v1) x
  change x = (eval v0 (eval v0 (eval x (eval H1 (eval v0 v0)))))
  have rawEq : (eval v0 (eval v0 (eval x (eval H1 (eval v0 v0))))) = (eval v0 (p v0 (p x (p H1 (p v0 v0))))) := by
    calc
      (eval v0 (eval v0 (eval x (eval H1 (eval v0 v0))))) = (eval v0 (eval v0 (eval x (eval H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval x (eval H1 q))))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval v0 (eval x (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval x q)))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval v0 (eval v0 (p x (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 q))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval v0 (p v0 (p x (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H1 s1))
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
