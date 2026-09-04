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
      (s0 : Step v1 v0 H0)
      (s1 : Step H0 v0 H1) :
      Code v0 (p (p v0 (p x (p v0 v0))) H1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v1 q_v0 q_H0 ∧ Step q_H0 q_v0 q_H1 ∧ a = q_v0 ∧ b = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R (L b)))
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
      change v = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) at e1
      have cyc : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 (p v k)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p q_v0 q_v0))) := congrArg (fun q => p q (p q_x (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_x (p q_v0 q_v0)) = (p q_x (p (p v k) (p v k))) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p (p v k) (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := Eq.trans (pst1) (pst6); let pst8 : (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 q_v0) q_v0)) := congrArg (fun q => p q (p (p q_v1 q_v0) q_v0)) (pst7); let pst9 : (p q_v1 q_v0) = (p q_v1 (p v k)) := congrArg (fun q => p q_v1 q) (pst0); let pst10 : (p (p q_v1 q_v0) q_v0) = (p (p q_v1 (p v k)) q_v0) := congrArg (fun q => p q q_v0) (pst9); let pst11 : (p (p q_v1 (p v k)) q_v0) = (p (p q_v1 (p v k)) (p v k)) := congrArg (fun q => p (p q_v1 (p v k)) q) (pst0); let pst12 : (p (p q_v1 q_v0) q_v0) = (p (p q_v1 (p v k)) (p v k)) := Eq.trans (pst10) (pst11); let pst13 : (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 q_v0) q_v0)) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 (p v k)) (p v k))) := congrArg (fun q => p (p (p v k) (p q_x (p (p v k) (p v k)))) q) (pst12); let pst14 : (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 (p v k)) (p v k))) := Eq.trans (pst8) (pst13); let pst15 : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 (p v k)) (p v k))) := Eq.trans (peq1) (pst14); pst15)
      have hlt : sz v < sz (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 (p v k)) (p v k))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p v k) (p v k))))) (sz_lt_p_left (p (p v k) (p q_x (p (p v k) (p v k)))) (p (p q_v1 (p v k)) (p v k)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) at e1
      have cyc : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p q_v0 q_v0))) := congrArg (fun q => p q (p q_x (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_x (p q_v0 q_v0)) = (p q_x (p (p v k) (p v k))) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p (p v k) (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := Eq.trans (pst1) (pst6); let pst8 : (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := congrArg (fun q => p q q_H1) (pst7); let pst9 : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p v k) (p v k))))) (sz_lt_p_left (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) at e1
      have cyc : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p q_v0 q_v0))) := congrArg (fun q => p q (p q_x (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_x (p q_v0 q_v0)) = (p q_x (p (p v k) (p v k))) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p (p v k) (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := Eq.trans (pst1) (pst6); let pst8 : (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 q_v0)) := congrArg (fun q => p q (p q_H0 q_v0)) (pst7); let pst9 : (p q_H0 q_v0) = (p q_H0 (p v k)) := congrArg (fun q => p q_H0 q) (pst0); let pst10 : (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 q_v0)) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 (p v k))) := congrArg (fun q => p (p (p v k) (p q_x (p (p v k) (p v k)))) q) (pst9); let pst11 : (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 (p v k))) := Eq.trans (pst8) (pst10); let pst12 : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 (p v k))) := Eq.trans (peq1) (pst11); pst12)
      have hlt : sz v < sz (p (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 (p v k))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p v k) (p v k))))) (sz_lt_p_left (p (p v k) (p q_x (p (p v k) (p v k)))) (p q_H0 (p v k)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) at e1
      have cyc : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p q_v0 q_v0))) := congrArg (fun q => p q (p q_x (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_x (p q_v0 q_v0)) = (p q_x (p (p v k) (p v k))) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p (p v k) (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p v k) (p q_x (p (p v k) (p v k)))) := Eq.trans (pst1) (pst6); let pst8 : (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) = (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := congrArg (fun q => p q q_H1) (pst7); let pst9 : v = (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p v k) (p v k))))) (sz_lt_p_left (p (p v k) (p q_x (p (p v k) (p v k)))) q_H1)
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
      change v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) at e1
      have cyc : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_x (p q_v0 q_v0))) (sz_lt_p_left (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) at e1
      have cyc : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_x (p q_v0 q_v0))) (sz_lt_p_left (p q_v0 (p q_x (p q_v0 q_v0))) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) at e1
      have cyc : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_x (p q_v0 q_v0))) (sz_lt_p_left (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) at e1
      have cyc : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_x (p q_v0 q_v0))) (sz_lt_p_left (p q_v0 (p q_x (p q_v0 q_v0))) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_v0 (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_v1 q_v0) q_v0) at e2
      have cyc : q_v0 = (p q_v1 q_v0) := (let peq1 : v0 = (p q_v0 (p q_x (p q_v0 q_v0))) := e1; let peq2 : v0 = (p (p q_v1 q_v0) q_v0) := e2; let pst0 : (p q_v0 (p q_x (p q_v0 q_v0))) = v0 := Eq.symm (peq1); let pst1 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p (p q_v1 q_v0) q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v1 q_v0) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_v1 q_v0) := sz_lt_p_right q_v1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change v0 = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change v0 = q_H1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_v0 (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p q_H0 q_v0) at e2
      have cyc : q_H0 = (p q_x (p q_H0 q_H0)) := (let peq1 : v0 = (p q_v0 (p q_x (p q_v0 q_v0))) := e1; let peq2 : v0 = (p q_H0 q_v0) := e2; let pst0 : (p q_v0 (p q_x (p q_v0 q_v0))) = v0 := Eq.symm (peq1); let pst1 : (p q_v0 (p q_x (p q_v0 q_v0))) = (p q_H0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_H0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v0) = (p q_H0 q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p q_H0 q_v0) = (p q_H0 q_H0) := congrArg (fun q => p q_H0 q) (pst2); let pst5 : (p q_v0 q_v0) = (p q_H0 q_H0) := Eq.trans (pst3) (pst4); let pst6 : (p q_x (p q_v0 q_v0)) = (p q_x (p q_H0 q_H0)) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p q_x (p q_H0 q_H0)) = (p q_x (p q_v0 q_v0)) := Eq.symm (pst6); let pst8 : (p q_x (p q_v0 q_v0)) = q_v0 := congrArg (fun q => R q) (pst1); let pst9 : (p q_x (p q_H0 q_H0)) = q_v0 := Eq.trans (pst7) (pst8); let pst10 : (p q_x (p q_H0 q_H0)) = q_H0 := Eq.trans (pst9) (pst2); let pst11 : q_H0 = (p q_x (p q_H0 q_H0)) := Eq.symm (pst10); pst11)
      have hlt : sz q_H0 < sz (p q_x (p q_H0 q_H0)) := Nat.lt_trans (sz_lt_p_left q_H0 q_H0) (sz_lt_p_right q_x (p q_H0 q_H0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change v0 = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change v0 = q_H1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p x (p v0 v0)) o := by
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
      have e1 := congrArg (fun q => (L q)) hb
      change x = (p q_v0 (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = (p q_v1 q_v0) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v0 = q_v0 at e3
      have cyc : q_v0 = (p q_v1 q_v0) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v1 q_v0) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v1 q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v1 q_v0) := sz_lt_p_right q_v1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v0 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change x = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change (p v0 v0) = q_H1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v0 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change x = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (hb)
      change v0 = q_H0 at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (hb)
      change v0 = q_v0 at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs0B qs1B z0 z1 z2 z3 z4
      omega
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v0 = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change x = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change (p v0 v0) = q_H1 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB qs0B qs1B z0 z1 z2 z3
      omega
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step H0 v0 H1) :
    ¬ ∃ o, Code (p v0 (p x (p v0 v0))) H1 o := by
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
        change (p v0 (p x (p v0 v0))) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H0 = (p q_v0 (p q_x (p q_v0 q_v0))) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_v1 q_v0) q_v0) at e2
        have cyc : v0 = (p (p q_v1 (p v0 (p x (p v0 v0)))) (p v0 (p x (p v0 v0)))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := e0; let peq2 : v0 = (p (p q_v1 q_v0) q_v0) := e2; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p q_v1 q_v0) = (p q_v1 (p v0 (p x (p v0 v0)))) := congrArg (fun q => p q_v1 q) (pst0); let pst2 : (p (p q_v1 q_v0) q_v0) = (p (p q_v1 (p v0 (p x (p v0 v0)))) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst3 : (p (p q_v1 (p v0 (p x (p v0 v0)))) q_v0) = (p (p q_v1 (p v0 (p x (p v0 v0)))) (p v0 (p x (p v0 v0)))) := congrArg (fun q => p (p q_v1 (p v0 (p x (p v0 v0)))) q) (pst0); let pst4 : (p (p q_v1 q_v0) q_v0) = (p (p q_v1 (p v0 (p x (p v0 v0)))) (p v0 (p x (p v0 v0)))) := Eq.trans (pst2) (pst3); let pst5 : v0 = (p (p q_v1 (p v0 (p x (p v0 v0)))) (p v0 (p x (p v0 v0)))) := Eq.trans (peq2) (pst4); pst5)
        have hlt : sz v0 < sz (p (p q_v1 (p v0 (p x (p v0 v0)))) (p v0 (p x (p v0 v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 (p x (p v0 v0))) (sz_lt_p_right q_v1 (p v0 (p x (p v0 v0))))) (sz_lt_p_left (p q_v1 (p v0 (p x (p v0 v0)))) (p v0 (p x (p v0 v0))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change (p v0 (p x (p v0 v0))) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change H0 = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change v0 = q_H1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB qs1hB s1B qs0B qs1B z0 z1 z2 z3
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v0 (p x (p v0 v0))) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H0 = (p q_v0 (p q_x (p q_v0 q_v0))) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_H0 q_v0) at e2
        have cyc : v0 = (p q_H0 (p v0 (p x (p v0 v0)))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := e0; let peq2 : v0 = (p q_H0 q_v0) := e2; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p q_H0 q_v0) = (p q_H0 (p v0 (p x (p v0 v0)))) := congrArg (fun q => p q_H0 q) (pst0); let pst2 : v0 = (p q_H0 (p v0 (p x (p v0 v0)))) := Eq.trans (peq2) (pst1); pst2)
        have hlt : sz v0 < sz (p q_H0 (p v0 (p x (p v0 v0)))) := Nat.lt_trans (sz_lt_p_left v0 (p x (p v0 v0))) (sz_lt_p_right q_H0 (p v0 (p x (p v0 v0))))
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
            have cyc : u0_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := ha; let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p (p u0_v1 u0_v0) u0_v0)) := u0b; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (peq2); let pst2 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq2); let pst3 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst4 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst3); let pst5 : (p x (p v0 v0)) = (p x (p q_H1 q_H1)) := congrArg (fun q => p x q) (pst4); let pst6 : (p q_H1 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst1) (pst6); let pst8 : q_v0 = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst0) (pst7); let pst9 : (p q_H1 (p x (p q_H1 q_H1))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H1 (p x (p q_H1 q_H1))) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p (p u0_v1 u0_v0) u0_v0)) := Eq.trans (pst9) (peq5); let pst11 : q_H1 = (p u0_v0 (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst10); let pst12 : (p q_H1 q_H1) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) q_H1) := congrArg (fun q => p q q_H1) (pst11); let pst13 : (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) q_H1) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) q) (pst11); let pst14 : (p q_H1 q_H1) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := Eq.trans (pst12) (pst13); let pst15 : (p x (p q_H1 q_H1)) = (p x (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))) := congrArg (fun q => p x q) (pst14); let pst16 : (p x (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))) = (p x (p q_H1 q_H1)) := Eq.symm (pst15); let pst17 : (p x (p q_H1 q_H1)) = (p (p u0_v1 u0_v0) u0_v0) := congrArg (fun q => R q) (pst10); let pst18 : (p x (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))) = (p (p u0_v1 u0_v0) u0_v0) := Eq.trans (pst16) (pst17); let pst19 : (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := congrArg (fun q => R q) (pst18); let pst20 : u0_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst19); pst20)
            have hlt : sz u0_v0 < sz (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (sz_lt_p_left u0_v0 (p u0_x (p u0_v0 u0_v0))) (sz_lt_p_left (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have hcB := code_bounds hc
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have u0s1hB := code_bounds u0s1h
            have s1B := s1B
            have qs0B := qs0B
            have qs1B := qs1B
            have u0s0B := u0s0B
            have u0s1B := u0s1B
            have p0 := ha
            change (p v0 (p x (p v0 v0))) = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H0 = (p q_v0 (p q_x (p q_v0 q_v0))) at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (R q)) (hb)
            change v0 = q_H1 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            have p4 := u0a
            change q_v1 = u0_v0 at p4
            have z4 := congrArg sz p4
            have p5 := u0b
            change q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) at p5
            have z5 := congrArg sz p5
            have p6 := u0o
            change q_H0 = u0_x at p6
            have z6 := congrArg sz p6
            simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB u0s1hB s1B qs0B qs1B u0s0B u0s1B z0 z1 z2 z3 z4 z5 z6
            omega
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := ha; let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0s0out u0_v0)) := u0b; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (peq2); let pst2 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq2); let pst3 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst4 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst3); let pst5 : (p x (p v0 v0)) = (p x (p q_H1 q_H1)) := congrArg (fun q => p x q) (pst4); let pst6 : (p q_H1 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst1) (pst6); let pst8 : q_v0 = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst0) (pst7); let pst9 : (p q_H1 (p x (p q_H1 q_H1))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H1 (p x (p q_H1 q_H1))) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0s0out u0_v0)) := Eq.trans (pst9) (peq5); let pst11 : q_H1 = (p u0_v0 (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst10); let pst12 : (p q_H1 q_H1) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) q_H1) := congrArg (fun q => p q q_H1) (pst11); let pst13 : (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) q_H1) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) q) (pst11); let pst14 : (p q_H1 q_H1) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := Eq.trans (pst12) (pst13); let pst15 : (p x (p q_H1 q_H1)) = (p x (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))) := congrArg (fun q => p x q) (pst14); let pst16 : (p x (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))) = (p x (p q_H1 q_H1)) := Eq.symm (pst15); let pst17 : (p x (p q_H1 q_H1)) = (p u0s0out u0_v0) := congrArg (fun q => R q) (pst10); let pst18 : (p x (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))) = (p u0s0out u0_v0) := Eq.trans (pst16) (pst17); let pst19 : (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := congrArg (fun q => R q) (pst18); let pst20 : u0_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst19); pst20)
            have hlt : sz u0_v0 < sz (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (sz_lt_p_left u0_v0 (p u0_x (p u0_v0 u0_v0))) (sz_lt_p_left (p u0_v0 (p u0_x (p u0_v0 u0_v0))) (p u0_v0 (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0B := step_bound u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1B := step_bound u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := ha; let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := u0b; let peq6 : q_H0 = u0_x := u0o; let peq7 : q_H0 = u1_v0 := u1a; let peq8 : q_v0 = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) (p (p u1_v1 u1_v0) u1_v0)) := u1b; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (peq2); let pst2 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq2); let pst3 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst4 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst3); let pst5 : (p x (p v0 v0)) = (p x (p q_H1 q_H1)) := congrArg (fun q => p x q) (pst4); let pst6 : (p q_H1 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst1) (pst6); let pst8 : q_v0 = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst0) (pst7); let pst9 : (p q_H1 (p x (p q_H1 q_H1))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H1 (p x (p q_H1 q_H1))) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := Eq.trans (pst9) (peq5); let pst11 : q_H1 = (p u0_v0 (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst10); let pst12 : u0_x = q_H0 := Eq.symm (peq6); let pst13 : u0_x = u1_v0 := Eq.trans (pst12) (peq7); let pst14 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst15 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst14); let pst16 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst15); let pst17 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst16); let pst18 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (pst17); let pst19 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst20 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst20); let pst22 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst21); let pst23 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) := congrArg (fun q => p q v0) (pst22); let pst24 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst25 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst24); let pst26 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst25); let pst27 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst26); let pst28 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst27); let pst29 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := Eq.trans (pst23) (pst28); let pst30 : (p x (p v0 v0)) = (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) := congrArg (fun q => p x q) (pst29); let pst31 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst30); let pst32 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst18) (pst31); let pst33 : q_v0 = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst0) (pst32); let pst34 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = q_v0 := Eq.symm (pst33); let pst35 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) (p (p u1_v1 u1_v0) u1_v0)) := Eq.trans (pst34) (peq8); let pst36 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_v0 (p u1_x (p u1_v0 u1_v0))) := congrArg (fun q => L q) (pst35); let pst37 : u0_v0 = u1_v0 := congrArg (fun q => L q) (pst36); let pst38 : (p u0_v0 u0_v0) = (p u1_v0 u0_v0) := congrArg (fun q => p q u0_v0) (pst37); let pst39 : (p u1_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (pst37); let pst40 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := Eq.trans (pst38) (pst39); let pst41 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_v0 (p u1_v0 u1_v0)) := congrArg (fun q => p u1_v0 q) (pst40); let pst42 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := Eq.symm (pst41); let pst43 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_v0 u1_v0)) := congrArg (fun q => R q) (pst36); let pst44 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_x (p u1_v0 u1_v0)) := Eq.trans (pst42) (pst43); let pst45 : u1_v0 = u1_x := congrArg (fun q => L q) (pst44); let pst46 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst47 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p q (p u1_v0 (p u0_v0 u0_v0))) (pst46); let pst48 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst45); let pst49 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst50 : (p u0_v0 u0_v0) = (p u1_x u0_v0) := congrArg (fun q => p q u0_v0) (pst49); let pst51 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst52 : (p u1_x u0_v0) = (p u1_x u1_x) := congrArg (fun q => p u1_x q) (pst51); let pst53 : (p u0_v0 u0_v0) = (p u1_x u1_x) := Eq.trans (pst50) (pst52); let pst54 : (p u1_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := congrArg (fun q => p u1_x q) (pst53); let pst55 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := Eq.trans (pst48) (pst54); let pst56 : (p u1_x (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := congrArg (fun q => p u1_x q) (pst55); let pst57 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst47) (pst56); let pst58 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := congrArg (fun q => p q (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) (pst57); let pst59 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst60 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p q (p u1_v0 (p u0_v0 u0_v0))) (pst59); let pst61 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst45); let pst62 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst63 : (p u0_v0 u0_v0) = (p u1_x u0_v0) := congrArg (fun q => p q u0_v0) (pst62); let pst64 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst65 : (p u1_x u0_v0) = (p u1_x u1_x) := congrArg (fun q => p u1_x q) (pst64); let pst66 : (p u0_v0 u0_v0) = (p u1_x u1_x) := Eq.trans (pst63) (pst65); let pst67 : (p u1_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := congrArg (fun q => p u1_x q) (pst66); let pst68 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := Eq.trans (pst61) (pst67); let pst69 : (p u1_x (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := congrArg (fun q => p u1_x q) (pst68); let pst70 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst60) (pst69); let pst71 : (p (p u1_x (p u1_x (p u1_x u1_x))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := congrArg (fun q => p (p u1_x (p u1_x (p u1_x u1_x))) q) (pst70); let pst72 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := Eq.trans (pst58) (pst71); let pst73 : (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) = (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) := congrArg (fun q => p x q) (pst72); let pst74 : (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) = (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) := Eq.symm (pst73); let pst75 : (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) = (p (p u1_v1 u1_v0) u1_v0) := congrArg (fun q => R q) (pst35); let pst76 : (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) = (p (p u1_v1 u1_v0) u1_v0) := Eq.trans (pst74) (pst75); let pst77 : (p u1_v1 u1_v0) = (p u1_v1 u1_x) := congrArg (fun q => p u1_v1 q) (pst45); let pst78 : (p (p u1_v1 u1_v0) u1_v0) = (p (p u1_v1 u1_x) u1_v0) := congrArg (fun q => p q u1_v0) (pst77); let pst79 : (p (p u1_v1 u1_x) u1_v0) = (p (p u1_v1 u1_x) u1_x) := congrArg (fun q => p (p u1_v1 u1_x) q) (pst45); let pst80 : (p (p u1_v1 u1_v0) u1_v0) = (p (p u1_v1 u1_x) u1_x) := Eq.trans (pst78) (pst79); let pst81 : (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) = (p (p u1_v1 u1_x) u1_x) := Eq.trans (pst76) (pst80); let pst82 : (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) = u1_x := congrArg (fun q => R q) (pst81); let pst83 : u1_x = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := Eq.symm (pst82); pst83)
                have hlt : sz u1_x < sz (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := Nat.lt_trans (sz_lt_p_left u1_x (p u1_x (p u1_x u1_x))) (sz_lt_p_left (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p u1_x (p u1_x (p u1_x u1_x))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := ha; let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := u0b; let peq6 : q_H0 = u0_x := u0o; let peq7 : q_H0 = u1_v0 := u1a; let peq8 : q_v0 = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) u1s1out) := u1b; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (peq2); let pst2 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq2); let pst3 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst4 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst3); let pst5 : (p x (p v0 v0)) = (p x (p q_H1 q_H1)) := congrArg (fun q => p x q) (pst4); let pst6 : (p q_H1 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst1) (pst6); let pst8 : q_v0 = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst0) (pst7); let pst9 : (p q_H1 (p x (p q_H1 q_H1))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H1 (p x (p q_H1 q_H1))) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := Eq.trans (pst9) (peq5); let pst11 : q_H1 = (p u0_v0 (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst10); let pst12 : u0_x = q_H0 := Eq.symm (peq6); let pst13 : u0_x = u1_v0 := Eq.trans (pst12) (peq7); let pst14 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst15 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst14); let pst16 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst15); let pst17 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst16); let pst18 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (pst17); let pst19 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst20 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst20); let pst22 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst21); let pst23 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) := congrArg (fun q => p q v0) (pst22); let pst24 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst25 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst24); let pst26 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst25); let pst27 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst26); let pst28 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst27); let pst29 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := Eq.trans (pst23) (pst28); let pst30 : (p x (p v0 v0)) = (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) := congrArg (fun q => p x q) (pst29); let pst31 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst30); let pst32 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst18) (pst31); let pst33 : q_v0 = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst0) (pst32); let pst34 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = q_v0 := Eq.symm (pst33); let pst35 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) u1s1out) := Eq.trans (pst34) (peq8); let pst36 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_v0 (p u1_x (p u1_v0 u1_v0))) := congrArg (fun q => L q) (pst35); let pst37 : u0_v0 = u1_v0 := congrArg (fun q => L q) (pst36); let pst38 : (p u0_v0 u0_v0) = (p u1_v0 u0_v0) := congrArg (fun q => p q u0_v0) (pst37); let pst39 : (p u1_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (pst37); let pst40 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := Eq.trans (pst38) (pst39); let pst41 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_v0 (p u1_v0 u1_v0)) := congrArg (fun q => p u1_v0 q) (pst40); let pst42 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := Eq.symm (pst41); let pst43 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_v0 u1_v0)) := congrArg (fun q => R q) (pst36); let pst44 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_x (p u1_v0 u1_v0)) := Eq.trans (pst42) (pst43); let pst45 : u1_v0 = u1_x := congrArg (fun q => L q) (pst44); let pst46 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst47 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u1_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => p q (p u0_x (p u0_v0 u0_v0))) (pst46); let pst48 : u0_x = u1_x := Eq.trans (pst13) (pst45); let pst49 : (p u0_x (p u0_v0 u0_v0)) = (p u1_x (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst48); let pst50 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst51 : (p u0_v0 u0_v0) = (p u1_x u0_v0) := congrArg (fun q => p q u0_v0) (pst50); let pst52 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst53 : (p u1_x u0_v0) = (p u1_x u1_x) := congrArg (fun q => p u1_x q) (pst52); let pst54 : (p u0_v0 u0_v0) = (p u1_x u1_x) := Eq.trans (pst51) (pst53); let pst55 : (p u1_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := congrArg (fun q => p u1_x q) (pst54); let pst56 : (p u0_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := Eq.trans (pst49) (pst55); let pst57 : (p u1_x (p u0_x (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := congrArg (fun q => p u1_x q) (pst56); let pst58 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst47) (pst57); let pst59 : q_H1 = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst11) (pst58); let pst60 : (p u1_x (p u1_x (p u1_x u1_x))) = q_H1 := Eq.symm (pst59); let pst61 : (p u1_x (p u1_x (p u1_x u1_x))) = u1_x := Eq.trans (pst60) (peq9); let pst62 : u1_x = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.symm (pst61); pst62)
                have hlt : sz u1_x < sz (p u1_x (p u1_x (p u1_x u1_x))) := sz_lt_p_left u1_x (p u1_x (p u1_x u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1B := step_bound u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := ha; let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := u0b; let peq6 : q_H0 = u0_x := u0o; let peq7 : q_H0 = u1_v0 := u1a; let peq8 : q_v0 = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) (p u1s0out u1_v0)) := u1b; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (peq2); let pst2 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq2); let pst3 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst4 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst3); let pst5 : (p x (p v0 v0)) = (p x (p q_H1 q_H1)) := congrArg (fun q => p x q) (pst4); let pst6 : (p q_H1 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst1) (pst6); let pst8 : q_v0 = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst0) (pst7); let pst9 : (p q_H1 (p x (p q_H1 q_H1))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H1 (p x (p q_H1 q_H1))) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := Eq.trans (pst9) (peq5); let pst11 : q_H1 = (p u0_v0 (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst10); let pst12 : u0_x = q_H0 := Eq.symm (peq6); let pst13 : u0_x = u1_v0 := Eq.trans (pst12) (peq7); let pst14 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst15 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst14); let pst16 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst15); let pst17 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst16); let pst18 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (pst17); let pst19 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst20 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst20); let pst22 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst21); let pst23 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) := congrArg (fun q => p q v0) (pst22); let pst24 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst25 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst24); let pst26 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst25); let pst27 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst26); let pst28 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst27); let pst29 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := Eq.trans (pst23) (pst28); let pst30 : (p x (p v0 v0)) = (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) := congrArg (fun q => p x q) (pst29); let pst31 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst30); let pst32 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst18) (pst31); let pst33 : q_v0 = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst0) (pst32); let pst34 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = q_v0 := Eq.symm (pst33); let pst35 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) (p u1s0out u1_v0)) := Eq.trans (pst34) (peq8); let pst36 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_v0 (p u1_x (p u1_v0 u1_v0))) := congrArg (fun q => L q) (pst35); let pst37 : u0_v0 = u1_v0 := congrArg (fun q => L q) (pst36); let pst38 : (p u0_v0 u0_v0) = (p u1_v0 u0_v0) := congrArg (fun q => p q u0_v0) (pst37); let pst39 : (p u1_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (pst37); let pst40 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := Eq.trans (pst38) (pst39); let pst41 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_v0 (p u1_v0 u1_v0)) := congrArg (fun q => p u1_v0 q) (pst40); let pst42 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := Eq.symm (pst41); let pst43 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_v0 u1_v0)) := congrArg (fun q => R q) (pst36); let pst44 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_x (p u1_v0 u1_v0)) := Eq.trans (pst42) (pst43); let pst45 : u1_v0 = u1_x := congrArg (fun q => L q) (pst44); let pst46 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst47 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p q (p u1_v0 (p u0_v0 u0_v0))) (pst46); let pst48 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst45); let pst49 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst50 : (p u0_v0 u0_v0) = (p u1_x u0_v0) := congrArg (fun q => p q u0_v0) (pst49); let pst51 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst52 : (p u1_x u0_v0) = (p u1_x u1_x) := congrArg (fun q => p u1_x q) (pst51); let pst53 : (p u0_v0 u0_v0) = (p u1_x u1_x) := Eq.trans (pst50) (pst52); let pst54 : (p u1_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := congrArg (fun q => p u1_x q) (pst53); let pst55 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := Eq.trans (pst48) (pst54); let pst56 : (p u1_x (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := congrArg (fun q => p u1_x q) (pst55); let pst57 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst47) (pst56); let pst58 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := congrArg (fun q => p q (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) (pst57); let pst59 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst60 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p q (p u1_v0 (p u0_v0 u0_v0))) (pst59); let pst61 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst45); let pst62 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst63 : (p u0_v0 u0_v0) = (p u1_x u0_v0) := congrArg (fun q => p q u0_v0) (pst62); let pst64 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst65 : (p u1_x u0_v0) = (p u1_x u1_x) := congrArg (fun q => p u1_x q) (pst64); let pst66 : (p u0_v0 u0_v0) = (p u1_x u1_x) := Eq.trans (pst63) (pst65); let pst67 : (p u1_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := congrArg (fun q => p u1_x q) (pst66); let pst68 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := Eq.trans (pst61) (pst67); let pst69 : (p u1_x (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := congrArg (fun q => p u1_x q) (pst68); let pst70 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst60) (pst69); let pst71 : (p (p u1_x (p u1_x (p u1_x u1_x))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := congrArg (fun q => p (p u1_x (p u1_x (p u1_x u1_x))) q) (pst70); let pst72 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := Eq.trans (pst58) (pst71); let pst73 : (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) = (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) := congrArg (fun q => p x q) (pst72); let pst74 : (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) = (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) := Eq.symm (pst73); let pst75 : (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) = (p u1s0out u1_v0) := congrArg (fun q => R q) (pst35); let pst76 : (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) = (p u1s0out u1_v0) := Eq.trans (pst74) (pst75); let pst77 : (p u1s0out u1_v0) = (p u1s0out u1_x) := congrArg (fun q => p u1s0out q) (pst45); let pst78 : (p x (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))) = (p u1s0out u1_x) := Eq.trans (pst76) (pst77); let pst79 : (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) = u1_x := congrArg (fun q => R q) (pst78); let pst80 : u1_x = (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := Eq.symm (pst79); pst80)
                have hlt : sz u1_x < sz (p (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x)))) := Nat.lt_trans (sz_lt_p_left u1_x (p u1_x (p u1_x u1_x))) (sz_lt_p_left (p u1_x (p u1_x (p u1_x u1_x))) (p u1_x (p u1_x (p u1_x u1_x))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p u1_x (p u1_x (p u1_x u1_x))) := (let peq0 : (p v0 (p x (p v0 v0))) = q_v0 := ha; let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := u0b; let peq6 : q_H0 = u0_x := u0o; let peq7 : q_H0 = u1_v0 := u1a; let peq8 : q_v0 = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) u1s1out) := u1b; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_v0 = (p v0 (p x (p v0 v0))) := Eq.symm (peq0); let pst1 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (peq2); let pst2 : (p v0 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (peq2); let pst3 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst4 : (p v0 v0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst3); let pst5 : (p x (p v0 v0)) = (p x (p q_H1 q_H1)) := congrArg (fun q => p x q) (pst4); let pst6 : (p q_H1 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p v0 (p x (p v0 v0))) = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst1) (pst6); let pst8 : q_v0 = (p q_H1 (p x (p q_H1 q_H1))) := Eq.trans (pst0) (pst7); let pst9 : (p q_H1 (p x (p q_H1 q_H1))) = q_v0 := Eq.symm (pst8); let pst10 : (p q_H1 (p x (p q_H1 q_H1))) = (p (p u0_v0 (p u0_x (p u0_v0 u0_v0))) u0s1out) := Eq.trans (pst9) (peq5); let pst11 : q_H1 = (p u0_v0 (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst10); let pst12 : u0_x = q_H0 := Eq.symm (peq6); let pst13 : u0_x = u1_v0 := Eq.trans (pst12) (peq7); let pst14 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst15 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst14); let pst16 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst15); let pst17 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst16); let pst18 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) := congrArg (fun q => p q (p x (p v0 v0))) (pst17); let pst19 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst20 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst19); let pst21 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst20); let pst22 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst21); let pst23 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) := congrArg (fun q => p q v0) (pst22); let pst24 : (p u0_x (p u0_v0 u0_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst13); let pst25 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := congrArg (fun q => p u0_v0 q) (pst24); let pst26 : q_H1 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (pst11) (pst25); let pst27 : v0 = (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) := Eq.trans (peq2) (pst26); let pst28 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst27); let pst29 : (p v0 v0) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))) := Eq.trans (pst23) (pst28); let pst30 : (p x (p v0 v0)) = (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))))) := congrArg (fun q => p x q) (pst29); let pst31 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := congrArg (fun q => p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) q) (pst30); let pst32 : (p v0 (p x (p v0 v0))) = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst18) (pst31); let pst33 : q_v0 = (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) := Eq.trans (pst0) (pst32); let pst34 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = q_v0 := Eq.symm (pst33); let pst35 : (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p x (p (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) (p u0_v0 (p u1_v0 (p u0_v0 u0_v0)))))) = (p (p u1_v0 (p u1_x (p u1_v0 u1_v0))) u1s1out) := Eq.trans (pst34) (peq8); let pst36 : (p u0_v0 (p u1_v0 (p u0_v0 u0_v0))) = (p u1_v0 (p u1_x (p u1_v0 u1_v0))) := congrArg (fun q => L q) (pst35); let pst37 : u0_v0 = u1_v0 := congrArg (fun q => L q) (pst36); let pst38 : (p u0_v0 u0_v0) = (p u1_v0 u0_v0) := congrArg (fun q => p q u0_v0) (pst37); let pst39 : (p u1_v0 u0_v0) = (p u1_v0 u1_v0) := congrArg (fun q => p u1_v0 q) (pst37); let pst40 : (p u0_v0 u0_v0) = (p u1_v0 u1_v0) := Eq.trans (pst38) (pst39); let pst41 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_v0 (p u1_v0 u1_v0)) := congrArg (fun q => p u1_v0 q) (pst40); let pst42 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_v0 (p u0_v0 u0_v0)) := Eq.symm (pst41); let pst43 : (p u1_v0 (p u0_v0 u0_v0)) = (p u1_x (p u1_v0 u1_v0)) := congrArg (fun q => R q) (pst36); let pst44 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_x (p u1_v0 u1_v0)) := Eq.trans (pst42) (pst43); let pst45 : u1_v0 = u1_x := congrArg (fun q => L q) (pst44); let pst46 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst47 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u1_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => p q (p u0_x (p u0_v0 u0_v0))) (pst46); let pst48 : u0_x = u1_x := Eq.trans (pst13) (pst45); let pst49 : (p u0_x (p u0_v0 u0_v0)) = (p u1_x (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst48); let pst50 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst51 : (p u0_v0 u0_v0) = (p u1_x u0_v0) := congrArg (fun q => p q u0_v0) (pst50); let pst52 : u0_v0 = u1_x := Eq.trans (pst37) (pst45); let pst53 : (p u1_x u0_v0) = (p u1_x u1_x) := congrArg (fun q => p u1_x q) (pst52); let pst54 : (p u0_v0 u0_v0) = (p u1_x u1_x) := Eq.trans (pst51) (pst53); let pst55 : (p u1_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := congrArg (fun q => p u1_x q) (pst54); let pst56 : (p u0_x (p u0_v0 u0_v0)) = (p u1_x (p u1_x u1_x)) := Eq.trans (pst49) (pst55); let pst57 : (p u1_x (p u0_x (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := congrArg (fun q => p u1_x q) (pst56); let pst58 : (p u0_v0 (p u0_x (p u0_v0 u0_v0))) = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst47) (pst57); let pst59 : q_H1 = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.trans (pst11) (pst58); let pst60 : (p u1_x (p u1_x (p u1_x u1_x))) = q_H1 := Eq.symm (pst59); let pst61 : (p u1_x (p u1_x (p u1_x u1_x))) = u1_x := Eq.trans (pst60) (peq9); let pst62 : u1_x = (p u1_x (p u1_x (p u1_x u1_x))) := Eq.symm (pst61); pst62)
                have hlt : sz u1_x < sz (p u1_x (p u1_x (p u1_x u1_x))) := sz_lt_p_left u1_x (p u1_x (p u1_x u1_x))
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
        change (p v0 (p x (p v0 v0))) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p (p q_v1 q_v0) q_v0)) at p1
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
        change (p v0 (p x (p v0 v0))) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) at p1
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
        change (p v0 (p x (p v0 v0))) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_v0 (p q_x (p q_v0 q_v0))) (p q_H0 q_v0)) at p1
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
        change (p v0 (p x (p v0 v0))) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_v0 (p q_x (p q_v0 q_v0))) q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval (eval v0 (eval x (eval v0 v0))) (eval (eval v1 v0) v0))) := by
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
  let H1 := eval (eval v1 v0) v0
  have e1a : (eval v1 v0) = H0 := by
    change H0 = H0
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step H0 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v1 v0) v0
  change x = (eval v0 (eval (eval v0 (eval x (eval v0 v0))) H1))
  have rawEq : (eval v0 (eval (eval v0 (eval x (eval v0 v0))) H1)) = (eval v0 (p (p v0 (p x (p v0 v0))) H1)) := by
    calc
      (eval v0 (eval (eval v0 (eval x (eval v0 v0))) H1)) = (eval v0 (eval (eval v0 (eval x (p v0 v0))) H1)) := congrArg (fun q => (eval v0 (eval (eval v0 (eval x q)) H1))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval (eval v0 (p x (p v0 v0))) H1)) := congrArg (fun q => (eval v0 (eval (eval v0 q) H1))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval (p v0 (p x (p v0 v0))) H1)) := congrArg (fun q => (eval v0 (eval q H1))) (eval_raw (nr2 x v0 v1))
      _ = (eval v0 (p (p v0 (p x (p v0 v0))) H1)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H1 s1))
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
