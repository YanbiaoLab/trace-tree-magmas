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
      (s1 : Step H0 v0 H1) :
      Code v0 (p v0 (p (p x x) (p H1 (p v0 v0)))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_H0 q_v0 q_H1 ∧ a = q_v0 ∧ b = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R b)))
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
      change v = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := congrArg (fun q => p q (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v1) = (p (p v k) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst3 : (p (p q_v0 q_v1) q_v0) = (p (p (p v k) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p (p v k) q_v1) q_v0) = (p (p (p v k) q_v1) (p v k)) := congrArg (fun q => p (p (p v k) q_v1) q) (pst0); let pst5 : (p (p q_v0 q_v1) q_v0) = (p (p (p v k) q_v1) (p v k)) := Eq.trans (pst3) (pst4); let pst6 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) = (p (p (p (p v k) q_v1) (p v k)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst5); let pst7 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst8 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst9 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst7) (pst8); let pst10 : (p (p (p (p v k) q_v1) (p v k)) (p q_v0 q_v0)) = (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))) := congrArg (fun q => p (p (p (p v k) q_v1) (p v k)) q) (pst9); let pst11 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) = (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))) := Eq.trans (pst6) (pst10); let pst12 : (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) = (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k)))) := congrArg (fun q => p (p q_x q_x) q) (pst11); let pst13 : (p (p v k) (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst12); let pst14 : (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))))) := Eq.trans (pst1) (pst13); let pst15 : v = (p (p v k) (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))))) := Eq.trans (peq1) (pst14); pst15)
      have hlt : sz v < sz (p (p v k) (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_x) (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p v k) (p v k))) := congrArg (fun q => p q_H1 q) (pst4); let pst6 : (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) = (p (p q_x q_x) (p q_H1 (p (p v k) (p v k)))) := congrArg (fun q => p (p q_x q_x) q) (pst5); let pst7 : (p (p v k) (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := congrArg (fun q => p q (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) (pst0); let pst2 : (p q_H0 q_v0) = (p q_H0 (p v k)) := congrArg (fun q => p q_H0 q) (pst0); let pst3 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p v k)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst2); let pst4 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_H0 (p v k)) (p q_v0 q_v0)) = (p (p q_H0 (p v k)) (p (p v k) (p v k))) := congrArg (fun q => p (p q_H0 (p v k)) q) (pst6); let pst8 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p v k)) (p (p v k) (p v k))) := Eq.trans (pst3) (pst7); let pst9 : (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) = (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k)))) := congrArg (fun q => p (p q_x q_x) q) (pst8); let pst10 : (p (p v k) (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst9); let pst11 : (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k))))) := Eq.trans (pst1) (pst10); let pst12 : v = (p (p v k) (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k))))) := Eq.trans (peq1) (pst11); pst12)
      have hlt : sz v < sz (p (p v k) (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_x) (p (p q_H0 (p v k)) (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p v k) (p v k))) := congrArg (fun q => p q_H1 q) (pst4); let pst6 : (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) = (p (p q_x q_x) (p q_H1 (p (p v k) (p v k)))) := congrArg (fun q => p (p q_x q_x) q) (pst5); let pst7 : (p (p v k) (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_x) (p q_H1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
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
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      apply code_no_pair_left q_v0 q_v1
      exact ⟨_, qs1h⟩
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
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
      change v0 = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      apply code_no_pair_left q_v0 q_v1
      exact ⟨_, qs1h⟩
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_x) (p q_H1 (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step H0 v0 H1) :
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
        change (p H0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) at e2
        have cyc : v0 = (p H0 v0) := (let peq0 : (p H0 v0) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq0); let pst1 : v0 = (p H0 v0) := Eq.trans (peq1) (pst0); pst1)
        have hlt : sz v0 < sz (p H0 v0) := sz_lt_p_right H0 v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        apply code_no_pair_left q_v0 q_v1
        exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p H0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) at e2
        have cyc : v0 = (p H0 v0) := (let peq0 : (p H0 v0) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq0); let pst1 : v0 = (p H0 v0) := Eq.trans (peq1) (pst0); pst1)
        have hlt : sz v0 < sz (p H0 v0) := sz_lt_p_right H0 v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p H0 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : v0 = (p H0 v0) := (let peq0 : (p H0 v0) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq0); let pst1 : v0 = (p H0 v0) := Eq.trans (peq1) (pst0); pst1)
        have hlt : sz v0 < sz (p H0 v0) := sz_lt_p_right H0 v0
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
        change v0 = (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0))) (sz_lt_p_right (p q_x q_x) (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        apply code_no_pair_left q_v0 q_v1
        exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p q_v0 q_v0))) (sz_lt_p_right (p q_x q_x) (p (p q_H0 q_v0) (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p (p q_x q_x) (p q_H1 (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_H1 (p q_v0 q_v0))) (sz_lt_p_right (p q_x q_x) (p q_H1 (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step H0 v0 H1) :
    ¬ ∃ o, Code (p x x) (p H1 (p v0 v0)) o := by
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
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p H0 v0) = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change v0 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) at e3
        have cyc : q_x = (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) := (let peq0 : (p x x) = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = (p q_x q_x) := e2; let peq3 : v0 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) := e3; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p H0 v0) = (p x x) := Eq.trans (peq1) (pst0); let pst2 : v0 = x := congrArg (fun q => R q) (pst1); let pst3 : x = v0 := Eq.symm (pst2); let pst4 : x = (p q_x q_x) := Eq.trans (pst3) (peq2); let pst5 : v0 = (p q_x q_x) := Eq.trans (pst2) (pst4); let pst6 : (p q_x q_x) = v0 := Eq.symm (pst5); let pst7 : (p q_x q_x) = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) := Eq.trans (pst6) (peq3); let pst8 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst9 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst10 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst8) (pst9); let pst11 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst10); let pst12 : (p q_v0 q_v1) = (p (p (p q_x q_x) (p q_x q_x)) q_v1) := congrArg (fun q => p q q_v1) (pst11); let pst13 : (p (p q_v0 q_v1) q_v0) = (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst12); let pst14 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst15 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst16 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst14) (pst15); let pst17 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst16); let pst18 : (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) q_v0) = (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p (p (p (p q_x q_x) (p q_x q_x)) q_v1) q) (pst17); let pst19 : (p (p q_v0 q_v1) q_v0) = (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) := Eq.trans (pst13) (pst18); let pst20 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) = (p (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst19); let pst21 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst22 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst23 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst21) (pst22); let pst24 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p q_x q_x) (p q_x q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst27 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst28 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst26) (pst27); let pst29 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst28); let pst30 : (p (p (p q_x q_x) (p q_x q_x)) q_v0) = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p (p (p q_x q_x) (p q_x q_x)) q) (pst29); let pst31 : (p q_v0 q_v0) = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := Eq.trans (pst25) (pst30); let pst32 : (p (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) (p q_v0 q_v0)) = (p (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := congrArg (fun q => p (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) q) (pst31); let pst33 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) = (p (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := Eq.trans (pst20) (pst32); let pst34 : (p q_x q_x) = (p (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := Eq.trans (pst7) (pst33); let pst35 : q_x = (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => L q) (pst34); pst35)
        have hlt : sz q_x < sz (p (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) (p q_x q_x))) (sz_lt_p_left (p (p q_x q_x) (p q_x q_x)) q_v1)) (sz_lt_p_left (p (p (p q_x q_x) (p q_x q_x)) q_v1) (p (p q_x q_x) (p q_x q_x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        apply code_no_pair_left q_v0 q_v1
        exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p H0 v0) = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change v0 = (p (p q_H0 q_v0) (p q_v0 q_v0)) at e3
        have cyc : q_x = (p q_H0 (p (p q_x q_x) (p q_x q_x))) := (let peq0 : (p x x) = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = (p q_x q_x) := e2; let peq3 : v0 = (p (p q_H0 q_v0) (p q_v0 q_v0)) := e3; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p H0 v0) = (p x x) := Eq.trans (peq1) (pst0); let pst2 : v0 = x := congrArg (fun q => R q) (pst1); let pst3 : x = v0 := Eq.symm (pst2); let pst4 : x = (p q_x q_x) := Eq.trans (pst3) (peq2); let pst5 : v0 = (p q_x q_x) := Eq.trans (pst2) (pst4); let pst6 : (p q_x q_x) = v0 := Eq.symm (pst5); let pst7 : (p q_x q_x) = (p (p q_H0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst6) (peq3); let pst8 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst9 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst10 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst8) (pst9); let pst11 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst10); let pst12 : (p q_H0 q_v0) = (p q_H0 (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p q_H0 q) (pst11); let pst13 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p (p q_x q_x) (p q_x q_x))) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst12); let pst14 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst15 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst16 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst14) (pst15); let pst17 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst16); let pst18 : (p q_v0 q_v0) = (p (p (p q_x q_x) (p q_x q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst17); let pst19 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst20 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst21 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst19) (pst20); let pst22 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst21); let pst23 : (p (p (p q_x q_x) (p q_x q_x)) q_v0) = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p (p (p q_x q_x) (p q_x q_x)) q) (pst22); let pst24 : (p q_v0 q_v0) = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := Eq.trans (pst18) (pst23); let pst25 : (p (p q_H0 (p (p q_x q_x) (p q_x q_x))) (p q_v0 q_v0)) = (p (p q_H0 (p (p q_x q_x) (p q_x q_x))) (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := congrArg (fun q => p (p q_H0 (p (p q_x q_x) (p q_x q_x))) q) (pst24); let pst26 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p (p q_x q_x) (p q_x q_x))) (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := Eq.trans (pst13) (pst25); let pst27 : (p q_x q_x) = (p (p q_H0 (p (p q_x q_x) (p q_x q_x))) (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := Eq.trans (pst7) (pst26); let pst28 : q_x = (p q_H0 (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => L q) (pst27); pst28)
        have hlt : sz q_x < sz (p q_H0 (p (p q_x q_x) (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p q_x q_x) (p q_x q_x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p H0 v0) = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change v0 = (p q_H1 (p q_v0 q_v0)) at e3
        have cyc : q_H1 = (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_H1 q_H1) (p q_H1 q_H1))) := (let peq0 : (p x x) = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = (p q_x q_x) := e2; let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := e3; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p H0 v0) = (p x x) := Eq.trans (peq1) (pst0); let pst2 : v0 = x := congrArg (fun q => R q) (pst1); let pst3 : x = v0 := Eq.symm (pst2); let pst4 : x = (p q_x q_x) := Eq.trans (pst3) (peq2); let pst5 : v0 = (p q_x q_x) := Eq.trans (pst2) (pst4); let pst6 : (p q_x q_x) = v0 := Eq.symm (pst5); let pst7 : (p q_x q_x) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst6) (peq3); let pst8 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst9 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst10 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst8) (pst9); let pst11 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst10); let pst12 : (p q_v0 q_v0) = (p (p (p q_x q_x) (p q_x q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst11); let pst13 : (p x x) = (p (p q_x q_x) x) := congrArg (fun q => p q x) (pst4); let pst14 : (p (p q_x q_x) x) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst4); let pst15 : (p x x) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst13) (pst14); let pst16 : q_v0 = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst0) (pst15); let pst17 : (p (p (p q_x q_x) (p q_x q_x)) q_v0) = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p (p (p q_x q_x) (p q_x q_x)) q) (pst16); let pst18 : (p q_v0 q_v0) = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := Eq.trans (pst12) (pst17); let pst19 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := congrArg (fun q => p q_H1 q) (pst18); let pst20 : (p q_x q_x) = (p q_H1 (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x)))) := Eq.trans (pst7) (pst19); let pst21 : q_x = q_H1 := congrArg (fun q => L q) (pst20); let pst22 : q_H1 = q_x := Eq.symm (pst21); let pst23 : q_x = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => R q) (pst20); let pst24 : q_H1 = (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) := Eq.trans (pst22) (pst23); let pst25 : (p q_x q_x) = (p q_H1 q_x) := congrArg (fun q => p q q_x) (pst21); let pst26 : (p q_H1 q_x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst21); let pst27 : (p q_x q_x) = (p q_H1 q_H1) := Eq.trans (pst25) (pst26); let pst28 : (p (p q_x q_x) (p q_x q_x)) = (p (p q_H1 q_H1) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst27); let pst29 : (p q_x q_x) = (p q_H1 q_x) := congrArg (fun q => p q q_x) (pst21); let pst30 : (p q_H1 q_x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst21); let pst31 : (p q_x q_x) = (p q_H1 q_H1) := Eq.trans (pst29) (pst30); let pst32 : (p (p q_H1 q_H1) (p q_x q_x)) = (p (p q_H1 q_H1) (p q_H1 q_H1)) := congrArg (fun q => p (p q_H1 q_H1) q) (pst31); let pst33 : (p (p q_x q_x) (p q_x q_x)) = (p (p q_H1 q_H1) (p q_H1 q_H1)) := Eq.trans (pst28) (pst32); let pst34 : (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) = (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p q (p (p q_x q_x) (p q_x q_x))) (pst33); let pst35 : (p q_x q_x) = (p q_H1 q_x) := congrArg (fun q => p q q_x) (pst21); let pst36 : (p q_H1 q_x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst21); let pst37 : (p q_x q_x) = (p q_H1 q_H1) := Eq.trans (pst35) (pst36); let pst38 : (p (p q_x q_x) (p q_x q_x)) = (p (p q_H1 q_H1) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst37); let pst39 : (p q_x q_x) = (p q_H1 q_x) := congrArg (fun q => p q q_x) (pst21); let pst40 : (p q_H1 q_x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst21); let pst41 : (p q_x q_x) = (p q_H1 q_H1) := Eq.trans (pst39) (pst40); let pst42 : (p (p q_H1 q_H1) (p q_x q_x)) = (p (p q_H1 q_H1) (p q_H1 q_H1)) := congrArg (fun q => p (p q_H1 q_H1) q) (pst41); let pst43 : (p (p q_x q_x) (p q_x q_x)) = (p (p q_H1 q_H1) (p q_H1 q_H1)) := Eq.trans (pst38) (pst42); let pst44 : (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_x q_x) (p q_x q_x))) = (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_H1 q_H1) (p q_H1 q_H1))) := congrArg (fun q => p (p (p q_H1 q_H1) (p q_H1 q_H1)) q) (pst43); let pst45 : (p (p (p q_x q_x) (p q_x q_x)) (p (p q_x q_x) (p q_x q_x))) = (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_H1 q_H1) (p q_H1 q_H1))) := Eq.trans (pst34) (pst44); let pst46 : q_H1 = (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_H1 q_H1) (p q_H1 q_H1))) := Eq.trans (pst24) (pst45); pst46)
        have hlt : sz q_H1 < sz (p (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_H1 q_H1) (p q_H1 q_H1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_H1 q_H1) (sz_lt_p_left (p q_H1 q_H1) (p q_H1 q_H1))) (sz_lt_p_left (p (p q_H1 q_H1) (p q_H1 q_H1)) (p (p q_H1 q_H1) (p q_H1 q_H1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H1 = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change v0 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) at e3
        have cyc : x = (p x x) := (let peq0 : (p x x) = q_v0 := e0; let peq2 : v0 = (p q_x q_x) := e2; let peq3 : v0 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) := e3; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_v0 q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : (p (p q_v0 q_v1) q_v0) = (p (p (p x x) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p (p x x) q_v1) q_v0) = (p (p (p x x) q_v1) (p x x)) := congrArg (fun q => p (p (p x x) q_v1) q) (pst2); let pst6 : (p (p q_v0 q_v1) q_v0) = (p (p (p x x) q_v1) (p x x)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) = (p (p (p (p x x) q_v1) (p x x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst6); let pst8 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst9 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst10 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst8) (pst9); let pst11 : (p (p (p (p x x) q_v1) (p x x)) (p q_v0 q_v0)) = (p (p (p (p x x) q_v1) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p (p x x) q_v1) (p x x)) q) (pst10); let pst12 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_v0)) = (p (p (p (p x x) q_v1) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst7) (pst11); let pst13 : (p q_x q_x) = (p (p (p (p x x) q_v1) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst1) (pst12); let pst14 : q_x = (p (p (p x x) q_v1) (p x x)) := congrArg (fun q => L q) (pst13); let pst15 : (p (p (p x x) q_v1) (p x x)) = q_x := Eq.symm (pst14); let pst16 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst13); let pst17 : (p (p (p x x) q_v1) (p x x)) = (p (p x x) (p x x)) := Eq.trans (pst15) (pst16); let pst18 : (p (p x x) q_v1) = (p x x) := congrArg (fun q => L q) (pst17); let pst19 : (p x x) = x := congrArg (fun q => L q) (pst18); let pst20 : x = (p x x) := Eq.symm (pst19); pst20)
        have hlt : sz x < sz (p x x) := sz_lt_p_left x x
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        apply code_no_pair_left q_v0 q_v1
        exact ⟨_, qs1h⟩
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
            have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := (let peq0 : (p x x) = q_v0 := ha; let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p (p q_H0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => (R (R q))) (hb); let peq6 : v0 = (p u0_v0 (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)))) := u0b; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p (p q_H0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_H0 q_v0) = (p q_H0 (p x x)) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst6 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst7 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst5) (pst6); let pst8 : (p (p q_H0 (p x x)) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p q_H0 (p x x)) q) (pst7); let pst9 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst8); let pst10 : (p q_x q_x) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := Eq.trans (pst1) (pst9); let pst11 : q_x = (p q_H0 (p x x)) := congrArg (fun q => L q) (pst10); let pst12 : (p q_H0 (p x x)) = q_x := Eq.symm (pst11); let pst13 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst10); let pst14 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := Eq.trans (pst12) (pst13); let pst15 : q_H0 = (p x x) := congrArg (fun q => L q) (pst14); let pst16 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := congrArg (fun q => p q (p x x)) (pst15); let pst17 : q_x = (p (p x x) (p x x)) := Eq.trans (pst11) (pst16); let pst18 : (p q_x q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst17); let pst19 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := congrArg (fun q => p q (p x x)) (pst15); let pst20 : q_x = (p (p x x) (p x x)) := Eq.trans (pst11) (pst19); let pst21 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst20); let pst22 : (p q_x q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst18) (pst21); let pst23 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq2) (pst22); let pst24 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst23); let pst25 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p u0_v0 (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)))) := Eq.trans (pst24) (peq6); let pst26 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0))) := congrArg (fun q => R q) (pst25); let pst27 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => L q) (pst25); let pst28 : u0_v0 = (p (p x x) (p x x)) := Eq.symm (pst27); let pst29 : (p u0_v0 u0_v1) = (p (p (p x x) (p x x)) u0_v1) := congrArg (fun q => p q u0_v1) (pst28); let pst30 : (p (p u0_v0 u0_v1) u0_v0) = (p (p (p (p x x) (p x x)) u0_v1) u0_v0) := congrArg (fun q => p q u0_v0) (pst29); let pst31 : (p (p (p (p x x) (p x x)) u0_v1) u0_v0) = (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) := congrArg (fun q => p (p (p (p x x) (p x x)) u0_v1) q) (pst28); let pst32 : (p (p u0_v0 u0_v1) u0_v0) = (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) := Eq.trans (pst30) (pst31); let pst33 : (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst32); let pst34 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) u0_v0) := congrArg (fun q => p q u0_v0) (pst28); let pst35 : (p (p (p x x) (p x x)) u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst28); let pst36 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst34) (pst35); let pst37 : (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p u0_v0 u0_v0)) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) q) (pst36); let pst38 : (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst33) (pst37); let pst39 : (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0))) = (p (p u0_x u0_x) (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := congrArg (fun q => p (p u0_x u0_x) q) (pst38); let pst40 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := Eq.trans (pst26) (pst39); let pst41 : (p x x) = (p u0_x u0_x) := congrArg (fun q => L q) (pst40); let pst42 : x = u0_x := congrArg (fun q => L q) (pst41); let pst43 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst44 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst45 : (p x x) = (p u0_x u0_x) := Eq.trans (pst43) (pst44); let pst46 : (p u0_x u0_x) = (p x x) := Eq.symm (pst45); let pst47 : (p x x) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => R q) (pst40); let pst48 : (p u0_x u0_x) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst46) (pst47); let pst49 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst50 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst51 : (p x x) = (p u0_x u0_x) := Eq.trans (pst49) (pst50); let pst52 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst51); let pst53 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst54 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst55 : (p x x) = (p u0_x u0_x) := Eq.trans (pst53) (pst54); let pst56 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst55); let pst57 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst52) (pst56); let pst58 : (p (p (p x x) (p x x)) u0_v1) = (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) := congrArg (fun q => p q u0_v1) (pst57); let pst59 : (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst58); let pst60 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst61 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst62 : (p x x) = (p u0_x u0_x) := Eq.trans (pst60) (pst61); let pst63 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst62); let pst64 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst65 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst66 : (p x x) = (p u0_x u0_x) := Eq.trans (pst64) (pst65); let pst67 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst66); let pst68 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst63) (pst67); let pst69 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p x x) (p x x))) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) q) (pst68); let pst70 : (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst59) (pst69); let pst71 : (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p q (p (p (p x x) (p x x)) (p (p x x) (p x x)))) (pst70); let pst72 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst73 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst74 : (p x x) = (p u0_x u0_x) := Eq.trans (pst72) (pst73); let pst75 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst74); let pst76 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst77 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst78 : (p x x) = (p u0_x u0_x) := Eq.trans (pst76) (pst77); let pst79 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst78); let pst80 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst75) (pst79); let pst81 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst80); let pst82 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst83 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst84 : (p x x) = (p u0_x u0_x) := Eq.trans (pst82) (pst83); let pst85 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst84); let pst86 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst42); let pst87 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst42); let pst88 : (p x x) = (p u0_x u0_x) := Eq.trans (pst86) (pst87); let pst89 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst88); let pst90 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst85) (pst89); let pst91 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst90); let pst92 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst81) (pst91); let pst93 : (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst92); let pst94 : (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst71) (pst93); let pst95 : (p u0_x u0_x) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst48) (pst94); let pst96 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => L q) (pst95); pst96)
            have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1)) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            apply code_no_pair_left u0_v0 u0_v1
            exact ⟨_, u0s1h⟩
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := (let peq0 : (p x x) = q_v0 := ha; let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p (p q_H0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => (R (R q))) (hb); let peq6 : v0 = (p u0_v0 (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0)))) := u0b; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p (p q_H0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_H0 q_v0) = (p q_H0 (p x x)) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst6 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst7 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst5) (pst6); let pst8 : (p (p q_H0 (p x x)) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p q_H0 (p x x)) q) (pst7); let pst9 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst8); let pst10 : (p q_x q_x) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := Eq.trans (pst1) (pst9); let pst11 : q_x = (p q_H0 (p x x)) := congrArg (fun q => L q) (pst10); let pst12 : (p q_H0 (p x x)) = q_x := Eq.symm (pst11); let pst13 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst10); let pst14 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := Eq.trans (pst12) (pst13); let pst15 : q_H0 = (p x x) := congrArg (fun q => L q) (pst14); let pst16 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := congrArg (fun q => p q (p x x)) (pst15); let pst17 : q_x = (p (p x x) (p x x)) := Eq.trans (pst11) (pst16); let pst18 : (p q_x q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst17); let pst19 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := congrArg (fun q => p q (p x x)) (pst15); let pst20 : q_x = (p (p x x) (p x x)) := Eq.trans (pst11) (pst19); let pst21 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst20); let pst22 : (p q_x q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst18) (pst21); let pst23 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq2) (pst22); let pst24 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst23); let pst25 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p u0_v0 (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0)))) := Eq.trans (pst24) (peq6); let pst26 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0))) := congrArg (fun q => R q) (pst25); let pst27 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => L q) (pst25); let pst28 : u0_v0 = (p (p x x) (p x x)) := Eq.symm (pst27); let pst29 : (p u0s0out u0_v0) = (p u0s0out (p (p x x) (p x x))) := congrArg (fun q => p u0s0out q) (pst28); let pst30 : (p (p u0s0out u0_v0) (p u0_v0 u0_v0)) = (p (p u0s0out (p (p x x) (p x x))) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst29); let pst31 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) u0_v0) := congrArg (fun q => p q u0_v0) (pst28); let pst32 : (p (p (p x x) (p x x)) u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst28); let pst33 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst31) (pst32); let pst34 : (p (p u0s0out (p (p x x) (p x x))) (p u0_v0 u0_v0)) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p (p u0s0out (p (p x x) (p x x))) q) (pst33); let pst35 : (p (p u0s0out u0_v0) (p u0_v0 u0_v0)) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst30) (pst34); let pst36 : (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0))) = (p (p u0_x u0_x) (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := congrArg (fun q => p (p u0_x u0_x) q) (pst35); let pst37 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := Eq.trans (pst26) (pst36); let pst38 : (p x x) = (p u0_x u0_x) := congrArg (fun q => L q) (pst37); let pst39 : x = u0_x := congrArg (fun q => L q) (pst38); let pst40 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst41 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst42 : (p x x) = (p u0_x u0_x) := Eq.trans (pst40) (pst41); let pst43 : (p u0_x u0_x) = (p x x) := Eq.symm (pst42); let pst44 : (p x x) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => R q) (pst37); let pst45 : (p u0_x u0_x) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst43) (pst44); let pst46 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst47 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst48 : (p x x) = (p u0_x u0_x) := Eq.trans (pst46) (pst47); let pst49 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst48); let pst50 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst51 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst52 : (p x x) = (p u0_x u0_x) := Eq.trans (pst50) (pst51); let pst53 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst52); let pst54 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst49) (pst53); let pst55 : (p u0s0out (p (p x x) (p x x))) = (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p u0s0out q) (pst54); let pst56 : (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p q (p (p (p x x) (p x x)) (p (p x x) (p x x)))) (pst55); let pst57 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst58 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst59 : (p x x) = (p u0_x u0_x) := Eq.trans (pst57) (pst58); let pst60 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst59); let pst61 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst62 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst63 : (p x x) = (p u0_x u0_x) := Eq.trans (pst61) (pst62); let pst64 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst63); let pst65 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst60) (pst64); let pst66 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst65); let pst67 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst68 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst69 : (p x x) = (p u0_x u0_x) := Eq.trans (pst67) (pst68); let pst70 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst69); let pst71 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst39); let pst72 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst39); let pst73 : (p x x) = (p u0_x u0_x) := Eq.trans (pst71) (pst72); let pst74 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst73); let pst75 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst70) (pst74); let pst76 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst75); let pst77 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst66) (pst76); let pst78 : (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst77); let pst79 : (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst56) (pst78); let pst80 : (p u0_x u0_x) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst45) (pst79); let pst81 : u0_x = (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => L q) (pst80); pst81)
            have hlt : sz u0_x < sz (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_right u0s0out (p (p u0_x u0_x) (p u0_x u0_x)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0s1out = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := (let peq0 : (p x x) = q_v0 := ha; let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p (p q_H0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => (R (R q))) (hb); let peq6 : v0 = (p u0_v0 (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0)))) := u0b; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p (p q_H0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_H0 q_v0) = (p q_H0 (p x x)) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst6 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst7 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst5) (pst6); let pst8 : (p (p q_H0 (p x x)) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p q_H0 (p x x)) q) (pst7); let pst9 : (p (p q_H0 q_v0) (p q_v0 q_v0)) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst8); let pst10 : (p q_x q_x) = (p (p q_H0 (p x x)) (p (p x x) (p x x))) := Eq.trans (pst1) (pst9); let pst11 : q_x = (p q_H0 (p x x)) := congrArg (fun q => L q) (pst10); let pst12 : (p q_H0 (p x x)) = q_x := Eq.symm (pst11); let pst13 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst10); let pst14 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := Eq.trans (pst12) (pst13); let pst15 : q_H0 = (p x x) := congrArg (fun q => L q) (pst14); let pst16 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := congrArg (fun q => p q (p x x)) (pst15); let pst17 : q_x = (p (p x x) (p x x)) := Eq.trans (pst11) (pst16); let pst18 : (p q_x q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst17); let pst19 : (p q_H0 (p x x)) = (p (p x x) (p x x)) := congrArg (fun q => p q (p x x)) (pst15); let pst20 : q_x = (p (p x x) (p x x)) := Eq.trans (pst11) (pst19); let pst21 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst20); let pst22 : (p q_x q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst18) (pst21); let pst23 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq2) (pst22); let pst24 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst23); let pst25 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p u0_v0 (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0)))) := Eq.trans (pst24) (peq6); let pst26 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0))) := congrArg (fun q => R q) (pst25); let pst27 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => L q) (pst25); let pst28 : u0_v0 = (p (p x x) (p x x)) := Eq.symm (pst27); let pst29 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) u0_v0) := congrArg (fun q => p q u0_v0) (pst28); let pst30 : (p (p (p x x) (p x x)) u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst28); let pst31 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst29) (pst30); let pst32 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p u0s1out q) (pst31); let pst33 : (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0))) = (p (p u0_x u0_x) (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := congrArg (fun q => p (p u0_x u0_x) q) (pst32); let pst34 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := Eq.trans (pst26) (pst33); let pst35 : (p x x) = (p u0_x u0_x) := congrArg (fun q => L q) (pst34); let pst36 : x = u0_x := congrArg (fun q => L q) (pst35); let pst37 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst38 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst39 : (p x x) = (p u0_x u0_x) := Eq.trans (pst37) (pst38); let pst40 : (p u0_x u0_x) = (p x x) := Eq.symm (pst39); let pst41 : (p x x) = (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => R q) (pst34); let pst42 : (p u0_x u0_x) = (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst40) (pst41); let pst43 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst44 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst45 : (p x x) = (p u0_x u0_x) := Eq.trans (pst43) (pst44); let pst46 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst45); let pst47 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst48 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst49 : (p x x) = (p u0_x u0_x) := Eq.trans (pst47) (pst48); let pst50 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst49); let pst51 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst46) (pst50); let pst52 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst51); let pst53 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst54 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst55 : (p x x) = (p u0_x u0_x) := Eq.trans (pst53) (pst54); let pst56 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst55); let pst57 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst58 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst59 : (p x x) = (p u0_x u0_x) := Eq.trans (pst57) (pst58); let pst60 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst59); let pst61 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst56) (pst60); let pst62 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst61); let pst63 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst52) (pst62); let pst64 : (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p u0s1out (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p u0s1out q) (pst63); let pst65 : (p u0_x u0_x) = (p u0s1out (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst42) (pst64); let pst66 : u0_x = u0s1out := congrArg (fun q => L q) (pst65); let pst67 : u0s1out = u0_x := Eq.symm (pst66); let pst68 : u0_x = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => R q) (pst65); let pst69 : u0s1out = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst67) (pst68); let pst70 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst66); let pst71 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst66); let pst72 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst70) (pst71); let pst73 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0_x u0_x)) := congrArg (fun q => p q (p u0_x u0_x)) (pst72); let pst74 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst66); let pst75 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst66); let pst76 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst74) (pst75); let pst77 : (p (p u0s1out u0s1out) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := congrArg (fun q => p (p u0s1out u0s1out) q) (pst76); let pst78 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := Eq.trans (pst73) (pst77); let pst79 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q (p (p u0_x u0_x) (p u0_x u0_x))) (pst78); let pst80 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst66); let pst81 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst66); let pst82 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst80) (pst81); let pst83 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0_x u0_x)) := congrArg (fun q => p q (p u0_x u0_x)) (pst82); let pst84 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst66); let pst85 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst66); let pst86 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst84) (pst85); let pst87 : (p (p u0s1out u0s1out) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := congrArg (fun q => p (p u0s1out u0s1out) q) (pst86); let pst88 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := Eq.trans (pst83) (pst87); let pst89 : (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0_x u0_x) (p u0_x u0_x))) = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := congrArg (fun q => p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) q) (pst88); let pst90 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := Eq.trans (pst79) (pst89); let pst91 : u0s1out = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := Eq.trans (pst69) (pst90); pst91)
            have hlt : sz u0s1out < sz (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0s1out u0s1out) (sz_lt_p_left (p u0s1out u0s1out) (p u0s1out u0s1out))) (sz_lt_p_left (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0B := step_bound u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1B := step_bound u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := (let peq0 : (p x x) = q_v0 := ha; let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := congrArg (fun q => (R (R q))) (hb); let peq6 : v0 = (p u0_v0 (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)))) := u0b; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x x) (p x x))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p q_x q_x) = (p q_H1 (p (p x x) (p x x))) := Eq.trans (pst1) (pst6); let pst8 : q_x = q_H1 := congrArg (fun q => L q) (pst7); let pst9 : q_H1 = q_x := Eq.symm (pst8); let pst10 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst7); let pst11 : q_H1 = (p (p x x) (p x x)) := Eq.trans (pst9) (pst10); let pst12 : q_x = (p (p x x) (p x x)) := Eq.trans (pst8) (pst11); let pst13 : (p q_x q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst12); let pst14 : q_x = (p (p x x) (p x x)) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst14); let pst16 : (p q_x q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst13) (pst15); let pst17 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq2) (pst16); let pst18 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p u0_v0 (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)))) := Eq.trans (pst18) (peq6); let pst20 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0))) := congrArg (fun q => R q) (pst19); let pst21 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => L q) (pst19); let pst22 : u0_v0 = (p (p x x) (p x x)) := Eq.symm (pst21); let pst23 : (p u0_v0 u0_v1) = (p (p (p x x) (p x x)) u0_v1) := congrArg (fun q => p q u0_v1) (pst22); let pst24 : (p (p u0_v0 u0_v1) u0_v0) = (p (p (p (p x x) (p x x)) u0_v1) u0_v0) := congrArg (fun q => p q u0_v0) (pst23); let pst25 : (p (p (p (p x x) (p x x)) u0_v1) u0_v0) = (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) := congrArg (fun q => p (p (p (p x x) (p x x)) u0_v1) q) (pst22); let pst26 : (p (p u0_v0 u0_v1) u0_v0) = (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) := Eq.trans (pst24) (pst25); let pst27 : (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst26); let pst28 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) u0_v0) := congrArg (fun q => p q u0_v0) (pst22); let pst29 : (p (p (p x x) (p x x)) u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst22); let pst30 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst28) (pst29); let pst31 : (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p u0_v0 u0_v0)) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) q) (pst30); let pst32 : (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0)) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst27) (pst31); let pst33 : (p (p u0_x u0_x) (p (p (p u0_v0 u0_v1) u0_v0) (p u0_v0 u0_v0))) = (p (p u0_x u0_x) (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := congrArg (fun q => p (p u0_x u0_x) q) (pst32); let pst34 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := Eq.trans (pst20) (pst33); let pst35 : (p x x) = (p u0_x u0_x) := congrArg (fun q => L q) (pst34); let pst36 : x = u0_x := congrArg (fun q => L q) (pst35); let pst37 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst38 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst39 : (p x x) = (p u0_x u0_x) := Eq.trans (pst37) (pst38); let pst40 : (p u0_x u0_x) = (p x x) := Eq.symm (pst39); let pst41 : (p x x) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => R q) (pst34); let pst42 : (p u0_x u0_x) = (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst40) (pst41); let pst43 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst44 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst45 : (p x x) = (p u0_x u0_x) := Eq.trans (pst43) (pst44); let pst46 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst45); let pst47 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst48 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst49 : (p x x) = (p u0_x u0_x) := Eq.trans (pst47) (pst48); let pst50 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst49); let pst51 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst46) (pst50); let pst52 : (p (p (p x x) (p x x)) u0_v1) = (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) := congrArg (fun q => p q u0_v1) (pst51); let pst53 : (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst52); let pst54 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst55 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst56 : (p x x) = (p u0_x u0_x) := Eq.trans (pst54) (pst55); let pst57 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst56); let pst58 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst59 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst60 : (p x x) = (p u0_x u0_x) := Eq.trans (pst58) (pst59); let pst61 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst60); let pst62 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst57) (pst61); let pst63 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p x x) (p x x))) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) q) (pst62); let pst64 : (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst53) (pst63); let pst65 : (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p q (p (p (p x x) (p x x)) (p (p x x) (p x x)))) (pst64); let pst66 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst67 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst68 : (p x x) = (p u0_x u0_x) := Eq.trans (pst66) (pst67); let pst69 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst68); let pst70 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst71 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst72 : (p x x) = (p u0_x u0_x) := Eq.trans (pst70) (pst71); let pst73 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst72); let pst74 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst69) (pst73); let pst75 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst74); let pst76 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst77 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst78 : (p x x) = (p u0_x u0_x) := Eq.trans (pst76) (pst77); let pst79 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst78); let pst80 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst36); let pst81 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst36); let pst82 : (p x x) = (p u0_x u0_x) := Eq.trans (pst80) (pst81); let pst83 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst82); let pst84 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst79) (pst83); let pst85 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst84); let pst86 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst75) (pst85); let pst87 : (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst86); let pst88 : (p (p (p (p (p x x) (p x x)) u0_v1) (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst65) (pst87); let pst89 : (p u0_x u0_x) = (p (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst42) (pst88); let pst90 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => L q) (pst89); pst90)
            have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1)) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) u0_v1) (p (p u0_x u0_x) (p u0_x u0_x)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            apply code_no_pair_left u0_v0 u0_v1
            exact ⟨_, u0s1h⟩
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := (let peq0 : (p x x) = q_v0 := ha; let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := congrArg (fun q => (R (R q))) (hb); let peq6 : v0 = (p u0_v0 (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0)))) := u0b; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x x) (p x x))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p q_x q_x) = (p q_H1 (p (p x x) (p x x))) := Eq.trans (pst1) (pst6); let pst8 : q_x = q_H1 := congrArg (fun q => L q) (pst7); let pst9 : q_H1 = q_x := Eq.symm (pst8); let pst10 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst7); let pst11 : q_H1 = (p (p x x) (p x x)) := Eq.trans (pst9) (pst10); let pst12 : q_x = (p (p x x) (p x x)) := Eq.trans (pst8) (pst11); let pst13 : (p q_x q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst12); let pst14 : q_x = (p (p x x) (p x x)) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst14); let pst16 : (p q_x q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst13) (pst15); let pst17 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq2) (pst16); let pst18 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p u0_v0 (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0)))) := Eq.trans (pst18) (peq6); let pst20 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0))) := congrArg (fun q => R q) (pst19); let pst21 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => L q) (pst19); let pst22 : u0_v0 = (p (p x x) (p x x)) := Eq.symm (pst21); let pst23 : (p u0s0out u0_v0) = (p u0s0out (p (p x x) (p x x))) := congrArg (fun q => p u0s0out q) (pst22); let pst24 : (p (p u0s0out u0_v0) (p u0_v0 u0_v0)) = (p (p u0s0out (p (p x x) (p x x))) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst23); let pst25 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) u0_v0) := congrArg (fun q => p q u0_v0) (pst22); let pst26 : (p (p (p x x) (p x x)) u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst22); let pst27 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst25) (pst26); let pst28 : (p (p u0s0out (p (p x x) (p x x))) (p u0_v0 u0_v0)) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p (p u0s0out (p (p x x) (p x x))) q) (pst27); let pst29 : (p (p u0s0out u0_v0) (p u0_v0 u0_v0)) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst24) (pst28); let pst30 : (p (p u0_x u0_x) (p (p u0s0out u0_v0) (p u0_v0 u0_v0))) = (p (p u0_x u0_x) (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := congrArg (fun q => p (p u0_x u0_x) q) (pst29); let pst31 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := Eq.trans (pst20) (pst30); let pst32 : (p x x) = (p u0_x u0_x) := congrArg (fun q => L q) (pst31); let pst33 : x = u0_x := congrArg (fun q => L q) (pst32); let pst34 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst35 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst36 : (p x x) = (p u0_x u0_x) := Eq.trans (pst34) (pst35); let pst37 : (p u0_x u0_x) = (p x x) := Eq.symm (pst36); let pst38 : (p x x) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => R q) (pst31); let pst39 : (p u0_x u0_x) = (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst37) (pst38); let pst40 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst41 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst42 : (p x x) = (p u0_x u0_x) := Eq.trans (pst40) (pst41); let pst43 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst42); let pst44 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst45 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst46 : (p x x) = (p u0_x u0_x) := Eq.trans (pst44) (pst45); let pst47 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst46); let pst48 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst43) (pst47); let pst49 : (p u0s0out (p (p x x) (p x x))) = (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p u0s0out q) (pst48); let pst50 : (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p q (p (p (p x x) (p x x)) (p (p x x) (p x x)))) (pst49); let pst51 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst52 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst53 : (p x x) = (p u0_x u0_x) := Eq.trans (pst51) (pst52); let pst54 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst53); let pst55 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst56 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst57 : (p x x) = (p u0_x u0_x) := Eq.trans (pst55) (pst56); let pst58 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst57); let pst59 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst54) (pst58); let pst60 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst59); let pst61 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst62 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst63 : (p x x) = (p u0_x u0_x) := Eq.trans (pst61) (pst62); let pst64 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst63); let pst65 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst33); let pst66 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst33); let pst67 : (p x x) = (p u0_x u0_x) := Eq.trans (pst65) (pst66); let pst68 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst67); let pst69 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst64) (pst68); let pst70 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst69); let pst71 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst60) (pst70); let pst72 : (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst71); let pst73 : (p (p u0s0out (p (p x x) (p x x))) (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst50) (pst72); let pst74 : (p u0_x u0_x) = (p (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst39) (pst73); let pst75 : u0_x = (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => L q) (pst74); pst75)
            have hlt : sz u0_x < sz (p u0s0out (p (p u0_x u0_x) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_right u0s0out (p (p u0_x u0_x) (p u0_x u0_x)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0s1out = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := (let peq0 : (p x x) = q_v0 := ha; let peq2 : v0 = (p q_x q_x) := congrArg (fun q => (L (R q))) (hb); let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := congrArg (fun q => (R (R q))) (hb); let peq6 : v0 = (p u0_v0 (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0)))) := u0b; let pst0 : (p q_x q_x) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_x) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x x) := Eq.symm (peq0); let pst3 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x x) (p x x))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p q_x q_x) = (p q_H1 (p (p x x) (p x x))) := Eq.trans (pst1) (pst6); let pst8 : q_x = q_H1 := congrArg (fun q => L q) (pst7); let pst9 : q_H1 = q_x := Eq.symm (pst8); let pst10 : q_x = (p (p x x) (p x x)) := congrArg (fun q => R q) (pst7); let pst11 : q_H1 = (p (p x x) (p x x)) := Eq.trans (pst9) (pst10); let pst12 : q_x = (p (p x x) (p x x)) := Eq.trans (pst8) (pst11); let pst13 : (p q_x q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst12); let pst14 : q_x = (p (p x x) (p x x)) := Eq.trans (pst8) (pst11); let pst15 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst14); let pst16 : (p q_x q_x) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst13) (pst15); let pst17 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq2) (pst16); let pst18 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p u0_v0 (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0)))) := Eq.trans (pst18) (peq6); let pst20 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0))) := congrArg (fun q => R q) (pst19); let pst21 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => L q) (pst19); let pst22 : u0_v0 = (p (p x x) (p x x)) := Eq.symm (pst21); let pst23 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) u0_v0) := congrArg (fun q => p q u0_v0) (pst22); let pst24 : (p (p (p x x) (p x x)) u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst22); let pst25 : (p u0_v0 u0_v0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst23) (pst24); let pst26 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => p u0s1out q) (pst25); let pst27 : (p (p u0_x u0_x) (p u0s1out (p u0_v0 u0_v0))) = (p (p u0_x u0_x) (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := congrArg (fun q => p (p u0_x u0_x) q) (pst26); let pst28 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x))))) := Eq.trans (pst20) (pst27); let pst29 : (p x x) = (p u0_x u0_x) := congrArg (fun q => L q) (pst28); let pst30 : x = u0_x := congrArg (fun q => L q) (pst29); let pst31 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst30); let pst32 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst30); let pst33 : (p x x) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : (p u0_x u0_x) = (p x x) := Eq.symm (pst33); let pst35 : (p x x) = (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := congrArg (fun q => R q) (pst28); let pst36 : (p u0_x u0_x) = (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) := Eq.trans (pst34) (pst35); let pst37 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst30); let pst38 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst30); let pst39 : (p x x) = (p u0_x u0_x) := Eq.trans (pst37) (pst38); let pst40 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst39); let pst41 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst30); let pst42 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst30); let pst43 : (p x x) = (p u0_x u0_x) := Eq.trans (pst41) (pst42); let pst44 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst43); let pst45 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst40) (pst44); let pst46 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) := congrArg (fun q => p q (p (p x x) (p x x))) (pst45); let pst47 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst30); let pst48 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst30); let pst49 : (p x x) = (p u0_x u0_x) := Eq.trans (pst47) (pst48); let pst50 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p x x)) := congrArg (fun q => p q (p x x)) (pst49); let pst51 : (p x x) = (p u0_x x) := congrArg (fun q => p q x) (pst30); let pst52 : (p u0_x x) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst30); let pst53 : (p x x) = (p u0_x u0_x) := Eq.trans (pst51) (pst52); let pst54 : (p (p u0_x u0_x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst53); let pst55 : (p (p x x) (p x x)) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst50) (pst54); let pst56 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst55); let pst57 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst46) (pst56); let pst58 : (p u0s1out (p (p (p x x) (p x x)) (p (p x x) (p x x)))) = (p u0s1out (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p u0s1out q) (pst57); let pst59 : (p u0_x u0_x) = (p u0s1out (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst36) (pst58); let pst60 : u0_x = u0s1out := congrArg (fun q => L q) (pst59); let pst61 : u0s1out = u0_x := Eq.symm (pst60); let pst62 : u0_x = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => R q) (pst59); let pst63 : u0s1out = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst61) (pst62); let pst64 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst60); let pst65 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst60); let pst66 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst64) (pst65); let pst67 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0_x u0_x)) := congrArg (fun q => p q (p u0_x u0_x)) (pst66); let pst68 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst60); let pst69 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst60); let pst70 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst68) (pst69); let pst71 : (p (p u0s1out u0s1out) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := congrArg (fun q => p (p u0s1out u0s1out) q) (pst70); let pst72 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := Eq.trans (pst67) (pst71); let pst73 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q (p (p u0_x u0_x) (p u0_x u0_x))) (pst72); let pst74 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst60); let pst75 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst60); let pst76 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst74) (pst75); let pst77 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0_x u0_x)) := congrArg (fun q => p q (p u0_x u0_x)) (pst76); let pst78 : (p u0_x u0_x) = (p u0s1out u0_x) := congrArg (fun q => p q u0_x) (pst60); let pst79 : (p u0s1out u0_x) = (p u0s1out u0s1out) := congrArg (fun q => p u0s1out q) (pst60); let pst80 : (p u0_x u0_x) = (p u0s1out u0s1out) := Eq.trans (pst78) (pst79); let pst81 : (p (p u0s1out u0s1out) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := congrArg (fun q => p (p u0s1out u0s1out) q) (pst80); let pst82 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p (p u0s1out u0s1out) (p u0s1out u0s1out)) := Eq.trans (pst77) (pst81); let pst83 : (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0_x u0_x) (p u0_x u0_x))) = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := congrArg (fun q => p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) q) (pst82); let pst84 : (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := Eq.trans (pst73) (pst83); let pst85 : u0s1out = (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := Eq.trans (pst63) (pst84); pst85)
            have hlt : sz u0s1out < sz (p (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0s1out u0s1out) (sz_lt_p_left (p u0s1out u0s1out) (p u0s1out u0s1out))) (sz_lt_p_left (p (p u0s1out u0s1out) (p u0s1out u0s1out)) (p (p u0s1out u0s1out) (p u0s1out u0s1out)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H1 : CM)
    (s1 : Step H0 v0 H1) :
    ¬ ∃ o, Code v0 (p (p x x) (p H1 (p v0 v0))) o := by
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
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (L (L (R q)))) hb
        change H0 = q_x at e2
        have e3 := congrArg (fun q => (R (L (R q)))) hb
        change v0 = q_x at e3
        have e4 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p (p q_v0 q_v1) q_v0) at e4
        have e5 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e5
        have cyc : x = (p (p x x) q_v1) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq4 : v0 = (p (p q_v0 q_v1) q_v0) := e4; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v0 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v0 := Eq.symm (pst1); let pst3 : (p x x) = (p (p q_v0 q_v1) q_v0) := Eq.trans (pst2) (peq4); let pst4 : (p q_v0 q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst5 : (p (p q_v0 q_v1) q_v0) = (p (p (p x x) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p (p x x) q_v1) q_v0) = (p (p (p x x) q_v1) (p x x)) := congrArg (fun q => p (p (p x x) q_v1) q) (pst0); let pst7 : (p (p q_v0 q_v1) q_v0) = (p (p (p x x) q_v1) (p x x)) := Eq.trans (pst5) (pst6); let pst8 : (p x x) = (p (p (p x x) q_v1) (p x x)) := Eq.trans (pst3) (pst7); let pst9 : x = (p (p x x) q_v1) := congrArg (fun q => L q) (pst8); pst9)
        have hlt : sz x < sz (p (p x x) q_v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        apply code_no_pair_left q_v0 q_v1
        exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (L (L (R q)))) hb
        change H0 = q_x at e2
        have e3 := congrArg (fun q => (R (L (R q)))) hb
        change v0 = q_x at e3
        have e4 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p q_H0 q_v0) at e4
        have e5 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e5
        have cyc : q_H0 = (p q_H0 q_H0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq4 : v0 = (p q_H0 q_v0) := e4; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v0 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v0 := Eq.symm (pst1); let pst3 : (p x x) = (p q_H0 q_v0) := Eq.trans (pst2) (peq4); let pst4 : (p q_H0 q_v0) = (p q_H0 (p x x)) := congrArg (fun q => p q_H0 q) (pst0); let pst5 : (p x x) = (p q_H0 (p x x)) := Eq.trans (pst3) (pst4); let pst6 : x = q_H0 := congrArg (fun q => L q) (pst5); let pst7 : q_H0 = x := Eq.symm (pst6); let pst8 : x = (p x x) := congrArg (fun q => R q) (pst5); let pst9 : q_H0 = (p x x) := Eq.trans (pst7) (pst8); let pst10 : (p x x) = (p q_H0 x) := congrArg (fun q => p q x) (pst6); let pst11 : (p q_H0 x) = (p q_H0 q_H0) := congrArg (fun q => p q_H0 q) (pst6); let pst12 : (p x x) = (p q_H0 q_H0) := Eq.trans (pst10) (pst11); let pst13 : q_H0 = (p q_H0 q_H0) := Eq.trans (pst9) (pst12); pst13)
        have hlt : sz q_H0 < sz (p q_H0 q_H0) := sz_lt_p_left q_H0 q_H0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (L (L (R q)))) hb
        change H0 = q_x at e2
        have e3 := congrArg (fun q => (R (L (R q)))) hb
        change v0 = q_x at e3
        have e4 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = q_H1 at e4
        have e5 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e5
        have cyc : x = (p x x) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq5 : v0 = (p q_v0 q_v0) := e5; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v0 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v0 := Eq.symm (pst1); let pst3 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst2) (peq5); let pst4 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst4) (pst5); let pst7 : (p x x) = (p (p x x) (p x x)) := Eq.trans (pst3) (pst6); let pst8 : x = (p x x) := congrArg (fun q => L q) (pst7); pst8)
        have hlt : sz x < sz (p x x) := sz_lt_p_left x x
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
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p (p q_v0 q_v1) q_v0) at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : x = (p (p x x) q_v1) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq3 : v0 = (p (p q_v0 q_v1) q_v0) := e3; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v0 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v0 := Eq.symm (pst1); let pst3 : (p x x) = (p (p q_v0 q_v1) q_v0) := Eq.trans (pst2) (peq3); let pst4 : (p q_v0 q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst5 : (p (p q_v0 q_v1) q_v0) = (p (p (p x x) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p (p x x) q_v1) q_v0) = (p (p (p x x) q_v1) (p x x)) := congrArg (fun q => p (p (p x x) q_v1) q) (pst0); let pst7 : (p (p q_v0 q_v1) q_v0) = (p (p (p x x) q_v1) (p x x)) := Eq.trans (pst5) (pst6); let pst8 : (p x x) = (p (p (p x x) q_v1) (p x x)) := Eq.trans (pst3) (pst7); let pst9 : x = (p (p x x) q_v1) := congrArg (fun q => L q) (pst8); pst9)
        have hlt : sz x < sz (p (p x x) q_v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        apply code_no_pair_left q_v0 q_v1
        exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = (p q_H0 q_v0) at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : q_H0 = (p q_H0 q_H0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq3 : v0 = (p q_H0 q_v0) := e3; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v0 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v0 := Eq.symm (pst1); let pst3 : (p x x) = (p q_H0 q_v0) := Eq.trans (pst2) (peq3); let pst4 : (p q_H0 q_v0) = (p q_H0 (p x x)) := congrArg (fun q => p q_H0 q) (pst0); let pst5 : (p x x) = (p q_H0 (p x x)) := Eq.trans (pst3) (pst4); let pst6 : x = q_H0 := congrArg (fun q => L q) (pst5); let pst7 : q_H0 = x := Eq.symm (pst6); let pst8 : x = (p x x) := congrArg (fun q => R q) (pst5); let pst9 : q_H0 = (p x x) := Eq.trans (pst7) (pst8); let pst10 : (p x x) = (p q_H0 x) := congrArg (fun q => p q x) (pst6); let pst11 : (p q_H0 x) = (p q_H0 q_H0) := congrArg (fun q => p q_H0 q) (pst6); let pst12 : (p x x) = (p q_H0 q_H0) := Eq.trans (pst10) (pst11); let pst13 : q_H0 = (p q_H0 q_H0) := Eq.trans (pst9) (pst12); pst13)
        have hlt : sz q_H0 < sz (p q_H0 q_H0) := sz_lt_p_left q_H0 q_H0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change H1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => (L (R (R q)))) hb
        change v0 = q_H1 at e3
        have e4 := congrArg (fun q => (R (R (R q)))) hb
        change v0 = (p q_v0 q_v0) at e4
        have cyc : x = (p x x) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : v0 = (p x x) := Eq.trans (peq0) (pst0); let pst2 : (p x x) = v0 := Eq.symm (pst1); let pst3 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst2) (peq4); let pst4 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst4) (pst5); let pst7 : (p x x) = (p (p x x) (p x x)) := Eq.trans (pst3) (pst6); let pst8 : x = (p x x) := congrArg (fun q => L q) (pst7); pst8)
        have hlt : sz x < sz (p x x) := sz_lt_p_left x x
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval x x) (eval (eval (eval v0 v1) v0) (eval v0 v0))))) := by
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
  let H1 := eval (eval v0 v1) v0
  have e1a : (eval v0 v1) = H0 := by
    change H0 = H0
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step H0 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v0 v1) v0
  change x = (eval v0 (eval v0 (eval (eval x x) (eval H1 (eval v0 v0)))))
  have rawEq : (eval v0 (eval v0 (eval (eval x x) (eval H1 (eval v0 v0))))) = (eval v0 (p v0 (p (p x x) (p H1 (p v0 v0))))) := by
    calc
      (eval v0 (eval v0 (eval (eval x x) (eval H1 (eval v0 v0))))) = (eval v0 (eval v0 (eval (p x x) (eval H1 (eval v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval q (eval H1 (eval v0 v0)))))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval v0 (eval (p x x) (eval H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval (p x x) (eval H1 q))))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval v0 (eval (p x x) (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval (p x x) q)))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval v0 (eval v0 (p (p x x) (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 q))) (eval_raw (nr3 x v0 v1 H1 s1))
      _ = (eval v0 (p v0 (p (p x x) (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr4 x v0 v1 H1 s1))
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
