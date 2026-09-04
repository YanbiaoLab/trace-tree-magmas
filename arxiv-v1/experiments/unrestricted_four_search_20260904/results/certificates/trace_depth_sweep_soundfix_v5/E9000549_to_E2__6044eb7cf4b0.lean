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
      (s1 : Step v0 v0 H1) :
      Code v0 (p (p (p x x) H0) (p v0 (p v1 H1))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_x q_H0 ∧ Step q_v0 q_v0 q_H1 ∧ a = q_v0 ∧ b = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (L b)))
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
      change v = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p v k) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p v k) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = (p (p (p q_x q_x) (p (p v k) q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_v0 (p q_v1 (p q_v0 q_v0)))) (pst2); let pst4 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p v k) (p q_v1 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_v1 (p q_v0 q_v0))) (pst0); let pst5 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst6 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst7 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst5) (pst6); let pst8 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p v k) (p v k))) := congrArg (fun q => p q_v1 q) (pst7); let pst9 : (p (p v k) (p q_v1 (p q_v0 q_v0))) = (p (p v k) (p q_v1 (p (p v k) (p v k)))) := congrArg (fun q => p (p v k) q) (pst8); let pst10 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p v k) (p q_v1 (p (p v k) (p v k)))) := Eq.trans (pst4) (pst9); let pst11 : (p (p (p q_x q_x) (p (p v k) q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := congrArg (fun q => p (p (p q_x q_x) (p (p v k) q_x)) q) (pst10); let pst12 : (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := Eq.trans (pst3) (pst11); let pst13 : v = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst12); pst13)
      have hlt : sz v < sz (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_x)) (sz_lt_p_right (p q_x q_x) (p (p v k) q_x))) (sz_lt_p_left (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) at e1
      have cyc : v = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 q_H1))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p v k) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p v k) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) = (p (p (p q_x q_x) (p (p v k) q_x)) (p q_v0 (p q_v1 q_H1))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_H1))) (pst2); let pst4 : (p q_v0 (p q_v1 q_H1)) = (p (p v k) (p q_v1 q_H1)) := congrArg (fun q => p q (p q_v1 q_H1)) (pst0); let pst5 : (p (p (p q_x q_x) (p (p v k) q_x)) (p q_v0 (p q_v1 q_H1))) = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 q_H1))) := congrArg (fun q => p (p (p q_x q_x) (p (p v k) q_x)) q) (pst4); let pst6 : (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 q_H1))) := Eq.trans (pst3) (pst5); let pst7 : v = (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 q_H1))) := Eq.trans (peq1) (pst6); pst7)
      have hlt : sz v < sz (p (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 q_H1))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_x)) (sz_lt_p_right (p q_x q_x) (p (p v k) q_x))) (sz_lt_p_left (p (p q_x q_x) (p (p v k) q_x)) (p (p v k) (p q_v1 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p v k) (p q_v1 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_v1 (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p v k) (p v k))) := congrArg (fun q => p q_v1 q) (pst4); let pst6 : (p (p v k) (p q_v1 (p q_v0 q_v0))) = (p (p v k) (p q_v1 (p (p v k) (p v k)))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p v k) (p q_v1 (p (p v k) (p v k)))) := Eq.trans (pst1) (pst6); let pst8 : (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := congrArg (fun q => p (p (p q_x q_x) q_H0) q) (pst7); let pst9 : v = (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 (p (p v k) (p v k))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_v1 (p (p v k) (p v k))))) (sz_lt_p_right (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) at e1
      have cyc : v = (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 q_H1))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 q_H1)) = (p (p v k) (p q_v1 q_H1)) := congrArg (fun q => p q (p q_v1 q_H1)) (pst0); let pst2 : (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) = (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 q_H1))) := congrArg (fun q => p (p (p q_x q_x) q_H0) q) (pst1); let pst3 : v = (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 q_H1))) := Eq.trans (peq1) (pst2); pst3)
      have hlt : sz v < sz (p (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 q_H1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_v1 q_H1))) (sz_lt_p_right (p (p q_x q_x) q_H0) (p (p v k) (p q_v1 q_H1)))
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
      change x = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right (p q_x q_x) (p q_v0 q_x))) (sz_lt_p_left (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) at e1
      have cyc : q_v0 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right (p q_x q_x) (p q_v0 q_x))) (sz_lt_p_left (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 (p q_v0 q_v0))) (sz_lt_p_right (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) at e1
      have cyc : q_v0 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_H1)) (sz_lt_p_right (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p x x) H0 o := by
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
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e2
        have cyc : x = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := (let peq0 : (p x x) = q_v0 := e0; let peq2 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p x x) (p q_v1 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_v1 (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst2) (pst3); let pst5 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p x x) (p x x))) := congrArg (fun q => p q_v1 q) (pst4); let pst6 : (p (p x x) (p q_v1 (p q_v0 q_v0))) = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := congrArg (fun q => p (p x x) q) (pst5); let pst7 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := Eq.trans (pst1) (pst6); let pst8 : x = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := Eq.trans (peq2) (pst7); pst8)
        have hlt : sz x < sz (p (p x x) (p q_v1 (p (p x x) (p x x)))) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p q_v1 (p (p x x) (p x x))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 (p q_v1 q_H1)) at e2
        have cyc : x = (p (p x x) (p q_v1 q_H1)) := (let peq0 : (p x x) = q_v0 := e0; let peq2 : x = (p q_v0 (p q_v1 q_H1)) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 q_H1)) = (p (p x x) (p q_v1 q_H1)) := congrArg (fun q => p q (p q_v1 q_H1)) (pst0); let pst2 : x = (p (p x x) (p q_v1 q_H1)) := Eq.trans (peq2) (pst1); pst2)
        have hlt : sz x < sz (p (p x x) (p q_v1 q_H1)) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p q_v1 q_H1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p (p q_x q_x) q_H0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e2
        have cyc : x = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := (let peq0 : (p x x) = q_v0 := e0; let peq2 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p x x) (p q_v1 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_v1 (p q_v0 q_v0))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst2) (pst3); let pst5 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p x x) (p x x))) := congrArg (fun q => p q_v1 q) (pst4); let pst6 : (p (p x x) (p q_v1 (p q_v0 q_v0))) = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := congrArg (fun q => p (p x x) q) (pst5); let pst7 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := Eq.trans (pst1) (pst6); let pst8 : x = (p (p x x) (p q_v1 (p (p x x) (p x x)))) := Eq.trans (peq2) (pst7); pst8)
        have hlt : sz x < sz (p (p x x) (p q_v1 (p (p x x) (p x x)))) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p q_v1 (p (p x x) (p x x))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x x) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p (p q_x q_x) q_H0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 (p q_v1 q_H1)) at e2
        have cyc : x = (p (p x x) (p q_v1 q_H1)) := (let peq0 : (p x x) = q_v0 := e0; let peq2 : x = (p q_v0 (p q_v1 q_H1)) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 q_H1)) = (p (p x x) (p q_v1 q_H1)) := congrArg (fun q => p q (p q_v1 q_H1)) (pst0); let pst2 : x = (p (p x x) (p q_v1 q_H1)) := Eq.trans (peq2) (pst1); pst2)
        have hlt : sz x < sz (p (p x x) (p q_v1 q_H1)) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p q_v1 q_H1))
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
        change (p x x) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz x < sz H0 := by
          have structural : sz x < sz (p (p (p q_x q_x) (p (p x x) q_x)) (p (p x x) (p q_v1 (p (p x x) (p x x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) q_x)) (sz_lt_p_right (p q_x q_x) (p (p x x) q_x))) (sz_lt_p_left (p (p q_x q_x) (p (p x x) q_x)) (p (p x x) (p q_v1 (p (p x x) (p x x)))))
          have large_eq : sz x = sz x := congrArg sz (rfl)
          have small_eq : sz H0 = sz (p (p (p q_x q_x) (p (p x x) q_x)) (p (p x x) (p q_v1 (p (p x x) (p x x))))) := congrArg sz (Eq.trans (p1) (Eq.trans (congrArg (fun q => p q (p q_v0 (p q_v1 (p q_v0 q_v0)))) (congrArg (fun q => p (p q_x q_x) q) (congrArg (fun q => p q q_x) (p0.symm)))) (congrArg (fun q => p (p (p q_x q_x) (p (p x x) q_x)) q) (Eq.trans (congrArg (fun q => p q (p q_v1 (p q_v0 q_v0))) (p0.symm)) (congrArg (fun q => p (p x x) q) (congrArg (fun q => p q_v1 q) (Eq.trans (congrArg (fun q => p q q_v0) (p0.symm)) (congrArg (fun q => p (p x x) q) (p0.symm)))))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change (p x x) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx := qs1hB.1
        rw [p0.symm] at hx
        have selflt : sz (p x x) < sz (p x x) := hx
        exact (Nat.lt_irrefl _ selflt).elim
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
        change (p x x) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have badlt : sz x < sz H0 := by
          have structural : sz x < sz (p (p (p q_x q_x) q_H0) (p (p x x) (p q_v1 (p (p x x) (p x x))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p q_v1 (p (p x x) (p x x))))) (sz_lt_p_right (p (p q_x q_x) q_H0) (p (p x x) (p q_v1 (p (p x x) (p x x)))))
          have large_eq : sz x = sz x := congrArg sz (rfl)
          have small_eq : sz H0 = sz (p (p (p q_x q_x) q_H0) (p (p x x) (p q_v1 (p (p x x) (p x x))))) := congrArg sz (Eq.trans (p1) (congrArg (fun q => p (p (p q_x q_x) q_H0) q) (Eq.trans (congrArg (fun q => p q (p q_v1 (p q_v0 q_v0))) (p0.symm)) (congrArg (fun q => p (p x x) q) (congrArg (fun q => p q_v1 q) (Eq.trans (congrArg (fun q => p q q_v0) (p0.symm)) (congrArg (fun q => p (p x x) q) (p0.symm))))))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change (p x x) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H0 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx := qs1hB.1
        rw [p0.symm] at hx
        have selflt : sz (p x x) < sz (p x x) := hx
        exact (Nat.lt_irrefl _ selflt).elim
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step v0 v0 H1) :
    ¬ ∃ o, Code v1 H1 o := by
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
        change v1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e2
        have cyc : q_x = (p (p q_x q_x) (p q_x q_x)) := (let peq1 : v0 = (p (p q_x q_x) (p q_v0 q_x)) := e1; let peq2 : v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e2; let pst0 : (p (p q_x q_x) (p q_v0 q_x)) = v0 := Eq.symm (peq1); let pst1 : (p (p q_x q_x) (p q_v0 q_x)) = (p q_v0 (p q_v1 (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); let pst2 : (p q_x q_x) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_x q_x) := Eq.symm (pst2); let pst4 : (p q_v0 q_x) = (p (p q_x q_x) q_x) := congrArg (fun q => p q q_x) (pst3); let pst5 : (p (p q_x q_x) q_x) = (p q_v0 q_x) := Eq.symm (pst4); let pst6 : (p q_v0 q_x) = (p q_v1 (p q_v0 q_v0)) := congrArg (fun q => R q) (pst1); let pst7 : (p (p q_x q_x) q_x) = (p q_v1 (p q_v0 q_v0)) := Eq.trans (pst5) (pst6); let pst8 : (p q_v0 q_v0) = (p (p q_x q_x) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst9 : (p (p q_x q_x) q_v0) = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst3); let pst10 : (p q_v0 q_v0) = (p (p q_x q_x) (p q_x q_x)) := Eq.trans (pst8) (pst9); let pst11 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p q_x q_x) (p q_x q_x))) := congrArg (fun q => p q_v1 q) (pst10); let pst12 : (p (p q_x q_x) q_x) = (p q_v1 (p (p q_x q_x) (p q_x q_x))) := Eq.trans (pst7) (pst11); let pst13 : q_x = (p (p q_x q_x) (p q_x q_x)) := congrArg (fun q => R q) (pst12); pst13)
        have hlt : sz q_x < sz (p (p q_x q_x) (p q_x q_x)) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) (p q_x q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = (p (p q_x q_x) (p q_v0 q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change v0 = (p q_v0 (p q_v1 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have hx := qs1hB.1
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have epa : q_v0 = (p q_x q_x) := Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (congrArg (fun q => (L q)) (hb))) (congrArg (fun q => (R q)) (hb))))
        have epb : q_x = q_x := rfl
        apply code_no_pair_left q_x q_x
        exact ⟨_, by simpa only [epa, epb] using qs0h⟩
      | hit qs1h =>
        have epa : q_v0 = (p q_x q_x) := Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (congrArg (fun q => (L q)) (hb))) (congrArg (fun q => (R q)) (hb))))
        have epb : q_x = q_x := rfl
        apply code_no_pair_left q_x q_x
        exact ⟨_, by simpa only [epa, epb] using qs0h⟩
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
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx := s1hB.1
        have selflt : sz v0 < sz v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p (p q_x q_x) (p q_v0 q_x)) (p q_v0 (p q_v1 q_H1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx := s1hB.1
        have selflt : sz v0 < sz v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
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
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 (p q_v0 q_v0)))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx := s1hB.1
        have selflt : sz v0 < sz v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v1 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p (p q_x q_x) q_H0) (p q_v0 (p q_v1 q_H1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx := s1hB.1
        have selflt : sz v0 < sz v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step v0 v0 H1) :
    ¬ ∃ o, Code v0 (p v1 H1) o := by
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
        change v1 = (p (p q_x q_x) (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change v0 = (p q_v1 (p q_v0 q_v0)) at e3
        have cyc : q_v0 = (p q_v1 (p q_v0 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p q_v1 (p q_v0 q_v0)) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); pst1)
        have hlt : sz q_v0 < sz (p q_v1 (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_v1 (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = (p (p q_x q_x) (p q_v0 q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change v0 = (p q_v1 q_H1) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have hx := qs1hB.1
        rw [Eq.trans (p2.symm) (p0)] at hx
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p (p q_x q_x) q_H0) at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change v0 = (p q_v1 (p q_v0 q_v0)) at e3
        have cyc : q_v0 = (p q_v1 (p q_v0 q_v0)) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p q_v1 (p q_v0 q_v0)) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); pst1)
        have hlt : sz q_v0 < sz (p q_v1 (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_v1 (p q_v0 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = (p (p q_x q_x) q_H0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change v0 = (p q_v1 q_H1) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have hx := qs1hB.1
        rw [Eq.trans (p2.symm) (p0)] at hx
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
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
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = (p (p q_x q_x) (p q_v0 q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have hx := s1hB.1
        rw [p0] at hx
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
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
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = (p (p q_x q_x) (p q_v0 q_x)) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_v0 (p q_v1 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have hx := s1hB.1
        rw [p0] at hx
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
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
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = (p (p q_x q_x) q_H0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have hx := s1hB.1
        rw [p0] at hx
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
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
        have p1 := congrArg (fun q => (L q)) (hb)
        change v1 = (p (p q_x q_x) q_H0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_v0 (p q_v1 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have hx := s1hB.1
        rw [p0] at hx
        have selflt : sz q_v0 < sz q_v0 := hx
        exact (Nat.lt_irrefl _ selflt).elim
theorem nr4 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 x H0)
    (s1 : Step v0 v0 H1) :
    ¬ ∃ o, Code (p (p x x) H0) (p v0 (p v1 H1)) o := by
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
          change (p (p x x) (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_v1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := (let peq0 : (p (p x x) (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p (p q_x q_x) (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p (p x x) (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p (p x x) (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right (p x x) (p v0 x))) (sz_lt_p_left (p (p x x) (p v0 x)) q_x)) (sz_lt_p_right (p q_x q_x) (p (p (p x x) (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p (p x x) (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_v1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = q_H1 at e4
          have cyc : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := (let peq0 : (p (p x x) (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p (p q_x q_x) (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p (p x x) (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p (p x x) (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right (p x x) (p v0 x))) (sz_lt_p_left (p (p x x) (p v0 x)) q_x)) (sz_lt_p_right (p q_x q_x) (p (p (p x x) (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p (p x x) (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p (p q_x q_x) q_H0) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_v1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : x = (p (p (p x x) (p x x)) q_H0) := (let peq0 : (p (p x x) (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p (p q_x q_x) q_H0) := e1; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : (p (p q_x q_x) q_H0) = v0 := Eq.symm (peq1); let pst1 : (p (p q_x q_x) q_H0) = (p q_v0 q_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p (p x x) (p v0 x)) := Eq.symm (peq0); let pst3 : (p v0 x) = (p (p (p q_x q_x) q_H0) x) := congrArg (fun q => p q x) (peq1); let pst4 : (p (p x x) (p v0 x)) = (p (p x x) (p (p (p q_x q_x) q_H0) x)) := congrArg (fun q => p (p x x) q) (pst3); let pst5 : q_v0 = (p (p x x) (p (p (p q_x q_x) q_H0) x)) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_v0) = (p (p (p x x) (p (p (p q_x q_x) q_H0) x)) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst7 : (p v0 x) = (p (p (p q_x q_x) q_H0) x) := congrArg (fun q => p q x) (peq1); let pst8 : (p (p x x) (p v0 x)) = (p (p x x) (p (p (p q_x q_x) q_H0) x)) := congrArg (fun q => p (p x x) q) (pst7); let pst9 : q_v0 = (p (p x x) (p (p (p q_x q_x) q_H0) x)) := Eq.trans (pst2) (pst8); let pst10 : (p (p (p x x) (p (p (p q_x q_x) q_H0) x)) q_v0) = (p (p (p x x) (p (p (p q_x q_x) q_H0) x)) (p (p x x) (p (p (p q_x q_x) q_H0) x))) := congrArg (fun q => p (p (p x x) (p (p (p q_x q_x) q_H0) x)) q) (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p x x) (p (p (p q_x q_x) q_H0) x)) (p (p x x) (p (p (p q_x q_x) q_H0) x))) := Eq.trans (pst6) (pst10); let pst12 : (p (p q_x q_x) q_H0) = (p (p (p x x) (p (p (p q_x q_x) q_H0) x)) (p (p x x) (p (p (p q_x q_x) q_H0) x))) := Eq.trans (pst1) (pst11); let pst13 : (p q_x q_x) = (p (p x x) (p (p (p q_x q_x) q_H0) x)) := congrArg (fun q => L q) (pst12); let pst14 : q_x = (p x x) := congrArg (fun q => L q) (pst13); let pst15 : (p x x) = q_x := Eq.symm (pst14); let pst16 : q_x = (p (p (p q_x q_x) q_H0) x) := congrArg (fun q => R q) (pst13); let pst17 : (p x x) = (p (p (p q_x q_x) q_H0) x) := Eq.trans (pst15) (pst16); let pst18 : (p q_x q_x) = (p (p x x) q_x) := congrArg (fun q => p q q_x) (pst14); let pst19 : (p (p x x) q_x) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst14); let pst20 : (p q_x q_x) = (p (p x x) (p x x)) := Eq.trans (pst18) (pst19); let pst21 : (p (p q_x q_x) q_H0) = (p (p (p x x) (p x x)) q_H0) := congrArg (fun q => p q q_H0) (pst20); let pst22 : (p (p (p q_x q_x) q_H0) x) = (p (p (p (p x x) (p x x)) q_H0) x) := congrArg (fun q => p q x) (pst21); let pst23 : (p x x) = (p (p (p (p x x) (p x x)) q_H0) x) := Eq.trans (pst17) (pst22); let pst24 : x = (p (p (p x x) (p x x)) q_H0) := congrArg (fun q => L q) (pst23); pst24)
          have hlt : sz x < sz (p (p (p x x) (p x x)) q_H0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p x x))) (sz_lt_p_left (p (p x x) (p x x)) q_H0)
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
          change (p (p x x) (p v0 x)) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (L (R (R q)))) (hb)
          change v0 = q_v1 at p3
          have z3 := congrArg sz p3
          have p4 := congrArg (fun q => (R (R (R q)))) (hb)
          change v0 = q_H1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          have hx := qs1hB.1
          rw [Eq.trans (p0.symm) (congrArg (fun q => p (p x x) q) (congrArg (fun q => p q x) (p1)))] at hx
          have selflt : sz (p (p x x) (p (p (p q_x q_x) q_H0) x)) < sz (p (p x x) (p (p (p q_x q_x) q_H0) x)) := hx
          exact (Nat.lt_irrefl _ selflt).elim
    | hit s1h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p (p x x) (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change H1 = (p q_v1 (p q_v0 q_v0)) at e3
          have cyc : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := (let peq0 : (p (p x x) (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p (p q_x q_x) (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p (p x x) (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p (p x x) (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right (p x x) (p v0 x))) (sz_lt_p_left (p (p x x) (p v0 x)) q_x)) (sz_lt_p_right (p q_x q_x) (p (p (p x x) (p v0 x)) q_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p (p x x) (p v0 x)) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change H1 = (p q_v1 q_H1) at e3
          have cyc : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := (let peq0 : (p (p x x) (p v0 x)) = q_v0 := e0; let peq1 : v0 = (p (p q_x q_x) (p q_v0 q_x)) := e1; let pst0 : q_v0 = (p (p x x) (p v0 x)) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p (p x x) (p v0 x)) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : v0 = (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Eq.trans (peq1) (pst2); pst3)
          have hlt : sz v0 < sz (p (p q_x q_x) (p (p (p x x) (p v0 x)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 x) (sz_lt_p_right (p x x) (p v0 x))) (sz_lt_p_left (p (p x x) (p v0 x)) q_x)) (sz_lt_p_right (p q_x q_x) (p (p (p x x) (p v0 x)) q_x))
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
          change (p (p x x) (p v0 x)) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v1 (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx := s1hB.1
          rw [p1] at hx
          have selflt : sz (p (p q_x q_x) q_H0) < sz (p (p q_x q_x) q_H0) := hx
          exact (Nat.lt_irrefl _ selflt).elim
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
          change (p (p x x) (p v0 x)) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v1 q_H1) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx := s1hB.1
          rw [p1] at hx
          have selflt : sz (p (p q_x q_x) q_H0) < sz (p (p q_x q_x) q_H0) := hx
          exact (Nat.lt_irrefl _ selflt).elim
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
          change (p (p x x) H0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v1 = q_v0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_v1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : x = (p x x) := (let peq0 : (p (p x x) H0) = q_v0 := e0; let peq1 : v0 = (p (p q_x q_x) (p q_v0 q_x)) := e1; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = (p (p x x) H0) := Eq.symm (peq0); let pst1 : (p q_v0 q_x) = (p (p (p x x) H0) q_x) := congrArg (fun q => p q q_x) (pst0); let pst2 : (p (p q_x q_x) (p q_v0 q_x)) = (p (p q_x q_x) (p (p (p x x) H0) q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst1); let pst3 : v0 = (p (p q_x q_x) (p (p (p x x) H0) q_x)) := Eq.trans (peq1) (pst2); let pst4 : (p (p q_x q_x) (p (p (p x x) H0) q_x)) = v0 := Eq.symm (pst3); let pst5 : (p (p q_x q_x) (p (p (p x x) H0) q_x)) = (p q_v0 q_v0) := Eq.trans (pst4) (peq4); let pst6 : (p q_v0 q_v0) = (p (p (p x x) H0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst7 : (p (p (p x x) H0) q_v0) = (p (p (p x x) H0) (p (p x x) H0)) := congrArg (fun q => p (p (p x x) H0) q) (pst0); let pst8 : (p q_v0 q_v0) = (p (p (p x x) H0) (p (p x x) H0)) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_x) (p (p (p x x) H0) q_x)) = (p (p (p x x) H0) (p (p x x) H0)) := Eq.trans (pst5) (pst8); let pst10 : (p q_x q_x) = (p (p x x) H0) := congrArg (fun q => L q) (pst9); let pst11 : q_x = (p x x) := congrArg (fun q => L q) (pst10); let pst12 : (p x x) = q_x := Eq.symm (pst11); let pst13 : q_x = H0 := congrArg (fun q => R q) (pst10); let pst14 : (p x x) = H0 := Eq.trans (pst12) (pst13); let pst15 : H0 = (p x x) := Eq.symm (pst14); let pst16 : (p (p x x) H0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst15); let pst17 : (p (p (p x x) H0) q_x) = (p (p (p x x) (p x x)) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p (p (p x x) (p x x)) q_x) = (p (p (p x x) (p x x)) (p x x)) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst11); let pst19 : (p (p (p x x) H0) q_x) = (p (p (p x x) (p x x)) (p x x)) := Eq.trans (pst17) (pst18); let pst20 : (p (p (p x x) (p x x)) (p x x)) = (p (p (p x x) H0) q_x) := Eq.symm (pst19); let pst21 : (p (p (p x x) H0) q_x) = (p (p x x) H0) := congrArg (fun q => R q) (pst9); let pst22 : (p (p (p x x) (p x x)) (p x x)) = (p (p x x) H0) := Eq.trans (pst20) (pst21); let pst23 : (p (p x x) H0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst15); let pst24 : (p (p (p x x) (p x x)) (p x x)) = (p (p x x) (p x x)) := Eq.trans (pst22) (pst23); let pst25 : (p (p x x) (p x x)) = (p x x) := congrArg (fun q => L q) (pst24); let pst26 : (p x x) = x := congrArg (fun q => L q) (pst25); let pst27 : x = (p x x) := Eq.symm (pst26); pst27)
          have hlt : sz x < sz (p x x) := sz_lt_p_left x x
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
          change (p (p x x) H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (L (R (R q)))) (hb)
          change v0 = q_v1 at p3
          have z3 := congrArg sz p3
          have p4 := congrArg (fun q => (R (R (R q)))) (hb)
          change v0 = q_H1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          have hx := qs1hB.1
          rw [p0.symm] at hx
          have selflt : sz (p (p x x) H0) < sz (p (p x x) H0) := hx
          exact (Nat.lt_irrefl _ selflt).elim
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have epa : q_v0 = (p (p x x) (p x x)) := Eq.trans (Eq.symm (ha)) (congrArg (fun q => p (p x x) q) (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => L q) (congrArg (fun q => L q) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L q)) (hb))) (congrArg (fun q => (R (R (R q)))) (hb))) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.symm (ha))) (congrArg (fun q => p (p (p x x) H0) q) (Eq.symm (ha)))))))) (congrArg (fun q => R q) (congrArg (fun q => L q) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L q)) (hb))) (congrArg (fun q => (R (R (R q)))) (hb))) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.symm (ha))) (congrArg (fun q => p (p (p x x) H0) q) (Eq.symm (ha))))))))))
          have epb : q_x = (p x x) := congrArg (fun q => L q) (congrArg (fun q => L q) (Eq.trans (Eq.trans (Eq.symm (congrArg (fun q => (L q)) (hb))) (congrArg (fun q => (R (R (R q)))) (hb))) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.symm (ha))) (congrArg (fun q => p (p (p x x) H0) q) (Eq.symm (ha))))))
          apply code_no_pair_left (p x x) (p x x)
          exact ⟨_, by simpa only [epa, epb] using qs0h⟩
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
          change (p (p x x) H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (L (R (R q)))) (hb)
          change v0 = q_v1 at p3
          have z3 := congrArg sz p3
          have p4 := congrArg (fun q => (R (R (R q)))) (hb)
          change v0 = q_H1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          have hx := qs1hB.1
          rw [p0.symm] at hx
          have selflt : sz (p (p x x) H0) < sz (p (p x x) H0) := hx
          exact (Nat.lt_irrefl _ selflt).elim
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
          change (p (p x x) H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v1 (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx := s1hB.1
          rw [Eq.trans (p1) (congrArg (fun q => p (p q_x q_x) q) (congrArg (fun q => p q q_x) (p0.symm)))] at hx
          have selflt : sz (p (p q_x q_x) (p (p (p x x) H0) q_x)) < sz (p (p q_x q_x) (p (p (p x x) H0) q_x)) := hx
          exact (Nat.lt_irrefl _ selflt).elim
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
          change (p (p x x) H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) (p q_v0 q_x)) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v1 q_H1) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx := s1hB.1
          rw [Eq.trans (p1) (congrArg (fun q => p (p q_x q_x) q) (congrArg (fun q => p q q_x) (p0.symm)))] at hx
          have selflt : sz (p (p q_x q_x) (p (p (p x x) H0) q_x)) < sz (p (p q_x q_x) (p (p (p x x) H0) q_x)) := hx
          exact (Nat.lt_irrefl _ selflt).elim
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
          change (p (p x x) H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v1 (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx := s1hB.1
          rw [p1] at hx
          have selflt : sz (p (p q_x q_x) q_H0) < sz (p (p q_x q_x) q_H0) := hx
          exact (Nat.lt_irrefl _ selflt).elim
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
          change (p (p x x) H0) = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (L q)) (hb)
          change v0 = (p (p q_x q_x) q_H0) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v1 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change H1 = (p q_v1 q_H1) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx := s1hB.1
          rw [p1] at hx
          have selflt : sz (p (p q_x q_x) q_H0) < sz (p (p q_x q_x) q_H0) := hx
          exact (Nat.lt_irrefl _ selflt).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval (eval (eval x x) (eval v0 x)) (eval v0 (eval v1 (eval v0 v0))))) := by
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
  let H1 := eval v0 v0
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step v0 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 v0
  change x = (eval v0 (eval (eval (eval x x) H0) (eval v0 (eval v1 H1))))
  have rawEq : (eval v0 (eval (eval (eval x x) H0) (eval v0 (eval v1 H1)))) = (eval v0 (p (p (p x x) H0) (p v0 (p v1 H1)))) := by
    calc
      (eval v0 (eval (eval (eval x x) H0) (eval v0 (eval v1 H1)))) = (eval v0 (eval (eval (p x x) H0) (eval v0 (eval v1 H1)))) := congrArg (fun q => (eval v0 (eval (eval q H0) (eval v0 (eval v1 H1))))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval (p (p x x) H0) (eval v0 (eval v1 H1)))) := congrArg (fun q => (eval v0 (eval q (eval v0 (eval v1 H1))))) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval v0 (eval (p (p x x) H0) (eval v0 (p v1 H1)))) := congrArg (fun q => (eval v0 (eval (p (p x x) H0) (eval v0 q)))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval v0 (eval (p (p x x) H0) (p v0 (p v1 H1)))) := congrArg (fun q => (eval v0 (eval (p (p x x) H0) q))) (eval_raw (nr3 x v0 v1 H1 s1))
      _ = (eval v0 (p (p (p x x) H0) (p v0 (p v1 H1)))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr4 x v0 v1 H0 H1 s0 s1))
  exact (eval_hit (Code.law x v0 v1 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op a b := eval b a
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro q0 q1 q2
    exact CM.source_holds q0 q1 q2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
