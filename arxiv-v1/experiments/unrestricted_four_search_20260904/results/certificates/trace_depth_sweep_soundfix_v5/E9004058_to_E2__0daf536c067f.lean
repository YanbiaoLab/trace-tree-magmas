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
  | law (x v0 v1 H0 H1 H2 : CM)
      (s0 : Step v0 v1 H0)
      (s1 : Step H0 v0 H1)
      (s2 : Step x v0 H2) :
      Code v0 (p v0 (p x (p H1 (p v0 H2)))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 q_H2 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_H0 q_v0 q_H1 ∧ Step q_x q_v0 q_H2 ∧ a = q_v0 ∧ b = (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 H2 s0 s1 s2 => ⟨x, v0, v1, H0, H1, H2, s0, s1, s2, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R b))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, s0, s1, s2, ha, hb, ho⟩
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) at e1
        have cyc : v = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) := congrArg (fun q => p q (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) (pst0); let pst2 : (p q_v0 q_v1) = (p (p v k) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst3 : (p (p q_v0 q_v1) q_v0) = (p (p (p v k) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p (p v k) q_v1) q_v0) = (p (p (p v k) q_v1) (p v k)) := congrArg (fun q => p (p (p v k) q_v1) q) (pst0); let pst5 : (p (p q_v0 q_v1) q_v0) = (p (p (p v k) q_v1) (p v k)) := Eq.trans (pst3) (pst4); let pst6 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))) = (p (p (p (p v k) q_v1) (p v k)) (p q_v0 (p q_x q_v0))) := congrArg (fun q => p q (p q_v0 (p q_x q_v0))) (pst5); let pst7 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x q_v0)) := congrArg (fun q => p q (p q_x q_v0)) (pst0); let pst8 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst9 : (p (p v k) (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := congrArg (fun q => p (p v k) q) (pst8); let pst10 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := Eq.trans (pst7) (pst9); let pst11 : (p (p (p (p v k) q_v1) (p v k)) (p q_v0 (p q_x q_v0))) = (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))) := congrArg (fun q => p (p (p (p v k) q_v1) (p v k)) q) (pst10); let pst12 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))) = (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))) := Eq.trans (pst6) (pst11); let pst13 : (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) = (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k))))) := congrArg (fun q => p q_x q) (pst12); let pst14 : (p (p v k) (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))))) := congrArg (fun q => p (p v k) q) (pst13); let pst15 : (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))))) := Eq.trans (pst1) (pst14); let pst16 : v = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))))) := Eq.trans (peq1) (pst15); pst16)
        have hlt : sz v < sz (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k)))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) (p q_x (p v k))))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) at e1
        have cyc : v = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) = (p (p v k) (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) := congrArg (fun q => p q (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) (pst0); let pst2 : (p q_v0 q_v1) = (p (p v k) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst3 : (p (p q_v0 q_v1) q_v0) = (p (p (p v k) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p (p v k) q_v1) q_v0) = (p (p (p v k) q_v1) (p v k)) := congrArg (fun q => p (p (p v k) q_v1) q) (pst0); let pst5 : (p (p q_v0 q_v1) q_v0) = (p (p (p v k) q_v1) (p v k)) := Eq.trans (pst3) (pst4); let pst6 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)) = (p (p (p (p v k) q_v1) (p v k)) (p q_v0 q_H2)) := congrArg (fun q => p q (p q_v0 q_H2)) (pst5); let pst7 : (p q_v0 q_H2) = (p (p v k) q_H2) := congrArg (fun q => p q q_H2) (pst0); let pst8 : (p (p (p (p v k) q_v1) (p v k)) (p q_v0 q_H2)) = (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)) := congrArg (fun q => p (p (p (p v k) q_v1) (p v k)) q) (pst7); let pst9 : (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)) = (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)) := Eq.trans (pst6) (pst8); let pst10 : (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) = (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2))) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p (p v k) (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)))) := congrArg (fun q => p (p v k) q) (pst10); let pst12 : (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)))) := Eq.trans (pst1) (pst11); let pst13 : v = (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)))) := Eq.trans (peq1) (pst12); pst13)
        have hlt : sz v < sz (p (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2)))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p (p (p v k) q_v1) (p v k)) (p (p v k) q_H2))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) at e1
        have cyc : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := congrArg (fun q => p q (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) (pst0); let pst2 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x q_v0)) := congrArg (fun q => p q (p q_x q_v0)) (pst0); let pst3 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst4 : (p (p v k) (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := congrArg (fun q => p (p v k) q) (pst3); let pst5 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := Eq.trans (pst2) (pst4); let pst6 : (p q_H1 (p q_v0 (p q_x q_v0))) = (p q_H1 (p (p v k) (p q_x (p v k)))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) = (p q_x (p q_H1 (p (p v k) (p q_x (p v k))))) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p (p v k) (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := Eq.trans (peq1) (pst9); pst10)
        have hlt : sz v < sz (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k))))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) at e1
        have cyc : v = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) = (p (p v k) (p q_x (p q_H1 (p q_v0 q_H2)))) := congrArg (fun q => p q (p q_x (p q_H1 (p q_v0 q_H2)))) (pst0); let pst2 : (p q_v0 q_H2) = (p (p v k) q_H2) := congrArg (fun q => p q q_H2) (pst0); let pst3 : (p q_H1 (p q_v0 q_H2)) = (p q_H1 (p (p v k) q_H2)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p q_x (p q_H1 (p q_v0 q_H2))) = (p q_x (p q_H1 (p (p v k) q_H2))) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p v k) (p q_x (p q_H1 (p q_v0 q_H2)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := congrArg (fun q => p (p v k) q) (pst4); let pst6 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := Eq.trans (pst1) (pst5); let pst7 : v = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := Eq.trans (peq1) (pst6); pst7)
        have hlt : sz v < sz (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p q_H1 (p (p v k) q_H2))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) at e1
        have cyc : v = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) := congrArg (fun q => p q (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) (pst0); let pst2 : (p q_H0 q_v0) = (p q_H0 (p v k)) := congrArg (fun q => p q_H0 q) (pst0); let pst3 : (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))) = (p (p q_H0 (p v k)) (p q_v0 (p q_x q_v0))) := congrArg (fun q => p q (p q_v0 (p q_x q_v0))) (pst2); let pst4 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x q_v0)) := congrArg (fun q => p q (p q_x q_v0)) (pst0); let pst5 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst6 : (p (p v k) (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := congrArg (fun q => p (p v k) q) (pst5); let pst7 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := Eq.trans (pst4) (pst6); let pst8 : (p (p q_H0 (p v k)) (p q_v0 (p q_x q_v0))) = (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))) := congrArg (fun q => p (p q_H0 (p v k)) q) (pst7); let pst9 : (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))) = (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))) := Eq.trans (pst3) (pst8); let pst10 : (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) = (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k))))) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p (p v k) (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))))) := congrArg (fun q => p (p v k) q) (pst10); let pst12 : (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))))) := Eq.trans (pst1) (pst11); let pst13 : v = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))))) := Eq.trans (peq1) (pst12); pst13)
        have hlt : sz v < sz (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k)))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) (p q_x (p v k))))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) at e1
        have cyc : v = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2)))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) = (p (p v k) (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) := congrArg (fun q => p q (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) (pst0); let pst2 : (p q_H0 q_v0) = (p q_H0 (p v k)) := congrArg (fun q => p q_H0 q) (pst0); let pst3 : (p (p q_H0 q_v0) (p q_v0 q_H2)) = (p (p q_H0 (p v k)) (p q_v0 q_H2)) := congrArg (fun q => p q (p q_v0 q_H2)) (pst2); let pst4 : (p q_v0 q_H2) = (p (p v k) q_H2) := congrArg (fun q => p q q_H2) (pst0); let pst5 : (p (p q_H0 (p v k)) (p q_v0 q_H2)) = (p (p q_H0 (p v k)) (p (p v k) q_H2)) := congrArg (fun q => p (p q_H0 (p v k)) q) (pst4); let pst6 : (p (p q_H0 q_v0) (p q_v0 q_H2)) = (p (p q_H0 (p v k)) (p (p v k) q_H2)) := Eq.trans (pst3) (pst5); let pst7 : (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2))) = (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2))) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p (p v k) (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2)))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2)))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2)))) := Eq.trans (peq1) (pst9); pst10)
        have hlt : sz v < sz (p (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2)))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p (p q_H0 (p v k)) (p (p v k) q_H2))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) at e1
        have cyc : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := congrArg (fun q => p q (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) (pst0); let pst2 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x q_v0)) := congrArg (fun q => p q (p q_x q_v0)) (pst0); let pst3 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst4 : (p (p v k) (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := congrArg (fun q => p (p v k) q) (pst3); let pst5 : (p q_v0 (p q_x q_v0)) = (p (p v k) (p q_x (p v k))) := Eq.trans (pst2) (pst4); let pst6 : (p q_H1 (p q_v0 (p q_x q_v0))) = (p q_H1 (p (p v k) (p q_x (p v k)))) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) = (p q_x (p q_H1 (p (p v k) (p q_x (p v k))))) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p (p v k) (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := Eq.trans (peq1) (pst9); pst10)
        have hlt : sz v < sz (p (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k)))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p q_H1 (p (p v k) (p q_x (p v k))))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have e0 := congrArg (fun q => q) ha
        change (p v k) = q_v0 at e0
        have e1 := congrArg (fun q => q) hb
        change v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) at e1
        have cyc : v = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) = (p (p v k) (p q_x (p q_H1 (p q_v0 q_H2)))) := congrArg (fun q => p q (p q_x (p q_H1 (p q_v0 q_H2)))) (pst0); let pst2 : (p q_v0 q_H2) = (p (p v k) q_H2) := congrArg (fun q => p q q_H2) (pst0); let pst3 : (p q_H1 (p q_v0 q_H2)) = (p q_H1 (p (p v k) q_H2)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p q_x (p q_H1 (p q_v0 q_H2))) = (p q_x (p q_H1 (p (p v k) q_H2))) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p v k) (p q_x (p q_H1 (p q_v0 q_H2)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := congrArg (fun q => p (p v k) q) (pst4); let pst6 : (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := Eq.trans (pst1) (pst5); let pst7 : v = (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := Eq.trans (peq1) (pst6); pst7)
        have hlt : sz v < sz (p (p v k) (p q_x (p q_H1 (p (p v k) q_H2)))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_x (p q_H1 (p (p v k) q_H2))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H2 : CM)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code v0 H2 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s2B := step_bound s2
  cases s2 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) at e2
          have cyc : q_v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))) (sz_lt_p_right q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) at e2
          have cyc : q_v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2))) (sz_lt_p_right q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          apply code_no_pair_left q_v0 q_v1
          exact ⟨_, qs1h⟩
        | hit qs2h =>
          apply code_no_pair_left q_v0 q_v1
          exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) at e2
          have cyc : q_v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))) (sz_lt_p_right q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2))) at e2
          have cyc : q_v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2))) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p q_v0 q_H2))) (sz_lt_p_right q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v0 = (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) at e2
          have cyc : q_v0 = (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p q_x (p q_H1 (p q_v0 (p q_x q_v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_x q_v0)) (sz_lt_p_right q_H1 (p q_v0 (p q_x q_v0)))) (sz_lt_p_right q_x (p q_H1 (p q_v0 (p q_x q_v0))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs2h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) hb
          change v0 = (p q_x (p q_H1 (p q_v0 q_H2))) at e2
          have cyc : q_v0 = (p q_x (p q_H1 (p q_v0 q_H2))) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_x (p q_H1 (p q_v0 q_H2))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_H1 (p q_v0 q_H2))) := Eq.trans (pst0) (peq2); pst1)
          have hlt : sz q_v0 < sz (p q_x (p q_H1 (p q_v0 q_H2))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H2) (sz_lt_p_right q_H1 (p q_v0 q_H2))) (sz_lt_p_right q_x (p q_H1 (p q_v0 q_H2)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s2h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change v0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change H2 = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have hx : sz q_v0 < sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) := by
            have q := hcB.1
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) := congrArg sz (p1)
            have q1 : sz q_v0 < sz H2 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) < sz q_v0 := by
            have q := s2hB.2
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) := congrArg sz (p1)
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have q1 : sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))))) < sz v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change v0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change H2 = (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have hx : sz q_v0 < sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) := by
            have q := hcB.1
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) := congrArg sz (p1)
            have q1 : sz q_v0 < sz H2 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) < sz q_v0 := by
            have q := s2hB.2
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) := congrArg sz (p1)
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have q1 : sz (p q_v0 (p q_x (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)))) < sz v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          apply code_no_pair_left q_v0 q_v1
          exact ⟨_, qs1h⟩
        | hit qs2h =>
          apply code_no_pair_left q_v0 q_v1
          exact ⟨_, qs1h⟩
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change v0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change H2 = (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have hx : sz q_v0 < sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) := by
            have q := hcB.1
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) := congrArg sz (p1)
            have q1 : sz q_v0 < sz H2 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) < sz q_v0 := by
            have q := s2hB.2
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) := congrArg sz (p1)
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have q1 : sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))))) < sz v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change v0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change H2 = (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have hx : sz q_v0 < sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) := by
            have q := hcB.1
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) := congrArg sz (p1)
            have q1 : sz q_v0 < sz H2 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) < sz q_v0 := by
            have q := s2hB.2
            have ev : sz H2 = sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) := congrArg sz (p1)
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have q1 : sz (p q_v0 (p q_x (p (p q_H0 q_v0) (p q_v0 q_H2)))) < sz v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change v0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change H2 = (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have hx : sz q_v0 < sz (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := by
            have q := hcB.1
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have ev : sz H2 = sz (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := congrArg sz (p1)
            have q1 : sz q_v0 < sz H2 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) < sz q_v0 := by
            have q := s2hB.2
            have ev : sz H2 = sz (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) := congrArg sz (p1)
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have q1 : sz (p q_v0 (p q_x (p q_H1 (p q_v0 (p q_x q_v0))))) < sz v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have hcB := code_bounds hc
          have s2hB := code_bounds s2h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have qs2hB := code_bounds qs2h
          have s2B := s2B
          have qs0B := qs0B
          have qs1B := qs1B
          have qs2B := qs2B
          have p0 := ha
          change v0 = q_v0 at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change H2 = (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          have hx : sz q_v0 < sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) := by
            have q := hcB.1
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have ev : sz H2 = sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) := congrArg sz (p1)
            have q1 : sz q_v0 < sz H2 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) < sz q_v0 := by
            have q := s2hB.2
            have ev : sz H2 = sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) := congrArg sz (p1)
            have eu : sz v0 = sz q_v0 := congrArg sz (p0)
            have q1 : sz (p q_v0 (p q_x (p q_H1 (p q_v0 q_H2)))) < sz v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x v0 v1 H1 H2 : CM)
    (s1 : Step H0 v0 H1)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code H1 (p v0 H2) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have he : H1 = v0 := (let peq0 : H1 = q_v0 := ha; let peq1 : v0 = q_v0 := congrArg (fun q => (L q)) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : H1 = v0 := Eq.trans (peq0) (pst0); pst1)
  exact step_ne_second (by simpa only [he] using s1)
theorem nr2 (x v0 v1 H1 H2 : CM)
    (s1 : Step H0 v0 H1)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code x (p H1 (p v0 H2)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have s2B := step_bound s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change x = q_v0 at e0
            have e1 := congrArg (fun q => (L q)) hb
            change (p H0 v0) = q_v0 at e1
            have e2 := congrArg (fun q => (L (R q))) hb
            change v0 = q_x at e2
            have e3 := congrArg (fun q => (L (R (R q)))) hb
            change x = (p (p q_v0 q_v1) q_v0) at e3
            have e4 := congrArg (fun q => (R (R (R q)))) hb
            change v0 = (p q_v0 (p q_x q_v0)) at e4
            have cyc : H0 = (p (p H0 q_x) q_v1) := (let peq0 : x = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = q_x := e2; let peq3 : x = (p (p q_v0 q_v1) q_v0) := e3; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq1); let pst1 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst2 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst1); let pst3 : x = (p H0 q_x) := Eq.trans (peq0) (pst2); let pst4 : (p H0 q_x) = x := Eq.symm (pst3); let pst5 : (p H0 q_x) = (p (p q_v0 q_v1) q_v0) := Eq.trans (pst4) (peq3); let pst6 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst7 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v0 q_v1) = (p (p H0 q_x) q_v1) := congrArg (fun q => p q q_v1) (pst7); let pst9 : (p (p q_v0 q_v1) q_v0) = (p (p (p H0 q_x) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst8); let pst10 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst11 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst10); let pst12 : (p (p (p H0 q_x) q_v1) q_v0) = (p (p (p H0 q_x) q_v1) (p H0 q_x)) := congrArg (fun q => p (p (p H0 q_x) q_v1) q) (pst11); let pst13 : (p (p q_v0 q_v1) q_v0) = (p (p (p H0 q_x) q_v1) (p H0 q_x)) := Eq.trans (pst9) (pst12); let pst14 : (p H0 q_x) = (p (p (p H0 q_x) q_v1) (p H0 q_x)) := Eq.trans (pst5) (pst13); let pst15 : H0 = (p (p H0 q_x) q_v1) := congrArg (fun q => L q) (pst14); pst15)
            have hlt : sz H0 < sz (p (p H0 q_x) q_v1) := Nat.lt_trans (sz_lt_p_left H0 q_x) (sz_lt_p_left (p H0 q_x) q_v1)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => q) ha
            change x = q_v0 at e0
            have e1 := congrArg (fun q => (L q)) hb
            change (p H0 v0) = q_v0 at e1
            have e2 := congrArg (fun q => (L (R q))) hb
            change v0 = q_x at e2
            have e3 := congrArg (fun q => (L (R (R q)))) hb
            change x = (p (p q_v0 q_v1) q_v0) at e3
            have e4 := congrArg (fun q => (R (R (R q)))) hb
            change v0 = (p q_v0 q_H2) at e4
            have cyc : H0 = (p (p H0 q_x) q_v1) := (let peq0 : x = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = q_x := e2; let peq3 : x = (p (p q_v0 q_v1) q_v0) := e3; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq1); let pst1 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst2 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst1); let pst3 : x = (p H0 q_x) := Eq.trans (peq0) (pst2); let pst4 : (p H0 q_x) = x := Eq.symm (pst3); let pst5 : (p H0 q_x) = (p (p q_v0 q_v1) q_v0) := Eq.trans (pst4) (peq3); let pst6 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst7 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst6); let pst8 : (p q_v0 q_v1) = (p (p H0 q_x) q_v1) := congrArg (fun q => p q q_v1) (pst7); let pst9 : (p (p q_v0 q_v1) q_v0) = (p (p (p H0 q_x) q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst8); let pst10 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst11 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst10); let pst12 : (p (p (p H0 q_x) q_v1) q_v0) = (p (p (p H0 q_x) q_v1) (p H0 q_x)) := congrArg (fun q => p (p (p H0 q_x) q_v1) q) (pst11); let pst13 : (p (p q_v0 q_v1) q_v0) = (p (p (p H0 q_x) q_v1) (p H0 q_x)) := Eq.trans (pst9) (pst12); let pst14 : (p H0 q_x) = (p (p (p H0 q_x) q_v1) (p H0 q_x)) := Eq.trans (pst5) (pst13); let pst15 : H0 = (p (p H0 q_x) q_v1) := congrArg (fun q => L q) (pst14); pst15)
            have hlt : sz H0 < sz (p (p H0 q_x) q_v1) := Nat.lt_trans (sz_lt_p_left H0 q_x) (sz_lt_p_left (p H0 q_x) q_v1)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            apply code_no_pair_left q_v0 q_v1
            exact ⟨_, qs1h⟩
          | hit qs2h =>
            apply code_no_pair_left q_v0 q_v1
            exact ⟨_, qs1h⟩
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change x = q_v0 at e0
            have e1 := congrArg (fun q => (L q)) hb
            change (p H0 v0) = q_v0 at e1
            have e2 := congrArg (fun q => (L (R q))) hb
            change v0 = q_x at e2
            have e3 := congrArg (fun q => (L (R (R q)))) hb
            change x = (p q_H0 q_v0) at e3
            have e4 := congrArg (fun q => (R (R (R q)))) hb
            change v0 = (p q_v0 (p q_x q_v0)) at e4
            have cyc : q_x = (p q_H0 q_x) := (let peq0 : x = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = q_x := e2; let peq3 : x = (p q_H0 q_v0) := e3; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq1); let pst1 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst2 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst1); let pst3 : x = (p H0 q_x) := Eq.trans (peq0) (pst2); let pst4 : (p H0 q_x) = x := Eq.symm (pst3); let pst5 : (p H0 q_x) = (p q_H0 q_v0) := Eq.trans (pst4) (peq3); let pst6 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst7 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst6); let pst8 : (p q_H0 q_v0) = (p q_H0 (p H0 q_x)) := congrArg (fun q => p q_H0 q) (pst7); let pst9 : (p H0 q_x) = (p q_H0 (p H0 q_x)) := Eq.trans (pst5) (pst8); let pst10 : q_x = (p H0 q_x) := congrArg (fun q => R q) (pst9); let pst11 : H0 = q_H0 := congrArg (fun q => L q) (pst9); let pst12 : (p H0 q_x) = (p q_H0 q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p q_H0 q_x) := Eq.trans (pst10) (pst12); pst13)
            have hlt : sz q_x < sz (p q_H0 q_x) := sz_lt_p_right q_H0 q_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => q) ha
            change x = q_v0 at e0
            have e1 := congrArg (fun q => (L q)) hb
            change (p H0 v0) = q_v0 at e1
            have e2 := congrArg (fun q => (L (R q))) hb
            change v0 = q_x at e2
            have e3 := congrArg (fun q => (L (R (R q)))) hb
            change x = (p q_H0 q_v0) at e3
            have e4 := congrArg (fun q => (R (R (R q)))) hb
            change v0 = (p q_v0 q_H2) at e4
            have cyc : q_x = (p q_H0 q_x) := (let peq0 : x = q_v0 := e0; let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = q_x := e2; let peq3 : x = (p q_H0 q_v0) := e3; let pst0 : q_v0 = (p H0 v0) := Eq.symm (peq1); let pst1 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst2 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst1); let pst3 : x = (p H0 q_x) := Eq.trans (peq0) (pst2); let pst4 : (p H0 q_x) = x := Eq.symm (pst3); let pst5 : (p H0 q_x) = (p q_H0 q_v0) := Eq.trans (pst4) (peq3); let pst6 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst7 : q_v0 = (p H0 q_x) := Eq.trans (pst0) (pst6); let pst8 : (p q_H0 q_v0) = (p q_H0 (p H0 q_x)) := congrArg (fun q => p q_H0 q) (pst7); let pst9 : (p H0 q_x) = (p q_H0 (p H0 q_x)) := Eq.trans (pst5) (pst8); let pst10 : q_x = (p H0 q_x) := congrArg (fun q => R q) (pst9); let pst11 : H0 = q_H0 := congrArg (fun q => L q) (pst9); let pst12 : (p H0 q_x) = (p q_H0 q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p q_H0 q_x) := Eq.trans (pst10) (pst12); pst13)
            have hlt : sz q_x < sz (p q_H0 q_x) := sz_lt_p_right q_H0 q_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change x = q_v0 at e0
            have e1 := congrArg (fun q => (L q)) hb
            change (p H0 v0) = q_v0 at e1
            have e2 := congrArg (fun q => (L (R q))) hb
            change v0 = q_x at e2
            have e3 := congrArg (fun q => (L (R (R q)))) hb
            change x = q_H1 at e3
            have e4 := congrArg (fun q => (R (R (R q)))) hb
            change v0 = (p q_v0 (p q_x q_v0)) at e4
            have cyc : q_x = (p (p H0 q_x) (p q_x (p H0 q_x))) := (let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = q_x := e2; let peq4 : v0 = (p q_v0 (p q_x q_v0)) := e4; let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = (p q_v0 (p q_x q_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p H0 v0) := Eq.symm (peq1); let pst3 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst4 : q_v0 = (p H0 q_x) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 (p q_x q_v0)) = (p (p H0 q_x) (p q_x q_v0)) := congrArg (fun q => p q (p q_x q_v0)) (pst4); let pst6 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst7 : q_v0 = (p H0 q_x) := Eq.trans (pst2) (pst6); let pst8 : (p q_x q_v0) = (p q_x (p H0 q_x)) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p (p H0 q_x) (p q_x q_v0)) = (p (p H0 q_x) (p q_x (p H0 q_x))) := congrArg (fun q => p (p H0 q_x) q) (pst8); let pst10 : (p q_v0 (p q_x q_v0)) = (p (p H0 q_x) (p q_x (p H0 q_x))) := Eq.trans (pst5) (pst9); let pst11 : q_x = (p (p H0 q_x) (p q_x (p H0 q_x))) := Eq.trans (pst1) (pst10); pst11)
            have hlt : sz q_x < sz (p (p H0 q_x) (p q_x (p H0 q_x))) := Nat.lt_trans (sz_lt_p_right H0 q_x) (sz_lt_p_left (p H0 q_x) (p q_x (p H0 q_x)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs2h =>
            have e0 := congrArg (fun q => q) ha
            change x = q_v0 at e0
            have e1 := congrArg (fun q => (L q)) hb
            change (p H0 v0) = q_v0 at e1
            have e2 := congrArg (fun q => (L (R q))) hb
            change v0 = q_x at e2
            have e3 := congrArg (fun q => (L (R (R q)))) hb
            change x = q_H1 at e3
            have e4 := congrArg (fun q => (R (R (R q)))) hb
            change v0 = (p q_v0 q_H2) at e4
            have cyc : q_x = (p (p H0 q_x) q_H2) := (let peq1 : (p H0 v0) = q_v0 := e1; let peq2 : v0 = q_x := e2; let peq4 : v0 = (p q_v0 q_H2) := e4; let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = (p q_v0 q_H2) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p H0 v0) := Eq.symm (peq1); let pst3 : (p H0 v0) = (p H0 q_x) := congrArg (fun q => p H0 q) (peq2); let pst4 : q_v0 = (p H0 q_x) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 q_H2) = (p (p H0 q_x) q_H2) := congrArg (fun q => p q q_H2) (pst4); let pst6 : q_x = (p (p H0 q_x) q_H2) := Eq.trans (pst1) (pst5); pst6)
            have hlt : sz q_x < sz (p (p H0 q_x) q_H2) := Nat.lt_trans (sz_lt_p_right H0 q_x) (sz_lt_p_left (p H0 q_x) q_H2)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s2h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p H0 v0) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have badlt : sz v0 < sz x := by
              have structural : sz q_x < sz (p H0 q_x) := sz_lt_p_right H0 q_x
              have large_eq : sz v0 = sz q_x := congrArg sz (p2)
              have small_eq : sz x = sz (p H0 q_x) := congrArg sz (Eq.trans (p0) (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2))))
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p H0 v0) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have hx : sz (p H0 q_x) < sz q_x := by
              have q := s2hB.1
              have eu : sz x = sz (p H0 q_x) := congrArg sz (Eq.trans (p0) (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2))))
              have ev : sz v0 = sz q_x := congrArg sz (p2)
              have q1 : sz (p H0 q_x) < sz v0 := lt_of_eq_of_lt eu.symm q
              exact lt_of_lt_of_eq q1 ev
            have hy : sz q_x < sz (p H0 q_x) := by
              have q := qs2hB.1
              have ev : sz q_x = sz q_x := congrArg sz (rfl)
              have eu : sz q_v0 = sz (p H0 q_x) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2)))
              have q1 : sz q_x < sz q_v0 := lt_of_eq_of_lt ev.symm q
              exact lt_of_lt_of_eq q1 eu
            exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs1h =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            apply code_no_pair_left q_v0 q_v1
            exact ⟨_, qs1h⟩
          | hit qs2h =>
            apply code_no_pair_left q_v0 q_v1
            exact ⟨_, qs1h⟩
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p H0 v0) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have badlt : sz v0 < sz x := by
              have structural : sz q_x < sz (p H0 q_x) := sz_lt_p_right H0 q_x
              have large_eq : sz v0 = sz q_x := congrArg sz (p2)
              have small_eq : sz x = sz (p H0 q_x) := congrArg sz (Eq.trans (p0) (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2))))
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p H0 v0) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p q_H0 q_v0) (p q_v0 q_H2)) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have hx : sz (p H0 q_x) < sz q_x := by
              have q := s2hB.1
              have eu : sz x = sz (p H0 q_x) := congrArg sz (Eq.trans (p0) (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2))))
              have ev : sz v0 = sz q_x := congrArg sz (p2)
              have q1 : sz (p H0 q_x) < sz v0 := lt_of_eq_of_lt eu.symm q
              exact lt_of_lt_of_eq q1 ev
            have hy : sz q_x < sz (p H0 q_x) := by
              have q := qs2hB.1
              have ev : sz q_x = sz q_x := congrArg sz (rfl)
              have eu : sz q_v0 = sz (p H0 q_x) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2)))
              have q1 : sz q_x < sz q_v0 := lt_of_eq_of_lt ev.symm q
              exact lt_of_lt_of_eq q1 eu
            exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs1h =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p H0 v0) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p q_H1 (p q_v0 (p q_x q_v0))) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have badlt : sz v0 < sz x := by
              have structural : sz q_x < sz (p H0 q_x) := sz_lt_p_right H0 q_x
              have large_eq : sz v0 = sz q_x := congrArg sz (p2)
              have small_eq : sz x = sz (p H0 q_x) := congrArg sz (Eq.trans (p0) (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2))))
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.1).elim
          | hit qs2h =>
            have hcB := code_bounds hc
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p H0 v0) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p q_H1 (p q_v0 q_H2)) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have hx : sz (p H0 q_x) < sz q_x := by
              have q := s2hB.1
              have eu : sz x = sz (p H0 q_x) := congrArg sz (Eq.trans (p0) (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2))))
              have ev : sz v0 = sz q_x := congrArg sz (p2)
              have q1 : sz (p H0 q_x) < sz v0 := lt_of_eq_of_lt eu.symm q
              exact lt_of_lt_of_eq q1 ev
            have hy : sz q_x < sz (p H0 q_x) := by
              have q := qs2hB.1
              have ev : sz q_x = sz q_x := congrArg sz (rfl)
              have eu : sz q_v0 = sz (p H0 q_x) := congrArg sz (Eq.trans (p1.symm) (congrArg (fun q => p H0 q) (p2)))
              have q1 : sz q_x < sz q_v0 := lt_of_eq_of_lt ev.symm q
              exact lt_of_lt_of_eq q1 eu
            exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
  | hit s1h =>
    have s2B := step_bound s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have he : q_H1 = q_v0 := (let peq0 : x = q_v0 := ha; let peq3 : x = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
        exact step_ne_second (by simpa only [he] using qs1)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 : x = q_v0 := ha; let peq3 : x = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
        exact step_ne_second (by simpa only [he] using qs1)
    | hit s2h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H1 = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have badlt : sz v0 < sz H2 := by
              have structural : sz q_x < sz (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_right q_v0 (p q_x q_v0))) (sz_lt_p_right (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0)))
              have large_eq : sz v0 = sz q_x := congrArg sz (p2)
              have small_eq : sz H2 = sz (p (p (p q_v0 q_v1) q_v0) (p q_v0 (p q_x q_v0))) := congrArg sz (p3)
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.2).elim
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H1 = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p (p q_v0 q_v1) q_v0) (p q_v0 q_H2)) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have hx : sz q_v0 < sz q_x := by
              have q := s1hB.2
              have eu : sz H1 = sz q_v0 := congrArg sz (p1)
              have ev : sz v0 = sz q_x := congrArg sz (p2)
              have q1 : sz q_v0 < sz v0 := lt_of_eq_of_lt eu.symm q
              exact lt_of_lt_of_eq q1 ev
            have hy : sz q_x < sz q_v0 := by
              have q := qs2hB.1
              have ev : sz q_x = sz q_x := congrArg sz (rfl)
              have eu : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have q1 : sz q_x < sz q_v0 := lt_of_eq_of_lt ev.symm q
              exact lt_of_lt_of_eq q1 eu
            exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs1h =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            apply code_no_pair_left q_v0 q_v1
            exact ⟨_, qs1h⟩
          | hit qs2h =>
            apply code_no_pair_left q_v0 q_v1
            exact ⟨_, qs1h⟩
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H1 = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have badlt : sz v0 < sz H2 := by
              have structural : sz q_x < sz (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_right q_v0 (p q_x q_v0))) (sz_lt_p_right (p q_H0 q_v0) (p q_v0 (p q_x q_v0)))
              have large_eq : sz v0 = sz q_x := congrArg sz (p2)
              have small_eq : sz H2 = sz (p (p q_H0 q_v0) (p q_v0 (p q_x q_v0))) := congrArg sz (p3)
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.2).elim
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H1 = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p (p q_H0 q_v0) (p q_v0 q_H2)) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have hx : sz q_v0 < sz q_x := by
              have q := s1hB.2
              have eu : sz H1 = sz q_v0 := congrArg sz (p1)
              have ev : sz v0 = sz q_x := congrArg sz (p2)
              have q1 : sz q_v0 < sz v0 := lt_of_eq_of_lt eu.symm q
              exact lt_of_lt_of_eq q1 ev
            have hy : sz q_x < sz q_v0 := by
              have q := qs2hB.1
              have ev : sz q_x = sz q_x := congrArg sz (rfl)
              have eu : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have q1 : sz q_x < sz q_v0 := lt_of_eq_of_lt ev.symm q
              exact lt_of_lt_of_eq q1 eu
            exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs1h =>
          have qs2B := step_bound qs2
          cases qs2 with
          | raw =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H1 = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p q_H1 (p q_v0 (p q_x q_v0))) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have badlt : sz v0 < sz H2 := by
              have structural : sz q_x < sz (p q_H1 (p q_v0 (p q_x q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_right q_v0 (p q_x q_v0))) (sz_lt_p_right q_H1 (p q_v0 (p q_x q_v0)))
              have large_eq : sz v0 = sz q_x := congrArg sz (p2)
              have small_eq : sz H2 = sz (p q_H1 (p q_v0 (p q_x q_v0))) := congrArg sz (p3)
              exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
            exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s2hB.2).elim
          | hit qs2h =>
            have hcB := code_bounds hc
            have s1hB := code_bounds s1h
            have s2hB := code_bounds s2h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have qs2hB := code_bounds qs2h
            have s1B := s1B
            have s2B := s2B
            have qs0B := qs0B
            have qs1B := qs1B
            have qs2B := qs2B
            have p0 := ha
            change x = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change H1 = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (L (R q))) (hb)
            change v0 = q_x at p2
            have z2 := congrArg sz p2
            have p3 := congrArg (fun q => (R (R q))) (hb)
            change H2 = (p q_H1 (p q_v0 q_H2)) at p3
            have z3 := congrArg sz p3
            have p4 := ho
            change o = q_x at p4
            have z4 := congrArg sz p4
            have hx : sz q_v0 < sz q_x := by
              have q := s1hB.2
              have eu : sz H1 = sz q_v0 := congrArg sz (p1)
              have ev : sz v0 = sz q_x := congrArg sz (p2)
              have q1 : sz q_v0 < sz v0 := lt_of_eq_of_lt eu.symm q
              exact lt_of_lt_of_eq q1 ev
            have hy : sz q_x < sz q_v0 := by
              have q := qs2hB.1
              have ev : sz q_x = sz q_x := congrArg sz (rfl)
              have eu : sz q_v0 = sz q_v0 := congrArg sz (rfl)
              have q1 : sz q_x < sz q_v0 := lt_of_eq_of_lt ev.symm q
              exact lt_of_lt_of_eq q1 eu
            exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr3 (x v0 v1 H1 H2 : CM)
    (s1 : Step H0 v0 H1)
    (s2 : Step x v0 H2) :
    ¬ ∃ o, Code v0 (p x (p H1 (p v0 H2))) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, qs0, qs1, qs2, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have s2B := step_bound s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let peq5 : v0 = q_H2 := congrArg (fun q => (R (R (R (R q))))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = q_H2 := Eq.trans (pst3) (peq5); let pst5 : q_v0 = q_H2 := Eq.trans (pst1) (pst4); let pst6 : q_H2 = q_v0 := Eq.symm (pst5); let pst7 : q_H1 = q_v0 := Eq.trans (pst4) (pst6); pst7)
        exact step_ne_second (by simpa only [he] using qs1)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let peq5 : v0 = q_H2 := congrArg (fun q => (R (R (R (R q))))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = q_H2 := Eq.trans (pst3) (peq5); let pst5 : q_v0 = q_H2 := Eq.trans (pst1) (pst4); let pst6 : q_H2 = q_v0 := Eq.symm (pst5); let pst7 : q_H1 = q_v0 := Eq.trans (pst4) (pst6); pst7)
        exact step_ne_second (by simpa only [he] using qs1)
    | hit s2h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
        exact step_ne_second (by simpa only [he] using qs1)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
        exact step_ne_second (by simpa only [he] using qs1)
  | hit s1h =>
    have s2B := step_bound s2
    cases s2 with
    | raw =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let peq5 : v0 = q_H2 := congrArg (fun q => (R (R (R (R q))))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = q_H2 := Eq.trans (pst3) (peq5); let pst5 : q_v0 = q_H2 := Eq.trans (pst1) (pst4); let pst6 : q_H2 = q_v0 := Eq.symm (pst5); let pst7 : q_H1 = q_v0 := Eq.trans (pst4) (pst6); pst7)
        exact step_ne_second (by simpa only [he] using qs1)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let peq5 : v0 = q_H2 := congrArg (fun q => (R (R (R (R q))))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = q_H2 := Eq.trans (pst3) (peq5); let pst5 : q_v0 = q_H2 := Eq.trans (pst1) (pst4); let pst6 : q_H2 = q_v0 := Eq.symm (pst5); let pst7 : q_H1 = q_v0 := Eq.trans (pst4) (pst6); pst7)
        exact step_ne_second (by simpa only [he] using qs1)
    | hit s2h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
        exact step_ne_second (by simpa only [he] using qs1)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq3 : v0 = q_H1 := congrArg (fun q => (L (R (R q)))) (hb); let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : q_H1 = q_v0 := Eq.symm (pst1); pst2)
        exact step_ne_second (by simpa only [he] using qs1)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval x (eval (eval (eval v0 v1) v0) (eval v0 (eval x v0)))))) := by
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
  let H2 := eval x v0
  have e2a : x = x := by
    change x = x
    rfl
  have e2b : v0 = v0 := by
    change v0 = v0
    rfl
  have s2 : Step x v0 H2 := by
    rw [← e2a, ← e2b]
    exact eval_step x v0
  change x = (eval v0 (eval v0 (eval x (eval H1 (eval v0 H2)))))
  have rawEq : (eval v0 (eval v0 (eval x (eval H1 (eval v0 H2))))) = (eval v0 (p v0 (p x (p H1 (p v0 H2))))) := by
    calc
      (eval v0 (eval v0 (eval x (eval H1 (eval v0 H2))))) = (eval v0 (eval v0 (eval x (eval H1 (p v0 H2))))) := congrArg (fun q => (eval v0 (eval v0 (eval x (eval H1 q))))) (eval_raw (nr0 x v0 v1 H2 s2))
      _ = (eval v0 (eval v0 (eval x (p H1 (p v0 H2))))) := congrArg (fun q => (eval v0 (eval v0 (eval x q)))) (eval_raw (nr1 x v0 v1 H1 H2 s1 s2))
      _ = (eval v0 (eval v0 (p x (p H1 (p v0 H2))))) := congrArg (fun q => (eval v0 (eval v0 q))) (eval_raw (nr2 x v0 v1 H1 H2 s1 s2))
      _ = (eval v0 (p v0 (p x (p H1 (p v0 H2))))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H1 H2 s1 s2))
  exact (eval_hit (Code.law x v0 v1 H0 H1 H2 s0 s1 s2)).symm.trans rawEq.symm
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
