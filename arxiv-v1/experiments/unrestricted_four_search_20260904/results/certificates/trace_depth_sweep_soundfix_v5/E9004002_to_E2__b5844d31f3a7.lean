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
      (s1 : Step x v1 H1) :
      Code v0 (p v0 (p H0 (p H1 (p v0 v0)))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v0 q_H0 ∧ Step q_x q_v1 q_H1 ∧ a = q_v0 ∧ b = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_unique {a q b o : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_left q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_left q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))
  ·
    cases s0 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) (sz_lt_p_right q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))))
    | hit h0 =>
      exact Nat.lt_trans (code_key_small h0) (sz_lt_p_left q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0))))
theorem step_first_unique {a q b o : CM} (h : Step a b o) (k : Step q b o) : a = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right a b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
  | hit hc =>
    cases k with
    | raw =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right q b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
    | hit hk => exact code_key_unique hc hk
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, hs0, hs1, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_H0, r_q_H1, rs0, rs1, ka, kb, ko⟩
  have et := congrArg (fun z => (L (R z))) (hb.symm.trans kb)
  have eo := congrArg (fun z => (L z)) (hb.symm.trans kb)
  change q_H0 = r_q_H0 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs0
  have er := step_first_unique hs0 rs0
  have ex : q_x = r_q_x := er
  exact ho.trans (ex.trans ko.symm)
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
      change v = (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) := congrArg (fun q => p q (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) (pst0); let pst2 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst3 : (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) = (p (p q_x (p v k)) (p (p q_x q_v1) (p q_v0 q_v0))) := congrArg (fun q => p q (p (p q_x q_v1) (p q_v0 q_v0))) (pst2); let pst4 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p v k) (p v k))) := congrArg (fun q => p (p q_x q_v1) q) (pst6); let pst8 : (p (p q_x (p v k)) (p (p q_x q_v1) (p q_v0 q_v0))) = (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k)))) := congrArg (fun q => p (p q_x (p v k)) q) (pst7); let pst9 : (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) = (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k)))) := Eq.trans (pst3) (pst8); let pst10 : (p (p v k) (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst9); let pst11 : (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) = (p (p v k) (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k))))) := Eq.trans (pst1) (pst10); let pst12 : v = (p (p v k) (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k))))) := Eq.trans (peq1) (pst11); pst12)
      have hlt : sz v < sz (p (p v k) (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p v k)) (p (p q_x q_v1) (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) (pst0); let pst2 : (p q_x q_v0) = (p q_x (p v k)) := congrArg (fun q => p q_x q) (pst0); let pst3 : (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) = (p (p q_x (p v k)) (p q_H1 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_H1 (p q_v0 q_v0))) (pst2); let pst4 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst4) (pst5); let pst7 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p v k) (p v k))) := congrArg (fun q => p q_H1 q) (pst6); let pst8 : (p (p q_x (p v k)) (p q_H1 (p q_v0 q_v0))) = (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k)))) := congrArg (fun q => p (p q_x (p v k)) q) (pst7); let pst9 : (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) = (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k)))) := Eq.trans (pst3) (pst8); let pst10 : (p (p v k) (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst9); let pst11 : (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k))))) := Eq.trans (pst1) (pst10); let pst12 : v = (p (p v k) (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst11); pst12)
      have hlt : sz v < sz (p (p v k) (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p v k)) (p q_H1 (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) = (p (p v k) (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p v k) (p v k))) := congrArg (fun q => p (p q_x q_v1) q) (pst4); let pst6 : (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) = (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k)))) := congrArg (fun q => p q_H0 q) (pst5); let pst7 : (p (p v k) (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) = (p (p v k) (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) = (p (p v k) (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_H0 (p (p q_x q_v1) (p (p v k) (p v k)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : v = (p (p v k) (p q_H0 (p q_H1 (p (p v k) (p v k))))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_H0 (p q_H1 (p q_v0 q_v0)))) := congrArg (fun q => p q (p q_H0 (p q_H1 (p q_v0 q_v0)))) (pst0); let pst2 : (p q_v0 q_v0) = (p (p v k) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst3 : (p (p v k) q_v0) = (p (p v k) (p v k)) := congrArg (fun q => p (p v k) q) (pst0); let pst4 : (p q_v0 q_v0) = (p (p v k) (p v k)) := Eq.trans (pst2) (pst3); let pst5 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p v k) (p v k))) := congrArg (fun q => p q_H1 q) (pst4); let pst6 : (p q_H0 (p q_H1 (p q_v0 q_v0))) = (p q_H0 (p q_H1 (p (p v k) (p v k)))) := congrArg (fun q => p q_H0 q) (pst5); let pst7 : (p (p v k) (p q_H0 (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_H0 (p q_H1 (p (p v k) (p v k))))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) = (p (p v k) (p q_H0 (p q_H1 (p (p v k) (p v k))))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p q_H0 (p q_H1 (p (p v k) (p v k))))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p q_H0 (p q_H1 (p (p v k) (p v k))))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p q_H0 (p q_H1 (p (p v k) (p v k)))))
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
      change v0 = (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) at e1
      have cyc : q_v0 = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))) := sz_lt_p_left q_v0 (p q_H0 (p q_H1 (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step x v1 H1) :
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
        change (p x v1) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) at e2
        have cyc : x = (p q_x (p x v1)) := (let peq0 : (p x v1) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p x v1) := Eq.symm (peq0); let pst1 : v0 = (p x v1) := Eq.trans (peq1) (pst0); let pst2 : (p x v1) = v0 := Eq.symm (pst1); let pst3 : (p x v1) = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_x q_v0) = (p q_x (p x v1)) := congrArg (fun q => p q_x q) (pst0); let pst5 : (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) = (p (p q_x (p x v1)) (p (p q_x q_v1) (p q_v0 q_v0))) := congrArg (fun q => p q (p (p q_x q_v1) (p q_v0 q_v0))) (pst4); let pst6 : (p q_v0 q_v0) = (p (p x v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst7 : (p (p x v1) q_v0) = (p (p x v1) (p x v1)) := congrArg (fun q => p (p x v1) q) (pst0); let pst8 : (p q_v0 q_v0) = (p (p x v1) (p x v1)) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p x v1) (p x v1))) := congrArg (fun q => p (p q_x q_v1) q) (pst8); let pst10 : (p (p q_x (p x v1)) (p (p q_x q_v1) (p q_v0 q_v0))) = (p (p q_x (p x v1)) (p (p q_x q_v1) (p (p x v1) (p x v1)))) := congrArg (fun q => p (p q_x (p x v1)) q) (pst9); let pst11 : (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) = (p (p q_x (p x v1)) (p (p q_x q_v1) (p (p x v1) (p x v1)))) := Eq.trans (pst5) (pst10); let pst12 : (p x v1) = (p (p q_x (p x v1)) (p (p q_x q_v1) (p (p x v1) (p x v1)))) := Eq.trans (pst3) (pst11); let pst13 : x = (p q_x (p x v1)) := congrArg (fun q => L q) (pst12); pst13)
        have hlt : sz x < sz (p q_x (p x v1)) := Nat.lt_trans (sz_lt_p_left x v1) (sz_lt_p_right q_x (p x v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x v1) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : x = (p q_x (p x v1)) := (let peq0 : (p x v1) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p x v1) := Eq.symm (peq0); let pst1 : v0 = (p x v1) := Eq.trans (peq1) (pst0); let pst2 : (p x v1) = v0 := Eq.symm (pst1); let pst3 : (p x v1) = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_x q_v0) = (p q_x (p x v1)) := congrArg (fun q => p q_x q) (pst0); let pst5 : (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) = (p (p q_x (p x v1)) (p q_H1 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_H1 (p q_v0 q_v0))) (pst4); let pst6 : (p q_v0 q_v0) = (p (p x v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst7 : (p (p x v1) q_v0) = (p (p x v1) (p x v1)) := congrArg (fun q => p (p x v1) q) (pst0); let pst8 : (p q_v0 q_v0) = (p (p x v1) (p x v1)) := Eq.trans (pst6) (pst7); let pst9 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x v1) (p x v1))) := congrArg (fun q => p q_H1 q) (pst8); let pst10 : (p (p q_x (p x v1)) (p q_H1 (p q_v0 q_v0))) = (p (p q_x (p x v1)) (p q_H1 (p (p x v1) (p x v1)))) := congrArg (fun q => p (p q_x (p x v1)) q) (pst9); let pst11 : (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) = (p (p q_x (p x v1)) (p q_H1 (p (p x v1) (p x v1)))) := Eq.trans (pst5) (pst10); let pst12 : (p x v1) = (p (p q_x (p x v1)) (p q_H1 (p (p x v1) (p x v1)))) := Eq.trans (pst3) (pst11); let pst13 : x = (p q_x (p x v1)) := congrArg (fun q => L q) (pst12); pst13)
        have hlt : sz x < sz (p q_x (p x v1)) := Nat.lt_trans (sz_lt_p_left x v1) (sz_lt_p_right q_x (p x v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p x v1) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) at e2
        have cyc : v1 = (p (p q_x q_v1) (p (p q_H0 v1) (p q_H0 v1))) := (let peq0 : (p x v1) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p x v1) := Eq.symm (peq0); let pst1 : v0 = (p x v1) := Eq.trans (peq1) (pst0); let pst2 : (p x v1) = v0 := Eq.symm (pst1); let pst3 : (p x v1) = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p x v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x v1) q_v0) = (p (p x v1) (p x v1)) := congrArg (fun q => p (p x v1) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x v1) (p x v1)) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p x v1) (p x v1))) := congrArg (fun q => p (p q_x q_v1) q) (pst6); let pst8 : (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) = (p q_H0 (p (p q_x q_v1) (p (p x v1) (p x v1)))) := congrArg (fun q => p q_H0 q) (pst7); let pst9 : (p x v1) = (p q_H0 (p (p q_x q_v1) (p (p x v1) (p x v1)))) := Eq.trans (pst3) (pst8); let pst10 : v1 = (p (p q_x q_v1) (p (p x v1) (p x v1))) := congrArg (fun q => R q) (pst9); let pst11 : x = q_H0 := congrArg (fun q => L q) (pst9); let pst12 : (p x v1) = (p q_H0 v1) := congrArg (fun q => p q v1) (pst11); let pst13 : (p (p x v1) (p x v1)) = (p (p q_H0 v1) (p x v1)) := congrArg (fun q => p q (p x v1)) (pst12); let pst14 : (p x v1) = (p q_H0 v1) := congrArg (fun q => p q v1) (pst11); let pst15 : (p (p q_H0 v1) (p x v1)) = (p (p q_H0 v1) (p q_H0 v1)) := congrArg (fun q => p (p q_H0 v1) q) (pst14); let pst16 : (p (p x v1) (p x v1)) = (p (p q_H0 v1) (p q_H0 v1)) := Eq.trans (pst13) (pst15); let pst17 : (p (p q_x q_v1) (p (p x v1) (p x v1))) = (p (p q_x q_v1) (p (p q_H0 v1) (p q_H0 v1))) := congrArg (fun q => p (p q_x q_v1) q) (pst16); let pst18 : v1 = (p (p q_x q_v1) (p (p q_H0 v1) (p q_H0 v1))) := Eq.trans (pst10) (pst17); pst18)
        have hlt : sz v1 < sz (p (p q_x q_v1) (p (p q_H0 v1) (p q_H0 v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 v1) (sz_lt_p_left (p q_H0 v1) (p q_H0 v1))) (sz_lt_p_right (p q_x q_v1) (p (p q_H0 v1) (p q_H0 v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x v1) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_H0 (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : v1 = (p q_H1 (p (p q_H0 v1) (p q_H0 v1))) := (let peq0 : (p x v1) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_H0 (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = (p x v1) := Eq.symm (peq0); let pst1 : v0 = (p x v1) := Eq.trans (peq1) (pst0); let pst2 : (p x v1) = v0 := Eq.symm (pst1); let pst3 : (p x v1) = (p q_H0 (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p x v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x v1) q_v0) = (p (p x v1) (p x v1)) := congrArg (fun q => p (p x v1) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x v1) (p x v1)) := Eq.trans (pst4) (pst5); let pst7 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x v1) (p x v1))) := congrArg (fun q => p q_H1 q) (pst6); let pst8 : (p q_H0 (p q_H1 (p q_v0 q_v0))) = (p q_H0 (p q_H1 (p (p x v1) (p x v1)))) := congrArg (fun q => p q_H0 q) (pst7); let pst9 : (p x v1) = (p q_H0 (p q_H1 (p (p x v1) (p x v1)))) := Eq.trans (pst3) (pst8); let pst10 : v1 = (p q_H1 (p (p x v1) (p x v1))) := congrArg (fun q => R q) (pst9); let pst11 : x = q_H0 := congrArg (fun q => L q) (pst9); let pst12 : (p x v1) = (p q_H0 v1) := congrArg (fun q => p q v1) (pst11); let pst13 : (p (p x v1) (p x v1)) = (p (p q_H0 v1) (p x v1)) := congrArg (fun q => p q (p x v1)) (pst12); let pst14 : (p x v1) = (p q_H0 v1) := congrArg (fun q => p q v1) (pst11); let pst15 : (p (p q_H0 v1) (p x v1)) = (p (p q_H0 v1) (p q_H0 v1)) := congrArg (fun q => p (p q_H0 v1) q) (pst14); let pst16 : (p (p x v1) (p x v1)) = (p (p q_H0 v1) (p q_H0 v1)) := Eq.trans (pst13) (pst15); let pst17 : (p q_H1 (p (p x v1) (p x v1))) = (p q_H1 (p (p q_H0 v1) (p q_H0 v1))) := congrArg (fun q => p q_H1 q) (pst16); let pst18 : v1 = (p q_H1 (p (p q_H0 v1) (p q_H0 v1))) := Eq.trans (pst10) (pst17); pst18)
        have hlt : sz v1 < sz (p q_H1 (p (p q_H0 v1) (p q_H0 v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 v1) (sz_lt_p_left (p q_H0 v1) (p q_H0 v1))) (sz_lt_p_right q_H1 (p (p q_H0 v1) (p q_H0 v1)))
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
        change v0 = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p (p q_x q_v1) (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p (p q_x q_v0) (p q_H1 (p q_v0 q_v0))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_H1 (p q_v0 q_v0)))
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
        change v0 = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_H0 (p (p q_x q_v1) (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p q_x q_v1) (p q_v0 q_v0))) (sz_lt_p_right q_H0 (p (p q_x q_v1) (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H1 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_H0 (p q_H1 (p q_v0 q_v0))) at e2
        have cyc : q_v0 = (p q_H0 (p q_H1 (p q_v0 q_v0))) := (let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p q_H0 (p q_H1 (p q_v0 q_v0))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq1); let pst1 : q_v0 = (p q_H0 (p q_H1 (p q_v0 q_v0))) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_H0 (p q_H1 (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_H1 (p q_v0 q_v0))) (sz_lt_p_right q_H0 (p q_H1 (p q_v0 q_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 H1 : CM)
    (s0 : Step x v0 H0)
    (s1 : Step x v1 H1) :
    ¬ ∃ o, Code H0 (p H1 (p v0 v0)) o := by
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
          change (p x v1) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at e3
          have cyc : v0 = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = (p q_x q_v0) := e2; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : v0 = (p q_x (p x v0)) := Eq.trans (peq2) (pst1); pst2)
          have hlt : sz v0 < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_right x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v1) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_H1 (p q_v0 q_v0)) at e3
          have cyc : v0 = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = (p q_x q_v0) := e2; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : v0 = (p q_x (p x v0)) := Eq.trans (peq2) (pst1); pst2)
          have hlt : sz v0 < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_right x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v1) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_H0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at e3
          have cyc : q_H0 = (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = q_H0 := e2; let peq3 : v0 = (p (p q_x q_v1) (p q_v0 q_v0)) := e3; let pst0 : q_H0 = v0 := Eq.symm (peq2); let pst1 : q_H0 = (p (p q_x q_v1) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x v0) := Eq.symm (peq0); let pst3 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst4 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst7 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst6); let pst8 : (p (p x q_H0) q_v0) = (p (p x q_H0) (p x q_H0)) := congrArg (fun q => p (p x q_H0) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p x q_H0) (p x q_H0)) := Eq.trans (pst5) (pst8); let pst10 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := congrArg (fun q => p (p q_x q_v1) q) (pst9); let pst11 : q_H0 = (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := Eq.trans (pst1) (pst10); pst11)
          have hlt : sz q_H0 < sz (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x q_H0) (sz_lt_p_left (p x q_H0) (p x q_H0))) (sz_lt_p_right (p q_x q_v1) (p (p x q_H0) (p x q_H0)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v1) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_H0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_H1 (p q_v0 q_v0)) at e3
          have cyc : q_H0 = (p q_H1 (p (p x q_H0) (p x q_H0))) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = q_H0 := e2; let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := e3; let pst0 : q_H0 = v0 := Eq.symm (peq2); let pst1 : q_H0 = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x v0) := Eq.symm (peq0); let pst3 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst4 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst7 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst6); let pst8 : (p (p x q_H0) q_v0) = (p (p x q_H0) (p x q_H0)) := congrArg (fun q => p (p x q_H0) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p x q_H0) (p x q_H0)) := Eq.trans (pst5) (pst8); let pst10 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x q_H0) (p x q_H0))) := congrArg (fun q => p q_H1 q) (pst9); let pst11 : q_H0 = (p q_H1 (p (p x q_H0) (p x q_H0))) := Eq.trans (pst1) (pst10); pst11)
          have hlt : sz q_H0 < sz (p q_H1 (p (p x q_H0) (p x q_H0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x q_H0) (sz_lt_p_left (p x q_H0) (p x q_H0))) (sz_lt_p_right q_H1 (p (p x q_H0) (p x q_H0)))
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
          change H1 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at e3
          have cyc : v0 = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = (p q_x q_v0) := e2; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : v0 = (p q_x (p x v0)) := Eq.trans (peq2) (pst1); pst2)
          have hlt : sz v0 < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_right x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H1 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_H1 (p q_v0 q_v0)) at e3
          have cyc : v0 = (p q_x (p x v0)) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = (p q_x q_v0) := e2; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : v0 = (p q_x (p x v0)) := Eq.trans (peq2) (pst1); pst2)
          have hlt : sz v0 < sz (p q_x (p x v0)) := Nat.lt_trans (sz_lt_p_right x v0) (sz_lt_p_right q_x (p x v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H1 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_H0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at e3
          have cyc : q_H0 = (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = q_H0 := e2; let peq3 : v0 = (p (p q_x q_v1) (p q_v0 q_v0)) := e3; let pst0 : q_H0 = v0 := Eq.symm (peq2); let pst1 : q_H0 = (p (p q_x q_v1) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x v0) := Eq.symm (peq0); let pst3 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst4 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst7 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst6); let pst8 : (p (p x q_H0) q_v0) = (p (p x q_H0) (p x q_H0)) := congrArg (fun q => p (p x q_H0) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p x q_H0) (p x q_H0)) := Eq.trans (pst5) (pst8); let pst10 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := congrArg (fun q => p (p q_x q_v1) q) (pst9); let pst11 : q_H0 = (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := Eq.trans (pst1) (pst10); pst11)
          have hlt : sz q_H0 < sz (p (p q_x q_v1) (p (p x q_H0) (p x q_H0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x q_H0) (sz_lt_p_left (p x q_H0) (p x q_H0))) (sz_lt_p_right (p q_x q_v1) (p (p x q_H0) (p x q_H0)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change (p x v0) = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H1 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = q_H0 at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_H1 (p q_v0 q_v0)) at e3
          have cyc : q_H0 = (p q_H1 (p (p x q_H0) (p x q_H0))) := (let peq0 : (p x v0) = q_v0 := e0; let peq2 : v0 = q_H0 := e2; let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := e3; let pst0 : q_H0 = v0 := Eq.symm (peq2); let pst1 : q_H0 = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x v0) := Eq.symm (peq0); let pst3 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst4 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst3); let pst5 : (p q_v0 q_v0) = (p (p x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p x v0) = (p x q_H0) := congrArg (fun q => p x q) (peq2); let pst7 : q_v0 = (p x q_H0) := Eq.trans (pst2) (pst6); let pst8 : (p (p x q_H0) q_v0) = (p (p x q_H0) (p x q_H0)) := congrArg (fun q => p (p x q_H0) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p x q_H0) (p x q_H0)) := Eq.trans (pst5) (pst8); let pst10 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x q_H0) (p x q_H0))) := congrArg (fun q => p q_H1 q) (pst9); let pst11 : q_H0 = (p q_H1 (p (p x q_H0) (p x q_H0))) := Eq.trans (pst1) (pst10); pst11)
          have hlt : sz q_H0 < sz (p q_H1 (p (p x q_H0) (p x q_H0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right x q_H0) (sz_lt_p_left (p x q_H0) (p x q_H0))) (sz_lt_p_right q_H1 (p (p x q_H0) (p x q_H0)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
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
          change H0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v1) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at e3
          have cyc : q_x = (p q_x q_v1) := (let peq1 : (p x v1) = q_v0 := e1; let peq2 : v0 = (p q_x q_v0) := e2; let peq3 : v0 = (p (p q_x q_v1) (p q_v0 q_v0)) := e3; let pst0 : q_v0 = (p x v1) := Eq.symm (peq1); let pst1 : (p q_x q_v0) = (p q_x (p x v1)) := congrArg (fun q => p q_x q) (pst0); let pst2 : v0 = (p q_x (p x v1)) := Eq.trans (peq2) (pst1); let pst3 : (p q_x (p x v1)) = v0 := Eq.symm (pst2); let pst4 : (p q_x (p x v1)) = (p (p q_x q_v1) (p q_v0 q_v0)) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 q_v0) = (p (p x v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst6 : (p (p x v1) q_v0) = (p (p x v1) (p x v1)) := congrArg (fun q => p (p x v1) q) (pst0); let pst7 : (p q_v0 q_v0) = (p (p x v1) (p x v1)) := Eq.trans (pst5) (pst6); let pst8 : (p (p q_x q_v1) (p q_v0 q_v0)) = (p (p q_x q_v1) (p (p x v1) (p x v1))) := congrArg (fun q => p (p q_x q_v1) q) (pst7); let pst9 : (p q_x (p x v1)) = (p (p q_x q_v1) (p (p x v1) (p x v1))) := Eq.trans (pst4) (pst8); let pst10 : q_x = (p q_x q_v1) := congrArg (fun q => L q) (pst9); pst10)
          have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change H0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v1) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_H1 (p q_v0 q_v0)) at e3
          have cyc : x = (p x v1) := (let peq1 : (p x v1) = q_v0 := e1; let peq2 : v0 = (p q_x q_v0) := e2; let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := e3; let pst0 : q_v0 = (p x v1) := Eq.symm (peq1); let pst1 : (p q_x q_v0) = (p q_x (p x v1)) := congrArg (fun q => p q_x q) (pst0); let pst2 : v0 = (p q_x (p x v1)) := Eq.trans (peq2) (pst1); let pst3 : (p q_x (p x v1)) = v0 := Eq.symm (pst2); let pst4 : (p q_x (p x v1)) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 q_v0) = (p (p x v1) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst6 : (p (p x v1) q_v0) = (p (p x v1) (p x v1)) := congrArg (fun q => p (p x v1) q) (pst0); let pst7 : (p q_v0 q_v0) = (p (p x v1) (p x v1)) := Eq.trans (pst5) (pst6); let pst8 : (p q_H1 (p q_v0 q_v0)) = (p q_H1 (p (p x v1) (p x v1))) := congrArg (fun q => p q_H1 q) (pst7); let pst9 : (p q_x (p x v1)) = (p q_H1 (p (p x v1) (p x v1))) := Eq.trans (pst4) (pst8); let pst10 : (p x v1) = (p (p x v1) (p x v1)) := congrArg (fun q => R q) (pst9); let pst11 : x = (p x v1) := congrArg (fun q => L q) (pst10); pst11)
          have hlt : sz x < sz (p x v1) := sz_lt_p_left x v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
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
          change (p x v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_H0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx : sz (p x v1) < sz q_H0 := by
            have q := s0hB.2
            have eu : sz H0 = sz (p x v1) := congrArg sz (Eq.trans (p0) (p1.symm))
            have ev : sz v0 = sz q_H0 := congrArg sz (p2)
            have q1 : sz (p x v1) < sz v0 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz q_H0 < sz (p x v1) := by
            have q := qs0hB.2
            have ev : sz q_H0 = sz q_H0 := congrArg sz (rfl)
            have eu : sz q_v0 = sz (p x v1) := congrArg sz (p1.symm)
            have q1 : sz q_H0 < sz q_v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
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
          change (p x v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_H0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = (p q_H1 (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx : sz (p x v1) < sz q_H0 := by
            have q := s0hB.2
            have eu : sz H0 = sz (p x v1) := congrArg sz (Eq.trans (p0) (p1.symm))
            have ev : sz v0 = sz q_H0 := congrArg sz (p2)
            have q1 : sz (p x v1) < sz v0 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz q_H0 < sz (p x v1) := by
            have q := qs0hB.2
            have ev : sz q_H0 = sz q_H0 := congrArg sz (rfl)
            have eu : sz q_v0 = sz (p x v1) := congrArg sz (p1.symm)
            have q1 : sz q_H0 < sz q_v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit s1h =>
      have qs0B := step_bound qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change H0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H1 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at e3
          have cyc : q_x = (p q_x q_v1) := (let peq2 : v0 = (p q_x q_v0) := e2; let peq3 : v0 = (p (p q_x q_v1) (p q_v0 q_v0)) := e3; let pst0 : (p q_x q_v0) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_v0) = (p (p q_x q_v1) (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_x = (p q_x q_v1) := congrArg (fun q => L q) (pst1); pst2)
          have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change H0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H1 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change v0 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (R (R q))) hb
          change v0 = (p q_H1 (p q_v0 q_v0)) at e3
          have cyc : q_v0 = (p q_v0 q_v0) := (let peq2 : v0 = (p q_x q_v0) := e2; let peq3 : v0 = (p q_H1 (p q_v0 q_v0)) := e3; let pst0 : (p q_x q_v0) = v0 := Eq.symm (peq2); let pst1 : (p q_x q_v0) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => R q) (pst1); pst2)
          have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
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
          change H1 = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_H0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = (p (p q_x q_v1) (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx : sz q_v0 < sz q_H0 := by
            have q := s0hB.2
            have eu : sz H0 = sz q_v0 := congrArg sz (p0)
            have ev : sz v0 = sz q_H0 := congrArg sz (p2)
            have q1 : sz q_v0 < sz v0 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz q_H0 < sz q_v0 := by
            have q := qs0hB.2
            have ev : sz q_H0 = sz q_H0 := congrArg sz (rfl)
            have eu : sz q_v0 = sz q_v0 := congrArg sz (rfl)
            have q1 : sz q_H0 < sz q_v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
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
          change H1 = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (L (R q))) (hb)
          change v0 = q_H0 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R (R q))) (hb)
          change v0 = (p q_H1 (p q_v0 q_v0)) at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          have hx : sz q_v0 < sz q_H0 := by
            have q := s0hB.2
            have eu : sz H0 = sz q_v0 := congrArg sz (p0)
            have ev : sz v0 = sz q_H0 := congrArg sz (p2)
            have q1 : sz q_v0 < sz v0 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz q_H0 < sz q_v0 := by
            have q := qs0hB.2
            have ev : sz q_H0 = sz q_H0 := congrArg sz (rfl)
            have eu : sz q_v0 = sz q_v0 := congrArg sz (rfl)
            have q1 : sz q_H0 < sz q_v0 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr3 (x v0 v1 H0 H1 : CM)
    (s0 : Step x v0 H0)
    (s1 : Step x v1 H1) :
    ¬ ∃ o, Code v0 (p H0 (p H1 (p v0 v0))) o := by
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
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (L (R q)))) hb
          change x = q_x at e2
          have e3 := congrArg (fun q => (R (L (R q)))) hb
          change v1 = q_v0 at e3
          have e4 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e4
          have e5 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e5
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (L (R q)))) hb
          change x = q_x at e2
          have e3 := congrArg (fun q => (R (L (R q)))) hb
          change v1 = q_v0 at e3
          have e4 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_H1 at e4
          have e5 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e5
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change (p x v1) = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change (p x v1) = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_H1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
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
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_H1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change (p x v0) = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_H1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_v0 = (p x q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x v0) = q_v0 := e1; let pst0 : (p x v0) = (p x q_v0) := congrArg (fun q => p x q) (peq0); let pst1 : (p x q_v0) = (p x v0) := Eq.symm (pst0); let pst2 : (p x q_v0) = q_v0 := Eq.trans (pst1) (peq1); let pst3 : q_v0 = (p x q_v0) := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p x q_v0) := sz_lt_p_right x q_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
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
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (L (R q)))) hb
          change x = q_x at e2
          have e3 := congrArg (fun q => (R (L (R q)))) hb
          change v1 = q_v0 at e3
          have e4 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e4
          have e5 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e5
          have cyc : q_x = (p q_x q_v1) := (let peq0 : v0 = q_v0 := e0; let peq4 : v0 = (p q_x q_v1) := e4; let peq5 : v0 = (p q_v0 q_v0) := e5; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_v1) := Eq.trans (pst0) (peq4); let pst2 : v0 = (p q_x q_v1) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_v1) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v0) := Eq.trans (pst3) (peq5); let pst5 : (p q_v0 q_v0) = (p (p q_x q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := congrArg (fun q => p (p q_x q_v1) q) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst5) (pst6); let pst8 : (p q_x q_v1) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst4) (pst7); let pst9 : q_x = (p q_x q_v1) := congrArg (fun q => L q) (pst8); pst9)
          have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (L (R q)))) hb
          change x = q_x at e2
          have e3 := congrArg (fun q => (R (L (R q)))) hb
          change v1 = q_v0 at e3
          have e4 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_H1 at e4
          have e5 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e5
          have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq4 : v0 = q_H1 := e4; let peq5 : v0 = (p q_v0 q_v0) := e5; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq4); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq5); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
          have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change (p x v1) = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_x = (p q_x q_v1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p q_x q_v1) := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_v1) := Eq.trans (pst0) (peq3); let pst2 : v0 = (p q_x q_v1) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_v1) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p (p q_x q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := congrArg (fun q => p (p q_x q_v1) q) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst5) (pst6); let pst8 : (p q_x q_v1) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst4) (pst7); let pst9 : q_x = (p q_x q_v1) := congrArg (fun q => L q) (pst8); pst9)
          have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change (p x v1) = q_H0 at e2
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
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = (p q_x q_v0) at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_x = (p q_x q_v1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p q_x q_v1) := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_v1) := Eq.trans (pst0) (peq3); let pst2 : v0 = (p q_x q_v1) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_v1) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p (p q_x q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := congrArg (fun q => p (p q_x q_v1) q) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst5) (pst6); let pst8 : (p q_x q_v1) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst4) (pst7); let pst9 : q_x = (p q_x q_v1) := congrArg (fun q => L q) (pst8); pst9)
          have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = (p q_x q_v0) at e2
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
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = (p q_x q_v1) at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_x = (p q_x q_v1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = (p q_x q_v1) := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_v1) := Eq.trans (pst0) (peq3); let pst2 : v0 = (p q_x q_v1) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_v1) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_v1) = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p (p q_x q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := congrArg (fun q => p (p q_x q_v1) q) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst5) (pst6); let pst8 : (p q_x q_v1) = (p (p q_x q_v1) (p q_x q_v1)) := Eq.trans (pst4) (pst7); let pst9 : q_x = (p q_x q_v1) := congrArg (fun q => L q) (pst8); pst9)
          have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => q) ha
          change v0 = q_v0 at e0
          have e1 := congrArg (fun q => (L q)) hb
          change H0 = q_v0 at e1
          have e2 := congrArg (fun q => (L (R q))) hb
          change H1 = q_H0 at e2
          have e3 := congrArg (fun q => (L (R (R q)))) hb
          change v0 = q_H1 at e3
          have e4 := congrArg (fun q => (R (R (R q)))) hb
          change v0 = (p q_v0 q_v0) at e4
          have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq3 : v0 = q_H1 := e3; let peq4 : v0 = (p q_v0 q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq3); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq4); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
          have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval x v0) (eval (eval x v1) (eval v0 v0))))) := by
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
  let H1 := eval x v1
  have e1a : x = x := by
    change x = x
    rfl
  have e1b : v1 = v1 := by
    change v1 = v1
    rfl
  have s1 : Step x v1 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step x v1
  change x = (eval v0 (eval v0 (eval H0 (eval H1 (eval v0 v0)))))
  have rawEq : (eval v0 (eval v0 (eval H0 (eval H1 (eval v0 v0))))) = (eval v0 (p v0 (p H0 (p H1 (p v0 v0))))) := by
    calc
      (eval v0 (eval v0 (eval H0 (eval H1 (eval v0 v0))))) = (eval v0 (eval v0 (eval H0 (eval H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval H0 (eval H1 q))))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval v0 (eval H0 (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 (eval H0 q)))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval v0 (eval v0 (p H0 (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 (eval v0 q))) (eval_raw (nr2 x v0 v1 H0 H1 s0 s1))
      _ = (eval v0 (p v0 (p H0 (p H1 (p v0 v0))))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H0 H1 s0 s1))
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
