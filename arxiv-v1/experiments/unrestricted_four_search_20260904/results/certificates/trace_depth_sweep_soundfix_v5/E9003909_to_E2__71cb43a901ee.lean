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
  | law (x v0 v1 v2 H0 H1 H2 H3 H4 : CM)
      (s0 : Step v1 x H0)
      (s1 : Step H0 v2 H1)
      (s2 : Step H1 v0 H2)
      (s3 : Step H2 x H3)
      (s4 : Step (p x H3) v0 H4) :
      Code v0 (p v0 H4) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 q_H2 q_H3 q_H4 : CM, Step q_v1 q_x q_H0 ∧ Step q_H0 q_v2 q_H1 ∧ Step q_H1 q_v0 q_H2 ∧ Step q_H2 q_x q_H3 ∧ Step (p q_x q_H3) q_v0 q_H4 ∧ a = q_v0 ∧ b = (p q_v0 q_H4) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 H2 H3 H4 s0 s1 s2 s3 s4 => ⟨x, v0, v1, v2, H0, H1, H2, H3, H4, s0, s1, s2, s3, s4, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_unique {a q b o : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, q_H4, s0, s1, s2, s3, s4, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_left q_v0 q_H4
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, q_H4, s0, s1, s2, s3, s4, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_left q_v0 q_H4
  ·
    cases s4 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_H3) (sz_lt_p_left (p q_x q_H3) q_v0)) (sz_lt_p_right q_v0 (p (p q_x q_H3) q_v0))
    | hit h4 =>
      exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_H3) (code_key_small h4)) (sz_lt_p_left q_v0 q_H4)
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
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, q_H4, hs0, hs1, hs2, hs3, hs4, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_v2, r_q_H0, r_q_H1, r_q_H2, r_q_H3, r_q_H4, rs0, rs1, rs2, rs3, rs4, ka, kb, ko⟩
  have et := congrArg (fun z => (R z)) (hb.symm.trans kb)
  have eo := congrArg (fun z => (L z)) (hb.symm.trans kb)
  change q_H4 = r_q_H4 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs4
  have er := step_first_unique hs4 rs4
  have ex : q_x = r_q_x := congrArg (fun z => (L z)) er
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, q_H4, qs0, qs1, qs2, qs3, qs4, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) (pst0); let pst2 : (p (p (p q_v1 q_x) q_v2) q_v0) = (p (p (p q_v1 q_x) q_v2) (p v k)) := congrArg (fun q => p (p (p q_v1 q_x) q_v2) q) (pst0); let pst3 : (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x) = (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) = (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0) = (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) q_v0) = (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k)) := congrArg (fun q => p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) q) (pst0); let pst7 : (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0) = (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k)) := Eq.trans (pst5) (pst6); let pst8 : (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k))) := Eq.trans (peq1) (pst9); pst10)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p (p (p (p q_v1 q_x) q_v2) (p v k)) q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p q_H2 q_x)) q_v0)) (pst0); let pst2 : (p (p q_x (p q_H2 q_x)) q_v0) = (p (p q_x (p q_H2 q_x)) (p v k)) := congrArg (fun q => p (p q_x (p q_H2 q_x)) q) (pst0); let pst3 : (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p q_H2 q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) (pst0); let pst2 : (p q_H1 q_v0) = (p q_H1 (p v k)) := congrArg (fun q => p q_H1 q) (pst0); let pst3 : (p (p q_H1 q_v0) q_x) = (p (p q_H1 (p v k)) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p (p q_H1 q_v0) q_x)) = (p q_x (p (p q_H1 (p v k)) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0) = (p (p q_x (p (p q_H1 (p v k)) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p q_x (p (p q_H1 (p v k)) q_x)) q_v0) = (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k)) := congrArg (fun q => p (p q_x (p (p q_H1 (p v k)) q_x)) q) (pst0); let pst7 : (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0) = (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k)) := Eq.trans (pst5) (pst6); let pst8 : (p (p v k) (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := Eq.trans (peq1) (pst9); pst10)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p q_H2 q_x)) q_v0)) (pst0); let pst2 : (p (p q_x (p q_H2 q_x)) q_v0) = (p (p q_x (p q_H2 q_x)) (p v k)) := congrArg (fun q => p (p q_x (p q_H2 q_x)) q) (pst0); let pst3 : (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p q_H2 q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) (pst0); let pst2 : (p (p q_H0 q_v2) q_v0) = (p (p q_H0 q_v2) (p v k)) := congrArg (fun q => p (p q_H0 q_v2) q) (pst0); let pst3 : (p (p (p q_H0 q_v2) q_v0) q_x) = (p (p (p q_H0 q_v2) (p v k)) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) = (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0) = (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) q_v0) = (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k)) := congrArg (fun q => p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) q) (pst0); let pst7 : (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0) = (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k)) := Eq.trans (pst5) (pst6); let pst8 : (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k))) := Eq.trans (peq1) (pst9); pst10)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p (p (p q_H0 q_v2) (p v k)) q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p q_H2 q_x)) q_v0)) (pst0); let pst2 : (p (p q_x (p q_H2 q_x)) q_v0) = (p (p q_x (p q_H2 q_x)) (p v k)) := congrArg (fun q => p (p q_x (p q_H2 q_x)) q) (pst0); let pst3 : (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p q_H2 q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) (pst0); let pst2 : (p q_H1 q_v0) = (p q_H1 (p v k)) := congrArg (fun q => p q_H1 q) (pst0); let pst3 : (p (p q_H1 q_v0) q_x) = (p (p q_H1 (p v k)) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p (p q_H1 q_v0) q_x)) = (p q_x (p (p q_H1 (p v k)) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0) = (p (p q_x (p (p q_H1 (p v k)) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p q_x (p (p q_H1 (p v k)) q_x)) q_v0) = (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k)) := congrArg (fun q => p (p q_x (p (p q_H1 (p v k)) q_x)) q) (pst0); let pst7 : (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0) = (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k)) := Eq.trans (pst5) (pst6); let pst8 : (p (p v k) (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst7); let pst9 : (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := Eq.trans (pst1) (pst8); let pst10 : v = (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := Eq.trans (peq1) (pst9); pst10)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p (p q_H1 (p v k)) q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs2h =>
        have qs3B := step_bound qs3
        cases qs3 with
        | raw =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg (fun q => p q (p (p q_x (p q_H2 q_x)) q_v0)) (pst0); let pst2 : (p (p q_x (p q_H2 q_x)) q_v0) = (p (p q_x (p q_H2 q_x)) (p v k)) := congrArg (fun q => p (p q_x (p q_H2 q_x)) q) (pst0); let pst3 : (p (p v k) (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x (p q_H2 q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x (p q_H2 q_x)) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs3h =>
          have qs4B := step_bound qs4
          cases qs4 with
          | raw =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 (p (p q_x q_H3) q_v0)) at e1
            have cyc : v = (p (p v k) (p (p q_x q_H3) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_x q_H3) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) q_v0)) := congrArg (fun q => p q (p (p q_x q_H3) q_v0)) (pst0); let pst2 : (p (p q_x q_H3) q_v0) = (p (p q_x q_H3) (p v k)) := congrArg (fun q => p (p q_x q_H3) q) (pst0); let pst3 : (p (p v k) (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_x q_H3) q_v0)) = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_x q_H3) (p v k))) := Eq.trans (peq1) (pst4); pst5)
            have hlt : sz v < sz (p (p v k) (p (p q_x q_H3) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_x q_H3) (p v k)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit qs4h =>
            have e0 := congrArg (fun q => q) ha
            change (p v k) = q_v0 at e0
            have e1 := congrArg (fun q => q) hb
            change v = (p q_v0 q_H4) at e1
            have cyc : v = (p (p v k) q_H4) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H4) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H4) = (p (p v k) q_H4) := congrArg (fun q => p q q_H4) (pst0); let pst2 : v = (p (p v k) q_H4) := Eq.trans (peq1) (pst1); pst2)
            have hlt : sz v < sz (p (p v k) q_H4) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H4)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 v2 H3 : CM)
    (s3 : Step H2 x H3) :
    ¬ ∃ o, Code x H3 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, q_H4, qs0, qs1, qs2, qs3, qs4, ha, hb, ho⟩
  have s3B := step_bound s3
  cases s3 with
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
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : x = q_v0 := ha; let peq2 : x = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H4 := Eq.trans (pst0) (peq2); let pst2 : q_H4 = q_v0 := Eq.symm (pst1); pst2)
            exact step_ne_second (by simpa only [he] using qs4)
  | hit s3h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs2hB := code_bounds qs2h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s3hB := code_bounds s3h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s3B := s3B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change x = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H3 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H3 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s3hB.2
                have ev : sz H3 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz x = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz x := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x v0 v1 v2 H4 : CM)
    (s4 : Step (p x H3) v0 H4) :
    ¬ ∃ o, Code v0 H4 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, q_H2, q_H3, q_H4, qs0, qs1, qs2, qs3, qs4, ha, hb, ho⟩
  have s4B := step_bound s4
  cases s4 with
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
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
          | hit qs3h =>
            have he : q_H4 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p x H3) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H4 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p x H3) := Eq.symm (peq1); let pst1 : v0 = (p x H3) := Eq.trans (peq0) (pst0); let pst2 : (p x H3) = v0 := Eq.symm (pst1); let pst3 : (p x H3) = q_H4 := Eq.trans (pst2) (peq2); let pst4 : q_H4 = (p x H3) := Eq.symm (pst3); let pst5 : (p x H3) = q_v0 := Eq.symm (pst0); let pst6 : q_H4 = q_v0 := Eq.trans (pst4) (pst5); pst6)
            exact step_ne_second (by simpa only [he] using qs4)
  | hit s4h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p (p (p q_v1 q_x) q_v2) q_v0) q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs2hB := code_bounds qs2h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p (p q_H0 q_v2) q_v0) q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have qs2B := step_bound qs2
        cases qs2 with
        | raw =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p (p q_H1 q_v0) q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
        | hit qs2h =>
          have qs3B := step_bound qs3
          cases qs3 with
          | raw =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x (p q_H2 q_x)) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
          | hit qs3h =>
            have qs4B := step_bound qs4
            cases qs4 with
            | raw =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 (p (p q_x q_H3) q_v0)) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H3) q_v0)) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 (p (p q_x q_H3) q_v0)) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 (p (p q_x q_H3) q_v0)) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
            | hit qs4h =>
              have hcB := code_bounds hc
              have s4hB := code_bounds s4h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have qs2hB := code_bounds qs2h
              have qs3hB := code_bounds qs3h
              have qs4hB := code_bounds qs4h
              have s4B := s4B
              have qs0B := qs0B
              have qs1B := qs1B
              have qs2B := qs2B
              have qs3B := qs3B
              have qs4B := qs4B
              have p0 := ha
              change v0 = q_v0 at p0
              have z0 := congrArg sz p0
              have p1 := hb
              change H4 = (p q_v0 q_H4) at p1
              have z1 := congrArg sz p1
              have p2 := ho
              change o = q_x at p2
              have z2 := congrArg sz p2
              have hx : sz q_v0 < sz (p q_v0 q_H4) := by
                have q := hcB.1
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have q1 : sz q_v0 < sz H4 := lt_of_eq_of_lt eu.symm q
                exact lt_of_lt_of_eq q1 ev
              have hy : sz (p q_v0 q_H4) < sz q_v0 := by
                have q := s4hB.2
                have ev : sz H4 = sz (p q_v0 q_H4) := congrArg sz (p1)
                have eu : sz v0 = sz q_v0 := congrArg sz (p0)
                have q1 : sz (p q_v0 q_H4) < sz v0 := lt_of_eq_of_lt ev.symm q
                exact lt_of_lt_of_eq q1 eu
              exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval v0 (eval v0 (eval (eval x (eval (eval (eval (eval v1 x) v2) v0) x)) v0))) := by
  let H0 := eval v1 x
  have e0a : v1 = v1 := by
    change v1 = v1
    rfl
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step v1 x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v1 x
  let H1 := eval (eval v1 x) v2
  have e1a : (eval v1 x) = H0 := by
    change H0 = H0
    rfl
  have e1b : v2 = v2 := by
    change v2 = v2
    rfl
  have s1 : Step H0 v2 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v1 x) v2
  let H2 := eval (eval (eval v1 x) v2) v0
  have e2a : (eval (eval v1 x) v2) = H1 := by
    change H1 = H1
    rfl
  have e2b : v0 = v0 := by
    change v0 = v0
    rfl
  have s2 : Step H1 v0 H2 := by
    rw [← e2a, ← e2b]
    exact eval_step (eval (eval v1 x) v2) v0
  let H3 := eval (eval (eval (eval v1 x) v2) v0) x
  have e3a : (eval (eval (eval v1 x) v2) v0) = H2 := by
    change H2 = H2
    rfl
  have e3b : x = x := by
    change x = x
    rfl
  have s3 : Step H2 x H3 := by
    rw [← e3a, ← e3b]
    exact eval_step (eval (eval (eval v1 x) v2) v0) x
  let H4 := eval (eval x (eval (eval (eval (eval v1 x) v2) v0) x)) v0
  have e4a : (eval x (eval (eval (eval (eval v1 x) v2) v0) x)) = (p x H3) := by
    change (eval x H3) = (p x H3)
    exact (eval_raw (nr0 x v0 v1 v2 H3 s3))
  have e4b : v0 = v0 := by
    change v0 = v0
    rfl
  have s4 : Step (p x H3) v0 H4 := by
    rw [← e4a, ← e4b]
    exact eval_step (eval x (eval (eval (eval (eval v1 x) v2) v0) x)) v0
  change x = (eval v0 (eval v0 H4))
  have rawEq : (eval v0 (eval v0 H4)) = (eval v0 (p v0 H4)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr1 x v0 v1 v2 H4 s4))
  exact (eval_hit (Code.law x v0 v1 v2 H0 H1 H2 H3 H4 s0 s1 s2 s3 s4)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1 v2
    exact CM.source_holds x v0 v1 v2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
