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
      (s0 : Step v0 (p (p x x) v1) H0)
      (s1 : Step v0 x H1) :
      Code (p (p H0 H1) v0) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 (p (p q_x q_x) q_v1) q_H0 ∧ Step q_v0 q_x q_H1 ∧ a = (p (p q_H0 q_H1) q_v0) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (R c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey a = b := by
  cases h <;> rfl
theorem code_key_unique {a b q o : CM} (h : Code a b o) (k : Code a q o) : b = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz b < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_right (p q_H0 q_H1) q_v0
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_right (p q_H0 q_H1) q_v0
  ·
    cases s0 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v1)) (sz_lt_p_right q_v0 (p (p q_x q_x) q_v1))) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) q_H1)) (sz_lt_p_left (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)
    | hit h0 =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v1)) (code_key_small h0)) (sz_lt_p_right (p q_H0 q_H1) q_v0)
theorem step_second_unique {a b q o : CM} (h : Step a b o) (k : Step a q o) : b = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := code_bounds hc
      have hp := sz_lt_p_left a b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
  | hit hc =>
    cases k with
    | raw =>
      have hb := code_bounds hc
      have hp := sz_lt_p_left a q
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
    | hit hk => exact code_key_unique hc hk
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, hs0, hs1, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_H0, r_q_H1, rs0, rs1, ka, kb, ko⟩
  have et := congrArg (fun z => (L (L z))) (ha.symm.trans ka)
  have eo := congrArg (fun z => (R z)) (ha.symm.trans ka)
  change q_H0 = r_q_H0 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs0
  have er := step_second_unique hs0 rs0
  have ex : q_x = r_q_x := congrArg (fun z => (L (L z))) er
  exact ho.trans (ex.trans ko.symm)
theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz b < sz (p o a) := by
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
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_x) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_x) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p q_H0 (p q_v0 q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p q_H0 (p q_v0 q_x)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H0 (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_H0 (p q_v0 q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      cases u0s0 with
      | raw =>
        have u0s1B := step_bound u0s1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) (p (p (p q_x q_x) q_v1) u0_x)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := Eq.symm (peq5); let pst7 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst6); let pst8 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst7); let pst9 := congrArg (fun q => p q u0_x) (pst6); let pst10 := congrArg (fun q => p (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) q) (pst9); let pst11 := Eq.trans (pst8) (pst10); let pst12 := Eq.trans (pst5) (pst11); let pst13 := Eq.symm (pst12); let pst14 := Eq.trans (pst13) (peq6); let pst15 := Eq.symm (pst14); pst15)
          have hlt : sz u0_x < sz (p (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) (p (p (p q_x q_x) q_v1) u0_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) u0_v1)) (sz_lt_p_right (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1))) (sz_lt_p_left (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) (p (p (p q_x q_x) q_v1) u0_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := Eq.symm (peq5); let pst7 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst6); let pst8 := congrArg (fun q => p q u0_H1) (pst7); let pst9 := Eq.trans (pst5) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq6); let pst12 := Eq.symm (pst11); pst12)
          have hlt : sz u0_x < sz (p (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) u0_v1)) (sz_lt_p_right (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1))) (sz_lt_p_left (p (p (p q_x q_x) q_v1) (p (p u0_x u0_x) u0_v1)) u0_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have u0s1B := step_bound u0s1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p u0_H0 (p (p (p q_x q_x) q_v1) u0_x)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := Eq.symm (peq5); let pst7 := congrArg (fun q => p q u0_x) (pst6); let pst8 := congrArg (fun q => p u0_H0 q) (pst7); let pst9 := Eq.trans (pst5) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq6); let pst12 := Eq.symm (pst11); pst12)
          have hlt : sz u0_x < sz (p u0_H0 (p (p (p q_x q_x) q_v1) u0_x)) := Nat.lt_trans (sz_lt_p_right (p (p q_x q_x) q_v1) u0_x) (sz_lt_p_right u0_H0 (p (p (p q_x q_x) q_v1) u0_x))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
          have u1s0B := step_bound u1s0
          cases u1s0 with
          | raw =>
            have u1s1B := step_bound u1s1
            cases u1s1 with
            | raw =>
              have cyc : q_x = (p (p q_x q_x) q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst5); let pst7 := congrArg (fun q => R q) (pst4); let pst8 := Eq.symm (peq5); let pst9 := Eq.trans (pst7) (pst8); let pst10 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst9); let pst11 := Eq.trans (pst6) (pst10); let pst12 := Eq.trans (pst2) (pst11); let pst13 := Eq.symm (pst12); let pst14 := Eq.trans (pst13) (peq7); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (peq8) (pst16); pst17)
              have hlt : sz q_x < sz (p (p q_x q_x) q_v1) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s1h =>
              have cyc : q_x = (p (p q_x q_x) q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst5); let pst7 := congrArg (fun q => R q) (pst4); let pst8 := Eq.symm (peq5); let pst9 := Eq.trans (pst7) (pst8); let pst10 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst9); let pst11 := Eq.trans (pst6) (pst10); let pst12 := Eq.trans (pst2) (pst11); let pst13 := Eq.symm (pst12); let pst14 := Eq.trans (pst13) (peq7); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (peq8) (pst16); pst17)
              have hlt : sz q_x < sz (p (p q_x q_x) q_v1) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u1s0h =>
            have u1s1B := step_bound u1s1
            cases u1s1 with
            | raw =>
              have cyc : q_x = (p (p q_x q_x) q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst5); let pst7 := congrArg (fun q => R q) (pst4); let pst8 := Eq.symm (peq5); let pst9 := Eq.trans (pst7) (pst8); let pst10 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst9); let pst11 := Eq.trans (pst6) (pst10); let pst12 := Eq.trans (pst2) (pst11); let pst13 := Eq.symm (pst12); let pst14 := Eq.trans (pst13) (peq7); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (peq8) (pst16); pst17)
              have hlt : sz q_x < sz (p (p q_x q_x) q_v1) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s1h =>
              have cyc : q_x = (p (p q_x q_x) q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq4); let pst5 := congrArg (fun q => L q) (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst5); let pst7 := congrArg (fun q => R q) (pst4); let pst8 := Eq.symm (peq5); let pst9 := Eq.trans (pst7) (pst8); let pst10 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst9); let pst11 := Eq.trans (pst6) (pst10); let pst12 := Eq.trans (pst2) (pst11); let pst13 := Eq.symm (pst12); let pst14 := Eq.trans (pst13) (peq7); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (peq8) (pst16); pst17)
              have hlt : sz q_x < sz (p (p q_x q_x) q_v1) := Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw => exact code_no_pair_left a b
  | hit sh =>
    rintro ⟨u, hk⟩
    have ho := (code_bounds sh).2
    have ha := (code_bounds hk).1
    omega
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_x) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x))) (sz_lt_p_left (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_x) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) q_H1)) (sz_lt_p_left (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_H0 (p q_v0 q_x)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_H0 (p q_v0 q_x)) q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 (p q_v0 q_x)) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_H0 (p q_v0 q_x))) (sz_lt_p_left (p q_H0 (p q_v0 q_x)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_H0 q_H1) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_H0 q_H1) q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 q_H1) q_v0) := sz_lt_p_right (p q_H0 q_H1) q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p x x) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_x) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_x) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_x q_x) q_v1)) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = (p q_H0 (p q_v0 q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = q_v0 at e2
      have cyc : q_v0 = (p q_H0 (p q_v0 q_x)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H0 (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_H0 (p q_v0 q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have epa : (p x x) = (p (p q_H0 q_H1) (p q_H0 q_H1)) := Eq.trans (congrArg (fun q => p q x) (congrArg (fun q => (L q)) (ha))) (congrArg (fun q => p (p q_H0 q_H1) q) (congrArg (fun q => (L q)) (ha)))
      have epb : v1 = (p q_H0 q_H1) := Eq.trans (hb) (Eq.symm (Eq.trans (Eq.symm (congrArg (fun q => (L q)) (ha))) (congrArg (fun q => (R q)) (ha))))
      apply code_no_pair_left (p q_H0 q_H1) (p q_H0 q_H1)
      exact ⟨_, by simpa only [epa, epb] using hc⟩
theorem nr2 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 (p (p x x) v1) H0)
    (s1 : Step v0 x H1) :
    ¬ ∃ o, Code H0 H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have s1B := step_bound s1
    have s1N := step_no_first s1
    cases s1 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v0 = (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change (p (p x x) v1) = q_v0 at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 x) = q_v0 at e2
          have cyc : x = (p (p (p x x) v1) (p (p q_x q_x) q_v1)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q (p q_v0 q_x)) (pst1); let pst3 := congrArg (fun q => p q q_x) (pst0); let pst4 := congrArg (fun q => p (p (p (p x x) v1) (p (p q_x q_x) q_v1)) q) (pst3); let pst5 := Eq.trans (pst2) (pst4); let pst6 := Eq.trans (peq0) (pst5); let pst7 := congrArg (fun q => p q x) (pst6); let pst8 := Eq.symm (pst7); let pst9 := Eq.trans (pst8) (peq2); let pst10 := Eq.trans (pst9) (pst0); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := congrArg (fun q => L q) (pst11); let pst13 := Eq.symm (pst12); pst13)
          have hlt : sz x < sz (p (p (p x x) v1) (p (p q_x q_x) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) (p (p q_x q_x) q_v1))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L q)) ha
          change v0 = (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change (p (p x x) v1) = q_v0 at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 x) = q_v0 at e2
          have cyc : x = (p (p (p x x) v1) (p (p q_x q_x) q_v1)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := congrArg (fun q => p q x) (pst3); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq2); let pst7 := Eq.trans (pst6) (pst0); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := Eq.symm (pst9); pst10)
          have hlt : sz x < sz (p (p (p x x) v1) (p (p q_x q_x) q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) (p (p q_x q_x) q_v1))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v0 = (p q_H0 (p q_v0 q_x)) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change (p (p x x) v1) = q_v0 at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 x) = q_v0 at e2
          have cyc : x = (p (p (p x x) v1) q_x) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q q_x) (pst0); let pst2 := congrArg (fun q => p q_H0 q) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := congrArg (fun q => p q x) (pst3); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq2); let pst7 := Eq.trans (pst6) (pst0); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); pst10)
          have hlt : sz x < sz (p (p (p x x) v1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) q_x)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have he : u0_H0 = u0_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q x) (peq0); let pst2 := Eq.symm (pst1); let pst3 := Eq.trans (pst2) (peq2); let pst4 := Eq.trans (pst3) (pst0); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := congrArg (fun q => p q x) (pst5); let pst7 := congrArg (fun q => p v1 q) (pst5); let pst8 := Eq.trans (pst6) (pst7); let pst9 := congrArg (fun q => p q v1) (pst8); let pst10 := Eq.trans (pst0) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq4); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := congrArg (fun q => R q) (pst13); let pst17 := Eq.trans (pst15) (pst16); let pst18 := Eq.trans (pst14) (pst17); let pst19 := Eq.symm (pst18); let pst20 := congrArg (fun q => R q) (pst12); let pst21 := Eq.trans (pst19) (pst20); let pst22 := Eq.symm (peq5); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst17) (pst23); let pst25 := Eq.symm (pst22); let pst26 := Eq.trans (pst24) (pst25); pst26)
          exact step_ne_first (by simpa only [he] using u0s0)
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have cyc : x = (p (p x x) (p (p u0_x u0_x) u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q (p q_v0 q_x)) (pst1); let pst3 := congrArg (fun q => p q q_x) (pst0); let pst4 := congrArg (fun q => p (p (p (p x x) v1) (p (p q_x q_x) q_v1)) q) (pst3); let pst5 := Eq.trans (pst2) (pst4); let pst6 := Eq.trans (peq0) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq4); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => L q) (pst9); let pst11 := congrArg (fun q => R q) (pst10); let pst12 := congrArg (fun q => p (p x x) q) (pst11); let pst13 := congrArg (fun q => p q q_x) (pst12); let pst14 := congrArg (fun q => R q) (pst9); let pst15 := congrArg (fun q => L q) (pst10); let pst16 := Eq.symm (pst15); let pst17 := congrArg (fun q => p q u0_x) (pst16); let pst18 := Eq.trans (pst14) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := congrArg (fun q => p (p (p x x) (p (p u0_x u0_x) u0_v1)) q) (pst20); let pst22 := Eq.trans (pst13) (pst21); let pst23 := Eq.symm (pst22); let pst24 := congrArg (fun q => R q) (pst8); let pst25 := Eq.trans (pst23) (pst24); let pst26 := Eq.trans (pst25) (pst16); let pst27 := congrArg (fun q => L q) (pst26); let pst28 := Eq.symm (pst27); pst28)
              have hlt : sz x < sz (p (p x x) (p (p u0_x u0_x) u0_v1)) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p (p u0_x u0_x) u0_v1))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : x = (p (p x x) (p (p u0_x u0_x) u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q (p q_v0 q_x)) (pst1); let pst3 := congrArg (fun q => p q q_x) (pst0); let pst4 := congrArg (fun q => p (p (p (p x x) v1) (p (p q_x q_x) q_v1)) q) (pst3); let pst5 := Eq.trans (pst2) (pst4); let pst6 := Eq.trans (peq0) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq4); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => L q) (pst9); let pst11 := congrArg (fun q => R q) (pst10); let pst12 := congrArg (fun q => p (p x x) q) (pst11); let pst13 := congrArg (fun q => p q q_x) (pst12); let pst14 := Eq.symm (pst13); let pst15 := congrArg (fun q => R q) (pst8); let pst16 := Eq.trans (pst14) (pst15); let pst17 := congrArg (fun q => L q) (pst10); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst16) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); pst21)
              have hlt : sz x < sz (p (p x x) (p (p u0_x u0_x) u0_v1)) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) (p (p u0_x u0_x) u0_v1))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have cyc : x = (p (p (p x x) v1) (p (p x x) v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q (p q_v0 q_x)) (pst1); let pst3 := congrArg (fun q => p q q_x) (pst0); let pst4 := congrArg (fun q => p (p (p (p x x) v1) (p (p q_x q_x) q_v1)) q) (pst3); let pst5 := Eq.trans (pst2) (pst4); let pst6 := Eq.trans (peq0) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq4); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => R q) (pst9); let pst11 := congrArg (fun q => L q) (pst10); let pst12 := Eq.symm (pst11); let pst13 := congrArg (fun q => R q) (pst8); let pst14 := Eq.trans (pst13) (pst12); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := Eq.symm (pst15); let pst17 := congrArg (fun q => p q q_x) (pst16); let pst18 := congrArg (fun q => p (p (p x x) v1) q) (pst16); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (pst12) (pst19); let pst21 := Eq.trans (peq5) (pst20); pst21)
              have hlt : sz x < sz (p (p (p x x) v1) (p (p x x) v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) (p (p x x) v1))
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : x = (p (p (p x x) v1) q_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q (p q_v0 q_x)) (pst1); let pst3 := congrArg (fun q => p q q_x) (pst0); let pst4 := congrArg (fun q => p (p (p (p x x) v1) (p (p q_x q_x) q_v1)) q) (pst3); let pst5 := Eq.trans (pst2) (pst4); let pst6 := Eq.trans (peq0) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq4); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (peq5) (pst10); pst11)
              have hlt : sz x < sz (p (p (p x x) v1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) q_x)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have cyc : x = (p x x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => L q) (pst5); let pst7 := congrArg (fun q => L q) (pst6); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (peq5) (pst9); pst10)
              have hlt : sz x < sz (p x x) := sz_lt_p_left x x
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : x = (p x x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => L q) (pst5); let pst7 := congrArg (fun q => L q) (pst6); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (peq5) (pst9); pst10)
              have hlt : sz x < sz (p x x) := sz_lt_p_left x x
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p u1_x u1_x) u1_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => L q) (pst5); let pst7 := congrArg (fun q => R q) (pst6); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (peq5) (pst9); let pst11 := congrArg (fun q => p q x) (pst10); let pst12 := congrArg (fun q => p (p q_x q_x) q) (pst10); let pst13 := Eq.trans (pst11) (pst12); let pst14 := congrArg (fun q => p q v1) (pst13); let pst15 := Eq.trans (pst0) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq7); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := congrArg (fun q => R q) (pst19); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst20) (pst23); let pst25 := congrArg (fun q => p q q_x) (pst24); let pst26 := Eq.trans (pst20) (pst23); let pst27 := congrArg (fun q => p (p (p u1_x u1_x) u1_v1) q) (pst26); let pst28 := Eq.trans (pst25) (pst27); let pst29 := Eq.symm (pst28); let pst30 := congrArg (fun q => R q) (pst18); let pst31 := Eq.trans (pst29) (pst30); let pst32 := congrArg (fun q => p q u1_x) (pst23); let pst33 := Eq.trans (pst31) (pst32); let pst34 := congrArg (fun q => R q) (pst33); let pst35 := Eq.symm (pst34); pst35)
                  have hlt : sz u1_x < sz (p (p u1_x u1_x) u1_v1) := Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) u1_v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p (p u1_x u1_x) u1_v1) (p (p u1_x u1_x) u1_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := congrArg (fun q => L q) (pst5); let pst8 := congrArg (fun q => R q) (pst7); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst6) (pst10); let pst12 := Eq.trans (peq5) (pst10); let pst13 := congrArg (fun q => p q x) (pst12); let pst14 := congrArg (fun q => p (p q_x q_x) q) (pst12); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => p q v1) (pst15); let pst17 := Eq.trans (pst0) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst18) (peq7); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := congrArg (fun q => L q) (pst20); let pst22 := congrArg (fun q => L q) (pst21); let pst23 := Eq.symm (pst22); let pst24 := congrArg (fun q => R q) (pst21); let pst25 := Eq.trans (pst23) (pst24); let pst26 := Eq.trans (pst22) (pst25); let pst27 := congrArg (fun q => p q q_x) (pst26); let pst28 := Eq.trans (pst22) (pst25); let pst29 := congrArg (fun q => p (p (p u1_x u1_x) u1_v1) q) (pst28); let pst30 := Eq.trans (pst27) (pst29); let pst31 := Eq.trans (pst11) (pst30); let pst32 := Eq.symm (pst31); let pst33 := Eq.trans (pst32) (peq9); let pst34 := Eq.symm (pst33); pst34)
                  have hlt : sz u1_x < sz (p (p (p u1_x u1_x) u1_v1) (p (p u1_x u1_x) u1_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_x) (sz_lt_p_left (p u1_x u1_x) u1_v1)) (sz_lt_p_left (p (p u1_x u1_x) u1_v1) (p (p u1_x u1_x) u1_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p u1_x u1_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := congrArg (fun q => L q) (pst5); let pst8 := congrArg (fun q => R q) (pst7); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst6) (pst10); let pst12 := Eq.trans (peq5) (pst10); let pst13 := congrArg (fun q => p q x) (pst12); let pst14 := congrArg (fun q => p (p q_x q_x) q) (pst12); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => p q v1) (pst15); let pst17 := Eq.trans (pst0) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst18) (peq7); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := congrArg (fun q => R q) (pst20); let pst22 := congrArg (fun q => L q) (pst21); let pst23 := Eq.symm (pst22); let pst24 := congrArg (fun q => R q) (pst21); let pst25 := Eq.trans (pst23) (pst24); let pst26 := Eq.trans (pst22) (pst25); let pst27 := congrArg (fun q => p q q_x) (pst26); let pst28 := Eq.trans (pst22) (pst25); let pst29 := congrArg (fun q => p u1_x q) (pst28); let pst30 := Eq.trans (pst27) (pst29); let pst31 := Eq.trans (pst11) (pst30); let pst32 := Eq.symm (pst31); let pst33 := Eq.trans (pst32) (peq9); let pst34 := Eq.symm (pst33); pst34)
                  have hlt : sz u1_x < sz (p u1_x u1_x) := sz_lt_p_left u1_x u1_x
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  rcases code_shape u0s0h with ⟨u2_x, u2_v0, u2_v1, u2_H0, u2_H1, u2s0, u2s1, u2a, u2b, u2o⟩
                  have u2s0B := step_bound u2s0
                  have u2s0N := step_no_first u2s0
                  cases u2s0 with
                  | raw =>
                    have u2s1B := step_bound u2s1
                    have u2s1N := step_no_first u2s1
                    cases u2s1 with
                    | raw =>
                      have cyc : u2_v0 = (p (p u2_v0 (p (p u2_x u2_x) u2_v1)) (p u2_v0 u2_x)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let peq10 := u2a; let peq11 := u2b; let peq12 := u2o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => L q) (pst5); let pst7 := congrArg (fun q => R q) (pst6); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => p q q_x) (peq8); let pst11 := congrArg (fun q => p u1_v0 q) (peq8); let pst12 := Eq.trans (pst10) (pst11); let pst13 := Eq.trans (pst9) (pst12); let pst14 := Eq.symm (pst13); let pst15 := Eq.trans (pst14) (peq10); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); pst20)
                      have hlt : sz u2_v0 < sz (p (p u2_v0 (p (p u2_x u2_x) u2_v1)) (p u2_v0 u2_x)) := Nat.lt_trans (sz_lt_p_left u2_v0 (p (p u2_x u2_x) u2_v1)) (sz_lt_p_left (p u2_v0 (p (p u2_x u2_x) u2_v1)) (p u2_v0 u2_x))
                      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                    | hit u2s1h =>
                      have cyc : u2_v0 = (p (p u2_v0 (p (p u2_x u2_x) u2_v1)) u2_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let peq10 := u2a; let peq11 := u2b; let peq12 := u2o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => L q) (pst5); let pst7 := congrArg (fun q => R q) (pst6); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => p q q_x) (peq8); let pst11 := congrArg (fun q => p u1_v0 q) (peq8); let pst12 := Eq.trans (pst10) (pst11); let pst13 := Eq.trans (pst9) (pst12); let pst14 := Eq.symm (pst13); let pst15 := Eq.trans (pst14) (peq10); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); pst20)
                      have hlt : sz u2_v0 < sz (p (p u2_v0 (p (p u2_x u2_x) u2_v1)) u2_H1) := Nat.lt_trans (sz_lt_p_left u2_v0 (p (p u2_x u2_x) u2_v1)) (sz_lt_p_left (p u2_v0 (p (p u2_x u2_x) u2_v1)) u2_H1)
                      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                  | hit u2s0h =>
                    have u2s1B := step_bound u2s1
                    have u2s1N := step_no_first u2s1
                    cases u2s1 with
                    | raw =>
                      have cyc : u2_v0 = (p u2_H0 (p u2_v0 u2_x)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let peq10 := u2a; let peq11 := u2b; let peq12 := u2o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => L q) (pst5); let pst7 := congrArg (fun q => R q) (pst6); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => p q q_x) (peq8); let pst11 := congrArg (fun q => p u1_v0 q) (peq8); let pst12 := Eq.trans (pst10) (pst11); let pst13 := Eq.trans (pst9) (pst12); let pst14 := Eq.symm (pst13); let pst15 := Eq.trans (pst14) (peq10); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); pst20)
                      have hlt : sz u2_v0 < sz (p u2_H0 (p u2_v0 u2_x)) := Nat.lt_trans (sz_lt_p_left u2_v0 u2_x) (sz_lt_p_right u2_H0 (p u2_v0 u2_x))
                      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                    | hit u2s1h =>
                      have cyc : u2_H0 = (p (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1)) (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1))) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let peq10 := u2a; let peq11 := u2b; let peq12 := u2o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (peq2) (pst0); let pst2 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst3 := congrArg (fun q => p q q_H1) (pst2); let pst4 := Eq.trans (peq0) (pst3); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq4); let pst7 := congrArg (fun q => L q) (pst6); let pst8 := congrArg (fun q => R q) (pst7); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (peq5) (pst10); let pst12 := congrArg (fun q => p q x) (pst11); let pst13 := congrArg (fun q => p (p q_x q_x) q) (pst11); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q v1) (pst14); let pst16 := Eq.trans (pst1) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq6); let pst19 := Eq.symm (pst18); let pst20 := congrArg (fun q => p q q_x) (peq8); let pst21 := congrArg (fun q => p u1_v0 q) (peq8); let pst22 := Eq.trans (pst20) (pst21); let pst23 := Eq.trans (pst10) (pst22); let pst24 := Eq.symm (pst23); let pst25 := Eq.trans (pst24) (peq10); let pst26 := congrArg (fun q => L q) (pst25); let pst27 := Eq.trans (peq8) (pst26); let pst28 := congrArg (fun q => p q q_x) (pst27); let pst29 := Eq.trans (peq8) (pst26); let pst30 := congrArg (fun q => p (p u2_H0 u2_H1) q) (pst29); let pst31 := Eq.trans (pst28) (pst30); let pst32 := congrArg (fun q => p q (p q_x q_x)) (pst31); let pst33 := Eq.trans (peq8) (pst26); let pst34 := congrArg (fun q => p q q_x) (pst33); let pst35 := Eq.trans (peq8) (pst26); let pst36 := congrArg (fun q => p (p u2_H0 u2_H1) q) (pst35); let pst37 := Eq.trans (pst34) (pst36); let pst38 := congrArg (fun q => p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) q) (pst37); let pst39 := Eq.trans (pst32) (pst38); let pst40 := congrArg (fun q => p q v1) (pst39); let pst41 := congrArg (fun q => p q x) (pst11); let pst42 := congrArg (fun q => p (p q_x q_x) q) (pst11); let pst43 := Eq.trans (pst41) (pst42); let pst44 := congrArg (fun q => p q v1) (pst43); let pst45 := Eq.trans (pst0) (pst44); let pst46 := Eq.symm (pst45); let pst47 := Eq.trans (pst46) (peq7); let pst48 := congrArg (fun q => R q) (pst47); let pst49 := Eq.trans (pst48) (pst26); let pst50 := congrArg (fun q => p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) q) (pst49); let pst51 := Eq.trans (pst40) (pst50); let pst52 := Eq.trans (pst19) (pst51); let pst53 := congrArg (fun q => p q u0_x) (pst52); let pst54 := Eq.trans (peq8) (pst26); let pst55 := congrArg (fun q => p q q_x) (pst54); let pst56 := Eq.trans (peq8) (pst26); let pst57 := congrArg (fun q => p (p u2_H0 u2_H1) q) (pst56); let pst58 := Eq.trans (pst55) (pst57); let pst59 := congrArg (fun q => p q (p q_x q_x)) (pst58); let pst60 := Eq.trans (peq8) (pst26); let pst61 := congrArg (fun q => p q q_x) (pst60); let pst62 := Eq.trans (peq8) (pst26); let pst63 := congrArg (fun q => p (p u2_H0 u2_H1) q) (pst62); let pst64 := Eq.trans (pst61) (pst63); let pst65 := congrArg (fun q => p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) q) (pst64); let pst66 := Eq.trans (pst59) (pst65); let pst67 := congrArg (fun q => p q v1) (pst66); let pst68 := Eq.trans (pst48) (pst26); let pst69 := congrArg (fun q => p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) q) (pst68); let pst70 := Eq.trans (pst67) (pst69); let pst71 := Eq.trans (pst19) (pst70); let pst72 := congrArg (fun q => p (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1)) q) (pst71); let pst73 := Eq.trans (pst53) (pst72); let pst74 := congrArg (fun q => p q u0_v1) (pst73); let pst75 := Eq.symm (pst74); let pst76 := Eq.trans (pst75) (peq11); let pst77 := Eq.symm (pst26); let pst78 := congrArg (fun q => R q) (pst25); let pst79 := Eq.trans (pst77) (pst78); let pst80 := Eq.symm (pst79); let pst81 := Eq.trans (pst76) (pst80); let pst82 := congrArg (fun q => L q) (pst81); let pst83 := Eq.symm (pst82); pst83)
                      have hlt : sz u2_H0 < sz (p (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1)) (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u2_H0 u2_H1) (sz_lt_p_left (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (sz_lt_p_left (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)))) (sz_lt_p_left (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1))) (sz_lt_p_left (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1)) (p (p (p (p u2_H0 u2_H1) (p u2_H0 u2_H1)) (p (p u2_H0 u2_H1) (p u2_H0 u2_H1))) (p u2_H0 u2_H1)))
                      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q (p (p q_x q_x) q_v1)) (pst0); let pst2 := congrArg (fun q => p q q_H1) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := Eq.symm (pst6); pst7)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (peq2) (pst0); let pst2 := congrArg (fun q => p q x) (peq5); let pst3 := congrArg (fun q => p u0_v0 q) (peq5); let pst4 := Eq.trans (pst2) (pst3); let pst5 := congrArg (fun q => p q v1) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => p q x) (peq5); let pst11 := congrArg (fun q => p u0_v0 q) (peq5); let pst12 := Eq.trans (pst10) (pst11); let pst13 := congrArg (fun q => p q v1) (pst12); let pst14 := Eq.trans (pst0) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst9) (pst15); pst16)
              apply qs1N
              refine ⟨u0_H1, ?_⟩
              simpa only [ena, enb] using u0s1h
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have cyc : x = (p (p (p x x) v1) q_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q q_x) (pst0); let pst2 := congrArg (fun q => p q_H0 q) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (peq5) (pst7); pst8)
              have hlt : sz x < sz (p (p (p x x) v1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) q_x)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : x = (p (p (p x x) v1) q_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q q_x) (pst0); let pst2 := congrArg (fun q => p q_H0 q) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (peq5) (pst7); pst8)
              have hlt : sz x < sz (p (p (p x x) v1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) q_x)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have cyc : x = (p (p (p x x) v1) q_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q q_x) (pst0); let pst2 := congrArg (fun q => p q_H0 q) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (peq5) (pst7); pst8)
              have hlt : sz x < sz (p (p (p x x) v1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) q_x)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : x = (p (p (p x x) v1) q_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q q_x) (pst0); let pst2 := congrArg (fun q => p q_H0 q) (pst1); let pst3 := Eq.trans (peq0) (pst2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst4) (peq4); let pst6 := congrArg (fun q => R q) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (peq5) (pst7); pst8)
              have hlt : sz x < sz (p (p (p x x) v1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)) (sz_lt_p_left (p (p x x) v1) q_x)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have hcB := code_bounds hc
              have s1hB := code_bounds s1h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have s0B := s0B
              have s1B := s1B
              have qs0B := qs0B
              have qs1B := qs1B
              have u0s0B := u0s0B
              have u0s1B := u0s1B
              have p0 := congrArg (fun q => (L q)) (ha)
              change v0 = (p q_H0 q_H1) at p0
              have z0 := congrArg sz p0
              have p1 := congrArg (fun q => (R q)) (ha)
              change (p (p x x) v1) = q_v0 at p1
              have z1 := congrArg sz p1
              have p2 := hb
              change H1 = q_v0 at p2
              have z2 := congrArg sz p2
              have p3 := ho
              change o = q_x at p3
              have z3 := congrArg sz p3
              have p4 := u0a
              change v0 = (p (p (p u0_v0 (p (p u0_x u0_x) u0_v1)) (p u0_v0 u0_x)) u0_v0) at p4
              have z4 := congrArg sz p4
              have p5 := u0b
              change x = u0_v0 at p5
              have z5 := congrArg sz p5
              have p6 := u0o
              change H1 = u0_x at p6
              have z6 := congrArg sz p6
              simp only [L, R, U, sz] at hcB s1hB qs0hB qs1hB s0B s1B qs0B qs1B u0s0B u0s1B z0 z1 z2 z3 z4 z5 z6
              omega
            | hit u0s1h =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => R q) (pst1); let pst3 := Eq.symm (pst2); pst3)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (peq2) (pst0); let pst2 := congrArg (fun q => p q x) (peq5); let pst3 := congrArg (fun q => p u0_v0 q) (peq5); let pst4 := Eq.trans (pst2) (pst3); let pst5 := congrArg (fun q => p q v1) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => p q x) (peq5); let pst11 := congrArg (fun q => p u0_v0 q) (peq5); let pst12 := Eq.trans (pst10) (pst11); let pst13 := congrArg (fun q => p q v1) (pst12); let pst14 := Eq.trans (pst0) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst9) (pst15); pst16)
              apply qs1N
              refine ⟨u0_H1, ?_⟩
              simpa only [ena, enb] using u0s1h
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have hcB := code_bounds hc
              have s1hB := code_bounds s1h
              have qs0hB := code_bounds qs0h
              have qs1hB := code_bounds qs1h
              have u0s0hB := code_bounds u0s0h
              have s0B := s0B
              have s1B := s1B
              have qs0B := qs0B
              have qs1B := qs1B
              have u0s0B := u0s0B
              have u0s1B := u0s1B
              have p0 := congrArg (fun q => (L q)) (ha)
              change v0 = (p q_H0 q_H1) at p0
              have z0 := congrArg sz p0
              have p1 := congrArg (fun q => (R q)) (ha)
              change (p (p x x) v1) = q_v0 at p1
              have z1 := congrArg sz p1
              have p2 := hb
              change H1 = q_v0 at p2
              have z2 := congrArg sz p2
              have p3 := ho
              change o = q_x at p3
              have z3 := congrArg sz p3
              have p4 := u0a
              change v0 = (p (p u0_H0 (p u0_v0 u0_x)) u0_v0) at p4
              have z4 := congrArg sz p4
              have p5 := u0b
              change x = u0_v0 at p5
              have z5 := congrArg sz p5
              have p6 := u0o
              change H1 = u0_x at p6
              have z6 := congrArg sz p6
              simp only [L, R, U, sz] at hcB s1hB qs0hB qs1hB u0s0hB s0B s1B qs0B qs1B u0s0B u0s1B z0 z1 z2 z3 z4 z5 z6
              omega
            | hit u0s1h =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => R q) (pst1); let pst3 := Eq.symm (pst2); pst3)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (peq2) (pst0); let pst2 := congrArg (fun q => p q x) (peq5); let pst3 := congrArg (fun q => p u0_v0 q) (peq5); let pst4 := Eq.trans (pst2) (pst3); let pst5 := congrArg (fun q => p q v1) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => p q x) (peq5); let pst11 := congrArg (fun q => p u0_v0 q) (peq5); let pst12 := Eq.trans (pst10) (pst11); let pst13 := congrArg (fun q => p q v1) (pst12); let pst14 := Eq.trans (pst0) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst9) (pst15); pst16)
              apply qs1N
              refine ⟨u0_H1, ?_⟩
              simpa only [ena, enb] using u0s1h
  | hit s0h =>
    have s1B := step_bound s1
    have s1N := step_no_first s1
    cases s1 with
    | raw =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change H0 = (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 x) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [L, R, U, sz] at hcB s0hB s0B s1B qs0B qs1B z0 z1 z2
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := ha
          change H0 = (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 x) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [L, R, U, sz] at hcB s0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2
          omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
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
          change H0 = (p (p q_H0 (p q_v0 q_x)) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 x) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [L, R, U, sz] at hcB s0hB qs0hB s0B s1B qs0B qs1B z0 z1 z2
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
          change H0 = (p (p q_H0 q_H1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 x) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2
          omega
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => R q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => R q) (pst22); let pst24 := Eq.symm (pst23); let pst25 := Eq.trans (peq7) (pst24); pst25)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => R q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => R q) (pst22); let pst24 := Eq.symm (pst23); let pst25 := Eq.trans (peq7) (pst24); pst25)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p (p q_v0 (p (p q_x q_x) q_v1)) q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => R q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => R q) (pst22); let pst24 := Eq.symm (pst23); let pst25 := Eq.trans (peq7) (pst24); pst25)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 (p q_v0 q_x)) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 (p q_v0 q_x)) q_v0) (p (p q_H0 (p q_v0 q_x)) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 (p q_v0 q_x)) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
          have u0s0B := step_bound u0s0
          have u0s0N := step_no_first u0s0
          cases u0s0 with
          | raw =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => L q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => L q) (pst22); let pst24 := congrArg (fun q => R q) (pst23); let pst25 := congrArg (fun q => L q) (pst24); let pst26 := Eq.symm (pst25); let pst27 := Eq.trans (peq7) (pst26); pst27)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q (p u0_v0 u0_x)) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst0); let pst13 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) q) (pst14); let pst16 := Eq.trans (pst11) (pst15); let pst17 := congrArg (fun q => p q u0_v0) (pst16); let pst18 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.trans (peq3) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (pst21) (peq6); let pst23 := congrArg (fun q => R q) (pst22); let pst24 := Eq.symm (pst23); let pst25 := Eq.trans (peq7) (pst24); pst25)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => L q) (pst18); let pst20 := congrArg (fun q => L q) (pst19); let pst21 := Eq.symm (pst20); let pst22 := Eq.trans (peq7) (pst21); pst22)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q (p (p u0_x u0_x) u0_v1)) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p q u0_x) (pst4); let pst6 := congrArg (fun q => p (p (p q_H0 q_H1) q_v0) q) (pst4); let pst7 := Eq.trans (pst5) (pst6); let pst8 := congrArg (fun q => p q u0_v1) (pst7); let pst9 := congrArg (fun q => p (p (p x x) v1) q) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q u0_H1) (pst10); let pst12 := congrArg (fun q => p q u0_v0) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p x x) v1) (p (p (p (p q_H0 q_H1) q_v0) (p (p q_H0 q_H1) q_v0)) u0_v1)) u0_H1) q) (pst0); let pst14 := Eq.trans (pst12) (pst13); let pst15 := Eq.trans (peq3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := congrArg (fun q => R q) (pst17); let pst19 := Eq.symm (pst18); let pst20 := Eq.trans (peq7) (pst19); pst20)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (peq7) (pst17); pst18)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p q u0_x) (pst0); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p x x) v1) q) (pst4); let pst6 := Eq.trans (pst1) (pst5); let pst7 := congrArg (fun q => p u0_H0 q) (pst6); let pst8 := congrArg (fun q => p q u0_v0) (pst7); let pst9 := congrArg (fun q => p (p u0_H0 (p (p (p x x) v1) (p (p q_H0 q_H1) q_v0))) q) (pst0); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (peq7) (pst15); pst16)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape s1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : x = (p (p x x) v1) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq4); let pst1 := congrArg (fun q => p (p u0_H0 u0_H1) q) (pst0); let pst2 := Eq.trans (peq3) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq6); let pst5 := congrArg (fun q => R q) (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (peq7) (pst6); pst7)
                  have hlt : sz x < sz (p (p x x) v1) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_left (p x x) v1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 (p (p x x) v1) H0)
    (s1 : Step v0 x H1) :
    ¬ ∃ o, Code (p H0 H1) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have he : H1 = v0 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.trans (peq0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (peq2) (pst3); pst4)
    exact step_ne_first (by simpa only [he] using s1)
  | hit s0h =>
    have he : H1 = v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let pst0 := Eq.symm (peq2); let pst1 := Eq.trans (peq1) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 (eval (eval x x) v1)) (eval v0 x)) v0) v0) := by
  let H0 := eval v0 (eval (eval x x) v1)
  have e0a : v0 = v0 := by
    change v0 = v0
    rfl
  have e0b : (eval (eval x x) v1) = (p (p x x) v1) := by
    change (eval (eval x x) v1) = (p (p x x) v1)
    calc
      (eval (eval x x) v1) = (eval (p x x) v1) := congrArg (fun q => (eval q v1)) (eval_raw (nr0 x v0 v1))
      _ = (p (p x x) v1) := (eval_raw (nr1 x v0 v1))
  have s0 : Step v0 (p (p x x) v1) H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v0 (eval (eval x x) v1)
  let H1 := eval v0 x
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : x = x := by
    change x = x
    rfl
  have s1 : Step v0 x H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 x
  change x = (eval (eval (eval H0 H1) v0) v0)
  have rawEq : (eval (eval (eval H0 H1) v0) v0) = (eval (p (p H0 H1) v0) v0) := by
    calc
      (eval (eval (eval H0 H1) v0) v0) = (eval (eval (p H0 H1) v0) v0) := congrArg (fun q => (eval (eval q v0) v0)) (eval_raw (nr2 x v0 v1 H0 H1 s0 s1))
      _ = (eval (p (p H0 H1) v0) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr3 x v0 v1 H0 H1 s0 s1))
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
