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
      (s0 : Step x v1 H0)
      (s1 : Step v0 (p H0 (p x x)) H1) :
      Code (p H1 v0) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v1 q_H0 ∧ Step q_v0 (p q_H0 (p q_x q_x)) q_H1 ∧ a = (p q_H1 q_v0) ∧ b = q_v0 ∧ o = q_x := by
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
  exact sz_lt_p_right q_H1 q_v0
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_right q_H1 q_v0
  ·
    cases s1 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right q_H0 (p q_x q_x))) (sz_lt_p_right q_v0 (p q_H0 (p q_x q_x)))) (sz_lt_p_left (p q_v0 (p q_H0 (p q_x q_x))) q_v0)
    | hit h1 =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right q_H0 (p q_x q_x))) (code_key_small h1)) (sz_lt_p_right q_H1 q_v0)
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
  have et := congrArg (fun z => (L z)) (ha.symm.trans ka)
  have eo := congrArg (fun z => (R z)) (ha.symm.trans ka)
  change q_H1 = r_q_H1 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs1
  have er := step_second_unique hs1 rs1
  have ex : q_x = r_q_x := congrArg (fun z => (L (R z))) er
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
    have he : q_H1 = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); pst1)
    exact step_ne_first (by simpa only [he] using qs1)
  | hit qs0h =>
    have he : q_H1 = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); pst1)
    exact step_ne_first (by simpa only [he] using qs1)
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
      change x = (p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_v1) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p q_x q_v1) (p q_x q_x))) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_H1 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_v0 (p q_H0 (p q_x q_x))) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_v0 (p q_H0 (p q_x q_x))) q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_H0 (p q_x q_x))) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_H0 (p q_x q_x))) (sz_lt_p_left (p q_v0 (p q_H0 (p q_x q_x))) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_H1 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 := e0; let peq1 := e1; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq1); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code H0 (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
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
        change x = (p q_v0 (p (p q_x q_v1) (p q_x q_x))) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) (p q_v0 (p (p q_x q_v1) (p q_x q_x)))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) (p q_v0 (p (p q_x q_v1) (p q_x q_x)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_x q_v1) (p q_x q_x))) (sz_lt_p_left (p q_v0 (p (p q_x q_v1) (p q_x q_x))) (p q_v0 (p (p q_x q_v1) (p q_x q_x))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape qs1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have he : u0_H1 = u0_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p q_H1 q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (pst6) (peq4); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => R q) (pst7); let pst11 := Eq.trans (pst9) (pst10); let pst12 := Eq.symm (peq5); let pst13 := Eq.trans (pst11) (pst12); let pst14 := Eq.symm (pst12); let pst15 := Eq.trans (pst13) (pst14); pst15)
        exact step_ne_first (by simpa only [he] using u0s1)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change x = (p q_v0 (p q_H0 (p q_x q_x))) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 (p q_H0 (p q_x q_x))) (p q_v0 (p q_H0 (p q_x q_x)))) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p (p q_v0 (p q_H0 (p q_x q_x))) q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p (p q_v0 (p q_H0 (p q_x q_x))) (p q_v0 (p q_H0 (p q_x q_x)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_H0 (p q_x q_x))) (sz_lt_p_left (p q_v0 (p q_H0 (p q_x q_x))) (p q_v0 (p q_H0 (p q_x q_x))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0B := step_bound u0s0
        have u0s0N := step_no_first u0s0
        cases u0s0 with
        | raw =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          cases u0s1 with
          | raw =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u0a; let peq8 := u0b; let peq9 := u0o; let peq10 := u1a; let peq11 := u1b; let peq12 := u1o; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p q_H1 q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (pst6) (peq10); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => R q) (pst7); let pst11 := Eq.trans (pst9) (pst10); let pst12 := congrArg (fun q => p q (p q_x q_x)) (peq6); let pst13 := congrArg (fun q => p q q_x) (peq4); let pst14 := congrArg (fun q => p (p (p u0_v0 (p (p u0_x u0_v1) (p u0_x u0_x))) u0_v0) q) (peq4); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => p u0_x q) (pst15); let pst17 := Eq.trans (pst12) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst18) (peq11); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst11) (pst20); let pst22 := Eq.symm (pst20); let pst23 := Eq.trans (pst21) (pst22); pst23)
            exact step_ne_first (by simpa only [he] using u1s1)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u0a; let peq8 := u0b; let peq9 := u0o; let peq10 := u1a; let peq11 := u1b; let peq12 := u1o; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p q_H1 q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (pst6) (peq10); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => R q) (pst7); let pst11 := Eq.trans (pst9) (pst10); let pst12 := congrArg (fun q => p q (p q_x q_x)) (peq6); let pst13 := congrArg (fun q => p q q_x) (peq4); let pst14 := congrArg (fun q => p (p u0_H1 u0_v0) q) (peq4); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => p u0_x q) (pst15); let pst17 := Eq.trans (pst12) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst18) (peq11); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst11) (pst20); let pst22 := Eq.symm (pst20); let pst23 := Eq.trans (pst21) (pst22); pst23)
            exact step_ne_first (by simpa only [he] using u1s1)
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          have u0s1N := step_no_first u0s1
          cases u0s1 with
          | raw =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u0a; let peq8 := u0b; let peq9 := u0o; let peq10 := u1a; let peq11 := u1b; let peq12 := u1o; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p q_H1 q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (pst6) (peq10); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => R q) (pst7); let pst11 := Eq.trans (pst9) (pst10); let pst12 := congrArg (fun q => p q (p q_x q_x)) (peq6); let pst13 := congrArg (fun q => p q q_x) (peq4); let pst14 := congrArg (fun q => p (p (p u0_v0 (p u0_H0 (p u0_x u0_x))) u0_v0) q) (peq4); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => p u0_x q) (pst15); let pst17 := Eq.trans (pst12) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst18) (peq11); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst11) (pst20); let pst22 := Eq.symm (pst20); let pst23 := Eq.trans (pst21) (pst22); pst23)
            exact step_ne_first (by simpa only [he] using u1s1)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u0a; let peq8 := u0b; let peq9 := u0o; let peq10 := u1a; let peq11 := u1b; let peq12 := u1o; let pst0 := congrArg (fun q => p q x) (peq0); let pst1 := congrArg (fun q => p q_H1 q) (peq0); let pst2 := Eq.trans (pst0) (pst1); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); let pst6 := Eq.symm (pst5); let pst7 := Eq.trans (pst6) (peq10); let pst8 := congrArg (fun q => L q) (pst7); let pst9 := Eq.symm (pst8); let pst10 := congrArg (fun q => R q) (pst7); let pst11 := Eq.trans (pst9) (pst10); let pst12 := congrArg (fun q => p q (p q_x q_x)) (peq6); let pst13 := congrArg (fun q => p q q_x) (peq4); let pst14 := congrArg (fun q => p (p u0_H1 u0_v0) q) (peq4); let pst15 := Eq.trans (pst13) (pst14); let pst16 := congrArg (fun q => p u0_x q) (pst15); let pst17 := Eq.trans (pst12) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst18) (peq11); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst11) (pst20); let pst22 := Eq.symm (pst20); let pst23 := Eq.trans (pst21) (pst22); pst23)
            exact step_ne_first (by simpa only [he] using u1s1)
  | hit s0h =>
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
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p (p q_v0 (p (p q_x q_v1) (p q_x q_x))) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s0hB s0B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s0hB qs1hB s0B qs0B qs1B z0 z1 z2
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
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p (p q_v0 (p q_H0 (p q_x q_x))) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s0hB qs0hB s0B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B qs0B qs1B z0 z1 z2
        omega
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step v0 (p H0 (p x x)) H1) :
    ¬ ∃ o, Code H1 v0 o := by
  exact step_no_first s1

theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 (eval (eval x v1) (eval x x))) v0) v0) := by
  let H0 := eval x v1
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step x v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v1
  let H1 := eval v0 (eval (eval x v1) (eval x x))
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval (eval x v1) (eval x x)) = (p H0 (p x x)) := by
    change (eval H0 (eval x x)) = (p H0 (p x x))
    calc
      (eval H0 (eval x x)) = (eval H0 (p x x)) := congrArg (fun q => (eval H0 q)) (eval_raw (nr0 x v0 v1))
      _ = (p H0 (p x x)) := (eval_raw (nr1 x v0 v1 H0 s0))
  have s1 : Step v0 (p H0 (p x x)) H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval (eval x v1) (eval x x))
  change x = (eval (eval H1 v0) v0)
  have rawEq : (eval (eval H1 v0) v0) = (eval (p H1 v0) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr2 x v0 v1 H1 s1))
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
