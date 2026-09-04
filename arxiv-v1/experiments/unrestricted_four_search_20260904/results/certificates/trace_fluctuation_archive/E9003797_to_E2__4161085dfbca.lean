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
      (s1 : Step v0 v1 H1) :
      Code (p (p (p H0 H1) v0) x) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_x q_H0 ∧ Step q_v0 q_v1 q_H1 ∧ a = (p (p (p q_H0 q_H1) q_v0) q_x) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R a)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

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
      change v = (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p q_v0 q_x) q_H1) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_x) q_H1) q_v0) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_x) q_H1) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H0 (p q_v0 q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H0 (p q_v0 q_v1)) q_v0) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 (p q_v0 q_v1)) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H0 q_H1) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H0 q_H1) q_v0) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq2); let pst2 := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H0 q_H1) q_v0) := sz_lt_p_right (p q_H0 q_H1) q_v0
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
theorem nr0 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 x H0)
    (s1 : Step v0 v1 H1) :
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
          change v0 = (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change x = q_x at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 v1) = q_v0 at e2
          have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L q)) ha
          change v0 = (p (p (p q_v0 q_x) q_H1) q_v0) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change x = q_x at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 v1) = q_v0 at e2
          have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L q)) ha
          change v0 = (p (p q_H0 (p q_v0 q_v1)) q_v0) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change x = q_x at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 v1) = q_v0 at e2
          have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L q)) ha
          change v0 = (p (p q_H0 q_H1) q_v0) at e0
          have e1 := congrArg (fun q => (R q)) ha
          change x = q_x at e1
          have e2 := congrArg (fun q => q) hb
          change (p v0 v1) = q_v0 at e2
          have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) v1) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
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
              have cyc : u0_v0 = (p (p u0_v0 u0_x) q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := congrArg (fun q => p q q_v1) (pst4); let pst6 := Eq.symm (pst5); let pst7 := congrArg (fun q => R q) (pst2); let pst8 := Eq.trans (pst6) (pst7); let pst9 := Eq.symm (pst8); pst9)
              have hlt : sz u0_v0 < sz (p (p u0_v0 u0_x) q_v1) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_left (p u0_v0 u0_x) q_v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_v0 = (p (p u0_v0 u0_x) q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := congrArg (fun q => p q q_v1) (pst4); let pst6 := Eq.symm (pst5); let pst7 := congrArg (fun q => R q) (pst2); let pst8 := Eq.trans (pst6) (pst7); let pst9 := Eq.symm (pst8); pst9)
              have hlt : sz u0_v0 < sz (p (p u0_v0 u0_x) q_v1) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_left (p u0_v0 u0_x) q_v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have ena : u0_v0 = (p q_v0 q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := congrArg (fun q => p q q_v1) (pst4); let pst6 := Eq.symm (pst5); let pst7 := congrArg (fun q => R q) (pst2); let pst8 := Eq.trans (pst6) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.symm (pst4); let pst11 := congrArg (fun q => R q) (pst1); let pst12 := Eq.trans (pst10) (pst11); let pst13 := congrArg (fun q => p q q_v1) (pst12); let pst14 := Eq.trans (pst9) (pst13); let pst15 := Eq.trans (pst4) (pst12); let pst16 := congrArg (fun q => p q q_v1) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst14) (pst17); pst18)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.trans (pst5) (pst6); let pst8 := Eq.trans (pst4) (pst7); let pst9 := Eq.symm (pst8); pst9)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
            | hit u0s1h =>
              have ena : u0_v0 = (p q_v0 q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := congrArg (fun q => p q q_v1) (pst4); let pst6 := Eq.symm (pst5); let pst7 := congrArg (fun q => R q) (pst2); let pst8 := Eq.trans (pst6) (pst7); let pst9 := Eq.symm (pst8); let pst10 := Eq.symm (pst4); let pst11 := congrArg (fun q => R q) (pst1); let pst12 := Eq.trans (pst10) (pst11); let pst13 := congrArg (fun q => p q q_v1) (pst12); let pst14 := Eq.trans (pst9) (pst13); let pst15 := Eq.trans (pst4) (pst12); let pst16 := congrArg (fun q => p q q_v1) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst14) (pst17); pst18)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.trans (pst5) (pst6); let pst8 := Eq.trans (pst4) (pst7); let pst9 := Eq.symm (pst8); pst9)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
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
              have cyc : u0_x = (p u0_v0 u0_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.trans (pst5) (pst6); let pst8 := Eq.symm (pst7); pst8)
              have hlt : sz u0_x < sz (p u0_v0 u0_x) := sz_lt_p_right u0_v0 u0_x
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_x = (p u0_v0 u0_x) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.trans (pst5) (pst6); let pst8 := Eq.symm (pst7); pst8)
              have hlt : sz u0_x < sz (p u0_v0 u0_x) := sz_lt_p_right u0_v0 u0_x
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => R q) (pst2); let pst4 := Eq.symm (pst3); pst4)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.trans (pst5) (pst6); let pst8 := Eq.trans (pst4) (pst7); let pst9 := Eq.symm (pst8); pst9)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
            | hit u0s1h =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => R q) (pst2); let pst4 := Eq.symm (pst3); pst4)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => L q) (pst3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.trans (pst5) (pst6); let pst8 := Eq.trans (pst4) (pst7); let pst9 := Eq.symm (pst8); pst9)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
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
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst14); let pst16 := Eq.trans (pst6) (pst8); let pst17 := congrArg (fun q => p q q_v1) (pst16); let pst18 := Eq.trans (pst5) (pst17); let pst19 := congrArg (fun q => p q u0_v1) (pst18); let pst20 := congrArg (fun q => p (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) q) (pst19); let pst21 := Eq.trans (pst15) (pst20); let pst22 := Eq.trans (pst3) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq9); let pst25 := Eq.symm (pst24); pst25)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (sz_lt_p_left (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst14); let pst16 := Eq.trans (pst6) (pst8); let pst17 := congrArg (fun q => p q q_v1) (pst16); let pst18 := Eq.trans (pst5) (pst17); let pst19 := congrArg (fun q => p q u0_v1) (pst18); let pst20 := congrArg (fun q => p (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) q) (pst19); let pst21 := Eq.trans (pst15) (pst20); let pst22 := Eq.trans (pst3) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq9); let pst25 := Eq.symm (pst24); pst25)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_x) u1_H1) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (sz_lt_p_left (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst14); let pst16 := Eq.trans (pst6) (pst8); let pst17 := congrArg (fun q => p q q_v1) (pst16); let pst18 := Eq.trans (pst5) (pst17); let pst19 := congrArg (fun q => p q u0_v1) (pst18); let pst20 := congrArg (fun q => p (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) q) (pst19); let pst21 := Eq.trans (pst15) (pst20); let pst22 := Eq.trans (pst3) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq9); let pst25 := Eq.symm (pst24); pst25)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) (sz_lt_p_left (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst14); let pst16 := Eq.trans (pst6) (pst8); let pst17 := congrArg (fun q => p q q_v1) (pst16); let pst18 := Eq.trans (pst5) (pst17); let pst19 := congrArg (fun q => p q u0_v1) (pst18); let pst20 := congrArg (fun q => p (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) q) (pst19); let pst21 := Eq.trans (pst15) (pst20); let pst22 := Eq.trans (pst3) (pst21); let pst23 := Eq.symm (pst22); let pst24 := Eq.trans (pst23) (peq9); let pst25 := Eq.symm (pst24); pst25)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 u1_H1) u1_v0) u1_x) (sz_lt_p_left (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q u0_H1) (pst14); let pst16 := Eq.trans (pst3) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq9); let pst19 := Eq.symm (pst18); pst19)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (sz_lt_p_left (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q u0_H1) (pst14); let pst16 := Eq.trans (pst3) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq9); let pst19 := Eq.symm (pst18); pst19)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_x) u1_H1) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (sz_lt_p_left (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x) q_v1) (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q u0_H1) (pst14); let pst16 := Eq.trans (pst3) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq9); let pst19 := Eq.symm (pst18); pst19)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) (sz_lt_p_left (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) q_v1) (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst2); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => R q) (pst1); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := congrArg (fun q => p q q_v1) (pst9); let pst11 := Eq.trans (pst5) (pst10); let pst12 := congrArg (fun q => p q u0_x) (pst11); let pst13 := congrArg (fun q => p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) q) (pst8); let pst14 := Eq.trans (pst12) (pst13); let pst15 := congrArg (fun q => p q u0_H1) (pst14); let pst16 := Eq.trans (pst3) (pst15); let pst17 := Eq.symm (pst16); let pst18 := Eq.trans (pst17) (peq9); let pst19 := Eq.symm (pst18); pst19)
                  have hlt : sz u1_x < sz (p (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 u1_H1) u1_v0) u1_x) (sz_lt_p_left (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1)) (sz_lt_p_left (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p (p (p (p (p u1_H0 u1_H1) u1_v0) u1_x) q_v1) (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have ena : u0_v0 = (p q_v0 q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => R q) (pst2); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => R q) (pst1); let pst6 := congrArg (fun q => p q q_v1) (pst5); let pst7 := Eq.trans (pst4) (pst6); let pst8 := congrArg (fun q => p q q_v1) (pst5); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst7) (pst9); pst10)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => R q) (pst1); let pst3 := Eq.symm (pst2); pst3)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
            | hit u0s1h =>
              have ena : u0_v0 = (p q_v0 q_v1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => R q) (pst2); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => R q) (pst1); let pst6 := congrArg (fun q => p q q_v1) (pst5); let pst7 := Eq.trans (pst4) (pst6); let pst8 := congrArg (fun q => p q q_v1) (pst5); let pst9 := Eq.symm (pst8); let pst10 := Eq.trans (pst7) (pst9); pst10)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => R q) (pst1); let pst3 := Eq.symm (pst2); pst3)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
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
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (p u0_v0 u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (p u0_v0 u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (sz_lt_p_right u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (p u0_v0 u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (p u0_v0 u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (p u0_v0 u0_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_x) u1_H1) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (sz_lt_p_right u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (p u0_v0 u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) (p u0_v0 u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) (p u0_v0 u0_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) (sz_lt_p_right u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) (p u0_v0 u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) (p u0_v0 u0_v1)) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) (p u0_v0 u0_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 u1_H1) u1_v0) u1_x) (sz_lt_p_right u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) (p u0_v0 u0_v1))
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q u0_H1) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) (sz_lt_p_right u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p (p u1_v0 u1_x) (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q u0_H1) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u1_v0 u1_x) (sz_lt_p_left (p u1_v0 u1_x) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_x) u1_H1) u1_v0)) (sz_lt_p_left (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) (sz_lt_p_right u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p (p u1_v0 u1_x) u1_H1) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q u0_H1) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x) (sz_lt_p_right u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_x = (p (p u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) u0_H1) := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let peq7 := u1a; let peq8 := u1b; let peq9 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => L q) (pst2); let pst4 := congrArg (fun q => R q) (pst1); let pst5 := Eq.symm (pst4); let pst6 := Eq.trans (pst5) (peq7); let pst7 := congrArg (fun q => p u0_v0 q) (pst6); let pst8 := congrArg (fun q => p q u0_H1) (pst7); let pst9 := Eq.trans (pst3) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst10) (peq9); let pst12 := Eq.symm (pst11); pst12)
                  have hlt : sz u1_x < sz (p (p u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) u0_H1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p (p u1_H0 u1_H1) u1_v0) u1_x) (sz_lt_p_right u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x))) (sz_lt_p_left (p u0_v0 (p (p (p u1_H0 u1_H1) u1_v0) u1_x)) u0_H1)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => R q) (pst2); let pst4 := Eq.symm (pst3); pst4)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => R q) (pst1); let pst3 := Eq.symm (pst2); pst3)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
            | hit u0s1h =>
              have ena : u0_v0 = q_H1 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := congrArg (fun q => R q) (pst2); let pst4 := Eq.symm (pst3); pst4)
              have enb : u0_x = q_v0 := (let peq0 := congrArg (fun q => (L q)) (ha); let peq1 := congrArg (fun q => (R q)) (ha); let peq2 := hb; let peq3 := ho; let peq4 := u0a; let peq5 := u0b; let peq6 := u0o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => R q) (pst1); let pst3 := Eq.symm (pst2); pst3)
              apply qs1N
              refine ⟨u0_H0, ?_⟩
              simpa only [ena, enb] using u0s0h
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
          change H0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB s0hB s0B s1B qs0B qs1B z0 z1 z2
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
          change H0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB s0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2
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
          change H0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B s1B qs0B qs1B z0 z1 z2
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
          change H0 = (p (p (p q_H0 q_H1) q_v0) q_x) at p0
          have z0 := congrArg sz p0
          have p1 := hb
          change (p v0 v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := ho
          change o = q_x at p2
          have z2 := congrArg sz p2
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_x) q_H1) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_x) q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))) (sz_lt_p_left (p q_H0 (p q_v0 q_v1)) q_v0)) (sz_lt_p_left (p (p q_H0 (p q_v0 q_v1)) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => R q) (pst16); let pst18 := Eq.symm (pst17); let pst19 := Eq.trans (pst1) (pst18); pst19)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p u0_v0 q) (pst4); let pst6 := congrArg (fun q => p q u0_H1) (pst5); let pst7 := congrArg (fun q => p q u0_v0) (pst6); let pst8 := congrArg (fun q => p q u0_x) (pst7); let pst9 := congrArg (fun q => p (p (p (p u0_v0 (p (p (p q_H0 q_H1) q_v0) q_x)) u0_H1) u0_v0) q) (pst4); let pst10 := Eq.trans (pst8) (pst9); let pst11 := Eq.trans (peq3) (pst10); let pst12 := Eq.symm (pst11); let pst13 := Eq.trans (pst12) (peq6); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := Eq.symm (pst14); let pst16 := Eq.trans (pst1) (pst15); pst16)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
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
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : q_v0 = (p (p (p q_H0 q_H1) q_v0) q_x) := (let peq0 := ha; let peq1 := hb; let peq2 := ho; let peq3 := u0a; let peq4 := u0b; let peq5 := u0o; let peq6 := u1a; let peq7 := u1b; let peq8 := u1o; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq8); let pst2 := Eq.symm (peq0); let pst3 := Eq.trans (pst2) (peq5); let pst4 := Eq.symm (pst3); let pst5 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst4); let pst6 := Eq.trans (peq3) (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq6); let pst9 := congrArg (fun q => R q) (pst8); let pst10 := Eq.symm (pst9); let pst11 := Eq.trans (pst1) (pst10); pst11)
                  have hlt : sz q_v0 < sz (p (p (p q_H0 q_H1) q_v0) q_x) := Nat.lt_trans (sz_lt_p_right (p q_H0 q_H1) q_v0) (sz_lt_p_left (p (p q_H0 q_H1) q_v0) q_x)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 x H0)
    (s1 : Step v0 v1 H1) :
    ¬ ∃ o, Code (p H0 H1) v0 o := by
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
          have e0 := congrArg (fun q => (L (L q))) ha
          change v0 = (p (p q_v0 q_x) (p q_v0 q_v1)) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change (p v0 v1) = q_x at e2
          have e3 := congrArg (fun q => q) hb
          change v0 = q_v0 at e3
          have cyc : q_x = (p (p (p q_v0 q_x) (p q_v0 q_v1)) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_x < sz (p (p (p q_v0 q_x) (p q_v0 q_v1)) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_x) (p q_v0 q_v1)) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change v0 = (p (p q_v0 q_x) q_H1) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change (p v0 v1) = q_x at e2
          have e3 := congrArg (fun q => q) hb
          change v0 = q_v0 at e3
          have cyc : q_x = (p (p (p q_v0 q_x) q_H1) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_x < sz (p (p (p q_v0 q_x) q_H1) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)) (sz_lt_p_left (p (p q_v0 q_x) q_H1) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change v0 = (p q_H0 (p q_v0 q_v1)) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change (p v0 v1) = q_x at e2
          have e3 := congrArg (fun q => q) hb
          change v0 = q_v0 at e3
          have cyc : q_v0 = (p q_H0 (p q_v0 q_v1)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p q_H0 (p q_v0 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))
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
              have cyc : u0_v0 = (p (p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) u0_x) v1) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := Eq.symm (peq0); let pst5 := Eq.trans (pst4) (peq3); let pst6 := Eq.symm (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq5); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => p q q_H1) (pst9); let pst11 := congrArg (fun q => R q) (pst8); let pst12 := congrArg (fun q => p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) q) (pst11); let pst13 := Eq.trans (pst10) (pst12); let pst14 := congrArg (fun q => p q v1) (pst13); let pst15 := Eq.trans (pst3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := Eq.symm (pst17); pst18)
              have hlt : sz u0_v0 < sz (p (p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) u0_x) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_left (p u0_v0 u0_x) (p u0_v0 u0_v1))) (sz_lt_p_left (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0)) (sz_lt_p_left (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) u0_x)) (sz_lt_p_left (p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) u0_x) v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_v0 = (p (p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) u0_x) v1) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := Eq.symm (peq0); let pst5 := Eq.trans (pst4) (peq3); let pst6 := Eq.symm (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq5); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => p q q_H1) (pst9); let pst11 := congrArg (fun q => R q) (pst8); let pst12 := congrArg (fun q => p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) q) (pst11); let pst13 := Eq.trans (pst10) (pst12); let pst14 := congrArg (fun q => p q v1) (pst13); let pst15 := Eq.trans (pst3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := Eq.symm (pst17); pst18)
              have hlt : sz u0_v0 < sz (p (p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) u0_x) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_left (p u0_v0 u0_x) u0_H1)) (sz_lt_p_left (p (p u0_v0 u0_x) u0_H1) u0_v0)) (sz_lt_p_left (p (p (p u0_v0 u0_x) u0_H1) u0_v0) u0_x)) (sz_lt_p_left (p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) u0_x) v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              have cyc : u0_v0 = (p (p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) u0_x) v1) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := Eq.symm (peq0); let pst5 := Eq.trans (pst4) (peq3); let pst6 := Eq.symm (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq5); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => p q q_H1) (pst9); let pst11 := congrArg (fun q => R q) (pst8); let pst12 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst11); let pst13 := Eq.trans (pst10) (pst12); let pst14 := congrArg (fun q => p q v1) (pst13); let pst15 := Eq.trans (pst3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := Eq.symm (pst17); pst18)
              have hlt : sz u0_v0 < sz (p (p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) u0_x) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v1) (sz_lt_p_right u0_H0 (p u0_v0 u0_v1))) (sz_lt_p_left (p u0_H0 (p u0_v0 u0_v1)) u0_v0)) (sz_lt_p_left (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) u0_x)) (sz_lt_p_left (p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) u0_x) v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              have cyc : u0_v0 = (p (p (p (p u0_H0 u0_H1) u0_v0) u0_x) v1) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); let pst4 := Eq.symm (peq0); let pst5 := Eq.trans (pst4) (peq3); let pst6 := Eq.symm (pst5); let pst7 := Eq.symm (pst6); let pst8 := Eq.trans (pst7) (peq5); let pst9 := congrArg (fun q => L q) (pst8); let pst10 := congrArg (fun q => p q q_H1) (pst9); let pst11 := congrArg (fun q => R q) (pst8); let pst12 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst11); let pst13 := Eq.trans (pst10) (pst12); let pst14 := congrArg (fun q => p q v1) (pst13); let pst15 := Eq.trans (pst3) (pst14); let pst16 := Eq.symm (pst15); let pst17 := Eq.trans (pst16) (peq6); let pst18 := Eq.symm (pst17); pst18)
              have hlt : sz u0_v0 < sz (p (p (p (p u0_H0 u0_H1) u0_v0) u0_x) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right (p u0_H0 u0_H1) u0_v0) (sz_lt_p_left (p (p u0_H0 u0_H1) u0_v0) u0_x)) (sz_lt_p_left (p (p (p u0_H0 u0_H1) u0_v0) u0_x) v1)
              exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change v0 = (p (p q_v0 q_x) (p q_v0 q_v1)) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change H1 = q_x at e2
          have e3 := congrArg (fun q => q) hb
          change v0 = q_v0 at e3
          have cyc : q_v0 = (p (p q_v0 q_x) (p q_v0 q_v1)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_v0 q_x) (p q_v0 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) (p q_v0 q_v1))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change v0 = (p (p q_v0 q_x) q_H1) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change H1 = q_x at e2
          have e3 := congrArg (fun q => q) hb
          change v0 = q_v0 at e3
          have cyc : q_v0 = (p (p q_v0 q_x) q_H1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p (p q_v0 q_x) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L q))) ha
          change v0 = (p q_H0 (p q_v0 q_v1)) at e0
          have e1 := congrArg (fun q => (R (L q))) ha
          change x = q_v0 at e1
          have e2 := congrArg (fun q => (R q)) ha
          change H1 = q_x at e2
          have e3 := congrArg (fun q => q) hb
          change v0 = q_v0 at e3
          have cyc : q_v0 = (p q_H0 (p q_v0 q_v1)) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.symm (pst1); pst2)
          have hlt : sz q_v0 < sz (p q_H0 (p q_v0 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_right q_H0 (p q_v0 q_v1))
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
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_x) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.symm (peq2); let pst20 := Eq.trans (pst19) (peq7); let pst21 := Eq.trans (pst20) (pst18); let pst22 := Eq.symm (pst21); let pst23 := Eq.trans (pst22) (peq9); let pst24 := Eq.trans (pst18) (pst23); let pst25 := congrArg (fun q => p u1_v0 q) (pst24); let pst26 := Eq.trans (pst17) (pst25); let pst27 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst26); let pst28 := congrArg (fun q => p q u0_v1) (pst16); let pst29 := congrArg (fun q => p q u0_v1) (pst16); let pst30 := Eq.symm (pst29); let pst31 := congrArg (fun q => R q) (pst14); let pst32 := Eq.trans (pst30) (pst31); let pst33 := congrArg (fun q => R q) (pst32); let pst34 := congrArg (fun q => p u1_v0 q) (pst33); let pst35 := Eq.trans (pst28) (pst34); let pst36 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst35); let pst37 := Eq.trans (pst27) (pst36); let pst38 := congrArg (fun q => p q u0_v0) (pst37); let pst39 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) q) (pst16); let pst40 := Eq.trans (pst38) (pst39); let pst41 := Eq.trans (pst2) (pst40); let pst42 := Eq.symm (pst41); let pst43 := Eq.trans (pst42) (peq10); let pst44 := Eq.trans (pst43) (pst23); let pst45 := Eq.symm (pst44); pst45)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_x) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.symm (peq2); let pst20 := Eq.trans (pst19) (peq7); let pst21 := Eq.trans (pst20) (pst18); let pst22 := Eq.symm (pst21); let pst23 := Eq.trans (pst22) (peq9); let pst24 := Eq.trans (pst18) (pst23); let pst25 := congrArg (fun q => p u1_v0 q) (pst24); let pst26 := Eq.trans (pst17) (pst25); let pst27 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst26); let pst28 := congrArg (fun q => p q u0_v1) (pst16); let pst29 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst28); let pst30 := Eq.trans (pst27) (pst29); let pst31 := congrArg (fun q => p q u0_v0) (pst30); let pst32 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) q) (pst16); let pst33 := Eq.trans (pst31) (pst32); let pst34 := Eq.trans (pst2) (pst33); let pst35 := Eq.symm (pst34); let pst36 := Eq.trans (pst35) (peq10); let pst37 := Eq.trans (pst36) (pst23); let pst38 := Eq.symm (pst37); pst38)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u0_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => R q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_x) (pst16); let pst18 := congrArg (fun q => R q) (pst12); let pst19 := Eq.symm (peq2); let pst20 := Eq.trans (pst19) (peq7); let pst21 := Eq.trans (pst20) (pst18); let pst22 := Eq.symm (pst21); let pst23 := Eq.trans (pst22) (peq9); let pst24 := Eq.trans (pst18) (pst23); let pst25 := congrArg (fun q => p u1_v0 q) (pst24); let pst26 := Eq.trans (pst17) (pst25); let pst27 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst26); let pst28 := congrArg (fun q => p q u0_v1) (pst16); let pst29 := congrArg (fun q => R q) (pst15); let pst30 := congrArg (fun q => p u1_v0 q) (pst29); let pst31 := Eq.trans (pst28) (pst30); let pst32 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst31); let pst33 := Eq.trans (pst27) (pst32); let pst34 := congrArg (fun q => p q u0_v0) (pst33); let pst35 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) q) (pst16); let pst36 := Eq.trans (pst34) (pst35); let pst37 := Eq.trans (pst2) (pst36); let pst38 := Eq.symm (pst37); let pst39 := Eq.trans (pst38) (peq10); let pst40 := Eq.trans (pst39) (pst23); let pst41 := Eq.symm (pst40); pst41)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := congrArg (fun q => p q u0_x) (pst14); let pst16 := congrArg (fun q => R q) (pst12); let pst17 := Eq.symm (peq2); let pst18 := Eq.trans (pst17) (peq7); let pst19 := Eq.trans (pst18) (pst16); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := Eq.trans (pst16) (pst21); let pst23 := congrArg (fun q => p u1_v0 q) (pst22); let pst24 := Eq.trans (pst15) (pst23); let pst25 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst24); let pst26 := congrArg (fun q => p q u0_v1) (pst14); let pst27 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst26); let pst28 := Eq.trans (pst25) (pst27); let pst29 := congrArg (fun q => p q u0_v0) (pst28); let pst30 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) q) (pst14); let pst31 := Eq.trans (pst29) (pst30); let pst32 := Eq.trans (pst2) (pst31); let pst33 := Eq.symm (pst32); let pst34 := Eq.trans (pst33) (peq10); let pst35 := Eq.trans (pst34) (pst21); let pst36 := Eq.symm (pst35); pst36)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u0_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_x) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.symm (peq2); let pst20 := Eq.trans (pst19) (peq7); let pst21 := Eq.trans (pst20) (pst18); let pst22 := Eq.symm (pst21); let pst23 := Eq.trans (pst22) (peq9); let pst24 := Eq.trans (pst18) (pst23); let pst25 := congrArg (fun q => p u1_v0 q) (pst24); let pst26 := Eq.trans (pst17) (pst25); let pst27 := congrArg (fun q => p q u0_H1) (pst26); let pst28 := congrArg (fun q => R q) (pst14); let pst29 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst28); let pst30 := Eq.trans (pst27) (pst29); let pst31 := congrArg (fun q => p q u0_v0) (pst30); let pst32 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) q) (pst16); let pst33 := Eq.trans (pst31) (pst32); let pst34 := Eq.trans (pst2) (pst33); let pst35 := Eq.symm (pst34); let pst36 := Eq.trans (pst35) (peq10); let pst37 := Eq.trans (pst36) (pst23); let pst38 := Eq.symm (pst37); pst38)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) u1_H1) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => L q) (pst15); let pst17 := congrArg (fun q => p q u0_x) (pst16); let pst18 := congrArg (fun q => R q) (pst15); let pst19 := Eq.symm (peq2); let pst20 := Eq.trans (pst19) (peq7); let pst21 := Eq.trans (pst20) (pst18); let pst22 := Eq.symm (pst21); let pst23 := Eq.trans (pst22) (peq9); let pst24 := Eq.trans (pst18) (pst23); let pst25 := congrArg (fun q => p u1_v0 q) (pst24); let pst26 := Eq.trans (pst17) (pst25); let pst27 := congrArg (fun q => p q u0_H1) (pst26); let pst28 := congrArg (fun q => R q) (pst14); let pst29 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst28); let pst30 := Eq.trans (pst27) (pst29); let pst31 := congrArg (fun q => p q u0_v0) (pst30); let pst32 := congrArg (fun q => p (p (p u1_v0 u1_v0) u1_H1) q) (pst16); let pst33 := Eq.trans (pst31) (pst32); let pst34 := Eq.trans (pst2) (pst33); let pst35 := Eq.symm (pst34); let pst36 := Eq.trans (pst35) (peq10); let pst37 := Eq.trans (pst36) (pst23); let pst38 := Eq.symm (pst37); pst38)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) u1_H1) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_v0) u1_H1) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := congrArg (fun q => p q u0_x) (pst14); let pst16 := congrArg (fun q => R q) (pst12); let pst17 := Eq.symm (peq2); let pst18 := Eq.trans (pst17) (peq7); let pst19 := Eq.trans (pst18) (pst16); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := Eq.trans (pst16) (pst21); let pst23 := congrArg (fun q => p u1_v0 q) (pst22); let pst24 := Eq.trans (pst15) (pst23); let pst25 := congrArg (fun q => p q u0_H1) (pst24); let pst26 := congrArg (fun q => L q) (pst13); let pst27 := congrArg (fun q => R q) (pst26); let pst28 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst27); let pst29 := Eq.trans (pst25) (pst28); let pst30 := congrArg (fun q => p q u0_v0) (pst29); let pst31 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) q) (pst14); let pst32 := Eq.trans (pst30) (pst31); let pst33 := Eq.trans (pst2) (pst32); let pst34 := Eq.symm (pst33); let pst35 := Eq.trans (pst34) (peq10); let pst36 := Eq.trans (pst35) (pst21); let pst37 := Eq.symm (pst36); pst37)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) u1_H1) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p (p u0_v0 u0_x) u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => R q) (pst13); let pst15 := congrArg (fun q => p q u0_x) (pst14); let pst16 := congrArg (fun q => R q) (pst12); let pst17 := Eq.symm (peq2); let pst18 := Eq.trans (pst17) (peq7); let pst19 := Eq.trans (pst18) (pst16); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := Eq.trans (pst16) (pst21); let pst23 := congrArg (fun q => p u1_v0 q) (pst22); let pst24 := Eq.trans (pst15) (pst23); let pst25 := congrArg (fun q => p q u0_H1) (pst24); let pst26 := congrArg (fun q => L q) (pst13); let pst27 := congrArg (fun q => R q) (pst26); let pst28 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst27); let pst29 := Eq.trans (pst25) (pst28); let pst30 := congrArg (fun q => p q u0_v0) (pst29); let pst31 := congrArg (fun q => p (p (p u1_v0 u1_v0) u1_H1) q) (pst14); let pst32 := Eq.trans (pst30) (pst31); let pst33 := Eq.trans (pst2) (pst32); let pst34 := Eq.symm (pst33); let pst35 := Eq.trans (pst34) (peq10); let pst36 := Eq.trans (pst35) (pst21); let pst37 := Eq.symm (pst36); pst37)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) u1_H1) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_v0) u1_H1) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s0h =>
            have u0s1B := step_bound u0s1
            have u0s1N := step_no_first u0s1
            cases u0s1 with
            | raw =>
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := Eq.symm (peq2); let pst17 := Eq.trans (pst16) (peq7); let pst18 := congrArg (fun q => R q) (pst12); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := congrArg (fun q => p u1_v0 q) (pst21); let pst23 := Eq.trans (pst15) (pst22); let pst24 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst23); let pst25 := congrArg (fun q => R q) (pst14); let pst26 := congrArg (fun q => L q) (pst25); let pst27 := congrArg (fun q => p q u0_v1) (pst26); let pst28 := congrArg (fun q => R q) (pst25); let pst29 := congrArg (fun q => p u1_v0 q) (pst28); let pst30 := Eq.trans (pst27) (pst29); let pst31 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst30); let pst32 := Eq.trans (pst24) (pst31); let pst33 := congrArg (fun q => p q u0_v0) (pst32); let pst34 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) q) (pst26); let pst35 := Eq.trans (pst33) (pst34); let pst36 := Eq.trans (pst2) (pst35); let pst37 := Eq.symm (pst36); let pst38 := Eq.trans (pst37) (peq10); let pst39 := Eq.trans (pst38) (pst21); let pst40 := Eq.symm (pst39); pst40)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := Eq.symm (peq2); let pst17 := Eq.trans (pst16) (peq7); let pst18 := congrArg (fun q => R q) (pst12); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := congrArg (fun q => p u1_v0 q) (pst21); let pst23 := Eq.trans (pst15) (pst22); let pst24 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst23); let pst25 := congrArg (fun q => R q) (pst13); let pst26 := congrArg (fun q => p q u0_v1) (pst25); let pst27 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst26); let pst28 := Eq.trans (pst24) (pst27); let pst29 := congrArg (fun q => p q u0_v0) (pst28); let pst30 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) q) (pst25); let pst31 := Eq.trans (pst29) (pst30); let pst32 := Eq.trans (pst2) (pst31); let pst33 := Eq.symm (pst32); let pst34 := Eq.trans (pst33) (peq10); let pst35 := Eq.trans (pst34) (pst21); let pst36 := Eq.symm (pst35); pst36)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u0_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u0_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst15); let pst17 := congrArg (fun q => R q) (pst14); let pst18 := congrArg (fun q => L q) (pst17); let pst19 := congrArg (fun q => p q u0_v1) (pst18); let pst20 := congrArg (fun q => R q) (pst17); let pst21 := congrArg (fun q => p u1_v0 q) (pst20); let pst22 := Eq.trans (pst19) (pst21); let pst23 := congrArg (fun q => p u1_H0 q) (pst22); let pst24 := Eq.trans (pst16) (pst23); let pst25 := congrArg (fun q => p q u0_v0) (pst24); let pst26 := congrArg (fun q => p (p u1_H0 (p u1_v0 u1_v1)) q) (pst18); let pst27 := Eq.trans (pst25) (pst26); let pst28 := Eq.trans (pst2) (pst27); let pst29 := Eq.symm (pst28); let pst30 := Eq.trans (pst29) (peq10); let pst31 := Eq.symm (peq2); let pst32 := Eq.trans (pst31) (peq7); let pst33 := congrArg (fun q => R q) (pst12); let pst34 := Eq.trans (pst32) (pst33); let pst35 := Eq.symm (pst34); let pst36 := Eq.trans (pst35) (peq9); let pst37 := Eq.trans (pst30) (pst36); let pst38 := Eq.symm (pst37); pst38)
                  have hlt : sz u1_v0 < sz (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v1) (sz_lt_p_right u1_H0 (p u1_v0 u1_v1))) (sz_lt_p_left (p u1_H0 (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p u1_H0 (p u1_v0 u0_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 (p u0_v0 u0_v1)) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => p q (p u0_v0 u0_v1)) (pst15); let pst17 := congrArg (fun q => R q) (pst13); let pst18 := congrArg (fun q => p q u0_v1) (pst17); let pst19 := congrArg (fun q => p u1_H0 q) (pst18); let pst20 := Eq.trans (pst16) (pst19); let pst21 := congrArg (fun q => p q u0_v0) (pst20); let pst22 := congrArg (fun q => p (p u1_H0 (p u1_v0 u0_v1)) q) (pst17); let pst23 := Eq.trans (pst21) (pst22); let pst24 := Eq.trans (pst2) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq10); let pst27 := Eq.symm (peq2); let pst28 := Eq.trans (pst27) (peq7); let pst29 := congrArg (fun q => R q) (pst12); let pst30 := Eq.trans (pst28) (pst29); let pst31 := Eq.symm (pst30); let pst32 := Eq.trans (pst31) (peq9); let pst33 := Eq.trans (pst26) (pst32); let pst34 := Eq.symm (pst33); pst34)
                  have hlt : sz u1_v0 < sz (p (p u1_H0 (p u1_v0 u0_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u0_v1) (sz_lt_p_right u1_H0 (p u1_v0 u0_v1))) (sz_lt_p_left (p u1_H0 (p u1_v0 u0_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u0s1h =>
              rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
              have u1s0B := step_bound u1s0
              have u1s0N := step_no_first u1s0
              cases u1s0 with
              | raw =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := Eq.symm (peq2); let pst17 := Eq.trans (pst16) (peq7); let pst18 := congrArg (fun q => R q) (pst12); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := congrArg (fun q => p u1_v0 q) (pst21); let pst23 := Eq.trans (pst15) (pst22); let pst24 := congrArg (fun q => p q u0_H1) (pst23); let pst25 := congrArg (fun q => R q) (pst14); let pst26 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst25); let pst27 := Eq.trans (pst24) (pst26); let pst28 := congrArg (fun q => p q u0_v0) (pst27); let pst29 := congrArg (fun q => R q) (pst13); let pst30 := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) q) (pst29); let pst31 := Eq.trans (pst28) (pst30); let pst32 := Eq.trans (pst2) (pst31); let pst33 := Eq.symm (pst32); let pst34 := Eq.trans (pst33) (peq10); let pst35 := Eq.trans (pst34) (pst21); let pst36 := Eq.symm (pst35); pst36)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v1))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) u1_H1) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := Eq.symm (peq2); let pst17 := Eq.trans (pst16) (peq7); let pst18 := congrArg (fun q => R q) (pst12); let pst19 := Eq.trans (pst17) (pst18); let pst20 := Eq.symm (pst19); let pst21 := Eq.trans (pst20) (peq9); let pst22 := congrArg (fun q => p u1_v0 q) (pst21); let pst23 := Eq.trans (pst15) (pst22); let pst24 := congrArg (fun q => p q u0_H1) (pst23); let pst25 := congrArg (fun q => R q) (pst14); let pst26 := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst25); let pst27 := Eq.trans (pst24) (pst26); let pst28 := congrArg (fun q => p q u0_v0) (pst27); let pst29 := congrArg (fun q => R q) (pst13); let pst30 := congrArg (fun q => p (p (p u1_v0 u1_v0) u1_H1) q) (pst29); let pst31 := Eq.trans (pst28) (pst30); let pst32 := Eq.trans (pst2) (pst31); let pst33 := Eq.symm (pst32); let pst34 := Eq.trans (pst33) (peq10); let pst35 := Eq.trans (pst34) (pst21); let pst36 := Eq.symm (pst35); pst36)
                  have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) u1_H1) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) u1_H1)) (sz_lt_p_left (p (p u1_v0 u1_v0) u1_H1) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s0h =>
                have u1s1B := step_bound u1s1
                have u1s1N := step_no_first u1s1
                cases u1s1 with
                | raw =>
                  have cyc : u1_v0 = (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => p q u0_H1) (pst15); let pst17 := congrArg (fun q => R q) (pst14); let pst18 := congrArg (fun q => p u1_H0 q) (pst17); let pst19 := Eq.trans (pst16) (pst18); let pst20 := congrArg (fun q => p q u0_v0) (pst19); let pst21 := congrArg (fun q => R q) (pst13); let pst22 := congrArg (fun q => p (p u1_H0 (p u1_v0 u1_v1)) q) (pst21); let pst23 := Eq.trans (pst20) (pst22); let pst24 := Eq.trans (pst2) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq10); let pst27 := Eq.symm (peq2); let pst28 := Eq.trans (pst27) (peq7); let pst29 := congrArg (fun q => R q) (pst12); let pst30 := Eq.trans (pst28) (pst29); let pst31 := Eq.symm (pst30); let pst32 := Eq.trans (pst31) (peq9); let pst33 := Eq.trans (pst26) (pst32); let pst34 := Eq.symm (pst33); pst34)
                  have hlt : sz u1_v0 < sz (p (p u1_H0 (p u1_v0 u1_v1)) u1_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v1) (sz_lt_p_right u1_H0 (p u1_v0 u1_v1))) (sz_lt_p_left (p u1_H0 (p u1_v0 u1_v1)) u1_v0)
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
                | hit u1s1h =>
                  have cyc : u1_v0 = (p (p u1_H0 u1_H1) u1_v0) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let peq5 := u0a; let peq6 := u0b; let peq7 := u0o; let peq8 := u1a; let peq9 := u1b; let peq10 := u1o; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq5); let pst2 := congrArg (fun q => L q) (pst1); let pst3 := Eq.symm (peq0); let pst4 := Eq.trans (pst3) (peq3); let pst5 := Eq.symm (pst4); let pst6 := congrArg (fun q => p q q_H1) (pst2); let pst7 := congrArg (fun q => R q) (pst1); let pst8 := congrArg (fun q => p (p (p u0_H0 u0_H1) u0_v0) q) (pst7); let pst9 := Eq.trans (pst6) (pst8); let pst10 := Eq.trans (pst5) (pst9); let pst11 := Eq.symm (pst10); let pst12 := Eq.trans (pst11) (peq8); let pst13 := congrArg (fun q => L q) (pst12); let pst14 := congrArg (fun q => L q) (pst13); let pst15 := congrArg (fun q => L q) (pst14); let pst16 := congrArg (fun q => p q u0_H1) (pst15); let pst17 := congrArg (fun q => R q) (pst14); let pst18 := congrArg (fun q => p u1_H0 q) (pst17); let pst19 := Eq.trans (pst16) (pst18); let pst20 := congrArg (fun q => p q u0_v0) (pst19); let pst21 := congrArg (fun q => R q) (pst13); let pst22 := congrArg (fun q => p (p u1_H0 u1_H1) q) (pst21); let pst23 := Eq.trans (pst20) (pst22); let pst24 := Eq.trans (pst2) (pst23); let pst25 := Eq.symm (pst24); let pst26 := Eq.trans (pst25) (peq10); let pst27 := Eq.symm (peq2); let pst28 := Eq.trans (pst27) (peq7); let pst29 := congrArg (fun q => R q) (pst12); let pst30 := Eq.trans (pst28) (pst29); let pst31 := Eq.symm (pst30); let pst32 := Eq.trans (pst31) (peq9); let pst33 := Eq.trans (pst26) (pst32); let pst34 := Eq.symm (pst33); pst34)
                  have hlt : sz u1_v0 < sz (p (p u1_H0 u1_H1) u1_v0) := sz_lt_p_right (p u1_H0 u1_H1) u1_v0
                  exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
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
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change (p v0 v1) = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p (p q_v0 q_x) q_H1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change (p v0 v1) = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
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
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p q_H0 (p q_v0 q_v1)) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change (p v0 v1) = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3
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
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p q_H0 q_H1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change (p v0 v1) = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
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
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p (p q_v0 q_x) (p q_v0 q_v1)) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change H1 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p (p q_v0 q_x) q_H1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change H1 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
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
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p q_H0 (p q_v0 q_v1)) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change H1 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs0hB s0B s1B qs0B qs1B z0 z1 z2 z3
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
          have p0 := congrArg (fun q => (L q)) (ha)
          change H0 = (p (p q_H0 q_H1) q_v0) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R q)) (ha)
          change H1 = q_x at p1
          have z1 := congrArg sz p1
          have p2 := hb
          change v0 = q_v0 at p2
          have z2 := congrArg sz p2
          have p3 := ho
          change o = q_x at p3
          have z3 := congrArg sz p3
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3
          omega
theorem nr2 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 x H0)
    (s1 : Step v0 v1 H1) :
    ¬ ∃ o, Code (p (p H0 H1) v0) x o := by
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
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p q_v0 q_x) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change x = (p q_v0 q_v1) at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change (p v0 v1) = q_v0 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v0 = q_x at e3
          have e4 := congrArg (fun q => q) hb
          change x = q_v0 at e4
          have cyc : q_v0 = (p (p q_v0 q_x) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let peq4 := e4; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p (p q_v0 q_x) v1) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p q_v0 q_x) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change x = q_H1 at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change (p v0 v1) = q_v0 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v0 = q_x at e3
          have e4 := congrArg (fun q => q) hb
          change x = q_v0 at e4
          have cyc : q_v0 = (p (p q_v0 q_x) v1) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let peq4 := e4; let pst0 := congrArg (fun q => p q v1) (peq0); let pst1 := Eq.symm (pst0); let pst2 := Eq.trans (pst1) (peq2); let pst3 := Eq.symm (pst2); pst3)
          have hlt : sz q_v0 < sz (p (p q_v0 q_x) v1) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_left (p q_v0 q_x) v1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 := congrArg (fun q => (L (L (L q)))) (ha); let peq1 := congrArg (fun q => (R (L (L q)))) (ha); let peq2 := congrArg (fun q => (R (L q))) (ha); let peq3 := congrArg (fun q => (R q)) (ha); let peq4 := hb; let peq5 := ho; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq4); let pst2 := congrArg (fun q => p q v1) (peq0); let pst3 := Eq.symm (pst2); let pst4 := Eq.trans (pst3) (peq2); let pst5 := Eq.symm (pst4); let pst6 := Eq.symm (peq0); let pst7 := Eq.trans (pst6) (peq3); let pst8 := congrArg (fun q => p q v1) (pst7); let pst9 := Eq.trans (pst5) (pst8); let pst10 := Eq.trans (pst1) (pst9); let pst11 := congrArg (fun q => p q v1) (pst7); let pst12 := Eq.trans (pst5) (pst11); let pst13 := Eq.symm (pst12); let pst14 := Eq.trans (pst10) (pst13); pst14)
        exact step_ne_first (by simpa only [he] using qs1)
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p q_v0 q_x) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change x = (p q_v0 q_v1) at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change H1 = q_v0 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v0 = q_x at e3
          have e4 := congrArg (fun q => q) hb
          change x = q_v0 at e4
          have cyc : q_x = (p q_v0 q_x) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let peq4 := e4; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p q_v0 q_x) := sz_lt_p_right q_v0 q_x
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p q_v0 q_x) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change x = q_H1 at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change H1 = q_v0 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v0 = q_x at e3
          have e4 := congrArg (fun q => q) hb
          change x = q_v0 at e4
          have cyc : q_x = (p q_v0 q_x) := (let peq0 := e0; let peq1 := e1; let peq2 := e2; let peq3 := e3; let peq4 := e4; let pst0 := Eq.symm (peq0); let pst1 := Eq.trans (pst0) (peq3); let pst2 := Eq.symm (pst1); pst2)
          have hlt : sz q_x < sz (p q_v0 q_x) := sz_lt_p_right q_v0 q_x
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have he : q_H1 = q_v0 := (let peq0 := congrArg (fun q => (L (L (L q)))) (ha); let peq1 := congrArg (fun q => (R (L (L q)))) (ha); let peq2 := congrArg (fun q => (R (L q))) (ha); let peq3 := congrArg (fun q => (R q)) (ha); let peq4 := hb; let peq5 := ho; let pst0 := Eq.symm (peq1); let pst1 := Eq.trans (pst0) (peq4); pst1)
        exact step_ne_first (by simpa only [he] using qs1)
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
          have p0 := congrArg (fun q => (L (L q))) (ha)
          change H0 = (p (p q_v0 q_x) (p q_v0 q_v1)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L q))) (ha)
          change (p v0 v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (ha)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := hb
          change x = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L q))) (ha)
          change H0 = (p (p q_v0 q_x) q_H1) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L q))) (ha)
          change (p v0 v1) = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (ha)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := hb
          change x = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : q_v0 = (p v0 v1) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q v1) (peq2); let pst2 := Eq.trans (pst0) (pst1); let pst3 := congrArg (fun q => p q v1) (peq2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst2) (pst4); pst5)
          have enb : q_x = v0 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq2); pst0)
          apply s1N
          refine ⟨q_H0, ?_⟩
          simpa only [ena, enb] using qs0h
        | hit qs1h =>
          have ena : q_v0 = (p v0 v1) := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq1); let pst1 := congrArg (fun q => p q v1) (peq2); let pst2 := Eq.trans (pst0) (pst1); let pst3 := congrArg (fun q => p q v1) (peq2); let pst4 := Eq.symm (pst3); let pst5 := Eq.trans (pst2) (pst4); pst5)
          have enb : q_x = v0 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq2); pst0)
          apply s1N
          refine ⟨q_H0, ?_⟩
          simpa only [ena, enb] using qs0h
    | hit s1h =>
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
          have s1hB := code_bounds s1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L q))) (ha)
          change H0 = (p (p q_v0 q_x) (p q_v0 q_v1)) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L q))) (ha)
          change H1 = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (ha)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := hb
          change x = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
        | hit qs1h =>
          have hcB := code_bounds hc
          have s0hB := code_bounds s0h
          have s1hB := code_bounds s1h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L q))) (ha)
          change H0 = (p (p q_v0 q_x) q_H1) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L q))) (ha)
          change H1 = q_v0 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R q)) (ha)
          change v0 = q_x at p2
          have z2 := congrArg sz p2
          have p3 := hb
          change x = q_v0 at p3
          have z3 := congrArg sz p3
          have p4 := ho
          change o = q_x at p4
          have z4 := congrArg sz p4
          simp only [getOut, L, R, U, sz] at hcB s0hB s1hB qs1hB s0B s1B qs0B qs1B z0 z1 z2 z3 z4
          omega
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : q_v0 = H1 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq1); pst0)
          have enb : q_x = v0 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq2); pst0)
          apply s1N
          refine ⟨q_H0, ?_⟩
          simpa only [ena, enb] using qs0h
        | hit qs1h =>
          have ena : q_v0 = H1 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq1); pst0)
          have enb : q_x = v0 := (let peq0 := congrArg (fun q => (L (L q))) (ha); let peq1 := congrArg (fun q => (R (L q))) (ha); let peq2 := congrArg (fun q => (R q)) (ha); let peq3 := hb; let peq4 := ho; let pst0 := Eq.symm (peq2); pst0)
          apply s1N
          refine ⟨q_H0, ?_⟩
          simpa only [ena, enb] using qs0h
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval v0 x) (eval v0 v1)) v0) x) v0) := by
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
  let H1 := eval v0 v1
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : v1 = v1 := by
    change v1 = v1
    rfl
  have s1 : Step v0 v1 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 v1
  change x = (eval (eval (eval (eval H0 H1) v0) x) v0)
  have rawEq : (eval (eval (eval (eval H0 H1) v0) x) v0) = (eval (p (p (p H0 H1) v0) x) v0) := by
    calc
      (eval (eval (eval (eval H0 H1) v0) x) v0) = (eval (eval (eval (p H0 H1) v0) x) v0) := congrArg (fun q => (eval (eval (eval q v0) x) v0)) (eval_raw (nr0 x v0 v1 H0 H1 s0 s1))
      _ = (eval (eval (p (p H0 H1) v0) x) v0) := congrArg (fun q => (eval (eval q x) v0)) (eval_raw (nr1 x v0 v1 H0 H1 s0 s1))
      _ = (eval (p (p (p H0 H1) v0) x) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr2 x v0 v1 H0 H1 s0 s1))
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
