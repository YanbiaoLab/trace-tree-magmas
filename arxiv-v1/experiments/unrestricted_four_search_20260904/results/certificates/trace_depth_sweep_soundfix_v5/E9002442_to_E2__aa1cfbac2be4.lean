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
      (s1 : Step v1 v0 H1) :
      Code (p v0 v0) (p H0 (p x (p v0 H1))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v0 q_H0 ∧ Step q_v1 q_v0 q_H1 ∧ a = (p q_v0 q_v0) ∧ b = (p q_H0 (p q_x (p q_v0 q_H1))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R b))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc)
    omega

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
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) at e2
      have cyc : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) at e2
      have cyc : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) (p q_x (p q_v0 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) at e2
      have cyc : q_v0 = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_right q_x (p q_v0 (p q_v1 q_v0)))) (sz_lt_p_right q_H0 (p q_x (p q_v0 (p q_v1 q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_H0 (p q_x (p q_v0 q_H1))) at e2
      have cyc : q_v0 = (p q_H0 (p q_x (p q_v0 q_H1))) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p q_H0 (p q_x (p q_v0 q_H1))) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 (p q_x (p q_v0 q_H1))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_H0 (p q_x (p q_v0 q_H1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H1) (sz_lt_p_right q_x (p q_v0 q_H1))) (sz_lt_p_right q_H0 (p q_x (p q_v0 q_H1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw =>
    rintro ⟨u, hc⟩
    exact code_no_pair_left a b ⟨u, hc⟩
  | hit sth =>
    rintro ⟨u, hc⟩
    rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : q_v0 = (p q_v0 q_H1) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_H1) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 q_H1) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : q_v0 = (p q_v0 q_H1) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_H1) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 q_H1) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : q_v0 = (p q_v0 q_H1) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_H1) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 q_H1) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : q_v0 = (p q_v0 q_H1) := (let peq1 : a = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let pst0 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_x q_v0) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_x q_v0) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p q_x q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_H1) = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : q_v0 = (p q_v0 q_H1) := Eq.symm (pst6); pst7)
            have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 (p q_v1 q_v0))) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v1 q_v0))) (peq6); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (peq7); let pst7 : (p q_v1 q_v0) = (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))) := congrArg (fun q => p q_v1 q) (peq7); let pst8 : (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := congrArg (fun q => p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))) := Eq.trans (pst6) (pst8); let pst10 : (p (p u1_v0 u1_v0) (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst9); let pst11 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst5) (pst10); let pst12 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst4) (pst11); let pst13 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.trans (pst2) (pst12); let pst14 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = q_H0 := Eq.symm (pst13); let pst15 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) = u1_x := Eq.trans (pst14) (peq8); let pst16 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Eq.symm (pst15); pst16)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out)))))) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) (p q_v1 (p u1s0out (p u1_x (p u1_v0 u1s1out))))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1_v0) (sz_lt_p_left (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p (p u1_x u1_v0) (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 (p u1_v1 u1_v0))) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0))))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 (p u1_v1 u1_v0)))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := (let peq1 : a = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq3 : a = (p u0_v0 u0_v0) := u0a; let peq6 : q_x = (p u1_v0 u1_v0) := u1a; let peq7 : q_v0 = (p u1s0out (p u1_x (p u1_v0 u1s1out))) := u1b; let peq8 : q_H0 = u1_x := u1o; let pst0 : (p q_H0 (p q_x (p q_v0 q_H1))) = a := Eq.symm (peq1); let pst1 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p u0_v0 u0_v0) := Eq.trans (pst0) (peq3); let pst2 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_v0 q_H1)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst4 : u0_v0 = (p q_x (p q_v0 q_H1)) := Eq.symm (pst3); let pst5 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p q_v0 q_H1)) := congrArg (fun q => p q (p q_v0 q_H1)) (peq6); let pst6 : (p q_v0 q_H1) = (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1) := congrArg (fun q => p q q_H1) (peq7); let pst7 : (p (p u1_v0 u1_v0) (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst5) (pst7); let pst9 : u0_v0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H0 = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.trans (pst2) (pst9); let pst11 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = q_H0 := Eq.symm (pst10); let pst12 : (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) = u1_x := Eq.trans (pst11) (peq8); let pst13 : u1_x = (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Eq.symm (pst12); pst13)
                have hlt : sz u1_x < sz (p (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1s1out)) (sz_lt_p_right u1s0out (p u1_x (p u1_v0 u1s1out)))) (sz_lt_p_left (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1)) (sz_lt_p_right (p u1_v0 u1_v0) (p (p u1s0out (p u1_x (p u1_v0 u1s1out))) q_H1))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) at e1
      have cyc : q_v0 = (p q_x q_v0) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x q_v0) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x q_v0) := sz_lt_p_right q_x q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) at e1
      have cyc : q_v0 = (p q_x q_v0) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x q_v0) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x q_v0) := sz_lt_p_right q_x q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) at e1
      have cyc : q_H0 = (p q_x (p q_H0 (p q_v1 q_H0))) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_H0 := congrArg (fun q => L q) (pst1); let pst3 : q_H0 = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := congrArg (fun q => R q) (pst1); let pst5 : q_H0 = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.trans (pst3) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p q_H0 (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst2); let pst7 : (p q_v1 q_v0) = (p q_v1 q_H0) := congrArg (fun q => p q_v1 q) (pst2); let pst8 : (p q_H0 (p q_v1 q_v0)) = (p q_H0 (p q_v1 q_H0)) := congrArg (fun q => p q_H0 q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p q_H0 (p q_v1 q_H0)) := Eq.trans (pst6) (pst8); let pst10 : (p q_x (p q_v0 (p q_v1 q_v0))) = (p q_x (p q_H0 (p q_v1 q_H0))) := congrArg (fun q => p q_x q) (pst9); let pst11 : q_H0 = (p q_x (p q_H0 (p q_v1 q_H0))) := Eq.trans (pst5) (pst10); pst11)
      have hlt : sz q_H0 < sz (p q_x (p q_H0 (p q_v1 q_H0))) := Nat.lt_trans (sz_lt_p_left q_H0 (p q_v1 q_H0)) (sz_lt_p_right q_x (p q_H0 (p q_v1 q_H0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_H0 (p q_x (p q_v0 q_H1))) at e1
      have cyc : q_H0 = (p q_x (p q_H0 q_H1)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_H0 (p q_x (p q_v0 q_H1))) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_H0 (p q_x (p q_v0 q_H1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_H0 := congrArg (fun q => L q) (pst1); let pst3 : q_H0 = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_x (p q_v0 q_H1)) := congrArg (fun q => R q) (pst1); let pst5 : q_H0 = (p q_x (p q_v0 q_H1)) := Eq.trans (pst3) (pst4); let pst6 : (p q_v0 q_H1) = (p q_H0 q_H1) := congrArg (fun q => p q q_H1) (pst2); let pst7 : (p q_x (p q_v0 q_H1)) = (p q_x (p q_H0 q_H1)) := congrArg (fun q => p q_x q) (pst6); let pst8 : q_H0 = (p q_x (p q_H0 q_H1)) := Eq.trans (pst5) (pst7); pst8)
      have hlt : sz q_H0 < sz (p q_x (p q_H0 q_H1)) := Nat.lt_trans (sz_lt_p_left q_H0 q_H1) (sz_lt_p_right q_x (p q_H0 q_H1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step v1 v0 H1) :
    ¬ ∃ o, Code v0 H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 q_v0) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p q_x q_v0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 (p q_v1 q_v0))) at e2
        have cyc : q_x = (p q_x (p q_v1 q_x)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq2 : v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := e2; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_v0 (p q_v1 q_v0)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_v0 (p q_v1 q_v0)) := Eq.trans (pst3) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p q_x (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst2); let pst7 : (p q_v1 q_v0) = (p q_v1 q_x) := congrArg (fun q => p q_v1 q) (pst2); let pst8 : (p q_x (p q_v1 q_v0)) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p q_x (p q_v1 q_x)) := Eq.trans (pst6) (pst8); let pst10 : q_x = (p q_x (p q_v1 q_x)) := Eq.trans (pst5) (pst9); pst10)
        have hlt : sz q_x < sz (p q_x (p q_v1 q_x)) := sz_lt_p_left q_x (p q_v1 q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 q_v0) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = (p q_x q_v0) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 q_H1)) at e2
        have cyc : q_x = (p q_x q_H1) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq2 : v0 = (p q_x (p q_v0 q_H1)) := e2; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_v0 q_H1)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_v0 q_H1) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_v0 q_H1) := Eq.trans (pst3) (pst4); let pst6 : (p q_v0 q_H1) = (p q_x q_H1) := congrArg (fun q => p q q_H1) (pst2); let pst7 : q_x = (p q_x q_H1) := Eq.trans (pst5) (pst6); pst7)
        have hlt : sz q_x < sz (p q_x q_H1) := sz_lt_p_left q_x q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 q_v0) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = q_H0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 (p q_v1 q_v0))) at e2
        have cyc : q_x = (p q_x (p q_v1 q_x)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq2 : v0 = (p q_x (p q_v0 (p q_v1 q_v0))) := e2; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_v0 (p q_v1 q_v0))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_v0 (p q_v1 q_v0)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_v0 (p q_v1 q_v0)) := Eq.trans (pst3) (pst4); let pst6 : (p q_v0 (p q_v1 q_v0)) = (p q_x (p q_v1 q_v0)) := congrArg (fun q => p q (p q_v1 q_v0)) (pst2); let pst7 : (p q_v1 q_v0) = (p q_v1 q_x) := congrArg (fun q => p q_v1 q) (pst2); let pst8 : (p q_x (p q_v1 q_v0)) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p q_v0 (p q_v1 q_v0)) = (p q_x (p q_v1 q_x)) := Eq.trans (pst6) (pst8); let pst10 : q_x = (p q_x (p q_v1 q_x)) := Eq.trans (pst5) (pst9); pst10)
        have hlt : sz q_x < sz (p q_x (p q_v1 q_x)) := sz_lt_p_left q_x (p q_v1 q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 q_v0) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = q_H0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = (p q_x (p q_v0 q_H1)) at e2
        have cyc : q_x = (p q_x q_H1) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq2 : v0 = (p q_x (p q_v0 q_H1)) := e2; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_v0 q_H1)) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_v0 q_H1) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_v0 q_H1) := Eq.trans (pst3) (pst4); let pst6 : (p q_v0 q_H1) = (p q_x q_H1) := congrArg (fun q => p q q_H1) (pst2); let pst7 : q_x = (p q_x q_H1) := Eq.trans (pst5) (pst6); pst7)
        have hlt : sz q_x < sz (p q_x q_H1) := sz_lt_p_left q_x q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have p0 := ha
        change v0 = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x q_v0) (p q_x (p q_v0 (p q_v1 q_v0)))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change v0 = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x q_v0) (p q_x (p q_v0 q_H1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB z0 z1 z2
        omega
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have p0 := ha
        change v0 = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_H0 (p q_x (p q_v0 (p q_v1 q_v0)))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB z0 z1 z2
        omega
      | hit qs1h =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := (let peq0 : v0 = (p q_v0 q_v0) := ha; let peq4 : v0 = (p (p u0_x u0_v0) (p u0_x (p u0_v0 (p u0_v1 u0_v0)))) := u0b; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p u0_x u0_v0) (p u0_x (p u0_v0 (p u0_v1 u0_v0)))) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p u0_x u0_v0) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_x (p u0_v0 (p u0_v1 u0_v0))) := congrArg (fun q => R q) (pst1); let pst5 : (p u0_x u0_v0) = (p u0_x (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst3) (pst4); let pst6 : u0_v0 = (p u0_v0 (p u0_v1 u0_v0)) := congrArg (fun q => R q) (pst5); pst6)
            have hlt : sz u0_v0 < sz (p u0_v0 (p u0_v1 u0_v0)) := sz_lt_p_left u0_v0 (p u0_v1 u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p u0_v0 u0s1out) := (let peq0 : v0 = (p q_v0 q_v0) := ha; let peq4 : v0 = (p (p u0_x u0_v0) (p u0_x (p u0_v0 u0s1out))) := u0b; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p u0_x u0_v0) (p u0_x (p u0_v0 u0s1out))) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p u0_x u0_v0) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_x (p u0_v0 u0s1out)) := congrArg (fun q => R q) (pst1); let pst5 : (p u0_x u0_v0) = (p u0_x (p u0_v0 u0s1out)) := Eq.trans (pst3) (pst4); let pst6 : u0_v0 = (p u0_v0 u0s1out) := congrArg (fun q => R q) (pst5); pst6)
            have hlt : sz u0_v0 < sz (p u0_v0 u0s1out) := sz_lt_p_left u0_v0 u0s1out
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) := (let peq0 : v0 = (p q_v0 q_v0) := ha; let peq1 : H1 = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq4 : v0 = (p u0s0out (p u0_x (p u0_v0 (p u0_v1 u0_v0)))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p u0s0out (p u0_x (p u0_v0 (p u0_v1 u0_v0)))) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s0out := congrArg (fun q => L q) (pst1); let pst3 : u0s0out = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_x (p u0_v0 (p u0_v1 u0_v0))) := congrArg (fun q => R q) (pst1); let pst5 : u0s0out = (p u0_x (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst3) (pst4); let pst6 : q_v0 = (p u0_x (p u0_v0 (p u0_v1 u0_v0))) := Eq.trans (pst2) (pst5); let pst7 : (p q_v0 q_H1) = (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1) := congrArg (fun q => p q q_H1) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1)) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) := congrArg (fun q => p q_H0 q) (pst8); let pst10 : H1 = (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) := Eq.trans (peq1) (pst9); let pst11 : (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) = H1 := Eq.symm (pst10); let pst12 : (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v0 (p u0_v1 u0_v0))) (sz_lt_p_left (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1)) (sz_lt_p_right q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1))) (sz_lt_p_right q_H0 (p q_x (p (p u0_x (p u0_v0 (p u0_v1 u0_v0))) q_H1)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) := (let peq0 : v0 = (p q_v0 q_v0) := ha; let peq1 : H1 = (p q_H0 (p q_x (p q_v0 q_H1))) := hb; let peq4 : v0 = (p u0s0out (p u0_x (p u0_v0 u0s1out))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p u0s0out (p u0_x (p u0_v0 u0s1out))) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s0out := congrArg (fun q => L q) (pst1); let pst3 : u0s0out = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p u0_x (p u0_v0 u0s1out)) := congrArg (fun q => R q) (pst1); let pst5 : u0s0out = (p u0_x (p u0_v0 u0s1out)) := Eq.trans (pst3) (pst4); let pst6 : q_v0 = (p u0_x (p u0_v0 u0s1out)) := Eq.trans (pst2) (pst5); let pst7 : (p q_v0 q_H1) = (p (p u0_x (p u0_v0 u0s1out)) q_H1) := congrArg (fun q => p q q_H1) (pst6); let pst8 : (p q_x (p q_v0 q_H1)) = (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1)) := congrArg (fun q => p q_x q) (pst7); let pst9 : (p q_H0 (p q_x (p q_v0 q_H1))) = (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) := congrArg (fun q => p q_H0 q) (pst8); let pst10 : H1 = (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) := Eq.trans (peq1) (pst9); let pst11 : (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) = H1 := Eq.symm (pst10); let pst12 : (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v0 u0s1out)) (sz_lt_p_left (p u0_x (p u0_v0 u0s1out)) q_H1)) (sz_lt_p_right q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1))) (sz_lt_p_right q_H0 (p q_x (p (p u0_x (p u0_v0 u0s1out)) q_H1)))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step v1 v0 H1) :
    ¬ ∃ o, Code x (p v0 H1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := (let peq1 : v0 = (p q_x q_v0) := congrArg (fun q => (L q)) (hb); let peq3 : v0 = (p q_v0 q_H1) := congrArg (fun q => (R (R q))) (hb); let pst0 : (p q_x q_v0) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_v0) = (p q_v0 q_H1) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = q_H1 := congrArg (fun q => R q) (pst1); let pst3 : q_H1 = q_v0 := Eq.symm (pst2); pst3)
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have p0 := ha
        change x = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change v1 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change v0 = (p q_v0 (p q_v1 q_v0)) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3 z4
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change x = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (L (R q))) (hb)
        change v1 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := congrArg (fun q => (R (R q))) (hb)
        change v0 = (p q_v0 q_H1) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3 z4
        omega
  | hit s1h =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have p0 := ha
        change x = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = (p q_x q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 (p q_v1 q_v0))) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change x = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = (p q_x q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB z0 z1 z2 z3
        omega
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have p0 := ha
        change x = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 (p q_v1 q_v0))) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change x = (p q_v0 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change H1 = (p q_x (p q_v0 q_H1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB z0 z1 z2 z3
        omega
theorem nr3 (x v0 v1 H0 H1 : CM)
    (s0 : Step x v0 H0)
    (s1 : Step v1 v0 H1) :
    ¬ ∃ o, Code H0 (p x (p v0 H1)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have s1N := step_no_first s1
    cases s1 with
    | raw =>
      have he : q_H0 = q_v0 := (let peq0 : x = q_v0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : x = q_H0 := congrArg (fun q => (L q)) (hb); let peq3 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq5 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H0 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_H0 := Eq.trans (peq1) (pst1); let pst3 : q_H0 = v0 := Eq.symm (pst2); let pst4 : q_H0 = q_x := Eq.trans (pst3) (peq3); let pst5 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst6 : v0 = q_x := Eq.trans (peq1) (pst5); let pst7 : q_x = v0 := Eq.symm (pst6); let pst8 : q_x = q_H1 := Eq.trans (pst7) (peq5); let pst9 : q_H0 = q_H1 := Eq.trans (pst4) (pst8); let pst10 : q_H0 = q_H1 := Eq.trans (pst4) (pst8); let pst11 : q_v0 = q_H1 := Eq.trans (pst1) (pst10); let pst12 : q_H1 = q_v0 := Eq.symm (pst11); let pst13 : q_H0 = q_v0 := Eq.trans (pst9) (pst12); pst13)
      exact step_ne_second (by simpa only [he] using qs0)
    | hit s1h =>
      have he : q_H0 = q_v0 := (let peq0 : x = q_v0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : x = q_H0 := congrArg (fun q => (L q)) (hb); let peq3 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H0 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_H0 := Eq.trans (peq1) (pst1); let pst3 : q_H0 = v0 := Eq.symm (pst2); let pst4 : q_H0 = q_x := Eq.trans (pst3) (peq3); let pst5 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst6 : q_x = q_v0 := Eq.symm (pst5); let pst7 : q_H0 = q_v0 := Eq.trans (pst4) (pst6); pst7)
      exact step_ne_second (by simpa only [he] using qs0)
  | hit s0h =>
    have s1N := step_no_first s1
    cases s1 with
    | raw =>
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : x = (p q_x q_v0) := (let peq1 : x = (p q_x q_v0) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq4 : v0 = (p q_v1 q_v0) := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = (p q_v1 q_v0) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_v0) = (p (p q_v1 q_v0) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst3 : x = (p (p q_v1 q_v0) q_v0) := Eq.trans (peq1) (pst2); let pst4 : (p q_x q_v0) = (p (p q_v1 q_v0) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst5 : (p (p q_v1 q_v0) q_v0) = (p q_x q_v0) := Eq.symm (pst4); let pst6 : x = (p q_x q_v0) := Eq.trans (pst3) (pst5); pst6)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq4 : v0 = (p q_v1 q_v0) := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = (p q_v1 q_v0) := Eq.trans (pst0) (peq4); let pst2 : v0 = (p q_v1 q_v0) := Eq.trans (peq2) (pst1); let pst3 : (p q_v1 q_v0) = q_x := Eq.symm (pst1); let pst4 : v0 = q_x := Eq.trans (pst2) (pst3); pst4)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : x = (p q_x q_v0) := (let peq1 : x = (p q_x q_v0) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = q_H1 := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst3 : x = (p q_H1 q_v0) := Eq.trans (peq1) (pst2); let pst4 : (p q_x q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst5 : (p q_H1 q_v0) = (p q_x q_v0) := Eq.symm (pst4); let pst6 : x = (p q_x q_v0) := Eq.trans (pst3) (pst5); pst6)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = q_H1 := Eq.trans (pst0) (peq4); let pst2 : v0 = q_H1 := Eq.trans (peq2) (pst1); let pst3 : q_H1 = q_x := Eq.symm (pst1); let pst4 : v0 = q_x := Eq.trans (pst2) (pst3); pst4)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
      | hit qs0h =>
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : x = q_H0 := (let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); peq1)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq4 : v0 = (p q_v1 q_v0) := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = (p q_v1 q_v0) := Eq.trans (pst0) (peq4); let pst2 : v0 = (p q_v1 q_v0) := Eq.trans (peq2) (pst1); let pst3 : (p q_v1 q_v0) = q_x := Eq.symm (pst1); let pst4 : v0 = q_x := Eq.trans (pst2) (pst3); pst4)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : x = q_H0 := (let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); peq1)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); let peq4 : v0 = q_H1 := congrArg (fun q => (R (R (R q)))) (hb); let pst0 : q_x = v0 := Eq.symm (peq2); let pst1 : q_x = q_H1 := Eq.trans (pst0) (peq4); let pst2 : v0 = q_H1 := Eq.trans (peq2) (pst1); let pst3 : q_H1 = q_x := Eq.symm (pst1); let pst4 : v0 = q_x := Eq.trans (pst2) (pst3); pst4)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
    | hit s1h =>
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : x = (p q_x q_v0) := (let peq1 : x = (p q_x q_v0) := congrArg (fun q => (L q)) (hb); peq1)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); peq2)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : x = (p q_x q_v0) := (let peq1 : x = (p q_x q_v0) := congrArg (fun q => (L q)) (hb); peq1)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); peq2)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
      | hit qs0h =>
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : x = q_H0 := (let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); peq1)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); peq2)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : x = q_H0 := (let peq1 : x = q_H0 := congrArg (fun q => (L q)) (hb); peq1)
          have enb : v0 = q_x := (let peq2 : v0 = q_x := congrArg (fun q => (L (R q))) (hb); peq2)
          apply qs0N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 v0) (eval (eval x v0) (eval x (eval v0 (eval v1 v0))))) := by
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
  let H1 := eval v1 v0
  have e1a : v1 = v1 := by
    change v1 = v1
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step v1 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v1 v0
  change x = (eval (eval v0 v0) (eval H0 (eval x (eval v0 H1))))
  have rawEq : (eval (eval v0 v0) (eval H0 (eval x (eval v0 H1)))) = (eval (p v0 v0) (p H0 (p x (p v0 H1)))) := by
    calc
      (eval (eval v0 v0) (eval H0 (eval x (eval v0 H1)))) = (eval (p v0 v0) (eval H0 (eval x (eval v0 H1)))) := congrArg (fun q => (eval q (eval H0 (eval x (eval v0 H1))))) (eval_raw (nr0 x v0 v1))
      _ = (eval (p v0 v0) (eval H0 (eval x (p v0 H1)))) := congrArg (fun q => (eval (p v0 v0) (eval H0 (eval x q)))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval (p v0 v0) (eval H0 (p x (p v0 H1)))) := congrArg (fun q => (eval (p v0 v0) (eval H0 q))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval (p v0 v0) (p H0 (p x (p v0 H1)))) := congrArg (fun q => (eval (p v0 v0) q)) (eval_raw (nr3 x v0 v1 H0 H1 s0 s1))
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
