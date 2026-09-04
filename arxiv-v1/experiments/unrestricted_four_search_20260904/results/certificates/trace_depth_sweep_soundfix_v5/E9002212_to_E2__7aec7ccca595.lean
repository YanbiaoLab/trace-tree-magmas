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
      (s1 : Step H0 v0 H1) :
      Code (p v0 H1) (p (p x (p x (p v0 v0))) v0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v1 q_H0 ∧ Step q_H0 q_v0 q_H1 ∧ a = (p q_v0 q_H1) ∧ b = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L b))
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
      change k = (p (p q_x q_v1) q_v0) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e2
      have cyc : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))) (sz_lt_p_left (p q_x (p q_x (p q_v0 q_v0))) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_H1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e2
      have cyc : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))) (sz_lt_p_left (p q_x (p q_x (p q_v0 q_v0))) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_H0 q_v0) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e2
      have cyc : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))) (sz_lt_p_left (p q_x (p q_x (p q_v0 q_v0))) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_H1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e2
      have cyc : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))) (sz_lt_p_left (p q_x (p q_x (p q_v0 q_v0))) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H1 : CM)
    (s1 : Step H0 v0 H1) :
    ¬ ∃ o, Code v0 H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s1 with
  | raw =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p (p q_x q_v1) q_v0)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = q_v0 at e2
        have cyc : q_v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := (let peq0 : v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_v1) q_v0)) := sz_lt_p_left q_v0 (p (p q_x q_v1) q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 q_H1) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : v0 = (p q_v0 q_H1) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 q_H1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p q_H0 q_v0)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = q_v0 at e2
        have cyc : q_v0 = (p q_v0 (p q_H0 q_v0)) := (let peq0 : v0 = (p q_v0 (p q_H0 q_v0)) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 (p q_H0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_H0 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 (p q_H0 q_v0)) := sz_lt_p_left q_v0 (p q_H0 q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 q_H1) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change H0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v0 = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : v0 = (p q_v0 q_H1) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 q_H1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p (p q_x q_v1) q) (pst2); let pst4 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p (p q_x q_v1) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_v1) q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p (p q_x q_v1) q) (pst2); let pst4 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p (p q_x q_v1) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_v1) q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p (p q_x q_v1) q) (pst2); let pst4 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p (p q_x q_v1) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_v1) q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p (p q_x q_v1) q) (pst2); let pst4 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p (p q_x q_v1) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_v1) q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right (p q_x q_v1) (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change v0 = (p q_v0 q_H1) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB z0 z1 z2
        omega
    | hit qs0h =>
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p q_H0 q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p q_H0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H0 q_v0) = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p q_H0 q_v0) := Eq.symm (pst3); let pst5 : (p q_H0 q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p q_H0 q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p q_H0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H0 q_v0) = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p q_H0 q_v0) := Eq.symm (pst3); let pst5 : (p q_H0 q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p q_H0 q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p q_H0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H0 q_v0) = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p q_H0 q_v0) := Eq.symm (pst3); let pst5 : (p q_H0 q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := (let peq0 : v0 = (p q_v0 (p q_H0 q_v0)) := ha; let peq4 : v0 = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := u0b; let pst0 : (p q_v0 (p q_H0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = (p (p u0_x (p u0_x (p u0_v0 u0_v0))) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_x (p u0_v0 u0_v0))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H0 q_v0) = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = (p q_H0 q_v0) := Eq.symm (pst3); let pst5 : (p q_H0 q_v0) = u0_v0 := congrArg (fun q => R q) (pst1); let pst6 : (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) = u0_v0 := Eq.trans (pst4) (pst5); let pst7 : u0_v0 = (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Eq.symm (pst6); pst7)
            have hlt : sz u0_v0 < sz (p q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_right u0_x (p u0_v0 u0_v0))) (sz_lt_p_right u0_x (p u0_x (p u0_v0 u0_v0)))) (sz_lt_p_right q_H0 (p u0_x (p u0_x (p u0_v0 u0_v0))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change v0 = (p q_v0 q_H1) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB z0 z1 z2
        omega
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 (p (p q_x q_v1) q_v0)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e1
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq0 : v0 = (p q_v0 (p (p q_x q_v1) q_v0)) := e0; let peq1 : v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e1; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 q_H1) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e1
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq0 : v0 = (p q_v0 q_H1) := e0; let peq1 : v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e1; let pst0 : (p q_v0 q_H1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 (p q_H0 q_v0)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e1
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq0 : v0 = (p q_v0 (p q_H0 q_v0)) := e0; let peq1 : v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e1; let pst0 : (p q_v0 (p q_H0 q_v0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p q_v0 q_H1) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e1
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq0 : v0 = (p q_v0 q_H1) := e0; let peq1 : v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e1; let pst0 : (p q_v0 q_H1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 (p (p q_x q_v1) q_v0)) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq1 : v0 = (p q_x (p q_x (p q_v0 q_v0))) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_x (p q_x (p q_v0 q_v0))) = v0 := Eq.symm (peq1); let pst1 : (p q_x (p q_x (p q_v0 q_v0))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 q_H1) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq1 : v0 = (p q_x (p q_x (p q_v0 q_v0))) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_x (p q_x (p q_v0 q_v0))) = v0 := Eq.symm (peq1); let pst1 : (p q_x (p q_x (p q_v0 q_v0))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 (p q_H0 q_v0)) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq1 : v0 = (p q_x (p q_x (p q_v0 q_v0))) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_x (p q_x (p q_v0 q_v0))) = v0 := Eq.symm (peq1); let pst1 : (p q_x (p q_x (p q_v0 q_v0))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 q_H1) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := (let peq1 : v0 = (p q_x (p q_x (p q_v0 q_v0))) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_x (p q_x (p q_v0 q_v0))) = v0 := Eq.symm (peq1); let pst1 : (p q_x (p q_x (p q_v0 q_v0))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x (p q_x (p q_v0 q_v0))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_x (p q_x (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_x (p q_v0 q_v0))) (sz_lt_p_right q_x (p q_x (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x (p x (p v0 v0)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 (p (p q_x q_v1) q_v0)) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change x = (p q_x (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change (p v0 v0) = q_v0 at e2
      have cyc : q_x = (p q_x q_v1) := (let peq0 : x = (p q_v0 (p (p q_x q_v1) q_v0)) := e0; let peq1 : x = (p q_x (p q_x (p q_v0 q_v0))) := e1; let pst0 : (p q_v0 (p (p q_x q_v1) q_v0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_x q_v1) q_v0)) = (p q_x (p q_x (p q_v0 q_v0))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_v1) q_v0) = (p (p q_x q_v1) q_x) := congrArg (fun q => p (p q_x q_v1) q) (pst2); let pst4 : (p (p q_x q_v1) q_x) = (p (p q_x q_v1) q_v0) := Eq.symm (pst3); let pst5 : (p (p q_x q_v1) q_v0) = (p q_x (p q_v0 q_v0)) := congrArg (fun q => R q) (pst1); let pst6 : (p (p q_x q_v1) q_x) = (p q_x (p q_v0 q_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p q_v0 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst8 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst2); let pst9 : (p q_v0 q_v0) = (p q_x q_x) := Eq.trans (pst7) (pst8); let pst10 : (p q_x (p q_v0 q_v0)) = (p q_x (p q_x q_x)) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p (p q_x q_v1) q_x) = (p q_x (p q_x q_x)) := Eq.trans (pst6) (pst10); let pst12 : (p q_x q_v1) = q_x := congrArg (fun q => L q) (pst11); let pst13 : q_x = (p q_x q_v1) := Eq.symm (pst12); pst13)
      have hlt : sz q_x < sz (p q_x q_v1) := sz_lt_p_left q_x q_v1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have epa : (p q_x q_v1) = (p (p v0 v0) q_v1) := congrArg (fun q => p q q_v1) (Eq.symm (Eq.trans (congrArg (fun q => (R q)) (hb)) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (congrArg (fun q => (L q)) (hb))))))
      have epb : q_v0 = (p v0 v0) := Eq.trans (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (congrArg (fun q => (L q)) (hb)))) (Eq.symm (Eq.trans (congrArg (fun q => (R q)) (hb)) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (congrArg (fun q => (L q)) (hb))))))
      apply code_no_pair_left (p v0 v0) q_v1
      exact ⟨_, by simpa only [epa, epb] using qs1h⟩
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 (p q_H0 q_v0)) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change x = (p q_x (p q_x (p q_v0 q_v0))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change (p v0 v0) = q_v0 at e2
      have cyc : q_x = (p q_x q_x) := (let peq0 : x = (p q_v0 (p q_H0 q_v0)) := e0; let peq1 : x = (p q_x (p q_x (p q_v0 q_v0))) := e1; let pst0 : (p q_v0 (p q_H0 q_v0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_H0 q_v0)) = (p q_x (p q_x (p q_v0 q_v0))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_H0 q_v0) = (p q_H0 q_x) := congrArg (fun q => p q_H0 q) (pst2); let pst4 : (p q_H0 q_x) = (p q_H0 q_v0) := Eq.symm (pst3); let pst5 : (p q_H0 q_v0) = (p q_x (p q_v0 q_v0)) := congrArg (fun q => R q) (pst1); let pst6 : (p q_H0 q_x) = (p q_x (p q_v0 q_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p q_v0 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst8 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst2); let pst9 : (p q_v0 q_v0) = (p q_x q_x) := Eq.trans (pst7) (pst8); let pst10 : (p q_x (p q_v0 q_v0)) = (p q_x (p q_x q_x)) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p q_H0 q_x) = (p q_x (p q_x q_x)) := Eq.trans (pst6) (pst10); let pst12 : q_x = (p q_x q_x) := congrArg (fun q => R q) (pst11); pst12)
      have hlt : sz q_x < sz (p q_x q_x) := sz_lt_p_left q_x q_x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change x = (p q_v0 q_H1) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change x = (p q_x (p q_x (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (hb)
      change (p v0 v0) = q_v0 at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3
      omega
theorem nr4 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p x (p x (p v0 v0))) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L (R q))) ha
      change x = (p q_x q_v1) at e1
      have e2 := congrArg (fun q => (R (R q))) ha
      change (p v0 v0) = q_v0 at e2
      have e3 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e3
      have cyc : q_v1 = (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (p q_v1 q_v1)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_x q_v1) := e1; let peq2 : (p v0 v0) = q_v0 := e2; let peq3 : v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e3; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p v0 v0) = (p q_x q_v1) := Eq.trans (peq2) (pst1); let pst3 : v0 = q_x := congrArg (fun q => L q) (pst2); let pst4 : q_x = v0 := Eq.symm (pst3); let pst5 : v0 = q_v1 := congrArg (fun q => R q) (pst2); let pst6 : q_x = q_v1 := Eq.trans (pst4) (pst5); let pst7 : v0 = q_v1 := Eq.trans (pst3) (pst6); let pst8 : q_v1 = v0 := Eq.symm (pst7); let pst9 : q_v1 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := Eq.trans (pst8) (peq3); let pst10 : (p q_x (p q_x (p q_v0 q_v0))) = (p q_v1 (p q_x (p q_v0 q_v0))) := congrArg (fun q => p q (p q_x (p q_v0 q_v0))) (pst6); let pst11 : (p q_x (p q_v0 q_v0)) = (p q_v1 (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst6); let pst12 : (p q_x q_v1) = (p q_v1 q_v1) := congrArg (fun q => p q q_v1) (pst6); let pst13 : q_v0 = (p q_v1 q_v1) := Eq.trans (pst1) (pst12); let pst14 : (p q_v0 q_v0) = (p (p q_v1 q_v1) q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst15 : (p q_x q_v1) = (p q_v1 q_v1) := congrArg (fun q => p q q_v1) (pst6); let pst16 : q_v0 = (p q_v1 q_v1) := Eq.trans (pst1) (pst15); let pst17 : (p (p q_v1 q_v1) q_v0) = (p (p q_v1 q_v1) (p q_v1 q_v1)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst16); let pst18 : (p q_v0 q_v0) = (p (p q_v1 q_v1) (p q_v1 q_v1)) := Eq.trans (pst14) (pst17); let pst19 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1))) := congrArg (fun q => p q_v1 q) (pst18); let pst20 : (p q_x (p q_v0 q_v0)) = (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1))) := Eq.trans (pst11) (pst19); let pst21 : (p q_v1 (p q_x (p q_v0 q_v0))) = (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) := congrArg (fun q => p q_v1 q) (pst20); let pst22 : (p q_x (p q_x (p q_v0 q_v0))) = (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) := Eq.trans (pst10) (pst21); let pst23 : (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) = (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) q_v0) := congrArg (fun q => p q q_v0) (pst22); let pst24 : (p q_x q_v1) = (p q_v1 q_v1) := congrArg (fun q => p q q_v1) (pst6); let pst25 : q_v0 = (p q_v1 q_v1) := Eq.trans (pst1) (pst24); let pst26 : (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) q_v0) = (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (p q_v1 q_v1)) := congrArg (fun q => p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) q) (pst25); let pst27 : (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) = (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (p q_v1 q_v1)) := Eq.trans (pst23) (pst26); let pst28 : q_v1 = (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (p q_v1 q_v1)) := Eq.trans (pst9) (pst27); pst28)
      have hlt : sz q_v1 < sz (p (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (sz_lt_p_left (p q_v1 (p q_v1 (p (p q_v1 q_v1) (p q_v1 q_v1)))) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs1hB := code_bounds qs1h
      have p0 := congrArg (fun q => (L q)) (ha)
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change (p x (p v0 v0)) = q_H1 at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs1hB z0 z1 z2 z3
      omega
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L (R q))) ha
      change x = q_H0 at e1
      have e2 := congrArg (fun q => (R (R q))) ha
      change (p v0 v0) = q_v0 at e2
      have e3 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at e3
      have cyc : v0 = (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) (p v0 v0)) := (let peq0 : x = q_v0 := e0; let peq1 : x = q_H0 := e1; let peq2 : (p v0 v0) = q_v0 := e2; let peq3 : v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) := e3; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = q_H0 := Eq.trans (pst0) (peq1); let pst2 : (p v0 v0) = q_H0 := Eq.trans (peq2) (pst1); let pst3 : q_H0 = (p v0 v0) := Eq.symm (pst2); let pst4 : q_v0 = (p v0 v0) := Eq.trans (pst1) (pst3); let pst5 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : q_v0 = (p v0 v0) := Eq.trans (pst1) (pst3); let pst7 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst6); let pst8 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst5) (pst7); let pst9 : (p q_x (p q_v0 q_v0)) = (p q_x (p (p v0 v0) (p v0 v0))) := congrArg (fun q => p q_x q) (pst8); let pst10 : (p q_x (p q_x (p q_v0 q_v0))) = (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) := congrArg (fun q => p q_x q) (pst9); let pst11 : (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) = (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) q_v0) := congrArg (fun q => p q q_v0) (pst10); let pst12 : q_v0 = (p v0 v0) := Eq.trans (pst1) (pst3); let pst13 : (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) q_v0) = (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) (p v0 v0)) := congrArg (fun q => p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) q) (pst12); let pst14 : (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) = (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) (p v0 v0)) := Eq.trans (pst11) (pst13); let pst15 : v0 = (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) (p v0 v0)) := Eq.trans (peq3) (pst14); pst15)
      have hlt : sz v0 < sz (p (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) (p v0 v0)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_right q_x (p (p v0 v0) (p v0 v0)))) (sz_lt_p_right q_x (p q_x (p (p v0 v0) (p v0 v0))))) (sz_lt_p_left (p q_x (p q_x (p (p v0 v0) (p v0 v0)))) (p v0 v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := congrArg (fun q => (L q)) (ha)
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change (p x (p v0 v0)) = q_H1 at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v0 = (p (p q_x (p q_x (p q_v0 q_v0))) q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3
      omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 (eval (eval x v1) v0)) (eval (eval x (eval x (eval v0 v0))) v0)) := by
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
  let H1 := eval (eval x v1) v0
  have e1a : (eval x v1) = H0 := by
    change H0 = H0
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step H0 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval x v1) v0
  change x = (eval (eval v0 H1) (eval (eval x (eval x (eval v0 v0))) v0))
  have rawEq : (eval (eval v0 H1) (eval (eval x (eval x (eval v0 v0))) v0)) = (eval (p v0 H1) (p (p x (p x (p v0 v0))) v0)) := by
    calc
      (eval (eval v0 H1) (eval (eval x (eval x (eval v0 v0))) v0)) = (eval (p v0 H1) (eval (eval x (eval x (eval v0 v0))) v0)) := congrArg (fun q => (eval q (eval (eval x (eval x (eval v0 v0))) v0))) (eval_raw (nr0 x v0 v1 H1 s1))
      _ = (eval (p v0 H1) (eval (eval x (eval x (p v0 v0))) v0)) := congrArg (fun q => (eval (p v0 H1) (eval (eval x (eval x q)) v0))) (eval_raw (nr1 x v0 v1))
      _ = (eval (p v0 H1) (eval (eval x (p x (p v0 v0))) v0)) := congrArg (fun q => (eval (p v0 H1) (eval (eval x q) v0))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p v0 H1) (eval (p x (p x (p v0 v0))) v0)) := congrArg (fun q => (eval (p v0 H1) (eval q v0))) (eval_raw (nr3 x v0 v1))
      _ = (eval (p v0 H1) (p (p x (p x (p v0 v0))) v0)) := congrArg (fun q => (eval (p v0 H1) q)) (eval_raw (nr4 x v0 v1))
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
