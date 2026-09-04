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
  | law (x v0 v1 H0 : CM)
      (s0 : Step v0 x H0) :
      Code (p v0 (p v1 (p v0 v0))) (p (p x H0) v0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_x q_H0 ∧ a = (p q_v0 (p q_v1 (p q_v0 q_v0))) ∧ b = (p (p q_x q_H0) q_v0) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L b))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x (p q_v0 q_x)) q_v0) at e1
    have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq0 : v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e0; let peq1 : v0 = (p (p q_x (p q_v0 q_x)) q_v0) := e1; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p q_x (p q_v0 q_x)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_v0 q_x)) := congrArg (fun q => L q) (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x q_H0) q_v0) at e1
    have cyc : q_H0 = (p (p q_x q_H0) (p q_x q_H0)) := (let peq0 : v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e0; let peq1 : v0 = (p (p q_x q_H0) q_v0) := e1; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p q_x q_H0) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x q_H0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v0) = (p (p q_x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p q_x q_H0) q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := congrArg (fun q => p (p q_x q_H0) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := Eq.trans (pst3) (pst4); let pst6 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p q_x q_H0) (p q_x q_H0))) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p q_v1 (p (p q_x q_H0) (p q_x q_H0))) = (p q_v1 (p q_v0 q_v0)) := Eq.symm (pst6); let pst8 : (p q_v1 (p q_v0 q_v0)) = q_v0 := congrArg (fun q => R q) (pst1); let pst9 : (p q_v1 (p (p q_x q_H0) (p q_x q_H0))) = q_v0 := Eq.trans (pst7) (pst8); let pst10 : (p q_v1 (p (p q_x q_H0) (p q_x q_H0))) = (p q_x q_H0) := Eq.trans (pst9) (pst2); let pst11 : (p (p q_x q_H0) (p q_x q_H0)) = q_H0 := congrArg (fun q => R q) (pst10); let pst12 : q_H0 = (p (p q_x q_H0) (p q_x q_H0)) := Eq.symm (pst11); pst12)
    have hlt : sz q_H0 < sz (p (p q_x q_H0) (p q_x q_H0)) := Nat.lt_trans (sz_lt_p_right q_x q_H0) (sz_lt_p_left (p q_x q_H0) (p q_x q_H0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x (p q_v0 q_x)) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change v0 = q_v0 at e2
    have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_x (p q_v0 q_x)) = v0 := Eq.symm (peq1); let pst1 : (p q_x (p q_v0 q_x)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x (p q_v0 q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
    let u0s0out := u0_H0
    cases u0s0 with
    | raw =>
      have cyc : u0_v0 = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := (let peq1 : v0 = (p q_x q_H0) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_v0 := congrArg (fun q => (R q)) (hb); let peq4 : q_v0 = (p u0_v0 (p u0_v1 (p u0_v0 u0_v0))) := u0a; let peq5 : q_x = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := u0b; let pst0 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_H0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x q_H0) := Eq.symm (pst1); let pst3 : (p q_x q_H0) = q_v0 := Eq.symm (pst2); let pst4 : (p q_x q_H0) = (p u0_v0 (p u0_v1 (p u0_v0 u0_v0))) := Eq.trans (pst3) (peq4); let pst5 : q_x = u0_v0 := congrArg (fun q => L q) (pst4); let pst6 : u0_v0 = q_x := Eq.symm (pst5); let pst7 : u0_v0 = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := Eq.trans (pst6) (peq5); pst7)
      have hlt : sz u0_v0 < sz (p (p u0_x (p u0_v0 u0_x)) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_right u0_x (p u0_v0 u0_x))) (sz_lt_p_left (p u0_x (p u0_v0 u0_x)) u0_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit u0s0h =>
      have cyc : u0_v0 = (p (p u0_x u0s0out) u0_v0) := (let peq1 : v0 = (p q_x q_H0) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_v0 := congrArg (fun q => (R q)) (hb); let peq4 : q_v0 = (p u0_v0 (p u0_v1 (p u0_v0 u0_v0))) := u0a; let peq5 : q_x = (p (p u0_x u0s0out) u0_v0) := u0b; let pst0 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_H0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_x q_H0) := Eq.symm (pst1); let pst3 : (p q_x q_H0) = q_v0 := Eq.symm (pst2); let pst4 : (p q_x q_H0) = (p u0_v0 (p u0_v1 (p u0_v0 u0_v0))) := Eq.trans (pst3) (peq4); let pst5 : q_x = u0_v0 := congrArg (fun q => L q) (pst4); let pst6 : u0_v0 = q_x := Eq.symm (pst5); let pst7 : u0_v0 = (p (p u0_x u0s0out) u0_v0) := Eq.trans (pst6) (peq5); pst7)
      have hlt : sz u0_v0 < sz (p (p u0_x u0s0out) u0_v0) := sz_lt_p_right (p u0_x u0s0out) u0_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p v1 (p v0 v0)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v1 = (p q_x (p q_v0 q_x)) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change (p v0 v0) = q_v0 at e2
    have cyc : q_v0 = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := (let peq0 : v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e0; let peq2 : (p v0 v0) = q_v0 := e2; let pst0 : (p v0 v0) = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p q_v1 (p q_v0 q_v0))) v0) = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := congrArg (fun q => p (p q_v0 (p q_v1 (p q_v0 q_v0))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Eq.symm (pst4); pst5)
    have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 (p q_v0 q_v0))) (sz_lt_p_left (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v1 = (p q_x q_H0) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change (p v0 v0) = q_v0 at e2
    have cyc : q_v0 = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := (let peq0 : v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e0; let peq2 : (p v0 v0) = q_v0 := e2; let pst0 : (p v0 v0) = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p q_v1 (p q_v0 q_v0))) v0) = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := congrArg (fun q => p (p q_v0 (p q_v1 (p q_v0 q_v0))) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Eq.trans (pst0) (pst1); let pst3 : (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = (p v0 v0) := Eq.symm (pst2); let pst4 : (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Eq.symm (pst4); pst5)
    have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 (p q_v0 q_v0))) (sz_lt_p_left (p q_v0 (p q_v1 (p q_v0 q_v0))) (p q_v0 (p q_v1 (p q_v0 q_v0))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code x H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x (p q_v0 q_x)) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = q_v0 at e2
      have cyc : q_v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := (let peq0 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e0; let peq2 : x = q_v0 := e2; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_v0 (p q_v1 (p q_v0 q_v0))) := sz_lt_p_left q_v0 (p q_v1 (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 (p q_v1 (p q_v0 q_v0))) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x q_H0) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = q_v0 at e2
      have cyc : q_v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := (let peq0 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := e0; let peq2 : x = q_v0 := e2; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_v1 (p q_v0 q_v0))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_v0 (p q_v1 (p q_v0 q_v0))) := sz_lt_p_left q_v0 (p q_v1 (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := (let peq0 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := ha; let peq4 : x = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := u0b; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v0) = (p (p u0_x (p u0_v0 u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p u0_x (p u0_v0 u0_x)) q_v0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x))) := congrArg (fun q => p (p u0_x (p u0_v0 u0_x)) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst3) (pst4); let pst6 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) = (p q_v1 (p q_v0 q_v0)) := Eq.symm (pst6); let pst8 : (p q_v1 (p q_v0 q_v0)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst9 : (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) = u0_v0 := Eq.trans (pst7) (pst8); let pst10 : u0_v0 = (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := Eq.symm (pst9); pst10)
        have hlt : sz u0_v0 < sz (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_right u0_x (p u0_v0 u0_x))) (sz_lt_p_left (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) (sz_lt_p_right q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_x = (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) := (let peq0 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := ha; let peq1 : H0 = (p (p q_x (p q_v0 q_x)) q_v0) := hb; let peq4 : x = (p (p u0_x u0s0out) u0_v0) := u0b; let peq5 : H0 = u0_x := u0o; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p u0_x u0s0out) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x u0s0out) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p (p u0_x u0s0out) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p (p u0_x u0s0out) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p (p q_x (p q_v0 q_x)) q_v0) = (p (p q_x (p (p u0_x u0s0out) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p (p q_x (p (p u0_x u0s0out) q_x)) q_v0) = (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) := congrArg (fun q => p (p q_x (p (p u0_x u0s0out) q_x)) q) (pst2); let pst7 : (p (p q_x (p q_v0 q_x)) q_v0) = (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) := Eq.trans (peq1) (pst7); let pst9 : (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) = H0 := Eq.symm (pst8); let pst10 : (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) = u0_x := Eq.trans (pst9) (peq5); let pst11 : u0_x = (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) := Eq.symm (pst10); pst11)
        have hlt : sz u0_x < sz (p (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s0out) (sz_lt_p_left (p u0_x u0s0out) q_x)) (sz_lt_p_right q_x (p (p u0_x u0s0out) q_x))) (sz_lt_p_left (p q_x (p (p u0_x u0s0out) q_x)) (p u0_x u0s0out))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := (let peq0 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := ha; let peq4 : x = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := u0b; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p u0_x (p u0_v0 u0_x)) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v0) = (p (p u0_x (p u0_v0 u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p u0_x (p u0_v0 u0_x)) q_v0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x))) := congrArg (fun q => p (p u0_x (p u0_v0 u0_x)) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst3) (pst4); let pst6 : (p q_v1 (p q_v0 q_v0)) = (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := congrArg (fun q => p q_v1 q) (pst5); let pst7 : (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) = (p q_v1 (p q_v0 q_v0)) := Eq.symm (pst6); let pst8 : (p q_v1 (p q_v0 q_v0)) = u0_v0 := congrArg (fun q => R q) (pst1); let pst9 : (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) = u0_v0 := Eq.trans (pst7) (pst8); let pst10 : u0_v0 = (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := Eq.symm (pst9); pst10)
        have hlt : sz u0_v0 < sz (p q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_right u0_x (p u0_v0 u0_x))) (sz_lt_p_left (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x)))) (sz_lt_p_right q_v1 (p (p u0_x (p u0_v0 u0_x)) (p u0_x (p u0_v0 u0_x))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_x = (p (p q_x q_H0) (p u0_x u0s0out)) := (let peq0 : x = (p q_v0 (p q_v1 (p q_v0 q_v0))) := ha; let peq1 : H0 = (p (p q_x q_H0) q_v0) := hb; let peq4 : x = (p (p u0_x u0s0out) u0_v0) := u0b; let peq5 : H0 = u0_x := u0o; let pst0 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_v1 (p q_v0 q_v0))) = (p (p u0_x u0s0out) u0_v0) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_x u0s0out) := congrArg (fun q => L q) (pst1); let pst3 : (p (p q_x q_H0) q_v0) = (p (p q_x q_H0) (p u0_x u0s0out)) := congrArg (fun q => p (p q_x q_H0) q) (pst2); let pst4 : H0 = (p (p q_x q_H0) (p u0_x u0s0out)) := Eq.trans (peq1) (pst3); let pst5 : (p (p q_x q_H0) (p u0_x u0s0out)) = H0 := Eq.symm (pst4); let pst6 : (p (p q_x q_H0) (p u0_x u0s0out)) = u0_x := Eq.trans (pst5) (peq5); let pst7 : u0_x = (p (p q_x q_H0) (p u0_x u0s0out)) := Eq.symm (pst6); pst7)
        have hlt : sz u0_x < sz (p (p q_x q_H0) (p u0_x u0s0out)) := Nat.lt_trans (sz_lt_p_left u0_x u0s0out) (sz_lt_p_right (p q_x q_H0) (p u0_x u0s0out))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p x H0) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L (R q))) ha
      change v0 = q_v1 at e1
      have e2 := congrArg (fun q => (R (R q))) ha
      change x = (p q_v0 q_v0) at e2
      have e3 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_v0 q_x)) q_v0) at e3
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v0 q_v0) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L (R q))) ha
      change v0 = q_v1 at e1
      have e2 := congrArg (fun q => (R (R q))) ha
      change x = (p q_v0 q_v0) at e2
      have e3 := congrArg (fun q => q) hb
      change v0 = (p (p q_x q_H0) q_v0) at e3
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v0 q_v0) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have p0 := congrArg (fun q => (L q)) (ha)
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change H0 = (p q_v1 (p q_v0 q_v0)) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v0 = (p (p q_x (p q_v0 q_x)) q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB s0hB z0 z1 z2 z3
      omega
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have p0 := congrArg (fun q => (L q)) (ha)
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change H0 = (p q_v1 (p q_v0 q_v0)) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v0 = (p (p q_x q_H0) q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB z0 z1 z2 z3
      omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 (eval v1 (eval v0 v0))) (eval (eval x (eval v0 x)) v0)) := by
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
  change x = (eval (eval v0 (eval v1 (eval v0 v0))) (eval (eval x H0) v0))
  have rawEq : (eval (eval v0 (eval v1 (eval v0 v0))) (eval (eval x H0) v0)) = (eval (p v0 (p v1 (p v0 v0))) (p (p x H0) v0)) := by
    calc
      (eval (eval v0 (eval v1 (eval v0 v0))) (eval (eval x H0) v0)) = (eval (eval v0 (eval v1 (p v0 v0))) (eval (eval x H0) v0)) := congrArg (fun q => (eval (eval v0 (eval v1 q)) (eval (eval x H0) v0))) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval v0 (p v1 (p v0 v0))) (eval (eval x H0) v0)) := congrArg (fun q => (eval (eval v0 q) (eval (eval x H0) v0))) (eval_raw (nr1 x v0 v1))
      _ = (eval (p v0 (p v1 (p v0 v0))) (eval (eval x H0) v0)) := congrArg (fun q => (eval q (eval (eval x H0) v0))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p v0 (p v1 (p v0 v0))) (eval (p x H0) v0)) := congrArg (fun q => (eval (p v0 (p v1 (p v0 v0))) (eval q v0))) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval (p v0 (p v1 (p v0 v0))) (p (p x H0) v0)) := congrArg (fun q => (eval (p v0 (p v1 (p v0 v0))) q)) (eval_raw (nr4 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
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
