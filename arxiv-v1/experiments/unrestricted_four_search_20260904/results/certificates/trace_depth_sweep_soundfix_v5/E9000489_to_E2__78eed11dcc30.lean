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
      (s0 : Step v0 v1 H0) :
      Code (p (p (p (p v0 v0) H0) (p x x)) v0) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_v1 q_H0 ∧ a = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R (L a)))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := (let peq0 : v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (sz_lt_p_left (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := (let peq0 : v0 = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (sz_lt_p_left (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p v0 v0) H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change (p v0 v1) = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change (p v0 v1) = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change H0 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change H0 = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v0 at e1
    have cyc : q_v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := (let peq0 : x = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x))) (sz_lt_p_left (p (p (p q_v0 q_v0) (p q_v0 q_v1)) (p q_x q_x)) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change x = q_v0 at e1
    have cyc : q_v0 = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := (let peq0 : x = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p q_x q_x))) (sz_lt_p_left (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p v0 v0) H0) (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = (p q_x q_x) at e1
      have e2 := congrArg (fun q => (R q)) ha
      change (p v0 v1) = q_v0 at e2
      have e3 := congrArg (fun q => q) hb
      change (p x x) = q_v0 at e3
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := (let peq0 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) := e0; let peq1 : v0 = (p q_x q_x) := e1; let peq2 : (p v0 v1) = q_v0 := e2; let pst0 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v1) = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : q_v1 = q_v0 := congrArg (fun q => R q) (pst5); let pst7 : (p q_v0 q_v1) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (pst6); let pst8 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst7); let pst9 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (peq0) (pst8); let pst10 : (p v0 v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := congrArg (fun q => p q v1) (pst9); let pst11 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) = (p v0 v1) := Eq.symm (pst10); let pst12 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) = q_v0 := Eq.trans (pst11) (peq2); let pst13 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := Eq.symm (pst12); pst13)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v0)) v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p (p q_v0 q_v0) q_H0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = (p q_x q_x) at e1
      have e2 := congrArg (fun q => (R q)) ha
      change (p v0 v1) = q_v0 at e2
      have e3 := congrArg (fun q => q) hb
      change (p x x) = q_v0 at e3
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := e0; let peq1 : v0 = (p q_x q_x) := e1; let peq2 : (p v0 v1) = q_v0 := e2; let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst5); let pst7 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (peq0) (pst6); let pst8 : (p v0 v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := congrArg (fun q => p q v1) (pst7); let pst9 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) = (p v0 v1) := Eq.symm (pst8); let pst10 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) = q_v0 := Eq.trans (pst9) (peq2); let pst11 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := Eq.symm (pst10); pst11)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v0)) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v0)) v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v1 = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := (let peq0 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p x x) = q_v0 := hb; let peq5 : v0 = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) (p u0_x u0_x)) u0_v0) := u0a; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p x x) (p x x)) (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst3); let pst5 : (p q_v0 q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst6 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst7 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p q_x q_x) := Eq.trans (pst6) (peq1); let pst8 : (p q_v0 q_v1) = q_x := congrArg (fun q => R q) (pst7); let pst9 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst7); let pst10 : q_x = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst8) (pst10); let pst12 : q_v1 = q_v0 := congrArg (fun q => R q) (pst11); let pst13 : q_v1 = (p x x) := Eq.trans (pst12) (pst0); let pst14 : (p (p x x) q_v1) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst13); let pst15 : (p q_v0 q_v1) = (p (p x x) (p x x)) := Eq.trans (pst5) (pst14); let pst16 : (p (p (p x x) (p x x)) (p q_v0 q_v1)) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst15); let pst17 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst16); let pst18 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq0) (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst18); let pst20 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) (p u0_x u0_x)) u0_v0) := Eq.trans (pst19) (peq5); let pst21 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) (p u0_x u0_x)) := congrArg (fun q => L q) (pst20); let pst22 : (p x x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) := congrArg (fun q => L q) (pst21); let pst23 : x = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst22); let pst24 : (p u0_v0 u0_v0) = x := Eq.symm (pst23); let pst25 : x = (p u0_v0 u0_v1) := congrArg (fun q => R q) (pst22); let pst26 : (p u0_v0 u0_v0) = (p u0_v0 u0_v1) := Eq.trans (pst24) (pst25); let pst27 : u0_v0 = u0_v1 := congrArg (fun q => R q) (pst26); let pst28 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst27); let pst29 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst27); let pst30 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst28) (pst29); let pst31 : x = (p u0_v1 u0_v1) := Eq.trans (pst23) (pst30); let pst32 : (p x x) = (p (p u0_v1 u0_v1) x) := congrArg (fun q => p q x) (pst31); let pst33 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst27); let pst34 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst27); let pst35 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst33) (pst34); let pst36 : x = (p u0_v1 u0_v1) := Eq.trans (pst23) (pst35); let pst37 : (p (p u0_v1 u0_v1) x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst36); let pst38 : (p x x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst32) (pst37); let pst39 : (p (p x x) (p x x)) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p x x)) := congrArg (fun q => p q (p x x)) (pst38); let pst40 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst27); let pst41 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst27); let pst42 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst40) (pst41); let pst43 : x = (p u0_v1 u0_v1) := Eq.trans (pst23) (pst42); let pst44 : (p x x) = (p (p u0_v1 u0_v1) x) := congrArg (fun q => p q x) (pst43); let pst45 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst27); let pst46 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst27); let pst47 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst45) (pst46); let pst48 : x = (p u0_v1 u0_v1) := Eq.trans (pst23) (pst47); let pst49 : (p (p u0_v1 u0_v1) x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst48); let pst50 : (p x x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst44) (pst49); let pst51 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p x x)) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) q) (pst50); let pst52 : (p (p x x) (p x x)) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst39) (pst51); let pst53 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = (p (p x x) (p x x)) := Eq.symm (pst52); let pst54 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => R q) (pst20); let pst55 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = u0_v0 := Eq.trans (pst53) (pst54); let pst56 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst55) (pst27); let pst57 : u0_v1 = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.symm (pst56); pst57)
        have hlt : sz u0_v1 < sz (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_left (p u0_v1 u0_v1) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := (let peq0 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v1)) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p x x) = q_v0 := hb; let peq5 : v0 = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) u0_v0) := u0a; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p x x) (p x x)) (p q_v0 q_v1)) := congrArg (fun q => p q (p q_v0 q_v1)) (pst3); let pst5 : (p q_v0 q_v1) = (p (p x x) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst6 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = v0 := Eq.symm (peq0); let pst7 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p q_x q_x) := Eq.trans (pst6) (peq1); let pst8 : (p q_v0 q_v1) = q_x := congrArg (fun q => R q) (pst7); let pst9 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst7); let pst10 : q_x = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst8) (pst10); let pst12 : q_v1 = q_v0 := congrArg (fun q => R q) (pst11); let pst13 : q_v1 = (p x x) := Eq.trans (pst12) (pst0); let pst14 : (p (p x x) q_v1) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst13); let pst15 : (p q_v0 q_v1) = (p (p x x) (p x x)) := Eq.trans (pst5) (pst14); let pst16 : (p (p (p x x) (p x x)) (p q_v0 q_v1)) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst15); let pst17 : (p (p q_v0 q_v0) (p q_v0 q_v1)) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst16); let pst18 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq0) (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst18); let pst20 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) u0_v0) := Eq.trans (pst19) (peq5); let pst21 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := congrArg (fun q => L q) (pst20); let pst22 : (p x x) = (p (p u0_v0 u0_v0) u0s0out) := congrArg (fun q => L q) (pst21); let pst23 : x = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst22); let pst24 : (p x x) = (p (p u0_v0 u0_v0) x) := congrArg (fun q => p q x) (pst23); let pst25 : (p (p u0_v0 u0_v0) x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst23); let pst26 : (p x x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := Eq.trans (pst24) (pst25); let pst27 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p x x)) := congrArg (fun q => p q (p x x)) (pst26); let pst28 : (p x x) = (p (p u0_v0 u0_v0) x) := congrArg (fun q => p q x) (pst23); let pst29 : (p (p u0_v0 u0_v0) x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst23); let pst30 : (p x x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := Eq.trans (pst28) (pst29); let pst31 : (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := congrArg (fun q => p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) q) (pst30); let pst32 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := Eq.trans (pst27) (pst31); let pst33 : (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) = (p (p x x) (p x x)) := Eq.symm (pst32); let pst34 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => R q) (pst20); let pst35 : (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) = u0_v0 := Eq.trans (pst33) (pst34); let pst36 : u0_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := Eq.symm (pst35); pst36)
        have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v0 u0_v0))) (sz_lt_p_left (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v1 = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p x x) = q_v0 := hb; let peq5 : v0 = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) (p u0_x u0_x)) u0_v0) := u0a; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) q_H0) = (p (p (p x x) (p x x)) q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst5 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst6 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst5) (peq1); let pst7 : q_H0 = q_x := congrArg (fun q => R q) (pst6); let pst8 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst6); let pst9 : q_x = (p q_v0 q_v0) := Eq.symm (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst7) (pst9); let pst11 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst12 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst13 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p x x) (p x x)) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p x x) (p x x)) q_H0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst14); let pst16 : (p (p q_v0 q_v0) q_H0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst15); let pst17 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq0) (pst16); let pst18 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) (p u0_x u0_x)) u0_v0) := Eq.trans (pst18) (peq5); let pst20 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) (p u0_x u0_x)) := congrArg (fun q => L q) (pst19); let pst21 : (p x x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v1)) := congrArg (fun q => L q) (pst20); let pst22 : x = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst21); let pst23 : (p u0_v0 u0_v0) = x := Eq.symm (pst22); let pst24 : x = (p u0_v0 u0_v1) := congrArg (fun q => R q) (pst21); let pst25 : (p u0_v0 u0_v0) = (p u0_v0 u0_v1) := Eq.trans (pst23) (pst24); let pst26 : u0_v0 = u0_v1 := congrArg (fun q => R q) (pst25); let pst27 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst26); let pst28 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst26); let pst29 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst27) (pst28); let pst30 : x = (p u0_v1 u0_v1) := Eq.trans (pst22) (pst29); let pst31 : (p x x) = (p (p u0_v1 u0_v1) x) := congrArg (fun q => p q x) (pst30); let pst32 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst26); let pst33 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst26); let pst34 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst32) (pst33); let pst35 : x = (p u0_v1 u0_v1) := Eq.trans (pst22) (pst34); let pst36 : (p (p u0_v1 u0_v1) x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst35); let pst37 : (p x x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst31) (pst36); let pst38 : (p (p x x) (p x x)) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p x x)) := congrArg (fun q => p q (p x x)) (pst37); let pst39 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst26); let pst40 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst26); let pst41 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst39) (pst40); let pst42 : x = (p u0_v1 u0_v1) := Eq.trans (pst22) (pst41); let pst43 : (p x x) = (p (p u0_v1 u0_v1) x) := congrArg (fun q => p q x) (pst42); let pst44 : (p u0_v0 u0_v0) = (p u0_v1 u0_v0) := congrArg (fun q => p q u0_v0) (pst26); let pst45 : (p u0_v1 u0_v0) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst26); let pst46 : (p u0_v0 u0_v0) = (p u0_v1 u0_v1) := Eq.trans (pst44) (pst45); let pst47 : x = (p u0_v1 u0_v1) := Eq.trans (pst22) (pst46); let pst48 : (p (p u0_v1 u0_v1) x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst47); let pst49 : (p x x) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst43) (pst48); let pst50 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p x x)) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) q) (pst49); let pst51 : (p (p x x) (p x x)) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst38) (pst50); let pst52 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = (p (p x x) (p x x)) := Eq.symm (pst51); let pst53 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => R q) (pst19); let pst54 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = u0_v0 := Eq.trans (pst52) (pst53); let pst55 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst54) (pst26); let pst56 : u0_v1 = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.symm (pst55); pst56)
        have hlt : sz u0_v1 < sz (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_left (p u0_v1 u0_v1) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R (L q))) (ha); let peq3 : (p x x) = q_v0 := hb; let peq5 : v0 = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) u0_v0) := u0a; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) q_H0) = (p (p (p x x) (p x x)) q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst5 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst6 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst5) (peq1); let pst7 : q_H0 = q_x := congrArg (fun q => R q) (pst6); let pst8 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst6); let pst9 : q_x = (p q_v0 q_v0) := Eq.symm (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst7) (pst9); let pst11 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst12 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst13 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p x x) (p x x)) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p x x) (p x x)) q_H0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := congrArg (fun q => p (p (p x x) (p x x)) q) (pst14); let pst16 : (p (p q_v0 q_v0) q_H0) = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (pst4) (pst15); let pst17 : v0 = (p (p (p x x) (p x x)) (p (p x x) (p x x))) := Eq.trans (peq0) (pst16); let pst18 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = v0 := Eq.symm (pst17); let pst19 : (p (p (p x x) (p x x)) (p (p x x) (p x x))) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) u0_v0) := Eq.trans (pst18) (peq5); let pst20 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := congrArg (fun q => L q) (pst19); let pst21 : (p x x) = (p (p u0_v0 u0_v0) u0s0out) := congrArg (fun q => L q) (pst20); let pst22 : x = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst21); let pst23 : (p x x) = (p (p u0_v0 u0_v0) x) := congrArg (fun q => p q x) (pst22); let pst24 : (p (p u0_v0 u0_v0) x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst22); let pst25 : (p x x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := Eq.trans (pst23) (pst24); let pst26 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p x x)) := congrArg (fun q => p q (p x x)) (pst25); let pst27 : (p x x) = (p (p u0_v0 u0_v0) x) := congrArg (fun q => p q x) (pst22); let pst28 : (p (p u0_v0 u0_v0) x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := congrArg (fun q => p (p u0_v0 u0_v0) q) (pst22); let pst29 : (p x x) = (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) := Eq.trans (pst27) (pst28); let pst30 : (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := congrArg (fun q => p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) q) (pst29); let pst31 : (p (p x x) (p x x)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := Eq.trans (pst26) (pst30); let pst32 : (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) = (p (p x x) (p x x)) := Eq.symm (pst31); let pst33 : (p (p x x) (p x x)) = u0_v0 := congrArg (fun q => R q) (pst19); let pst34 : (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) = u0_v0 := Eq.trans (pst32) (pst33); let pst35 : u0_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := Eq.symm (pst34); pst35)
        have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v0 u0_v0))) (sz_lt_p_left (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)) (p (p u0_v0 u0_v0) (p u0_v0 u0_v0)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p (p (p v0 v0) H0) (p x x)) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L (L q)))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L (L q)))) ha
      change v0 = (p q_v0 q_v1) at e1
      have e2 := congrArg (fun q => (L (R (L q)))) ha
      change v0 = q_x at e2
      have e3 := congrArg (fun q => (R (R (L q)))) ha
      change v1 = q_x at e3
      have e4 := congrArg (fun q => (R q)) ha
      change (p x x) = q_v0 at e4
      have e5 := congrArg (fun q => q) hb
      change v0 = q_v0 at e5
      have cyc : x = (p x x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_v0 q_v1) := e1; let peq4 : (p x x) = q_v0 := e4; let peq5 : v0 = q_v0 := e5; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_v0 q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p x x) = q_v1 := Eq.trans (peq4) (pst2); let pst4 : q_v1 = (p x x) := Eq.symm (pst3); let pst5 : q_v0 = (p x x) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst7 : q_v0 = (p x x) := Eq.trans (pst2) (pst4); let pst8 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst6) (pst8); let pst10 : v0 = (p (p x x) (p x x)) := Eq.trans (peq0) (pst9); let pst11 : (p (p x x) (p x x)) = v0 := Eq.symm (pst10); let pst12 : (p (p x x) (p x x)) = q_v0 := Eq.trans (pst11) (peq5); let pst13 : q_v0 = (p x x) := Eq.trans (pst2) (pst4); let pst14 : (p (p x x) (p x x)) = (p x x) := Eq.trans (pst12) (pst13); let pst15 : (p x x) = x := congrArg (fun q => L q) (pst14); let pst16 : x = (p x x) := Eq.symm (pst15); pst16)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L (L q)))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L (L q)))) ha
      change v0 = q_H0 at e1
      have e2 := congrArg (fun q => (L (R (L q)))) ha
      change v0 = q_x at e2
      have e3 := congrArg (fun q => (R (R (L q)))) ha
      change v1 = q_x at e3
      have e4 := congrArg (fun q => (R q)) ha
      change (p x x) = q_v0 at e4
      have e5 := congrArg (fun q => q) hb
      change v0 = q_v0 at e5
      have cyc : x = (p x x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq4 : (p x x) = q_v0 := e4; let peq5 : v0 = q_v0 := e5; let pst0 : q_v0 = (p x x) := Eq.symm (peq4); let pst1 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst1) (pst2); let pst4 : v0 = (p (p x x) (p x x)) := Eq.trans (peq0) (pst3); let pst5 : (p (p x x) (p x x)) = v0 := Eq.symm (pst4); let pst6 : (p (p x x) (p x x)) = q_v0 := Eq.trans (pst5) (peq5); let pst7 : (p (p x x) (p x x)) = (p x x) := Eq.trans (pst6) (pst0); let pst8 : (p x x) = x := congrArg (fun q => L q) (pst7); let pst9 : x = (p x x) := Eq.symm (pst8); pst9)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L (L q)))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L (L q)))) ha
      change v0 = (p q_v0 q_v1) at e1
      have e2 := congrArg (fun q => (R (L q))) ha
      change H0 = (p q_x q_x) at e2
      have e3 := congrArg (fun q => (R q)) ha
      change (p x x) = q_v0 at e3
      have e4 := congrArg (fun q => q) hb
      change v0 = q_v0 at e4
      have cyc : x = (p x x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_v0 q_v1) := e1; let peq3 : (p x x) = q_v0 := e3; let peq4 : v0 = q_v0 := e4; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_v0 q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p x x) = q_v1 := Eq.trans (peq3) (pst2); let pst4 : q_v1 = (p x x) := Eq.symm (pst3); let pst5 : q_v0 = (p x x) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst7 : q_v0 = (p x x) := Eq.trans (pst2) (pst4); let pst8 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst7); let pst9 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst6) (pst8); let pst10 : v0 = (p (p x x) (p x x)) := Eq.trans (peq0) (pst9); let pst11 : (p (p x x) (p x x)) = v0 := Eq.symm (pst10); let pst12 : (p (p x x) (p x x)) = q_v0 := Eq.trans (pst11) (peq4); let pst13 : q_v0 = (p x x) := Eq.trans (pst2) (pst4); let pst14 : (p (p x x) (p x x)) = (p x x) := Eq.trans (pst12) (pst13); let pst15 : (p x x) = x := congrArg (fun q => L q) (pst14); let pst16 : x = (p x x) := Eq.symm (pst15); pst16)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L (L q)))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L (L q)))) ha
      change v0 = q_H0 at e1
      have e2 := congrArg (fun q => (R (L q))) ha
      change H0 = (p q_x q_x) at e2
      have e3 := congrArg (fun q => (R q)) ha
      change (p x x) = q_v0 at e3
      have e4 := congrArg (fun q => q) hb
      change v0 = q_v0 at e4
      have cyc : x = (p x x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq3 : (p x x) = q_v0 := e3; let peq4 : v0 = q_v0 := e4; let pst0 : q_v0 = (p x x) := Eq.symm (peq3); let pst1 : (p q_v0 q_v0) = (p (p x x) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x x) q_v0) = (p (p x x) (p x x)) := congrArg (fun q => p (p x x) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x x) (p x x)) := Eq.trans (pst1) (pst2); let pst4 : v0 = (p (p x x) (p x x)) := Eq.trans (peq0) (pst3); let pst5 : (p (p x x) (p x x)) = v0 := Eq.symm (pst4); let pst6 : (p (p x x) (p x x)) = q_v0 := Eq.trans (pst5) (peq4); let pst7 : (p (p x x) (p x x)) = (p x x) := Eq.trans (pst6) (pst0); let pst8 : (p x x) = x := congrArg (fun q => L q) (pst7); let pst9 : x = (p x x) := Eq.symm (pst8); pst9)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval v0 v0) (eval v0 v1)) (eval x x)) v0) v0) := by
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
  change x = (eval (eval (eval (eval (eval v0 v0) H0) (eval x x)) v0) v0)
  have rawEq : (eval (eval (eval (eval (eval v0 v0) H0) (eval x x)) v0) v0) = (eval (p (p (p (p v0 v0) H0) (p x x)) v0) v0) := by
    calc
      (eval (eval (eval (eval (eval v0 v0) H0) (eval x x)) v0) v0) = (eval (eval (eval (eval (p v0 v0) H0) (eval x x)) v0) v0) := congrArg (fun q => (eval (eval (eval (eval q H0) (eval x x)) v0) v0)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval (eval (p (p v0 v0) H0) (eval x x)) v0) v0) := congrArg (fun q => (eval (eval (eval q (eval x x)) v0) v0)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval (eval (p (p v0 v0) H0) (p x x)) v0) v0) := congrArg (fun q => (eval (eval (eval (p (p v0 v0) H0) q) v0) v0)) (eval_raw (nr2 x v0 v1))
      _ = (eval (eval (p (p (p v0 v0) H0) (p x x)) v0) v0) := congrArg (fun q => (eval (eval q v0) v0)) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval (p (p (p (p v0 v0) H0) (p x x)) v0) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr4 x v0 v1 H0 s0))
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
