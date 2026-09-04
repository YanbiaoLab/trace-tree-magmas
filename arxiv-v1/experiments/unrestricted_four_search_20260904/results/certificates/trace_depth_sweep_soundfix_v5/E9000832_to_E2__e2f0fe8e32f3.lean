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
      (s0 : Step (p v0 v0) v1 H0) :
      Code (p (p (p v0 H0) v0) x) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step (p q_v0 q_v0) q_v1 q_H0 ∧ a = (p (p (p q_v0 q_H0) q_v0) q_x) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R a)
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
    change v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := (let peq0 : v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0)) (sz_lt_p_left (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p q_v0 q_H0) q_v0) q_x) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_v0 q_H0) q_v0) q_x) := (let peq0 : v0 = (p (p (p q_v0 q_H0) q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_H0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_H0) q_v0) q_x) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) q_x)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step (p v0 v0) v1 H0) :
    ¬ ∃ o, Code v0 H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change (p (p v0 v0) v1) = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1) := (let peq0 : v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := e0; let peq1 : (p (p v0 v0) v1) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) v0) = (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) := congrArg (fun q => p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) q) (peq0); let pst2 : (p v0 v0) = (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) v1) = (p (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1) := congrArg (fun q => p q v1) (pst2); let pst4 : (p (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1) = (p (p v0 v0) v1) := Eq.symm (pst3); let pst5 : (p (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1) = q_v0 := Eq.trans (pst4) (peq1); let pst6 : q_v0 = (p (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0)) (sz_lt_p_left (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) (sz_lt_p_left (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x))) (sz_lt_p_left (p (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x)) v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_v0 q_H0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change (p (p v0 v0) v1) = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1) := (let peq0 : v0 = (p (p (p q_v0 q_H0) q_v0) q_x) := e0; let peq1 : (p (p v0 v0) v1) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p (p (p q_v0 q_H0) q_v0) q_x) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p (p (p q_v0 q_H0) q_v0) q_x) v0) = (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) := congrArg (fun q => p (p (p (p q_v0 q_H0) q_v0) q_x) q) (peq0); let pst2 : (p v0 v0) = (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) v1) = (p (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1) := congrArg (fun q => p q v1) (pst2); let pst4 : (p (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1) = (p (p v0 v0) v1) := Eq.symm (pst3); let pst5 : (p (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1) = q_v0 := Eq.trans (pst4) (peq1); let pst6 : q_v0 = (p (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) q_x)) (sz_lt_p_left (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x))) (sz_lt_p_left (p (p (p (p q_v0 q_H0) q_v0) q_x) (p (p (p q_v0 q_H0) q_v0) q_x)) v1)
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
        have cyc : q_v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) u0_v1) := (let peq0 : v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := ha; let peq3 : v0 = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := congrArg (fun q => (L q)) (u0a); let pst0 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p u0_v0 u0_v0) u0_v1) := congrArg (fun q => R q) (pst2); let pst4 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = u0_v0 := congrArg (fun q => L q) (pst2); let pst5 : u0_v0 = (p q_v0 (p (p q_v0 q_v0) q_v1)) := Eq.symm (pst4); let pst6 : (p u0_v0 u0_v0) = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) u0_v0) := congrArg (fun q => p q u0_v0) (pst5); let pst7 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) u0_v0) = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) := congrArg (fun q => p (p q_v0 (p (p q_v0 q_v0) q_v1)) q) (pst5); let pst8 : (p u0_v0 u0_v0) = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) := Eq.trans (pst6) (pst7); let pst9 : (p (p u0_v0 u0_v0) u0_v1) = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) u0_v1) := congrArg (fun q => p q u0_v1) (pst8); let pst10 : q_v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) u0_v1) := Eq.trans (pst3) (pst9); pst10)
        have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) u0_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1)))) (sz_lt_p_left (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) u0_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0s0out = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := (let peq0 : v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) := ha; let peq1 : H0 = q_v0 := hb; let peq3 : v0 = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => (L q)) (u0a); let peq4 : v0 = u0_x := congrArg (fun q => (R q)) (u0a); let peq6 : H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = (p u0_v0 u0s0out) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst4 : H0 = u0s0out := Eq.trans (peq1) (pst3); let pst5 : u0s0out = H0 := Eq.symm (pst4); let pst6 : u0s0out = u0_x := Eq.trans (pst5) (peq6); let pst7 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = (p u0s0out (p (p q_v0 q_v0) q_v1)) := congrArg (fun q => p q (p (p q_v0 q_v0) q_v1)) (pst3); let pst8 : (p q_v0 q_v0) = (p u0s0out q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst9 : (p u0s0out q_v0) = (p u0s0out u0s0out) := congrArg (fun q => p u0s0out q) (pst3); let pst10 : (p q_v0 q_v0) = (p u0s0out u0s0out) := Eq.trans (pst8) (pst9); let pst11 : (p (p q_v0 q_v0) q_v1) = (p (p u0s0out u0s0out) q_v1) := congrArg (fun q => p q q_v1) (pst10); let pst12 : (p u0s0out (p (p q_v0 q_v0) q_v1)) = (p u0s0out (p (p u0s0out u0s0out) q_v1)) := congrArg (fun q => p u0s0out q) (pst11); let pst13 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = (p u0s0out (p (p u0s0out u0s0out) q_v1)) := Eq.trans (pst7) (pst12); let pst14 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst15 : (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) q_v0) = (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) := congrArg (fun q => p (p u0s0out (p (p u0s0out u0s0out) q_v1)) q) (pst3); let pst16 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) := Eq.trans (pst14) (pst15); let pst17 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : q_x = u0_v0 := congrArg (fun q => R q) (pst1); let pst19 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = u0_v0 := congrArg (fun q => L q) (pst2); let pst20 : u0_v0 = (p q_v0 (p (p q_v0 q_v0) q_v1)) := Eq.symm (pst19); let pst21 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = (p u0s0out (p (p q_v0 q_v0) q_v1)) := congrArg (fun q => p q (p (p q_v0 q_v0) q_v1)) (pst3); let pst22 : (p q_v0 q_v0) = (p u0s0out q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst23 : (p u0s0out q_v0) = (p u0s0out u0s0out) := congrArg (fun q => p u0s0out q) (pst3); let pst24 : (p q_v0 q_v0) = (p u0s0out u0s0out) := Eq.trans (pst22) (pst23); let pst25 : (p (p q_v0 q_v0) q_v1) = (p (p u0s0out u0s0out) q_v1) := congrArg (fun q => p q q_v1) (pst24); let pst26 : (p u0s0out (p (p q_v0 q_v0) q_v1)) = (p u0s0out (p (p u0s0out u0s0out) q_v1)) := congrArg (fun q => p u0s0out q) (pst25); let pst27 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = (p u0s0out (p (p u0s0out u0s0out) q_v1)) := Eq.trans (pst21) (pst26); let pst28 : u0_v0 = (p u0s0out (p (p u0s0out u0s0out) q_v1)) := Eq.trans (pst20) (pst27); let pst29 : q_x = (p u0s0out (p (p u0s0out u0s0out) q_v1)) := Eq.trans (pst18) (pst28); let pst30 : (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) q_x) = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := congrArg (fun q => p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) q) (pst29); let pst31 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) q_x) = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := Eq.trans (pst17) (pst30); let pst32 : v0 = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := Eq.trans (peq0) (pst31); let pst33 : (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) = v0 := Eq.symm (pst32); let pst34 : (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) = u0_x := Eq.trans (pst33) (peq4); let pst35 : u0_x = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := Eq.symm (pst34); let pst36 : u0s0out = (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := Eq.trans (pst6) (pst35); pst36)
        have hlt : sz u0s0out < sz (p (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0s0out (p (p u0s0out u0s0out) q_v1)) (sz_lt_p_left (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out)) (sz_lt_p_left (p (p u0s0out (p (p u0s0out u0s0out) q_v1)) u0s0out) (p u0s0out (p (p u0s0out u0s0out) q_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : q_v0 = (p (p (p q_v0 q_H0) (p q_v0 q_H0)) u0_v1) := (let peq0 : v0 = (p (p (p q_v0 q_H0) q_v0) q_x) := ha; let peq3 : v0 = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := congrArg (fun q => (L q)) (u0a); let pst0 : (p (p (p q_v0 q_H0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) q_x) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p (p q_v0 q_H0) q_v0) = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p u0_v0 u0_v0) u0_v1) := congrArg (fun q => R q) (pst2); let pst4 : (p q_v0 q_H0) = u0_v0 := congrArg (fun q => L q) (pst2); let pst5 : u0_v0 = (p q_v0 q_H0) := Eq.symm (pst4); let pst6 : (p u0_v0 u0_v0) = (p (p q_v0 q_H0) u0_v0) := congrArg (fun q => p q u0_v0) (pst5); let pst7 : (p (p q_v0 q_H0) u0_v0) = (p (p q_v0 q_H0) (p q_v0 q_H0)) := congrArg (fun q => p (p q_v0 q_H0) q) (pst5); let pst8 : (p u0_v0 u0_v0) = (p (p q_v0 q_H0) (p q_v0 q_H0)) := Eq.trans (pst6) (pst7); let pst9 : (p (p u0_v0 u0_v0) u0_v1) = (p (p (p q_v0 q_H0) (p q_v0 q_H0)) u0_v1) := congrArg (fun q => p q u0_v1) (pst8); let pst10 : q_v0 = (p (p (p q_v0 q_H0) (p q_v0 q_H0)) u0_v1) := Eq.trans (pst3) (pst9); pst10)
        have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) (p q_v0 q_H0)) u0_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p q_v0 q_H0))) (sz_lt_p_left (p (p q_v0 q_H0) (p q_v0 q_H0)) u0_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0s0out = (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := (let peq0 : v0 = (p (p (p q_v0 q_H0) q_v0) q_x) := ha; let peq1 : H0 = q_v0 := hb; let peq3 : v0 = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => (L q)) (u0a); let peq4 : v0 = u0_x := congrArg (fun q => (R q)) (u0a); let peq6 : H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_H0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) q_x) = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (pst0) (peq3); let pst2 : (p (p q_v0 q_H0) q_v0) = (p u0_v0 u0s0out) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst4 : H0 = u0s0out := Eq.trans (peq1) (pst3); let pst5 : u0s0out = H0 := Eq.symm (pst4); let pst6 : u0s0out = u0_x := Eq.trans (pst5) (peq6); let pst7 : (p q_v0 q_H0) = (p u0s0out q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst8 : (p (p q_v0 q_H0) q_v0) = (p (p u0s0out q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst7); let pst9 : (p (p u0s0out q_H0) q_v0) = (p (p u0s0out q_H0) u0s0out) := congrArg (fun q => p (p u0s0out q_H0) q) (pst3); let pst10 : (p (p q_v0 q_H0) q_v0) = (p (p u0s0out q_H0) u0s0out) := Eq.trans (pst8) (pst9); let pst11 : (p (p (p q_v0 q_H0) q_v0) q_x) = (p (p (p u0s0out q_H0) u0s0out) q_x) := congrArg (fun q => p q q_x) (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst1); let pst13 : (p q_v0 q_H0) = u0_v0 := congrArg (fun q => L q) (pst2); let pst14 : u0_v0 = (p q_v0 q_H0) := Eq.symm (pst13); let pst15 : (p q_v0 q_H0) = (p u0s0out q_H0) := congrArg (fun q => p q q_H0) (pst3); let pst16 : u0_v0 = (p u0s0out q_H0) := Eq.trans (pst14) (pst15); let pst17 : q_x = (p u0s0out q_H0) := Eq.trans (pst12) (pst16); let pst18 : (p (p (p u0s0out q_H0) u0s0out) q_x) = (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := congrArg (fun q => p (p (p u0s0out q_H0) u0s0out) q) (pst17); let pst19 : (p (p (p q_v0 q_H0) q_v0) q_x) = (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := Eq.trans (pst11) (pst18); let pst20 : v0 = (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := Eq.trans (peq0) (pst19); let pst21 : (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) = v0 := Eq.symm (pst20); let pst22 : (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) = u0_x := Eq.trans (pst21) (peq4); let pst23 : u0_x = (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := Eq.symm (pst22); let pst24 : u0s0out = (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := Eq.trans (pst6) (pst23); pst24)
        have hlt : sz u0s0out < sz (p (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0s0out q_H0) (sz_lt_p_left (p u0s0out q_H0) u0s0out)) (sz_lt_p_left (p (p u0s0out q_H0) u0s0out) (p u0s0out q_H0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step (p v0 v0) v1 H0) :
    ¬ ∃ o, Code (p v0 H0) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change (p (p v0 v0) v1) = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := (let peq0 : v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_v0 q_H0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change (p (p v0 v0) v1) = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 q_H0) q_v0) := (let peq0 : v0 = (p (p q_v0 q_H0) q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 q_H0) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change H0 = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := (let peq0 : v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_v0 q_v0) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_v0 q_H0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change H0 = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v0 = q_v0 at e2
      have cyc : q_v0 = (p (p q_v0 q_H0) q_v0) := (let peq0 : v0 = (p (p q_v0 q_H0) q_v0) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p (p q_v0 q_H0) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_H0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 q_H0) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step (p v0 v0) v1 H0) :
    ¬ ∃ o, Code (p (p v0 H0) v0) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 (p (p q_v0 q_v0) q_v1)) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change (p (p v0 v0) v1) = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) ha
      change v0 = q_x at e2
      have e3 := congrArg (fun q => q) hb
      change x = q_v0 at e3
      have cyc : q_v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1) := (let peq0 : v0 = (p q_v0 (p (p q_v0 q_v0) q_v1)) := e0; let peq1 : (p (p v0 v0) v1) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 (p (p q_v0 q_v0) q_v1)) v0) = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) := congrArg (fun q => p (p q_v0 (p (p q_v0 q_v0) q_v1)) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) v1) = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1) := congrArg (fun q => p q v1) (pst2); let pst4 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1) = (p (p v0 v0) v1) := Eq.symm (pst3); let pst5 : (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1) = q_v0 := Eq.trans (pst4) (peq1); let pst6 : q_v0 = (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p (p q_v0 q_v0) q_v1)) (sz_lt_p_left (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1)))) (sz_lt_p_left (p (p q_v0 (p (p q_v0 q_v0) q_v1)) (p q_v0 (p (p q_v0 q_v0) q_v1))) v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 q_H0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change (p (p v0 v0) v1) = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) ha
      change v0 = q_x at e2
      have e3 := congrArg (fun q => q) hb
      change x = q_v0 at e3
      have cyc : q_v0 = (p (p (p q_v0 q_H0) (p q_v0 q_H0)) v1) := (let peq0 : v0 = (p q_v0 q_H0) := e0; let peq1 : (p (p v0 v0) v1) = q_v0 := e1; let pst0 : (p v0 v0) = (p (p q_v0 q_H0) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 q_H0) v0) = (p (p q_v0 q_H0) (p q_v0 q_H0)) := congrArg (fun q => p (p q_v0 q_H0) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 q_H0) (p q_v0 q_H0)) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) v1) = (p (p (p q_v0 q_H0) (p q_v0 q_H0)) v1) := congrArg (fun q => p q v1) (pst2); let pst4 : (p (p (p q_v0 q_H0) (p q_v0 q_H0)) v1) = (p (p v0 v0) v1) := Eq.symm (pst3); let pst5 : (p (p (p q_v0 q_H0) (p q_v0 q_H0)) v1) = q_v0 := Eq.trans (pst4) (peq1); let pst6 : q_v0 = (p (p (p q_v0 q_H0) (p q_v0 q_H0)) v1) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) (p q_v0 q_H0)) v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) (p q_v0 q_H0))) (sz_lt_p_left (p (p q_v0 q_H0) (p q_v0 q_H0)) v1)
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
        have cyc : u0_v0 = (p (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1) := (let peq0 : v0 = (p q_v0 (p (p q_v0 q_v0) q_v1)) := congrArg (fun q => (L (L q))) (ha); let peq5 : v0 = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := congrArg (fun q => (L q)) (u0a); let pst0 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (pst0) (peq5); let pst2 : q_v0 = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) q_v0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) := congrArg (fun q => p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) := Eq.trans (pst3) (pst4); let pst6 : (p (p q_v0 q_v0) q_v1) = (p (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (pst5); let pst7 : (p (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1) = (p (p q_v0 q_v0) q_v1) := Eq.symm (pst6); let pst8 : (p (p q_v0 q_v0) q_v1) = u0_v0 := congrArg (fun q => R q) (pst1); let pst9 : (p (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1) = u0_v0 := Eq.trans (pst7) (pst8); let pst10 : u0_v0 = (p (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1) := Eq.symm (pst9); pst10)
        have hlt : sz u0_v0 < sz (p (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (sz_lt_p_left (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)))) (sz_lt_p_left (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) (p u0_v0 (p (p u0_v0 u0_v0) u0_v1))) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1) := (let peq0 : v0 = (p q_v0 (p (p q_v0 q_v0) q_v1)) := congrArg (fun q => (L (L q))) (ha); let peq5 : v0 = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => (L q)) (u0a); let pst0 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_v0 q_v0) q_v1)) = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (pst0) (peq5); let pst2 : q_v0 = (p u0_v0 u0s0out) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v0) = (p (p u0_v0 u0s0out) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p u0_v0 u0s0out) q_v0) = (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) := congrArg (fun q => p (p u0_v0 u0s0out) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) := Eq.trans (pst3) (pst4); let pst6 : (p (p q_v0 q_v0) q_v1) = (p (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1) := congrArg (fun q => p q q_v1) (pst5); let pst7 : (p (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1) = (p (p q_v0 q_v0) q_v1) := Eq.symm (pst6); let pst8 : (p (p q_v0 q_v0) q_v1) = u0_v0 := congrArg (fun q => R q) (pst1); let pst9 : (p (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1) = u0_v0 := Eq.trans (pst7) (pst8); let pst10 : u0_v0 = (p (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1) := Eq.symm (pst9); pst10)
        have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0s0out) (sz_lt_p_left (p u0_v0 u0s0out) (p u0_v0 u0s0out))) (sz_lt_p_left (p (p u0_v0 u0s0out) (p u0_v0 u0s0out)) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      have u0s0B := step_bound u0s0
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v0 = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := (let peq0 : v0 = (p q_v0 q_H0) := congrArg (fun q => (L (L q))) (ha); let peq1 : H0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq5 : v0 = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := congrArg (fun q => (L q)) (u0a); let peq6 : v0 = u0_x := congrArg (fun q => (R q)) (u0a); let peq8 : H0 = u0_x := u0o; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (pst0) (peq5); let pst2 : q_v0 = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := congrArg (fun q => L q) (pst1); let pst3 : H0 = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := Eq.trans (peq1) (pst2); let pst4 : (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) = H0 := Eq.symm (pst3); let pst5 : (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) = u0_x := Eq.trans (pst4) (peq8); let pst6 : (p q_v0 q_H0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst7 : q_H0 = u0_v0 := congrArg (fun q => R q) (pst1); let pst8 : (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) q_H0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := congrArg (fun q => p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) q) (pst7); let pst9 : (p q_v0 q_H0) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (pst6) (pst8); let pst10 : v0 = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (peq0) (pst9); let pst11 : (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) = v0 := Eq.symm (pst10); let pst12 : (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) = u0_x := Eq.trans (pst11) (peq6); let pst13 : u0_x = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.symm (pst12); let pst14 : (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) = (p (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) u0_v0) := Eq.trans (pst5) (pst13); let pst15 : u0_v0 = (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := congrArg (fun q => L q) (pst14); pst15)
        have hlt : sz u0_v0 < sz (p u0_v0 (p (p u0_v0 u0_v0) u0_v1)) := sz_lt_p_left u0_v0 (p (p u0_v0 u0_v0) u0_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v0 = (p u0_v0 u0s0out) := (let peq0 : v0 = (p q_v0 q_H0) := congrArg (fun q => (L (L q))) (ha); let peq1 : H0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq5 : v0 = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => (L q)) (u0a); let peq6 : v0 = u0_x := congrArg (fun q => (R q)) (u0a); let peq8 : H0 = u0_x := u0o; let pst0 : (p q_v0 q_H0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_H0) = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (pst0) (peq5); let pst2 : q_v0 = (p u0_v0 u0s0out) := congrArg (fun q => L q) (pst1); let pst3 : H0 = (p u0_v0 u0s0out) := Eq.trans (peq1) (pst2); let pst4 : (p u0_v0 u0s0out) = H0 := Eq.symm (pst3); let pst5 : (p u0_v0 u0s0out) = u0_x := Eq.trans (pst4) (peq8); let pst6 : (p q_v0 q_H0) = (p (p u0_v0 u0s0out) q_H0) := congrArg (fun q => p q q_H0) (pst2); let pst7 : q_H0 = u0_v0 := congrArg (fun q => R q) (pst1); let pst8 : (p (p u0_v0 u0s0out) q_H0) = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => p (p u0_v0 u0s0out) q) (pst7); let pst9 : (p q_v0 q_H0) = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (pst6) (pst8); let pst10 : v0 = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (peq0) (pst9); let pst11 : (p (p u0_v0 u0s0out) u0_v0) = v0 := Eq.symm (pst10); let pst12 : (p (p u0_v0 u0s0out) u0_v0) = u0_x := Eq.trans (pst11) (peq6); let pst13 : u0_x = (p (p u0_v0 u0s0out) u0_v0) := Eq.symm (pst12); let pst14 : (p u0_v0 u0s0out) = (p (p u0_v0 u0s0out) u0_v0) := Eq.trans (pst5) (pst13); let pst15 : u0_v0 = (p u0_v0 u0s0out) := congrArg (fun q => L q) (pst14); pst15)
        have hlt : sz u0_v0 < sz (p u0_v0 u0s0out) := sz_lt_p_left u0_v0 u0s0out
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 (eval (eval v0 v0) v1)) v0) x) v0) := by
  let H0 := eval (eval v0 v0) v1
  have e0a : (eval v0 v0) = (p v0 v0) := by
    change (eval v0 v0) = (p v0 v0)
    exact (eval_raw (nr0 x v0 v1))
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step (p v0 v0) v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step (eval v0 v0) v1
  change x = (eval (eval (eval (eval v0 H0) v0) x) v0)
  have rawEq : (eval (eval (eval (eval v0 H0) v0) x) v0) = (eval (p (p (p v0 H0) v0) x) v0) := by
    calc
      (eval (eval (eval (eval v0 H0) v0) x) v0) = (eval (eval (eval (p v0 H0) v0) x) v0) := congrArg (fun q => (eval (eval (eval q v0) x) v0)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval (p (p v0 H0) v0) x) v0) := congrArg (fun q => (eval (eval q x) v0)) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval (p (p (p v0 H0) v0) x) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr3 x v0 v1 H0 s0))
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
