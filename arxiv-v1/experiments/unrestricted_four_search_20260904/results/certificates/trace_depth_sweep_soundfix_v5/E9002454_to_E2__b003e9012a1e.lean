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
      (s0 : Step x v1 H0) :
      Code (p v0 v0) (p x (p H0 (p v1 v1))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_x q_v1 q_H0 ∧ a = (p q_v0 q_v0) ∧ b = (p q_x (p q_H0 (p q_v1 q_v1))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L b)
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
    change v0 = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p q_x (p (p q_x q_v1) (p q_v1 q_v1))) at e1
    have cyc : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_x (p (p q_x q_v1) (p q_v1 q_v1))) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p (p q_x q_v1) (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p (p q_x q_v1) (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := Eq.trans (pst3) (pst4); pst5)
    have hlt : sz q_x < sz (p (p q_x q_v1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_x q_v1) (sz_lt_p_left (p q_x q_v1) (p q_v1 q_v1))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
    let u0s0out := u0_H0
    cases u0s0 with
    | raw =>
      have cyc : u0_x = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := (let peq0 : v0 = (p q_v0 q_v0) := ha; let peq1 : v0 = (p q_x (p q_H0 (p q_v1 q_v1))) := hb; let peq3 : q_x = (p u0_v0 u0_v0) := u0a; let peq4 : q_v1 = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := u0b; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H0 (p q_v1 q_v1)) = q_x := Eq.symm (pst5); let pst7 : (p q_H0 (p q_v1 q_v1)) = (p u0_v0 u0_v0) := Eq.trans (pst6) (peq3); let pst8 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p q_v1 q_v1) = u0_v0 := congrArg (fun q => R q) (pst7); let pst10 : u0_v0 = (p q_v1 q_v1) := Eq.symm (pst9); let pst11 : (p q_v1 q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (peq4); let pst12 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q) (peq4); let pst13 : (p q_v1 q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst10) (pst13); let pst15 : q_H0 = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst8) (pst14); let pst16 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) = q_H0 := Eq.symm (pst15); let pst17 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) = u0_x := Eq.trans (pst16) (peq5); let pst18 : u0_x = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.symm (pst17); pst18)
      have hlt : sz u0_x < sz (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Nat.lt_trans (sz_lt_p_left u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (sz_lt_p_left (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit u0s0h =>
      have cyc : u0_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := (let peq0 : v0 = (p q_v0 q_v0) := ha; let peq1 : v0 = (p q_x (p q_H0 (p q_v1 q_v1))) := hb; let peq3 : q_x = (p u0_v0 u0_v0) := u0a; let peq4 : q_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H0 (p q_v1 q_v1)) = q_x := Eq.symm (pst5); let pst7 : (p q_H0 (p q_v1 q_v1)) = (p u0_v0 u0_v0) := Eq.trans (pst6) (peq3); let pst8 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p q_v1 q_v1) = u0_v0 := congrArg (fun q => R q) (pst7); let pst10 : u0_v0 = (p q_v1 q_v1) := Eq.symm (pst9); let pst11 : (p q_v1 q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (peq4); let pst12 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := congrArg (fun q => p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q) (peq4); let pst13 : (p q_v1 q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst10) (pst13); let pst15 : q_H0 = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst8) (pst14); let pst16 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) = q_H0 := Eq.symm (pst15); let pst17 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) = u0_x := Eq.trans (pst16) (peq5); let pst18 : u0_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.symm (pst17); pst18)
      have hlt : sz u0_x < sz (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Nat.lt_trans (sz_lt_p_left u0_x (p u0s0out (p u0_v1 u0_v1))) (sz_lt_p_left (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p q_x (p (p q_x q_v1) (p q_v1 q_v1))) at e1
    have cyc : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := (let peq0 : v1 = (p q_v0 q_v0) := e0; let peq1 : v1 = (p q_x (p (p q_x q_v1) (p q_v1 q_v1))) := e1; let pst0 : (p q_v0 q_v0) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p (p q_x q_v1) (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p (p q_x q_v1) (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := Eq.trans (pst3) (pst4); pst5)
    have hlt : sz q_x < sz (p (p q_x q_v1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_x q_v1) (sz_lt_p_left (p q_x q_v1) (p q_v1 q_v1))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
    let u0s0out := u0_H0
    cases u0s0 with
    | raw =>
      have cyc : u0_x = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := (let peq0 : v1 = (p q_v0 q_v0) := ha; let peq1 : v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := hb; let peq3 : q_x = (p u0_v0 u0_v0) := u0a; let peq4 : q_v1 = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := u0b; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_v0 q_v0) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H0 (p q_v1 q_v1)) = q_x := Eq.symm (pst5); let pst7 : (p q_H0 (p q_v1 q_v1)) = (p u0_v0 u0_v0) := Eq.trans (pst6) (peq3); let pst8 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p q_v1 q_v1) = u0_v0 := congrArg (fun q => R q) (pst7); let pst10 : u0_v0 = (p q_v1 q_v1) := Eq.symm (pst9); let pst11 : (p q_v1 q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (peq4); let pst12 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q) (peq4); let pst13 : (p q_v1 q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst10) (pst13); let pst15 : q_H0 = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst8) (pst14); let pst16 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) = q_H0 := Eq.symm (pst15); let pst17 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) = u0_x := Eq.trans (pst16) (peq5); let pst18 : u0_x = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.symm (pst17); pst18)
      have hlt : sz u0_x < sz (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Nat.lt_trans (sz_lt_p_left u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (sz_lt_p_left (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit u0s0h =>
      have cyc : u0_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := (let peq0 : v1 = (p q_v0 q_v0) := ha; let peq1 : v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := hb; let peq3 : q_x = (p u0_v0 u0_v0) := u0a; let peq4 : q_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_v0 q_v0) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); let pst5 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst3) (pst4); let pst6 : (p q_H0 (p q_v1 q_v1)) = q_x := Eq.symm (pst5); let pst7 : (p q_H0 (p q_v1 q_v1)) = (p u0_v0 u0_v0) := Eq.trans (pst6) (peq3); let pst8 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p q_v1 q_v1) = u0_v0 := congrArg (fun q => R q) (pst7); let pst10 : u0_v0 = (p q_v1 q_v1) := Eq.symm (pst9); let pst11 : (p q_v1 q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (peq4); let pst12 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := congrArg (fun q => p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q) (peq4); let pst13 : (p q_v1 q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst10) (pst13); let pst15 : q_H0 = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst8) (pst14); let pst16 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) = q_H0 := Eq.symm (pst15); let pst17 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) = u0_x := Eq.trans (pst16) (peq5); let pst18 : u0_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.symm (pst17); pst18)
      have hlt : sz u0_x < sz (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Nat.lt_trans (sz_lt_p_left u0_x (p u0s0out (p u0_v1 u0_v1))) (sz_lt_p_left (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code H0 (p v1 v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e2
      have e3 := congrArg (fun q => (R q)) hb
      change v1 = (p (p q_x q_v1) (p q_v1 q_v1)) at e3
      have cyc : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := (let peq1 : v1 = q_v0 := e1; let peq2 : v1 = q_x := e2; let peq3 : v1 = (p (p q_x q_v1) (p q_v1 q_v1)) := e3; let pst0 : q_v0 = v1 := Eq.symm (peq1); let pst1 : q_v0 = q_x := Eq.trans (pst0) (peq2); let pst2 : v1 = q_x := Eq.trans (peq1) (pst1); let pst3 : q_x = v1 := Eq.symm (pst2); let pst4 : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := Eq.trans (pst3) (peq3); pst4)
      have hlt : sz q_x < sz (p (p q_x q_v1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_x q_v1) (sz_lt_p_left (p q_x q_v1) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_x = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := (let peq1 : v1 = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : v1 = q_x := congrArg (fun q => (L q)) (hb); let peq3 : v1 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R q)) (hb); let peq5 : q_x = (p u0_v0 u0_v0) := u0a; let peq6 : q_v1 = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := u0b; let peq7 : q_H0 = u0_x := u0o; let pst0 : q_v0 = v1 := Eq.symm (peq1); let pst1 : q_v0 = q_x := Eq.trans (pst0) (peq2); let pst2 : v1 = q_x := Eq.trans (peq1) (pst1); let pst3 : q_x = v1 := Eq.symm (pst2); let pst4 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst3) (peq3); let pst5 : (p q_H0 (p q_v1 q_v1)) = q_x := Eq.symm (pst4); let pst6 : (p q_H0 (p q_v1 q_v1)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (peq5); let pst7 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst6); let pst8 : (p q_v1 q_v1) = u0_v0 := congrArg (fun q => R q) (pst6); let pst9 : u0_v0 = (p q_v1 q_v1) := Eq.symm (pst8); let pst10 : (p q_v1 q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (peq6); let pst11 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) q) (peq6); let pst12 : (p q_v1 q_v1) = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst9) (pst12); let pst14 : q_H0 = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.trans (pst7) (pst13); let pst15 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) = u0_x := Eq.trans (pst15) (peq7); let pst17 : u0_x = (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Eq.symm (pst16); pst17)
        have hlt : sz u0_x < sz (p (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1)))) := Nat.lt_trans (sz_lt_p_left u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (sz_lt_p_left (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := (let peq1 : v1 = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : v1 = q_x := congrArg (fun q => (L q)) (hb); let peq3 : v1 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R q)) (hb); let peq5 : q_x = (p u0_v0 u0_v0) := u0a; let peq6 : q_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq7 : q_H0 = u0_x := u0o; let pst0 : q_v0 = v1 := Eq.symm (peq1); let pst1 : q_v0 = q_x := Eq.trans (pst0) (peq2); let pst2 : v1 = q_x := Eq.trans (peq1) (pst1); let pst3 : q_x = v1 := Eq.symm (pst2); let pst4 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst3) (peq3); let pst5 : (p q_H0 (p q_v1 q_v1)) = q_x := Eq.symm (pst4); let pst6 : (p q_H0 (p q_v1 q_v1)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (peq5); let pst7 : q_H0 = u0_v0 := congrArg (fun q => L q) (pst6); let pst8 : (p q_v1 q_v1) = u0_v0 := congrArg (fun q => R q) (pst6); let pst9 : u0_v0 = (p q_v1 q_v1) := Eq.symm (pst8); let pst10 : (p q_v1 q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q_v1) := congrArg (fun q => p q q_v1) (peq6); let pst11 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := congrArg (fun q => p (p u0_x (p u0s0out (p u0_v1 u0_v1))) q) (peq6); let pst12 : (p q_v1 q_v1) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst9) (pst12); let pst14 : q_H0 = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.trans (pst7) (pst13); let pst15 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) = u0_x := Eq.trans (pst15) (peq7); let pst17 : u0_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Eq.symm (pst16); pst17)
        have hlt : sz u0_x < sz (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1)))) := Nat.lt_trans (sz_lt_p_left u0_x (p u0s0out (p u0_v1 u0_v1))) (sz_lt_p_left (p u0_x (p u0s0out (p u0_v1 u0_v1))) (p u0_x (p u0s0out (p u0_v1 u0_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change H0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = (p (p q_x q_v1) (p q_v1 q_v1)) at e2
      have cyc : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := (let peq1 : v1 = q_x := e1; let peq2 : v1 = (p (p q_x q_v1) (p q_v1 q_v1)) := e2; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p (p q_x q_v1) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_x < sz (p (p q_x q_v1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_x q_v1) (sz_lt_p_left (p q_x q_v1) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1s0, u1a, u1b, u1o⟩
        let u1s0out := u1_H0
        cases u1s0 with
        | raw =>
          have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := (let peq0 : H0 = (p q_v0 q_v0) := ha; let peq1 : v1 = q_x := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R q)) (hb); let peq5 : v1 = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := u0b; let peq6 : H0 = u0_x := u0o; let peq7 : q_x = (p u1_v0 u1_v0) := u1a; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : v1 = (p q_H0 (p q_v1 q_v1)) := Eq.trans (peq1) (pst1); let pst3 : (p q_H0 (p q_v1 q_v1)) = v1 := Eq.symm (pst2); let pst4 : (p q_H0 (p q_v1 q_v1)) = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst3) (peq5); let pst5 : q_H0 = u0_x := congrArg (fun q => L q) (pst4); let pst6 : (p q_v1 q_v1) = (p (p u0_x u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst4); let pst7 : q_v1 = (p u0_x u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_x u0_v1) = q_v1 := Eq.symm (pst7); let pst9 : q_v1 = (p u0_v1 u0_v1) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_x u0_v1) = (p u0_v1 u0_v1) := Eq.trans (pst8) (pst9); let pst11 : u0_x = u0_v1 := congrArg (fun q => L q) (pst10); let pst12 : (p q_v0 q_v0) = H0 := Eq.symm (peq0); let pst13 : (p q_v0 q_v0) = u0_x := Eq.trans (pst12) (peq6); let pst14 : (p q_v0 q_v0) = u0_v1 := Eq.trans (pst13) (pst11); let pst15 : u0_v1 = (p q_v0 q_v0) := Eq.symm (pst14); let pst16 : u0_x = (p q_v0 q_v0) := Eq.trans (pst11) (pst15); let pst17 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst5) (pst16); let pst18 : (p q_H0 (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p q_v1 q_v1)) := congrArg (fun q => p q (p q_v1 q_v1)) (pst17); let pst19 : u0_x = (p q_v0 q_v0) := Eq.trans (pst11) (pst15); let pst20 : (p u0_x u0_v1) = (p (p q_v0 q_v0) u0_v1) := congrArg (fun q => p q u0_v1) (pst19); let pst21 : (p (p q_v0 q_v0) u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst15); let pst22 : (p u0_x u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst20) (pst21); let pst23 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst7) (pst22); let pst24 : (p q_v1 q_v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) q_v1) := congrArg (fun q => p q q_v1) (pst23); let pst25 : u0_x = (p q_v0 q_v0) := Eq.trans (pst11) (pst15); let pst26 : (p u0_x u0_v1) = (p (p q_v0 q_v0) u0_v1) := congrArg (fun q => p q u0_v1) (pst25); let pst27 : (p (p q_v0 q_v0) u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst15); let pst28 : (p u0_x u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst26) (pst27); let pst29 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst7) (pst28); let pst30 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) q_v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) := congrArg (fun q => p (p (p q_v0 q_v0) (p q_v0 q_v0)) q) (pst29); let pst31 : (p q_v1 q_v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) := Eq.trans (pst24) (pst30); let pst32 : (p (p q_v0 q_v0) (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) := congrArg (fun q => p (p q_v0 q_v0) q) (pst31); let pst33 : (p q_H0 (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) := Eq.trans (pst18) (pst32); let pst34 : q_x = (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) := Eq.trans (pst1) (pst33); let pst35 : (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) = q_x := Eq.symm (pst34); let pst36 : (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) = (p u1_v0 u1_v0) := Eq.trans (pst35) (peq7); let pst37 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) = u1_v0 := congrArg (fun q => R q) (pst36); let pst38 : (p q_v0 q_v0) = u1_v0 := congrArg (fun q => L q) (pst36); let pst39 : u1_v0 = (p q_v0 q_v0) := Eq.symm (pst38); let pst40 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) = (p q_v0 q_v0) := Eq.trans (pst37) (pst39); let pst41 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = q_v0 := congrArg (fun q => L q) (pst40); let pst42 : q_v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.symm (pst41); pst42)
          have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u1s0h =>
          have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := (let peq0 : H0 = (p q_v0 q_v0) := ha; let peq1 : v1 = q_x := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R q)) (hb); let peq5 : v1 = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := u0b; let peq6 : H0 = u0_x := u0o; let peq7 : q_x = (p u1_v0 u1_v0) := u1a; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : v1 = (p q_H0 (p q_v1 q_v1)) := Eq.trans (peq1) (pst1); let pst3 : (p q_H0 (p q_v1 q_v1)) = v1 := Eq.symm (pst2); let pst4 : (p q_H0 (p q_v1 q_v1)) = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst3) (peq5); let pst5 : q_H0 = u0_x := congrArg (fun q => L q) (pst4); let pst6 : (p q_v1 q_v1) = (p (p u0_x u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst4); let pst7 : q_v1 = (p u0_x u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_x u0_v1) = q_v1 := Eq.symm (pst7); let pst9 : q_v1 = (p u0_v1 u0_v1) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_x u0_v1) = (p u0_v1 u0_v1) := Eq.trans (pst8) (pst9); let pst11 : u0_x = u0_v1 := congrArg (fun q => L q) (pst10); let pst12 : (p q_v0 q_v0) = H0 := Eq.symm (peq0); let pst13 : (p q_v0 q_v0) = u0_x := Eq.trans (pst12) (peq6); let pst14 : (p q_v0 q_v0) = u0_v1 := Eq.trans (pst13) (pst11); let pst15 : u0_v1 = (p q_v0 q_v0) := Eq.symm (pst14); let pst16 : u0_x = (p q_v0 q_v0) := Eq.trans (pst11) (pst15); let pst17 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst5) (pst16); let pst18 : (p q_H0 (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p q_v1 q_v1)) := congrArg (fun q => p q (p q_v1 q_v1)) (pst17); let pst19 : u0_x = (p q_v0 q_v0) := Eq.trans (pst11) (pst15); let pst20 : (p u0_x u0_v1) = (p (p q_v0 q_v0) u0_v1) := congrArg (fun q => p q u0_v1) (pst19); let pst21 : (p (p q_v0 q_v0) u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst15); let pst22 : (p u0_x u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst20) (pst21); let pst23 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst7) (pst22); let pst24 : (p q_v1 q_v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) q_v1) := congrArg (fun q => p q q_v1) (pst23); let pst25 : u0_x = (p q_v0 q_v0) := Eq.trans (pst11) (pst15); let pst26 : (p u0_x u0_v1) = (p (p q_v0 q_v0) u0_v1) := congrArg (fun q => p q u0_v1) (pst25); let pst27 : (p (p q_v0 q_v0) u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst15); let pst28 : (p u0_x u0_v1) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst26) (pst27); let pst29 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst7) (pst28); let pst30 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) q_v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) := congrArg (fun q => p (p (p q_v0 q_v0) (p q_v0 q_v0)) q) (pst29); let pst31 : (p q_v1 q_v1) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) := Eq.trans (pst24) (pst30); let pst32 : (p (p q_v0 q_v0) (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) := congrArg (fun q => p (p q_v0 q_v0) q) (pst31); let pst33 : (p q_H0 (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) := Eq.trans (pst18) (pst32); let pst34 : q_x = (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) := Eq.trans (pst1) (pst33); let pst35 : (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) = q_x := Eq.symm (pst34); let pst36 : (p (p q_v0 q_v0) (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) = (p u1_v0 u1_v0) := Eq.trans (pst35) (peq7); let pst37 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) = u1_v0 := congrArg (fun q => R q) (pst36); let pst38 : (p q_v0 q_v0) = u1_v0 := congrArg (fun q => L q) (pst36); let pst39 : u1_v0 = (p q_v0 q_v0) := Eq.symm (pst38); let pst40 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) = (p q_v0 q_v0) := Eq.trans (pst37) (pst39); let pst41 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = q_v0 := congrArg (fun q => L q) (pst40); let pst42 : q_v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.symm (pst41); pst42)
          have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1s0, u1a, u1b, u1o⟩
        let u1s0out := u1_H0
        cases u1s0 with
        | raw =>
          have cyc : u1_x = (p (p u1_x u1_v1) (p u1_v1 u1_v1)) := (let peq1 : v1 = q_x := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R q)) (hb); let peq5 : v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq8 : q_v1 = (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) := u1b; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : v1 = (p q_H0 (p q_v1 q_v1)) := Eq.trans (peq1) (pst1); let pst3 : (p q_H0 (p q_v1 q_v1)) = v1 := Eq.symm (pst2); let pst4 : (p q_H0 (p q_v1 q_v1)) = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Eq.trans (pst3) (peq5); let pst5 : (p q_v1 q_v1) = (p u0s0out (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst4); let pst6 : q_v1 = u0s0out := congrArg (fun q => L q) (pst5); let pst7 : u0s0out = q_v1 := Eq.symm (pst6); let pst8 : q_v1 = (p u0_v1 u0_v1) := congrArg (fun q => R q) (pst5); let pst9 : u0s0out = (p u0_v1 u0_v1) := Eq.trans (pst7) (pst8); let pst10 : q_v1 = (p u0_v1 u0_v1) := Eq.trans (pst6) (pst9); let pst11 : (p u0_v1 u0_v1) = q_v1 := Eq.symm (pst10); let pst12 : (p u0_v1 u0_v1) = (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) := Eq.trans (pst11) (peq8); let pst13 : u0_v1 = u1_x := congrArg (fun q => L q) (pst12); let pst14 : u1_x = u0_v1 := Eq.symm (pst13); let pst15 : u0_v1 = (p (p u1_x u1_v1) (p u1_v1 u1_v1)) := congrArg (fun q => R q) (pst12); let pst16 : u1_x = (p (p u1_x u1_v1) (p u1_v1 u1_v1)) := Eq.trans (pst14) (pst15); pst16)
          have hlt : sz u1_x < sz (p (p u1_x u1_v1) (p u1_v1 u1_v1)) := Nat.lt_trans (sz_lt_p_left u1_x u1_v1) (sz_lt_p_left (p u1_x u1_v1) (p u1_v1 u1_v1))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u1s0h =>
          have cyc : u1s0out = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := (let peq0 : H0 = (p q_v0 q_v0) := ha; let peq1 : v1 = q_x := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R q)) (hb); let peq5 : v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq6 : H0 = u0_x := u0o; let peq7 : q_x = (p u1_v0 u1_v0) := u1a; let peq8 : q_v1 = (p u1_x (p u1s0out (p u1_v1 u1_v1))) := u1b; let peq9 : q_H0 = u1_x := u1o; let pst0 : q_x = v1 := Eq.symm (peq1); let pst1 : q_x = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : v1 = (p q_H0 (p q_v1 q_v1)) := Eq.trans (peq1) (pst1); let pst3 : (p q_H0 (p q_v1 q_v1)) = v1 := Eq.symm (pst2); let pst4 : (p q_H0 (p q_v1 q_v1)) = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Eq.trans (pst3) (peq5); let pst5 : q_H0 = u0_x := congrArg (fun q => L q) (pst4); let pst6 : (p q_v0 q_v0) = H0 := Eq.symm (peq0); let pst7 : (p q_v0 q_v0) = u0_x := Eq.trans (pst6) (peq6); let pst8 : u0_x = (p q_v0 q_v0) := Eq.symm (pst7); let pst9 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst5) (pst8); let pst10 : (p q_H0 (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p q_v1 q_v1)) := congrArg (fun q => p q (p q_v1 q_v1)) (pst9); let pst11 : (p q_v1 q_v1) = (p u0s0out (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst4); let pst12 : q_v1 = u0s0out := congrArg (fun q => L q) (pst11); let pst13 : u0s0out = q_v1 := Eq.symm (pst12); let pst14 : q_v1 = (p u0_v1 u0_v1) := congrArg (fun q => R q) (pst11); let pst15 : u0s0out = (p u0_v1 u0_v1) := Eq.trans (pst13) (pst14); let pst16 : q_v1 = (p u0_v1 u0_v1) := Eq.trans (pst12) (pst15); let pst17 : (p q_v1 q_v1) = (p (p u0_v1 u0_v1) q_v1) := congrArg (fun q => p q q_v1) (pst16); let pst18 : q_v1 = (p u0_v1 u0_v1) := Eq.trans (pst12) (pst15); let pst19 : (p (p u0_v1 u0_v1) q_v1) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst18); let pst20 : (p q_v1 q_v1) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst17) (pst19); let pst21 : (p (p q_v0 q_v0) (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := congrArg (fun q => p (p q_v0 q_v0) q) (pst20); let pst22 : (p q_H0 (p q_v1 q_v1)) = (p (p q_v0 q_v0) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst10) (pst21); let pst23 : q_x = (p (p q_v0 q_v0) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst1) (pst22); let pst24 : (p (p q_v0 q_v0) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = q_x := Eq.symm (pst23); let pst25 : (p (p q_v0 q_v0) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = (p u1_v0 u1_v0) := Eq.trans (pst24) (peq7); let pst26 : (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) = u1_v0 := congrArg (fun q => R q) (pst25); let pst27 : (p q_v0 q_v0) = u1_v0 := congrArg (fun q => L q) (pst25); let pst28 : u1_v0 = (p q_v0 q_v0) := Eq.symm (pst27); let pst29 : (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) = (p q_v0 q_v0) := Eq.trans (pst26) (pst28); let pst30 : (p u0_v1 u0_v1) = q_v0 := congrArg (fun q => L q) (pst29); let pst31 : q_v0 = (p u0_v1 u0_v1) := Eq.symm (pst30); let pst32 : q_v1 = (p u0_v1 u0_v1) := Eq.trans (pst12) (pst15); let pst33 : (p u0_v1 u0_v1) = q_v1 := Eq.symm (pst32); let pst34 : (p u0_v1 u0_v1) = (p u1_x (p u1s0out (p u1_v1 u1_v1))) := Eq.trans (pst33) (peq8); let pst35 : u0_v1 = u1_x := congrArg (fun q => L q) (pst34); let pst36 : u1_x = u0_v1 := Eq.symm (pst35); let pst37 : u0_v1 = (p u1s0out (p u1_v1 u1_v1)) := congrArg (fun q => R q) (pst34); let pst38 : u1_x = (p u1s0out (p u1_v1 u1_v1)) := Eq.trans (pst36) (pst37); let pst39 : u0_v1 = (p u1s0out (p u1_v1 u1_v1)) := Eq.trans (pst35) (pst38); let pst40 : (p u0_v1 u0_v1) = (p (p u1s0out (p u1_v1 u1_v1)) u0_v1) := congrArg (fun q => p q u0_v1) (pst39); let pst41 : u0_v1 = (p u1s0out (p u1_v1 u1_v1)) := Eq.trans (pst35) (pst38); let pst42 : (p (p u1s0out (p u1_v1 u1_v1)) u0_v1) = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := congrArg (fun q => p (p u1s0out (p u1_v1 u1_v1)) q) (pst41); let pst43 : (p u0_v1 u0_v1) = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := Eq.trans (pst40) (pst42); let pst44 : q_v0 = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := Eq.trans (pst31) (pst43); let pst45 : (p q_v0 q_v0) = (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) q_v0) := congrArg (fun q => p q q_v0) (pst44); let pst46 : u0_v1 = (p u1s0out (p u1_v1 u1_v1)) := Eq.trans (pst35) (pst38); let pst47 : (p u0_v1 u0_v1) = (p (p u1s0out (p u1_v1 u1_v1)) u0_v1) := congrArg (fun q => p q u0_v1) (pst46); let pst48 : u0_v1 = (p u1s0out (p u1_v1 u1_v1)) := Eq.trans (pst35) (pst38); let pst49 : (p (p u1s0out (p u1_v1 u1_v1)) u0_v1) = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := congrArg (fun q => p (p u1s0out (p u1_v1 u1_v1)) q) (pst48); let pst50 : (p u0_v1 u0_v1) = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := Eq.trans (pst47) (pst49); let pst51 : q_v0 = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := Eq.trans (pst31) (pst50); let pst52 : (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) q_v0) = (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) := congrArg (fun q => p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) q) (pst51); let pst53 : (p q_v0 q_v0) = (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) := Eq.trans (pst45) (pst52); let pst54 : u0_x = (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) := Eq.trans (pst8) (pst53); let pst55 : q_H0 = (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) := Eq.trans (pst5) (pst54); let pst56 : (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) = q_H0 := Eq.symm (pst55); let pst57 : (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) = u1_x := Eq.trans (pst56) (peq9); let pst58 : (p (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))) = (p u1s0out (p u1_v1 u1_v1)) := Eq.trans (pst57) (pst38); let pst59 : (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) = u1s0out := congrArg (fun q => L q) (pst58); let pst60 : u1s0out = (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := Eq.symm (pst59); pst60)
          have hlt : sz u1s0out < sz (p (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1))) := Nat.lt_trans (sz_lt_p_left u1s0out (p u1_v1 u1_v1)) (sz_lt_p_left (p u1s0out (p u1_v1 u1_v1)) (p u1s0out (p u1_v1 u1_v1)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code x (p H0 (p v1 v1)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p x v1) = q_x at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v1 = (p q_x q_v1) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v1 = (p q_v1 q_v1) at e3
      have cyc : v1 = (p (p (p q_v0 q_v0) v1) q_v1) := (let peq0 : x = (p q_v0 q_v0) := e0; let peq1 : (p x v1) = q_x := e1; let peq2 : v1 = (p q_x q_v1) := e2; let pst0 : (p x v1) = (p (p q_v0 q_v0) v1) := congrArg (fun q => p q v1) (peq0); let pst1 : (p (p q_v0 q_v0) v1) = (p x v1) := Eq.symm (pst0); let pst2 : (p (p q_v0 q_v0) v1) = q_x := Eq.trans (pst1) (peq1); let pst3 : q_x = (p (p q_v0 q_v0) v1) := Eq.symm (pst2); let pst4 : (p q_x q_v1) = (p (p (p q_v0 q_v0) v1) q_v1) := congrArg (fun q => p q q_v1) (pst3); let pst5 : v1 = (p (p (p q_v0 q_v0) v1) q_v1) := Eq.trans (peq2) (pst4); pst5)
      have hlt : sz v1 < sz (p (p (p q_v0 q_v0) v1) q_v1) := Nat.lt_trans (sz_lt_p_right (p q_v0 q_v0) v1) (sz_lt_p_left (p (p q_v0 q_v0) v1) q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have p0 := ha
      change x = (p q_v0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change (p x v1) = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (hb)
      change v1 = q_H0 at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (hb)
      change v1 = (p q_v1 q_v1) at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3 z4
      omega
  | hit s0h =>
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_x = (p (p u0_x u0_v1) (p u0_v1 u0_v1)) := (let peq2 : v1 = (p q_x q_v1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let peq6 : v1 = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := u0b; let pst0 : (p q_x q_v1) = v1 := Eq.symm (peq2); let pst1 : (p q_x q_v1) = (p q_v1 q_v1) := Eq.trans (pst0) (peq3); let pst2 : q_x = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_v1) = (p q_v1 q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : v1 = (p q_v1 q_v1) := Eq.trans (peq2) (pst3); let pst5 : (p q_v1 q_v1) = v1 := Eq.symm (pst4); let pst6 : (p q_v1 q_v1) = (p u0_x (p (p u0_x u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst5) (peq6); let pst7 : q_v1 = u0_x := congrArg (fun q => L q) (pst6); let pst8 : u0_x = q_v1 := Eq.symm (pst7); let pst9 : q_v1 = (p (p u0_x u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst6); let pst10 : u0_x = (p (p u0_x u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst8) (pst9); pst10)
        have hlt : sz u0_x < sz (p (p u0_x u0_v1) (p u0_v1 u0_v1)) := Nat.lt_trans (sz_lt_p_left u0_x u0_v1) (sz_lt_p_left (p u0_x u0_v1) (p u0_v1 u0_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        rcases code_shape u0s0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1s0, u1a, u1b, u1o⟩
        let u1s0out := u1_H0
        cases u1s0 with
        | raw =>
          have cyc : u1_x = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := (let peq2 : v1 = (p q_x q_v1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let peq6 : v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq8 : u0_x = (p u1_v0 u1_v0) := u1a; let peq9 : u0_v1 = (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) := u1b; let peq10 : u0s0out = u1_x := u1o; let pst0 : (p q_x q_v1) = v1 := Eq.symm (peq2); let pst1 : (p q_x q_v1) = (p q_v1 q_v1) := Eq.trans (pst0) (peq3); let pst2 : q_x = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_v1) = (p q_v1 q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : v1 = (p q_v1 q_v1) := Eq.trans (peq2) (pst3); let pst5 : (p q_v1 q_v1) = v1 := Eq.symm (pst4); let pst6 : (p q_v1 q_v1) = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Eq.trans (pst5) (peq6); let pst7 : q_v1 = u0_x := congrArg (fun q => L q) (pst6); let pst8 : u0_x = q_v1 := Eq.symm (pst7); let pst9 : q_v1 = (p u0s0out (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst6); let pst10 : u0_x = (p u0s0out (p u0_v1 u0_v1)) := Eq.trans (pst8) (pst9); let pst11 : (p u0s0out (p u0_v1 u0_v1)) = u0_x := Eq.symm (pst10); let pst12 : (p u0s0out (p u0_v1 u0_v1)) = (p u1_v0 u1_v0) := Eq.trans (pst11) (peq8); let pst13 : u0s0out = u1_v0 := congrArg (fun q => L q) (pst12); let pst14 : (p u0_v1 u0_v1) = u1_v0 := congrArg (fun q => R q) (pst12); let pst15 : u1_v0 = (p u0_v1 u0_v1) := Eq.symm (pst14); let pst16 : (p u0_v1 u0_v1) = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) u0_v1) := congrArg (fun q => p q u0_v1) (peq9); let pst17 : (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) u0_v1) = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := congrArg (fun q => p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) q) (peq9); let pst18 : (p u0_v1 u0_v1) = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := Eq.trans (pst16) (pst17); let pst19 : u1_v0 = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := Eq.trans (pst15) (pst18); let pst20 : u0s0out = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := Eq.trans (pst13) (pst19); let pst21 : (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) = u0s0out := Eq.symm (pst20); let pst22 : (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) = u1_x := Eq.trans (pst21) (peq10); let pst23 : u1_x = (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := Eq.symm (pst22); pst23)
          have hlt : sz u1_x < sz (p (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1)))) := Nat.lt_trans (sz_lt_p_left u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (sz_lt_p_left (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))) (p u1_x (p (p u1_x u1_v1) (p u1_v1 u1_v1))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u1s0h =>
          have cyc : u1_x = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := (let peq2 : v1 = (p q_x q_v1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let peq6 : v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := u0b; let peq8 : u0_x = (p u1_v0 u1_v0) := u1a; let peq9 : u0_v1 = (p u1_x (p u1s0out (p u1_v1 u1_v1))) := u1b; let peq10 : u0s0out = u1_x := u1o; let pst0 : (p q_x q_v1) = v1 := Eq.symm (peq2); let pst1 : (p q_x q_v1) = (p q_v1 q_v1) := Eq.trans (pst0) (peq3); let pst2 : q_x = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_v1) = (p q_v1 q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : v1 = (p q_v1 q_v1) := Eq.trans (peq2) (pst3); let pst5 : (p q_v1 q_v1) = v1 := Eq.symm (pst4); let pst6 : (p q_v1 q_v1) = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Eq.trans (pst5) (peq6); let pst7 : q_v1 = u0_x := congrArg (fun q => L q) (pst6); let pst8 : u0_x = q_v1 := Eq.symm (pst7); let pst9 : q_v1 = (p u0s0out (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst6); let pst10 : u0_x = (p u0s0out (p u0_v1 u0_v1)) := Eq.trans (pst8) (pst9); let pst11 : (p u0s0out (p u0_v1 u0_v1)) = u0_x := Eq.symm (pst10); let pst12 : (p u0s0out (p u0_v1 u0_v1)) = (p u1_v0 u1_v0) := Eq.trans (pst11) (peq8); let pst13 : u0s0out = u1_v0 := congrArg (fun q => L q) (pst12); let pst14 : (p u0_v1 u0_v1) = u1_v0 := congrArg (fun q => R q) (pst12); let pst15 : u1_v0 = (p u0_v1 u0_v1) := Eq.symm (pst14); let pst16 : (p u0_v1 u0_v1) = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) u0_v1) := congrArg (fun q => p q u0_v1) (peq9); let pst17 : (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) u0_v1) = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := congrArg (fun q => p (p u1_x (p u1s0out (p u1_v1 u1_v1))) q) (peq9); let pst18 : (p u0_v1 u0_v1) = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := Eq.trans (pst16) (pst17); let pst19 : u1_v0 = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := Eq.trans (pst15) (pst18); let pst20 : u0s0out = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := Eq.trans (pst13) (pst19); let pst21 : (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) = u0s0out := Eq.symm (pst20); let pst22 : (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) = u1_x := Eq.trans (pst21) (peq10); let pst23 : u1_x = (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := Eq.symm (pst22); pst23)
          have hlt : sz u1_x < sz (p (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1)))) := Nat.lt_trans (sz_lt_p_left u1_x (p u1s0out (p u1_v1 u1_v1))) (sz_lt_p_left (p u1_x (p u1s0out (p u1_v1 u1_v1))) (p u1_x (p u1s0out (p u1_v1 u1_v1))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have p0 := ha
      change x = (p q_v0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (L q)) (hb)
      change H0 = q_x at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (hb)
      change v1 = q_H0 at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (hb)
      change v1 = (p q_v1 q_v1) at p3
      have z3 := congrArg sz p3
      have p4 := ho
      change o = q_x at p4
      have z4 := congrArg sz p4
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB z0 z1 z2 z3 z4
      omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 v0) (eval x (eval (eval x v1) (eval v1 v1)))) := by
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
  change x = (eval (eval v0 v0) (eval x (eval H0 (eval v1 v1))))
  have rawEq : (eval (eval v0 v0) (eval x (eval H0 (eval v1 v1)))) = (eval (p v0 v0) (p x (p H0 (p v1 v1)))) := by
    calc
      (eval (eval v0 v0) (eval x (eval H0 (eval v1 v1)))) = (eval (p v0 v0) (eval x (eval H0 (eval v1 v1)))) := congrArg (fun q => (eval q (eval x (eval H0 (eval v1 v1))))) (eval_raw (nr0 x v0 v1))
      _ = (eval (p v0 v0) (eval x (eval H0 (p v1 v1)))) := congrArg (fun q => (eval (p v0 v0) (eval x (eval H0 q)))) (eval_raw (nr1 x v0 v1))
      _ = (eval (p v0 v0) (eval x (p H0 (p v1 v1)))) := congrArg (fun q => (eval (p v0 v0) (eval x q))) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval (p v0 v0) (p x (p H0 (p v1 v1)))) := congrArg (fun q => (eval (p v0 v0) q)) (eval_raw (nr3 x v0 v1 H0 s0))
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
