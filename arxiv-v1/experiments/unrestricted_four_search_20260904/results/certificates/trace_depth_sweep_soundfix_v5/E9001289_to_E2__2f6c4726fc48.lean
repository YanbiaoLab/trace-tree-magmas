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
      Code (p (p (p v0 v0) H0) (p x x)) (p v1 v1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_x q_H0 ∧ a = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) ∧ b = (p q_v1 q_v1) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_first {a b : CM} : ¬ Step a b a := by
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
    change v0 = (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p q_v1 q_v1) at e1
    have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) := e0; let peq1 : v0 = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) (p q_v0 q_x)) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_x)) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) (p q_v0 q_x)) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = (p q_v0 q_x) := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = (p q_v0 q_x) := Eq.trans (pst7) (pst8); let pst10 : (p q_v0 q_x) = (p q_v0 (p q_v0 q_v0)) := congrArg (fun q => p q_v0 q) (pst6); let pst11 : (p q_v0 q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst9) (pst10); let pst12 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => R q) (pst11); pst12)
    have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
    let u0s0out := u0_H0
    cases u0s0 with
    | raw =>
      have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := ha; let peq1 : v0 = (p q_v1 q_v1) := hb; let peq3 : q_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) q_H0) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) q_H0) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) q_H0) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = q_H0 := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst7) (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq3); let pst12 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q) (peq3); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.symm (pst16); pst17)
      have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0_v0 u0_x) (sz_lt_p_right (p u0_v0 u0_v0) (p u0_v0 u0_x))) (sz_lt_p_left (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit u0s0h =>
      have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := ha; let peq1 : v0 = (p q_v1 q_v1) := hb; let peq3 : q_v0 = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) q_H0) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) q_H0) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) q_H0) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = q_H0 := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst7) (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq3); let pst12 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q) (peq3); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.symm (pst16); pst17)
      have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_right (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p v0 v0) H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_v0 q_v0) (p q_v0 q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p q_x q_x) at e1
      have e2 := congrArg (fun q => (L q)) hb
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => (R q)) hb
      change x = q_v1 at e3
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p (p q_v0 q_v0) (p q_v0 q_x)) := e0; let peq1 : v0 = (p q_x q_x) := e1; let pst0 : (p (p q_v0 q_v0) (p q_v0 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) (p q_v0 q_x)) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = (p q_v0 q_v0) := Eq.symm (pst2); let pst4 : (p q_v0 q_x) = (p q_v0 (p q_v0 q_v0)) := congrArg (fun q => p q_v0 q) (pst3); let pst5 : (p q_v0 (p q_v0 q_v0)) = (p q_v0 q_x) := Eq.symm (pst4); let pst6 : (p q_v0 q_x) = q_x := congrArg (fun q => R q) (pst1); let pst7 : (p q_v0 (p q_v0 q_v0)) = q_x := Eq.trans (pst5) (pst6); let pst8 : (p q_v0 (p q_v0 q_v0)) = (p q_v0 q_v0) := Eq.trans (pst7) (pst3); let pst9 : (p q_v0 q_v0) = q_v0 := congrArg (fun q => R q) (pst8); let pst10 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst9); pst10)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : q_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) := u0a; let peq7 : q_H0 = u0_x := u0o; let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq5); let pst7 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q) (peq5); let pst8 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst6) (pst7); let pst9 : q_H0 = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst5) (pst8); let pst10 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = q_H0 := Eq.symm (pst9); let pst11 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = u0_x := Eq.trans (pst10) (peq7); let pst12 : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.symm (pst11); pst12)
        have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0_v0 u0_x) (sz_lt_p_right (p u0_v0 u0_v0) (p u0_v0 u0_x))) (sz_lt_p_left (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : q_v0 = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := u0a; let peq7 : q_H0 = u0_x := u0o; let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq5); let pst7 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q) (peq5); let pst8 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst6) (pst7); let pst9 : q_H0 = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst5) (pst8); let pst10 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = q_H0 := Eq.symm (pst9); let pst11 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = u0_x := Eq.trans (pst10) (peq7); let pst12 : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.symm (pst11); pst12)
        have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_right (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v0 = (p (p q_v0 q_v0) (p q_v0 q_x)) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change v0 = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change H0 = (p q_v1 q_v1) at e2
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p (p q_v0 q_v0) (p q_v0 q_x)) := e0; let peq1 : v0 = (p q_x q_x) := e1; let pst0 : (p (p q_v0 q_v0) (p q_v0 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) (p q_v0 q_x)) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = (p q_v0 q_v0) := Eq.symm (pst2); let pst4 : (p q_v0 q_x) = (p q_v0 (p q_v0 q_v0)) := congrArg (fun q => p q_v0 q) (pst3); let pst5 : (p q_v0 (p q_v0 q_v0)) = (p q_v0 q_x) := Eq.symm (pst4); let pst6 : (p q_v0 q_x) = q_x := congrArg (fun q => R q) (pst1); let pst7 : (p q_v0 (p q_v0 q_v0)) = q_x := Eq.trans (pst5) (pst6); let pst8 : (p q_v0 (p q_v0 q_v0)) = (p q_v0 q_v0) := Eq.trans (pst7) (pst3); let pst9 : (p q_v0 q_v0) = q_v0 := congrArg (fun q => R q) (pst8); let pst10 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst9); pst10)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_x = (p u0_x u0_x) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq4 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) := u0a; let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst5); let pst7 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (peq0) (pst6); let pst8 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = v0 := Eq.symm (pst7); let pst9 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) := Eq.trans (pst8) (peq4); let pst10 : (p q_v0 q_v0) = (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) := congrArg (fun q => L q) (pst9); let pst11 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst11); let pst13 : q_v0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst10); let pst14 : (p u0_v0 u0_v0) = (p u0_v0 u0_x) := Eq.trans (pst12) (pst13); let pst15 : u0_v0 = u0_x := congrArg (fun q => R q) (pst14); let pst16 : (p u0_v0 u0_v0) = (p u0_x u0_v0) := congrArg (fun q => p q u0_v0) (pst15); let pst17 : (p u0_x u0_v0) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst15); let pst18 : (p u0_v0 u0_v0) = (p u0_x u0_x) := Eq.trans (pst16) (pst17); let pst19 : q_v0 = (p u0_x u0_x) := Eq.trans (pst11) (pst18); let pst20 : (p q_v0 q_v0) = (p (p u0_x u0_x) q_v0) := congrArg (fun q => p q q_v0) (pst19); let pst21 : (p u0_v0 u0_v0) = (p u0_x u0_v0) := congrArg (fun q => p q u0_v0) (pst15); let pst22 : (p u0_x u0_v0) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst15); let pst23 : (p u0_v0 u0_v0) = (p u0_x u0_x) := Eq.trans (pst21) (pst22); let pst24 : q_v0 = (p u0_x u0_x) := Eq.trans (pst11) (pst23); let pst25 : (p (p u0_x u0_x) q_v0) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst24); let pst26 : (p q_v0 q_v0) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst20) (pst25); let pst27 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p q_v0 q_v0) := Eq.symm (pst26); let pst28 : (p q_v0 q_v0) = (p u0_x u0_x) := congrArg (fun q => R q) (pst9); let pst29 : (p (p u0_x u0_x) (p u0_x u0_x)) = (p u0_x u0_x) := Eq.trans (pst27) (pst28); let pst30 : (p u0_x u0_x) = u0_x := congrArg (fun q => L q) (pst29); let pst31 : u0_x = (p u0_x u0_x) := Eq.symm (pst30); pst31)
        have hlt : sz u0_x < sz (p u0_x u0_x) := sz_lt_p_left u0_x u0_x
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1s0, u1a, u1b, u1o⟩
        let u1s0out := u1_H0
        cases u1s0 with
        | raw =>
          have cyc : u1_v0 = (p u1_v0 u1_v0) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq4 : v0 = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := u0a; let peq7 : q_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_x)) (p u1_x u1_x)) := u1a; let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst5); let pst7 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (peq0) (pst6); let pst8 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = v0 := Eq.symm (pst7); let pst9 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := Eq.trans (pst8) (peq4); let pst10 : (p q_v0 q_v0) = (p (p u0_v0 u0_v0) u0s0out) := congrArg (fun q => L q) (pst9); let pst11 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst11); let pst13 : (p u0_v0 u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_x)) (p u1_x u1_x)) := Eq.trans (pst12) (peq7); let pst14 : u0_v0 = (p (p u1_v0 u1_v0) (p u1_v0 u1_x)) := congrArg (fun q => L q) (pst13); let pst15 : (p (p u1_v0 u1_v0) (p u1_v0 u1_x)) = u0_v0 := Eq.symm (pst14); let pst16 : u0_v0 = (p u1_x u1_x) := congrArg (fun q => R q) (pst13); let pst17 : (p (p u1_v0 u1_v0) (p u1_v0 u1_x)) = (p u1_x u1_x) := Eq.trans (pst15) (pst16); let pst18 : (p u1_v0 u1_v0) = u1_x := congrArg (fun q => L q) (pst17); let pst19 : u1_x = (p u1_v0 u1_v0) := Eq.symm (pst18); let pst20 : (p u1_v0 u1_x) = (p u1_v0 (p u1_v0 u1_v0)) := congrArg (fun q => p u1_v0 q) (pst19); let pst21 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_v0 u1_x) := Eq.symm (pst20); let pst22 : (p u1_v0 u1_x) = u1_x := congrArg (fun q => R q) (pst17); let pst23 : (p u1_v0 (p u1_v0 u1_v0)) = u1_x := Eq.trans (pst21) (pst22); let pst24 : (p u1_v0 (p u1_v0 u1_v0)) = (p u1_v0 u1_v0) := Eq.trans (pst23) (pst19); let pst25 : (p u1_v0 u1_v0) = u1_v0 := congrArg (fun q => R q) (pst24); let pst26 : u1_v0 = (p u1_v0 u1_v0) := Eq.symm (pst25); pst26)
          have hlt : sz u1_v0 < sz (p u1_v0 u1_v0) := sz_lt_p_left u1_v0 u1_v0
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u1s0h =>
          have cyc : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq4 : v0 = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := u0a; let peq7 : q_v0 = (p (p (p u1_v0 u1_v0) u1s0out) (p u1_x u1_x)) := u1a; let peq9 : q_H0 = u1_x := u1o; let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_v0) := Eq.symm (pst3); let pst5 : q_H0 = (p q_v0 q_v0) := Eq.trans (pst2) (pst4); let pst6 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (pst5); let pst7 : v0 = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (peq0) (pst6); let pst8 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = v0 := Eq.symm (pst7); let pst9 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := Eq.trans (pst8) (peq4); let pst10 : (p q_v0 q_v0) = (p (p u0_v0 u0_v0) u0s0out) := congrArg (fun q => L q) (pst9); let pst11 : q_v0 = (p u0_v0 u0_v0) := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v0) = q_v0 := Eq.symm (pst11); let pst13 : (p u0_v0 u0_v0) = (p (p (p u1_v0 u1_v0) u1s0out) (p u1_x u1_x)) := Eq.trans (pst12) (peq7); let pst14 : u0_v0 = (p (p u1_v0 u1_v0) u1s0out) := congrArg (fun q => L q) (pst13); let pst15 : (p (p u1_v0 u1_v0) u1s0out) = u0_v0 := Eq.symm (pst14); let pst16 : u0_v0 = (p u1_x u1_x) := congrArg (fun q => R q) (pst13); let pst17 : (p (p u1_v0 u1_v0) u1s0out) = (p u1_x u1_x) := Eq.trans (pst15) (pst16); let pst18 : u1s0out = u1_x := congrArg (fun q => R q) (pst17); let pst19 : (p u1_v0 u1_v0) = u1_x := congrArg (fun q => L q) (pst17); let pst20 : u1_x = (p u1_v0 u1_v0) := Eq.symm (pst19); let pst21 : u1s0out = (p u1_v0 u1_v0) := Eq.trans (pst18) (pst20); let pst22 : (p (p u1_v0 u1_v0) u1s0out) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst21); let pst23 : u0_v0 = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst14) (pst22); let pst24 : (p u0_v0 u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) u0_v0) := congrArg (fun q => p q u0_v0) (pst23); let pst25 : (p (p u1_v0 u1_v0) u1s0out) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst21); let pst26 : u0_v0 = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst14) (pst25); let pst27 : (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) q) (pst26); let pst28 : (p u0_v0 u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := Eq.trans (pst24) (pst27); let pst29 : q_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := Eq.trans (pst11) (pst28); let pst30 : (p q_v0 q_v0) = (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) q_v0) := congrArg (fun q => p q q_v0) (pst29); let pst31 : (p (p u1_v0 u1_v0) u1s0out) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst21); let pst32 : u0_v0 = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst14) (pst31); let pst33 : (p u0_v0 u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) u0_v0) := congrArg (fun q => p q u0_v0) (pst32); let pst34 : (p (p u1_v0 u1_v0) u1s0out) = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := congrArg (fun q => p (p u1_v0 u1_v0) q) (pst21); let pst35 : u0_v0 = (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) := Eq.trans (pst14) (pst34); let pst36 : (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := congrArg (fun q => p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) q) (pst35); let pst37 : (p u0_v0 u0_v0) = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := Eq.trans (pst33) (pst36); let pst38 : q_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := Eq.trans (pst11) (pst37); let pst39 : (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) q_v0) = (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))) := congrArg (fun q => p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) q) (pst38); let pst40 : (p q_v0 q_v0) = (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))) := Eq.trans (pst30) (pst39); let pst41 : q_H0 = (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))) := Eq.trans (pst5) (pst40); let pst42 : (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))) = q_H0 := Eq.symm (pst41); let pst43 : (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))) = u1_x := Eq.trans (pst42) (peq9); let pst44 : (p (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))) = (p u1_v0 u1_v0) := Eq.trans (pst43) (pst20); let pst45 : (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) = u1_v0 := congrArg (fun q => L q) (pst44); let pst46 : u1_v0 = (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := Eq.symm (pst45); pst46)
          have hlt : sz u1_v0 < sz (p (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_v0 u1_v0) (sz_lt_p_left (p u1_v0 u1_v0) (p u1_v0 u1_v0))) (sz_lt_p_left (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)) (p (p u1_v0 u1_v0) (p u1_v0 u1_v0)))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p q_v1 q_v1) at e1
    have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) := e0; let peq1 : x = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) (p q_v0 q_x)) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_x)) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) (p q_v0 q_x)) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = (p q_v0 q_x) := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = (p q_v0 q_x) := Eq.trans (pst7) (pst8); let pst10 : (p q_v0 q_x) = (p q_v0 (p q_v0 q_v0)) := congrArg (fun q => p q_v0 q) (pst6); let pst11 : (p q_v0 q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst9) (pst10); let pst12 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => R q) (pst11); pst12)
    have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
    let u0s0out := u0_H0
    cases u0s0 with
    | raw =>
      have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := (let peq0 : x = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := ha; let peq1 : x = (p q_v1 q_v1) := hb; let peq3 : q_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) q_H0) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) q_H0) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) q_H0) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = q_H0 := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst7) (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq3); let pst12 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q) (peq3); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.symm (pst16); pst17)
      have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0_v0 u0_x) (sz_lt_p_right (p u0_v0 u0_v0) (p u0_v0 u0_x))) (sz_lt_p_left (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit u0s0h =>
      have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := (let peq0 : x = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := ha; let peq1 : x = (p q_v1 q_v1) := hb; let peq3 : q_v0 = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) q_H0) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) q_H0) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) q_H0) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = q_H0 := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst7) (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq3); let pst12 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q) (peq3); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.symm (pst16); pst17)
      have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_right (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p (p v0 v0) H0) (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = (p q_v0 q_x) at e1
      have e2 := congrArg (fun q => (L (R q))) ha
      change v0 = q_x at e2
      have e3 := congrArg (fun q => (R (R q))) ha
      change x = q_x at e3
      have e4 := congrArg (fun q => (L q)) hb
      change x = q_v1 at e4
      have e5 := congrArg (fun q => (R q)) hb
      change x = q_v1 at e5
      have cyc : q_x = (p q_x q_x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_v0 q_x) := e1; let peq2 : v0 = q_x := e2; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_v0 q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst2); let pst5 : (p q_v0 q_v0) = (p q_x q_x) := Eq.trans (pst3) (pst4); let pst6 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst5); let pst7 : (p q_x q_x) = v0 := Eq.symm (pst6); let pst8 : (p q_x q_x) = q_x := Eq.trans (pst7) (peq2); let pst9 : q_x = (p q_x q_x) := Eq.symm (pst8); pst9)
      have hlt : sz q_x < sz (p q_x q_x) := sz_lt_p_left q_x q_x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change v0 = (p q_v0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = q_H0 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (L (R q))) (ha)
      change v0 = q_x at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (R (R q))) (ha)
      change x = q_x at p3
      have z3 := congrArg sz p3
      have p4 := congrArg (fun q => (L q)) (hb)
      change x = q_v1 at p4
      have z4 := congrArg sz p4
      have p5 := congrArg (fun q => (R q)) (hb)
      change x = q_v1 at p5
      have z5 := congrArg sz p5
      have p6 := ho
      change o = q_x at p6
      have z6 := congrArg sz p6
      simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3 z4 z5 z6
      omega
  | hit s0h =>
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change v0 = (p q_v0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = (p q_v0 q_x) at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (ha)
      change H0 = (p q_x q_x) at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (L q)) (hb)
      change x = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := congrArg (fun q => (R q)) (hb)
      change x = q_v1 at p4
      have z4 := congrArg sz p4
      have p5 := ho
      change o = q_x at p5
      have z5 := congrArg sz p5
      simp only [getOut, L, R, U, sz] at hcB s0hB z0 z1 z2 z3 z4 z5
      omega
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have p0 := congrArg (fun q => (L (L q))) (ha)
      change v0 = (p q_v0 q_v0) at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R (L q))) (ha)
      change v0 = q_H0 at p1
      have z1 := congrArg sz p1
      have p2 := congrArg (fun q => (R q)) (ha)
      change H0 = (p q_x q_x) at p2
      have z2 := congrArg sz p2
      have p3 := congrArg (fun q => (L q)) (hb)
      change x = q_v1 at p3
      have z3 := congrArg sz p3
      have p4 := congrArg (fun q => (R q)) (hb)
      change x = q_v1 at p4
      have z4 := congrArg sz p4
      have p5 := ho
      change o = q_x at p5
      have z5 := congrArg sz p5
      simp only [getOut, L, R, U, sz] at hcB s0hB qs0hB z0 z1 z2 z3 z4 z5
      omega
theorem nr4 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p q_v1 q_v1) at e1
    have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v1 = (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_v0 q_x)) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) (p q_v0 q_x)) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) (p q_v0 q_x)) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) (p q_v0 q_x)) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = (p q_v0 q_x) := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = (p q_v0 q_x) := Eq.trans (pst7) (pst8); let pst10 : (p q_v0 q_x) = (p q_v0 (p q_v0 q_v0)) := congrArg (fun q => p q_v0 q) (pst6); let pst11 : (p q_v0 q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst9) (pst10); let pst12 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => R q) (pst11); pst12)
    have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
    let u0s0out := u0_H0
    cases u0s0 with
    | raw =>
      have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := (let peq0 : v1 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := ha; let peq1 : v1 = (p q_v1 q_v1) := hb; let peq3 : q_v0 = (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) q_H0) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) q_H0) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) q_H0) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = q_H0 := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst7) (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq3); let pst12 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) q) (peq3); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : u0_x = (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Eq.symm (pst16); pst17)
      have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right u0_v0 u0_x) (sz_lt_p_right (p u0_v0 u0_v0) (p u0_v0 u0_x))) (sz_lt_p_left (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) (p u0_v0 u0_x)) (p u0_x u0_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit u0s0h =>
      have cyc : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := (let peq0 : v1 = (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) := ha; let peq1 : v1 = (p q_v1 q_v1) := hb; let peq3 : q_v0 = (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p q_x q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst3 : (p (p q_v0 q_v0) q_H0) = q_v1 := congrArg (fun q => L q) (pst1); let pst4 : q_v1 = (p (p q_v0 q_v0) q_H0) := Eq.symm (pst3); let pst5 : (p q_x q_x) = (p (p q_v0 q_v0) q_H0) := Eq.trans (pst2) (pst4); let pst6 : q_x = (p q_v0 q_v0) := congrArg (fun q => L q) (pst5); let pst7 : (p q_v0 q_v0) = q_x := Eq.symm (pst6); let pst8 : q_x = q_H0 := congrArg (fun q => R q) (pst5); let pst9 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst7) (pst8); let pst10 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst9); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (peq3); let pst12 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := congrArg (fun q => p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) q) (peq3); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst11) (pst12); let pst14 : q_H0 = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.trans (pst10) (pst13); let pst15 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = q_H0 := Eq.symm (pst14); let pst16 : (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : u0_x = (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Eq.symm (pst16); pst17)
      have hlt : sz u0_x < sz (p (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_right (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x))) (sz_lt_p_left (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)) (p (p (p u0_v0 u0_v0) u0s0out) (p u0_x u0_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 v0) (eval v0 x)) (eval x x)) (eval v1 v1)) := by
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
  change x = (eval (eval (eval (eval v0 v0) H0) (eval x x)) (eval v1 v1))
  have rawEq : (eval (eval (eval (eval v0 v0) H0) (eval x x)) (eval v1 v1)) = (eval (p (p (p v0 v0) H0) (p x x)) (p v1 v1)) := by
    calc
      (eval (eval (eval (eval v0 v0) H0) (eval x x)) (eval v1 v1)) = (eval (eval (eval (p v0 v0) H0) (eval x x)) (eval v1 v1)) := congrArg (fun q => (eval (eval (eval q H0) (eval x x)) (eval v1 v1))) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval (p (p v0 v0) H0) (eval x x)) (eval v1 v1)) := congrArg (fun q => (eval (eval q (eval x x)) (eval v1 v1))) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval (p (p v0 v0) H0) (p x x)) (eval v1 v1)) := congrArg (fun q => (eval (eval (p (p v0 v0) H0) q) (eval v1 v1))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p (p (p v0 v0) H0) (p x x)) (eval v1 v1)) := congrArg (fun q => (eval q (eval v1 v1))) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval (p (p (p v0 v0) H0) (p x x)) (p v1 v1)) := congrArg (fun q => (eval (p (p (p v0 v0) H0) (p x x)) q)) (eval_raw (nr4 x v0 v1))
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
