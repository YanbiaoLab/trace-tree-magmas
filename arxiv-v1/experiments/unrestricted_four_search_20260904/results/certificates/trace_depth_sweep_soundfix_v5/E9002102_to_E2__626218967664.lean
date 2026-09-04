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
  | law (x v0 v1 v2 H0 H1 : CM)
      (s0 : Step v0 v1 H0)
      (s1 : Step v2 x H1) :
      Code H0 (p v1 (p (p x H1) (p v1 v1))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_v2 q_x q_H1 ∧ a = q_H0 ∧ b = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 s0 s1 => ⟨x, v0, v1, v2, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R b)))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, s0, s1, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 v2 H1 : CM)
    (s1 : Step v2 x H1) :
    ¬ ∃ o, Code x H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s1 with
  | raw =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change x = (p q_v0 q_v1) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v2 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) at e2
        have cyc : q_v1 = (p q_v1 q_v1) := (let peq0 : x = (p q_v0 q_v1) := e0; let peq2 : x = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := e2; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_v1 q_v1) := congrArg (fun q => R q) (pst1); pst2)
        have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change x = (p q_v0 q_v1) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v2 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p (p q_x q_H1) (p q_v1 q_v1)) at e2
        have cyc : q_v1 = (p q_v1 q_v1) := (let peq0 : x = (p q_v0 q_v1) := e0; let peq2 : x = (p (p q_x q_H1) (p q_v1 q_v1)) := e2; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p (p q_x q_H1) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_v1 q_v1) := congrArg (fun q => R q) (pst1); pst2)
        have hlt : sz q_v1 < sz (p q_v1 q_v1) := sz_lt_p_left q_v1 q_v1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have p0 := ha
        change x = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v2 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change x = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change x = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v2 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change x = (p (p q_x q_H1) (p q_v1 q_v1)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3
        omega
  | hit s1h =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) = (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x (p q_v2 q_x)) q) (pst6); let pst8 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v2 u0_x)) (sz_lt_p_left (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x u0s1out) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) = (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x (p q_v2 q_x)) q) (pst6); let pst8 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s1out) (sz_lt_p_left (p u0_x u0s1out) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) = (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x (p q_v2 q_x)) q) (pst6); let pst8 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v2 u0_x)) (sz_lt_p_left (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x u0s1out) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) = (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x (p q_v2 q_x)) q) (pst6); let pst8 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s1out) (sz_lt_p_left (p u0_x u0s1out) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x (p q_v2 q_x)) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x q_H1) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_H1) (p q_v1 q_v1)) = (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x q_H1) q) (pst6); let pst8 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v2 u0_x)) (sz_lt_p_left (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x u0s1out) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x q_H1) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_H1) (p q_v1 q_v1)) = (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x q_H1) q) (pst6); let pst8 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s1out) (sz_lt_p_left (p u0_x u0s1out) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x q_H1) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_H1) (p q_v1 q_v1)) = (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x q_H1) q) (pst6); let pst8 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x (p u0_v2 u0_x)) (sz_lt_p_left (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)) (p (p u0_x (p u0_v2 u0_x)) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := (let peq0 : x = (p q_v0 q_v1) := ha; let peq1 : H1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) := hb; let peq4 : x = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := u0b; let peq5 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p u0_v1 (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst0) (peq4); let pst2 : q_v1 = (p (p u0_x u0s1out) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) := congrArg (fun q => p q (p (p q_x q_H1) (p q_v1 q_v1))) (pst2); let pst4 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst5 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst2); let pst6 : (p q_v1 q_v1) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_H1) (p q_v1 q_v1)) = (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))) := congrArg (fun q => p (p q_x q_H1) q) (pst6); let pst8 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := congrArg (fun q => p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) q) (pst7); let pst9 : (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (pst3) (pst8); let pst10 : H1 = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.trans (peq1) (pst9); let pst11 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = H1 := Eq.symm (pst10); let pst12 : (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) = u0_x := Eq.trans (pst11) (peq5); let pst13 : u0_x = (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Eq.symm (pst12); pst13)
            have hlt : sz u0_x < sz (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0s1out) (sz_lt_p_left (p u0_x u0s1out) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p q_x q_H1) (p (p (p u0_x u0s1out) (p u0_v1 u0_v1)) (p (p u0_x u0s1out) (p u0_v1 u0_v1)))))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have p0 := ha
        change x = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change x = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB z0 z1 z2
        omega
theorem nr1 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p q_v0 q_v1) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) at e1
      have cyc : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := (let peq0 : v1 = (p q_v0 q_v1) := e0; let peq1 : v1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := e1; let pst0 : (p q_v0 q_v1) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x (p q_v2 q_x)) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p q_v0 q_v1) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) at e1
      have cyc : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := (let peq0 : v1 = (p q_v0 q_v1) := e0; let peq1 : v1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) := e1; let pst0 : (p q_v0 q_v1) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := congrArg (fun q => R q) (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p q_x q_H1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x q_H1) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have p0 := ha
      change v1 = q_H0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v1 = (p q_v1 (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2
      omega
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := ha
      change v1 = q_H0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v1 = (p q_v1 (p (p q_x q_H1) (p q_v1 q_v1))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2
      omega
theorem nr2 (x v0 v1 v2 H1 : CM)
    (s1 : Step v2 x H1) :
    ¬ ∃ o, Code (p x H1) (p v1 v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s1 with
  | raw =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change (p v2 x) = q_v1 at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) at e3
        have cyc : q_v0 = (p (p (p q_x (p q_v2 q_x)) q_v0) (p (p q_x (p q_v2 q_x)) q_v0)) := (let peq0 : x = q_v0 := e0; let peq1 : (p v2 x) = q_v1 := e1; let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := e3; let pst0 : (p v2 x) = (p v2 q_v0) := congrArg (fun q => p v2 q) (peq0); let pst1 : (p v2 q_v0) = (p v2 x) := Eq.symm (pst0); let pst2 : (p v2 q_v0) = q_v1 := Eq.trans (pst1) (peq1); let pst3 : q_v1 = (p v2 q_v0) := Eq.symm (pst2); let pst4 : v1 = (p v2 q_v0) := Eq.trans (peq2) (pst3); let pst5 : (p v2 q_v0) = v1 := Eq.symm (pst4); let pst6 : (p v2 q_v0) = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Eq.trans (pst5) (peq3); let pst7 : (p q_v1 q_v1) = (p (p v2 q_v0) q_v1) := congrArg (fun q => p q q_v1) (pst3); let pst8 : (p (p v2 q_v0) q_v1) = (p (p v2 q_v0) (p v2 q_v0)) := congrArg (fun q => p (p v2 q_v0) q) (pst3); let pst9 : (p q_v1 q_v1) = (p (p v2 q_v0) (p v2 q_v0)) := Eq.trans (pst7) (pst8); let pst10 : (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) = (p (p q_x (p q_v2 q_x)) (p (p v2 q_v0) (p v2 q_v0))) := congrArg (fun q => p (p q_x (p q_v2 q_x)) q) (pst9); let pst11 : (p v2 q_v0) = (p (p q_x (p q_v2 q_x)) (p (p v2 q_v0) (p v2 q_v0))) := Eq.trans (pst6) (pst10); let pst12 : q_v0 = (p (p v2 q_v0) (p v2 q_v0)) := congrArg (fun q => R q) (pst11); let pst13 : v2 = (p q_x (p q_v2 q_x)) := congrArg (fun q => L q) (pst11); let pst14 : (p v2 q_v0) = (p (p q_x (p q_v2 q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst15 : (p (p v2 q_v0) (p v2 q_v0)) = (p (p (p q_x (p q_v2 q_x)) q_v0) (p v2 q_v0)) := congrArg (fun q => p q (p v2 q_v0)) (pst14); let pst16 : (p v2 q_v0) = (p (p q_x (p q_v2 q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst17 : (p (p (p q_x (p q_v2 q_x)) q_v0) (p v2 q_v0)) = (p (p (p q_x (p q_v2 q_x)) q_v0) (p (p q_x (p q_v2 q_x)) q_v0)) := congrArg (fun q => p (p (p q_x (p q_v2 q_x)) q_v0) q) (pst16); let pst18 : (p (p v2 q_v0) (p v2 q_v0)) = (p (p (p q_x (p q_v2 q_x)) q_v0) (p (p q_x (p q_v2 q_x)) q_v0)) := Eq.trans (pst15) (pst17); let pst19 : q_v0 = (p (p (p q_x (p q_v2 q_x)) q_v0) (p (p q_x (p q_v2 q_x)) q_v0)) := Eq.trans (pst12) (pst18); pst19)
        have hlt : sz q_v0 < sz (p (p (p q_x (p q_v2 q_x)) q_v0) (p (p q_x (p q_v2 q_x)) q_v0)) := Nat.lt_trans (sz_lt_p_right (p q_x (p q_v2 q_x)) q_v0) (sz_lt_p_left (p (p q_x (p q_v2 q_x)) q_v0) (p (p q_x (p q_v2 q_x)) q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change (p v2 x) = q_v1 at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x q_H1) (p q_v1 q_v1)) at e3
        have cyc : q_v0 = (p (p (p q_x q_H1) q_v0) (p (p q_x q_H1) q_v0)) := (let peq0 : x = q_v0 := e0; let peq1 : (p v2 x) = q_v1 := e1; let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := e3; let pst0 : (p v2 x) = (p v2 q_v0) := congrArg (fun q => p v2 q) (peq0); let pst1 : (p v2 q_v0) = (p v2 x) := Eq.symm (pst0); let pst2 : (p v2 q_v0) = q_v1 := Eq.trans (pst1) (peq1); let pst3 : q_v1 = (p v2 q_v0) := Eq.symm (pst2); let pst4 : v1 = (p v2 q_v0) := Eq.trans (peq2) (pst3); let pst5 : (p v2 q_v0) = v1 := Eq.symm (pst4); let pst6 : (p v2 q_v0) = (p (p q_x q_H1) (p q_v1 q_v1)) := Eq.trans (pst5) (peq3); let pst7 : (p q_v1 q_v1) = (p (p v2 q_v0) q_v1) := congrArg (fun q => p q q_v1) (pst3); let pst8 : (p (p v2 q_v0) q_v1) = (p (p v2 q_v0) (p v2 q_v0)) := congrArg (fun q => p (p v2 q_v0) q) (pst3); let pst9 : (p q_v1 q_v1) = (p (p v2 q_v0) (p v2 q_v0)) := Eq.trans (pst7) (pst8); let pst10 : (p (p q_x q_H1) (p q_v1 q_v1)) = (p (p q_x q_H1) (p (p v2 q_v0) (p v2 q_v0))) := congrArg (fun q => p (p q_x q_H1) q) (pst9); let pst11 : (p v2 q_v0) = (p (p q_x q_H1) (p (p v2 q_v0) (p v2 q_v0))) := Eq.trans (pst6) (pst10); let pst12 : q_v0 = (p (p v2 q_v0) (p v2 q_v0)) := congrArg (fun q => R q) (pst11); let pst13 : v2 = (p q_x q_H1) := congrArg (fun q => L q) (pst11); let pst14 : (p v2 q_v0) = (p (p q_x q_H1) q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst15 : (p (p v2 q_v0) (p v2 q_v0)) = (p (p (p q_x q_H1) q_v0) (p v2 q_v0)) := congrArg (fun q => p q (p v2 q_v0)) (pst14); let pst16 : (p v2 q_v0) = (p (p q_x q_H1) q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst17 : (p (p (p q_x q_H1) q_v0) (p v2 q_v0)) = (p (p (p q_x q_H1) q_v0) (p (p q_x q_H1) q_v0)) := congrArg (fun q => p (p (p q_x q_H1) q_v0) q) (pst16); let pst18 : (p (p v2 q_v0) (p v2 q_v0)) = (p (p (p q_x q_H1) q_v0) (p (p q_x q_H1) q_v0)) := Eq.trans (pst15) (pst17); let pst19 : q_v0 = (p (p (p q_x q_H1) q_v0) (p (p q_x q_H1) q_v0)) := Eq.trans (pst12) (pst18); pst19)
        have hlt : sz q_v0 < sz (p (p (p q_x q_H1) q_v0) (p (p q_x q_H1) q_v0)) := Nat.lt_trans (sz_lt_p_right (p q_x q_H1) q_v0) (sz_lt_p_left (p (p q_x q_H1) q_v0) (p (p q_x q_H1) q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p x (p v2 x)) = q_H0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) at e2
        have cyc : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := (let peq1 : v1 = q_v1 := e1; let peq2 : v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := e2; let pst0 : q_v1 = v1 := Eq.symm (peq1); let pst1 : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v1 < sz (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x (p q_v2 q_x)) (p q_v1 q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x (p v2 x)) = q_H0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x q_H1) (p q_v1 q_v1)) at e2
        have cyc : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := (let peq1 : v1 = q_v1 := e1; let peq2 : v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := e2; let pst0 : q_v1 = v1 := Eq.symm (peq1); let pst1 : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v1 < sz (p (p q_x q_H1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x q_H1) (p q_v1 q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H1 = q_v1 at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) at e3
        have cyc : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := (let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := e3; let pst0 : q_v1 = v1 := Eq.symm (peq2); let pst1 : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Eq.trans (pst0) (peq3); pst1)
        have hlt : sz q_v1 < sz (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x (p q_v2 q_x)) (p q_v1 q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change H1 = q_v1 at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x q_H1) (p q_v1 q_v1)) at e3
        have cyc : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := (let peq2 : v1 = q_v1 := e2; let peq3 : v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := e3; let pst0 : q_v1 = v1 := Eq.symm (peq2); let pst1 : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := Eq.trans (pst0) (peq3); pst1)
        have hlt : sz q_v1 < sz (p (p q_x q_H1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x q_H1) (p q_v1 q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p x H1) = q_H0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) at e2
        have cyc : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := (let peq1 : v1 = q_v1 := e1; let peq2 : v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := e2; let pst0 : q_v1 = v1 := Eq.symm (peq1); let pst1 : q_v1 = (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v1 < sz (p (p q_x (p q_v2 q_x)) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x (p q_v2 q_x)) (p q_v1 q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change (p x H1) = q_H0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change v1 = (p (p q_x q_H1) (p q_v1 q_v1)) at e2
        have cyc : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := (let peq1 : v1 = q_v1 := e1; let peq2 : v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := e2; let pst0 : q_v1 = v1 := Eq.symm (peq1); let pst1 : q_v1 = (p (p q_x q_H1) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v1 < sz (p (p q_x q_H1) (p q_v1 q_v1)) := Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p q_x q_H1) (p q_v1 q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 v2 H1 : CM)
    (s1 : Step v2 x H1) :
    ¬ ∃ o, Code v1 (p (p x H1) (p v1 v1)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s1 with
  | raw =>
    cases qs0 with
    | raw =>
      have he : q_H1 = q_x := (let peq0 : v1 = (p q_v0 q_v1) := ha; let peq1 : (p x (p v2 x)) = q_v1 := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_x q_H1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let pst0 : q_v1 = (p x (p v2 x)) := Eq.symm (peq1); let pst1 : (p q_v0 q_v1) = (p q_v0 (p x (p v2 x))) := congrArg (fun q => p q_v0 q) (pst0); let pst2 : v1 = (p q_v0 (p x (p v2 x))) := Eq.trans (peq0) (pst1); let pst3 : (p q_v0 (p x (p v2 x))) = v1 := Eq.symm (pst2); let pst4 : (p q_v0 (p x (p v2 x))) = (p q_x q_H1) := Eq.trans (pst3) (peq2); let pst5 : (p x (p v2 x)) = q_H1 := congrArg (fun q => R q) (pst4); let pst6 : q_H1 = (p x (p v2 x)) := Eq.symm (pst5); let pst7 : q_v0 = q_x := congrArg (fun q => L q) (pst4); let pst8 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst7); let pst9 : (p q_x q_v1) = (p q_x (p x (p v2 x))) := congrArg (fun q => p q_x q) (pst0); let pst10 : (p q_v0 q_v1) = (p q_x (p x (p v2 x))) := Eq.trans (pst8) (pst9); let pst11 : v1 = (p q_x (p x (p v2 x))) := Eq.trans (peq0) (pst10); let pst12 : (p q_x (p x (p v2 x))) = v1 := Eq.symm (pst11); let pst13 : (p q_x (p x (p v2 x))) = (p q_v1 q_v1) := Eq.trans (pst12) (peq3); let pst14 : (p q_v1 q_v1) = (p (p x (p v2 x)) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst15 : (p (p x (p v2 x)) q_v1) = (p (p x (p v2 x)) (p x (p v2 x))) := congrArg (fun q => p (p x (p v2 x)) q) (pst0); let pst16 : (p q_v1 q_v1) = (p (p x (p v2 x)) (p x (p v2 x))) := Eq.trans (pst14) (pst15); let pst17 : (p q_x (p x (p v2 x))) = (p (p x (p v2 x)) (p x (p v2 x))) := Eq.trans (pst13) (pst16); let pst18 : q_x = (p x (p v2 x)) := congrArg (fun q => L q) (pst17); let pst19 : (p x (p v2 x)) = q_x := Eq.symm (pst18); let pst20 : q_H1 = q_x := Eq.trans (pst6) (pst19); pst20)
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_x := (let peq0 : v1 = q_H0 := ha; let peq1 : (p x (p v2 x)) = q_v1 := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_x q_H1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let pst0 : q_H0 = v1 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_H1) := Eq.trans (pst0) (peq2); let pst2 : v1 = (p q_x q_H1) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_H1) = v1 := Eq.symm (pst2); let pst4 : (p q_x q_H1) = (p q_v1 q_v1) := Eq.trans (pst3) (peq3); let pst5 : q_v1 = (p x (p v2 x)) := Eq.symm (peq1); let pst6 : (p q_v1 q_v1) = (p (p x (p v2 x)) q_v1) := congrArg (fun q => p q q_v1) (pst5); let pst7 : (p (p x (p v2 x)) q_v1) = (p (p x (p v2 x)) (p x (p v2 x))) := congrArg (fun q => p (p x (p v2 x)) q) (pst5); let pst8 : (p q_v1 q_v1) = (p (p x (p v2 x)) (p x (p v2 x))) := Eq.trans (pst6) (pst7); let pst9 : (p q_x q_H1) = (p (p x (p v2 x)) (p x (p v2 x))) := Eq.trans (pst4) (pst8); let pst10 : q_H1 = (p x (p v2 x)) := congrArg (fun q => R q) (pst9); let pst11 : q_x = (p x (p v2 x)) := congrArg (fun q => L q) (pst9); let pst12 : (p x (p v2 x)) = q_x := Eq.symm (pst11); let pst13 : q_H1 = q_x := Eq.trans (pst10) (pst12); pst13)
      exact step_ne_second (by simpa only [he] using qs1)
  | hit s1h =>
    cases qs0 with
    | raw =>
      have he : q_H1 = q_x := (let peq0 : v1 = (p q_v0 q_v1) := ha; let peq1 : (p x H1) = q_v1 := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_x q_H1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let pst0 : q_v1 = (p x H1) := Eq.symm (peq1); let pst1 : (p q_v0 q_v1) = (p q_v0 (p x H1)) := congrArg (fun q => p q_v0 q) (pst0); let pst2 : v1 = (p q_v0 (p x H1)) := Eq.trans (peq0) (pst1); let pst3 : (p q_v0 (p x H1)) = v1 := Eq.symm (pst2); let pst4 : (p q_v0 (p x H1)) = (p q_x q_H1) := Eq.trans (pst3) (peq2); let pst5 : (p x H1) = q_H1 := congrArg (fun q => R q) (pst4); let pst6 : q_H1 = (p x H1) := Eq.symm (pst5); let pst7 : q_v0 = q_x := congrArg (fun q => L q) (pst4); let pst8 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst7); let pst9 : (p q_x q_v1) = (p q_x (p x H1)) := congrArg (fun q => p q_x q) (pst0); let pst10 : (p q_v0 q_v1) = (p q_x (p x H1)) := Eq.trans (pst8) (pst9); let pst11 : v1 = (p q_x (p x H1)) := Eq.trans (peq0) (pst10); let pst12 : (p q_x (p x H1)) = v1 := Eq.symm (pst11); let pst13 : (p q_x (p x H1)) = (p q_v1 q_v1) := Eq.trans (pst12) (peq3); let pst14 : (p q_v1 q_v1) = (p (p x H1) q_v1) := congrArg (fun q => p q q_v1) (pst0); let pst15 : (p (p x H1) q_v1) = (p (p x H1) (p x H1)) := congrArg (fun q => p (p x H1) q) (pst0); let pst16 : (p q_v1 q_v1) = (p (p x H1) (p x H1)) := Eq.trans (pst14) (pst15); let pst17 : (p q_x (p x H1)) = (p (p x H1) (p x H1)) := Eq.trans (pst13) (pst16); let pst18 : q_x = (p x H1) := congrArg (fun q => L q) (pst17); let pst19 : (p x H1) = q_x := Eq.symm (pst18); let pst20 : q_H1 = q_x := Eq.trans (pst6) (pst19); pst20)
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_x := (let peq0 : v1 = q_H0 := ha; let peq1 : (p x H1) = q_v1 := congrArg (fun q => (L q)) (hb); let peq2 : v1 = (p q_x q_H1) := congrArg (fun q => (L (R q))) (hb); let peq3 : v1 = (p q_v1 q_v1) := congrArg (fun q => (R (R q))) (hb); let pst0 : q_H0 = v1 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_H1) := Eq.trans (pst0) (peq2); let pst2 : v1 = (p q_x q_H1) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_H1) = v1 := Eq.symm (pst2); let pst4 : (p q_x q_H1) = (p q_v1 q_v1) := Eq.trans (pst3) (peq3); let pst5 : q_v1 = (p x H1) := Eq.symm (peq1); let pst6 : (p q_v1 q_v1) = (p (p x H1) q_v1) := congrArg (fun q => p q q_v1) (pst5); let pst7 : (p (p x H1) q_v1) = (p (p x H1) (p x H1)) := congrArg (fun q => p (p x H1) q) (pst5); let pst8 : (p q_v1 q_v1) = (p (p x H1) (p x H1)) := Eq.trans (pst6) (pst7); let pst9 : (p q_x q_H1) = (p (p x H1) (p x H1)) := Eq.trans (pst4) (pst8); let pst10 : q_H1 = (p x H1) := congrArg (fun q => R q) (pst9); let pst11 : q_x = (p x H1) := congrArg (fun q => L q) (pst9); let pst12 : (p x H1) = q_x := Eq.symm (pst11); let pst13 : q_H1 = q_x := Eq.trans (pst10) (pst12); pst13)
      exact step_ne_second (by simpa only [he] using qs1)
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval v0 v1) (eval v1 (eval (eval x (eval v2 x)) (eval v1 v1)))) := by
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
  let H1 := eval v2 x
  have e1a : v2 = v2 := by
    change v2 = v2
    rfl
  have e1b : x = x := by
    change x = x
    rfl
  have s1 : Step v2 x H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v2 x
  change x = (eval H0 (eval v1 (eval (eval x H1) (eval v1 v1))))
  have rawEq : (eval H0 (eval v1 (eval (eval x H1) (eval v1 v1)))) = (eval H0 (p v1 (p (p x H1) (p v1 v1)))) := by
    calc
      (eval H0 (eval v1 (eval (eval x H1) (eval v1 v1)))) = (eval H0 (eval v1 (eval (p x H1) (eval v1 v1)))) := congrArg (fun q => (eval H0 (eval v1 (eval q (eval v1 v1))))) (eval_raw (nr0 x v0 v1 v2 H1 s1))
      _ = (eval H0 (eval v1 (eval (p x H1) (p v1 v1)))) := congrArg (fun q => (eval H0 (eval v1 (eval (p x H1) q)))) (eval_raw (nr1 x v0 v1 v2))
      _ = (eval H0 (eval v1 (p (p x H1) (p v1 v1)))) := congrArg (fun q => (eval H0 (eval v1 q))) (eval_raw (nr2 x v0 v1 v2 H1 s1))
      _ = (eval H0 (p v1 (p (p x H1) (p v1 v1)))) := congrArg (fun q => (eval H0 q)) (eval_raw (nr3 x v0 v1 v2 H1 s1))
  exact (eval_hit (Code.law x v0 v1 v2 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1 v2
    exact CM.source_holds x v0 v1 v2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
