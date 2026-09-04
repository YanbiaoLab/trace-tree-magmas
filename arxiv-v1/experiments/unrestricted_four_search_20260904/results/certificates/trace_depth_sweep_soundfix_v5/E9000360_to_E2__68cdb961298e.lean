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
      (s0 : Step v1 v0 H0)
      (s1 : Step v0 H0 H1) :
      Code (p (p (p H1 v0) v0) x) (p v0 (p v0 v0)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v1 q_v0 q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ a = (p (p (p q_H1 q_v0) q_v0) q_x) ∧ b = (p q_v0 (p q_v0 q_v0)) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R a)
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
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
theorem code_no_pair_left (v k : CM) :
    ¬ ∃ o, Code (p v k) v o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p (p q_v0 (p q_v1 q_v0)) q_v0) := (let peq0 : v = (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) := e0; let peq2 : v = (p q_v0 (p q_v0 q_v0)) := e2; let pst0 : (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : (p (p q_v0 (p q_v1 q_v0)) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p q_v0 (p q_v1 q_v0)) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_v0 (p q_v1 q_v0)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H1 q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v = (p (p q_H1 q_v0) q_v0) := e0; let peq2 : v = (p q_v0 (p q_v0 q_v0)) := e2; let pst0 : (p (p q_H1 q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : (p q_H1 q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p q_v0 q_H0) q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p (p q_v0 q_H0) q_v0) := (let peq0 : v = (p (p (p q_v0 q_H0) q_v0) q_v0) := e0; let peq2 : v = (p q_v0 (p q_v0 q_v0)) := e2; let pst0 : (p (p (p q_v0 q_H0) q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : (p (p q_v0 q_H0) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p q_v0 q_H0) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_v0 q_H0) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H1 q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_x at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_v0 (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : v = (p (p q_H1 q_v0) q_v0) := e0; let peq2 : v = (p q_v0 (p q_v0 q_v0)) := e2; let pst0 : (p (p q_H1 q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : (p q_H1 q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
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
        have hcB := code_bounds hc
        have sthB := code_bounds sth
        have p0 := ha
        change o = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change a = (p q_v0 (p q_v0 q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change u = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB sthB z0 z1 z2
        omega
      | hit qs1h =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 (p u0_v1 u0_v0)) (sz_lt_p_left (p u0_v0 (p u0_v1 u0_v0)) u0_v0)) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p u0s1out u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0s0out) (sz_lt_p_left (p u0_v0 u0s0out) u0_v0)) (sz_lt_p_left (p (p u0_v0 u0s0out) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p u0s1out u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have sthB := code_bounds sth
        have qs0hB := code_bounds qs0h
        have p0 := ha
        change o = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change a = (p q_v0 (p q_v0 q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change u = q_x at p2
        have z2 := congrArg sz p2
        simp only [getOut, L, R, U, sz] at hcB sthB qs0hB z0 z1 z2
        omega
      | hit qs1h =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_x) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 (p u0_v1 u0_v0)) (sz_lt_p_left (p u0_v0 (p u0_v1 u0_v0)) u0_v0)) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p u0s1out u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_x) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p u0_v0 u0s0out) u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0s0out) (sz_lt_p_left (p u0_v0 u0s0out) u0_v0)) (sz_lt_p_left (p (p u0_v0 u0s0out) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : o = (p (p (p q_H1 q_v0) q_v0) q_x) := ha; let peq1 : a = (p q_v0 (p q_v0 q_v0)) := hb; let peq3 : a = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_v0 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst2); let pst4 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst2); let pst6 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := congrArg (fun q => p q q_x) (pst6); let pst8 : o = (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) := Eq.trans (peq0) (pst7); let pst9 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = o := Eq.symm (pst8); let pst10 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = u0_x := Eq.trans (pst9) (peq5); let pst11 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst12 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst2); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst13); let pst15 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst1); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst16); let pst18 : (p (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) q_x) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst10) (pst17); let pst19 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst18); let pst20 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p u0s1out u0_v0) := congrArg (fun q => L q) (pst19); let pst21 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst20); let pst22 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst21); pst22)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code H1 v0 o := by
  exact step_no_first s1

theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p H1 v0) v0 o := by
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
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p q_v0 (p q_v1 q_v0)) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_x at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = (p q_v0 (p q_v0 q_v0)) at e3
        have cyc : q_v0 = (p q_v0 (p q_v1 q_v0)) := (let peq0 : v0 = (p (p q_v0 (p q_v1 q_v0)) q_v0) := e0; let peq3 : v0 = (p q_v0 (p q_v0 q_v0)) := e3; let pst0 : (p (p q_v0 (p q_v1 q_v0)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v1 q_v0)) q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 (p q_v1 q_v0)) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 (p q_v1 q_v0)) := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p q_v0 (p q_v1 q_v0)) := sz_lt_p_left q_v0 (p q_v1 q_v0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_x at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = (p q_v0 (p q_v0 q_v0)) at e3
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p q_H1 q_v0) := e0; let peq3 : v0 = (p q_v0 (p q_v0 q_v0)) := e3; let pst0 : (p q_H1 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => R q) (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p q_v0 q_H0) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_x at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = (p q_v0 (p q_v0 q_v0)) at e3
        have cyc : q_v0 = (p q_v0 q_H0) := (let peq0 : v0 = (p (p q_v0 q_H0) q_v0) := e0; let peq3 : v0 = (p q_v0 (p q_v0 q_v0)) := e3; let pst0 : (p (p q_v0 q_H0) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_H0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_H0) := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p q_v0 q_H0) := sz_lt_p_left q_v0 q_H0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_x at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = (p q_v0 (p q_v0 q_v0)) at e3
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p q_H1 q_v0) := e0; let peq3 : v0 = (p q_v0 (p q_v0 q_v0)) := e3; let pst0 : (p q_H1 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => R q) (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
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
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_x at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = (p q_v0 (p q_v0 q_v0)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB z0 z1 z2 z3
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
            have cyc : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 (p u0_v1 u0_v0)) (sz_lt_p_left (p u0_v0 (p u0_v1 u0_v0)) u0_v0)) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0s0out) (sz_lt_p_left (p u0_v0 u0s0out) u0_v0)) (sz_lt_p_left (p (p u0_v0 u0s0out) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p (p q_v0 q_H0) q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_x at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = (p q_v0 (p q_v0 q_v0)) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB z0 z1 z2 z3
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
            have cyc : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)) = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 (p u0_v1 u0_v0)) (sz_lt_p_left (p u0_v0 (p u0_v1 u0_v0)) u0_v0)) (sz_lt_p_left (p (p u0_v0 (p u0_v1 u0_v0)) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := congrArg (fun q => p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p (p u0_v0 u0s0out) u0_v0) u0_v0)) = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p (p u0_v0 u0s0out) u0_v0) u0_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v0 u0s0out) (sz_lt_p_left (p u0_v0 u0s0out) u0_v0)) (sz_lt_p_left (p (p u0_v0 u0s0out) u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := (let peq0 : H1 = (p (p q_H1 q_v0) q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R q)) (ha); let peq2 : v0 = (p q_v0 (p q_v0 q_v0)) := hb; let peq4 : v0 = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); let pst2 : v0 = (p q_v0 (p q_v0 q_v0)) := Eq.trans (peq1) (pst1); let pst3 : (p q_v0 (p q_v0 q_v0)) = v0 := Eq.symm (pst2); let pst4 : (p q_v0 (p q_v0 q_v0)) = (p (p (p u0s1out u0_v0) u0_v0) u0_x) := Eq.trans (pst3) (peq4); let pst5 : q_v0 = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_H1 (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p q_H1 q) (pst5); let pst7 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) q) (pst5); let pst9 : (p (p q_H1 q_v0) q_v0) = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst7) (pst8); let pst10 : H1 = (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (peq0) (pst9); let pst11 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = H1 := Eq.symm (pst10); let pst12 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst11) (peq6); let pst13 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) q_v0) := congrArg (fun q => p q q_v0) (pst5); let pst14 : (p (p (p u0s1out u0_v0) u0_v0) q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := congrArg (fun q => p (p (p u0s1out u0_v0) u0_v0) q) (pst5); let pst15 : (p q_v0 q_v0) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst13) (pst14); let pst16 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = (p q_v0 q_v0) := Eq.symm (pst15); let pst17 : (p q_v0 q_v0) = u0_x := congrArg (fun q => R q) (pst4); let pst18 : (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) = u0_x := Eq.trans (pst16) (pst17); let pst19 : u0_x = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.symm (pst18); let pst20 : (p (p q_H1 (p (p u0s1out u0_v0) u0_v0)) (p (p u0s1out u0_v0) u0_v0)) = (p (p (p u0s1out u0_v0) u0_v0) (p (p u0s1out u0_v0) u0_v0)) := Eq.trans (pst12) (pst19); let pst21 : (p q_H1 (p (p u0s1out u0_v0) u0_v0)) = (p (p u0s1out u0_v0) u0_v0) := congrArg (fun q => L q) (pst20); let pst22 : (p (p u0s1out u0_v0) u0_v0) = u0_v0 := congrArg (fun q => R q) (pst21); let pst23 : u0_v0 = (p (p u0s1out u0_v0) u0_v0) := Eq.symm (pst22); pst23)
            have hlt : sz u0_v0 < sz (p (p u0s1out u0_v0) u0_v0) := Nat.lt_trans (sz_lt_p_right u0s1out u0_v0) (sz_lt_p_left (p u0s1out u0_v0) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p (p H1 v0) v0) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq3 : v0 = q_x := congrArg (fun q => (R q)) (ha); let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = q_v0 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_v0 := Eq.trans (peq0) (pst1); let pst3 : q_v0 = v0 := Eq.symm (pst2); let pst4 : q_v0 = q_x := Eq.trans (pst3) (peq3); let pst5 : q_H1 = q_x := Eq.trans (pst1) (pst4); let pst6 : q_x = q_v0 := Eq.symm (pst4); let pst7 : q_H1 = q_v0 := Eq.trans (pst5) (pst6); pst7)
      exact step_ne_first (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq3 : v0 = q_x := congrArg (fun q => (R q)) (ha); let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = q_v0 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_v0 := Eq.trans (peq0) (pst1); let pst3 : q_v0 = v0 := Eq.symm (pst2); let pst4 : q_v0 = q_x := Eq.trans (pst3) (peq3); let pst5 : q_H1 = q_x := Eq.trans (pst1) (pst4); let pst6 : q_x = q_v0 := Eq.symm (pst4); let pst7 : q_H1 = q_v0 := Eq.trans (pst5) (pst6); pst7)
      exact step_ne_first (by simpa only [he] using qs1)
  | hit s1h =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p (p q_v0 (p q_v1 q_v0)) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change x = (p q_v0 (p q_v0 q_v0)) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB z0 z1 z2 z3 z4
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change x = (p q_v0 (p q_v0 q_v0)) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB z0 z1 z2 z3 z4
        omega
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p (p q_v0 q_H0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change x = (p q_v0 (p q_v0 q_v0)) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB z0 z1 z2 z3 z4
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change x = (p q_v0 (p q_v0 q_v0)) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB z0 z1 z2 z3 z4
        omega
theorem nr3 (x v0 v1 : CM)
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
      change v0 = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_v0 q_v0)) at e1
      have cyc : q_v0 = (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) := (let peq0 : v0 = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) := e0; let peq1 : v0 = (p q_v0 (p q_v0 q_v0)) := e1; let pst0 : (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq1); let pst2 : (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_H1 q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_v0 q_v0)) at e1
      have cyc : q_v0 = (p (p q_H1 q_v0) q_v0) := (let peq0 : v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := e0; let peq1 : v0 = (p q_v0 (p q_v0 q_v0)) := e1; let pst0 : (p (p (p q_H1 q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_H1 q_v0) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p q_H1 q_v0) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) q_v0) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_v0 q_v0)) at e1
      have cyc : q_v0 = (p (p (p q_v0 q_H0) q_v0) q_v0) := (let peq0 : v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) := e0; let peq1 : v0 = (p q_v0 (p q_v0 q_v0)) := e1; let pst0 : (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq1); let pst2 : (p (p (p q_v0 q_H0) q_v0) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p (p q_v0 q_H0) q_v0) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) q_v0) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_H1 q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p q_v0 (p q_v0 q_v0)) at e1
      have cyc : q_v0 = (p (p q_H1 q_v0) q_v0) := (let peq0 : v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := e0; let peq1 : v0 = (p q_v0 (p q_v0 q_v0)) := e1; let pst0 : (p (p (p q_H1 q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) q_v0) q_x) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_H1 q_v0) q_v0) = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p (p q_H1 q_v0) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) q_v0) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) := (let peq0 : v0 = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_v0)) (sz_lt_p_left (p q_v0 (p q_v1 q_v0)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0)) (sz_lt_p_left (p (p (p q_v0 (p q_v1 q_v0)) q_v0) q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_H1 q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := (let peq0 : v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_H1 q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H1 q_v0) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)) (sz_lt_p_left (p (p q_H1 q_v0) q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) := (let peq0 : v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_H0) q_v0) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_H0) q_v0) q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p (p q_H1 q_v0) q_v0) q_x) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p q_v0 q_v0) at e2
      have cyc : q_v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := (let peq0 : v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_H1 q_v0) q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H1 q_v0) q_v0) q_x) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H1 q_v0) q_v0) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)) (sz_lt_p_left (p (p q_H1 q_v0) q_v0) q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval v0 (eval v1 v0)) v0) v0) x) (eval v0 (eval v0 v0))) := by
  let H0 := eval v1 v0
  have e0a : v1 = v1 := by
    change v1 = v1
    rfl
  have e0b : v0 = v0 := by
    change v0 = v0
    rfl
  have s0 : Step v1 v0 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v1 v0
  let H1 := eval v0 (eval v1 v0)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval v1 v0) = H0 := by
    change H0 = H0
    rfl
  have s1 : Step v0 H0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval v1 v0)
  change x = (eval (eval (eval (eval H1 v0) v0) x) (eval v0 (eval v0 v0)))
  have rawEq : (eval (eval (eval (eval H1 v0) v0) x) (eval v0 (eval v0 v0))) = (eval (p (p (p H1 v0) v0) x) (p v0 (p v0 v0))) := by
    calc
      (eval (eval (eval (eval H1 v0) v0) x) (eval v0 (eval v0 v0))) = (eval (eval (eval (p H1 v0) v0) x) (eval v0 (eval v0 v0))) := congrArg (fun q => (eval (eval (eval q v0) x) (eval v0 (eval v0 v0)))) (eval_raw (nr0 x v0 v1 H1 s1))
      _ = (eval (eval (p (p H1 v0) v0) x) (eval v0 (eval v0 v0))) := congrArg (fun q => (eval (eval q x) (eval v0 (eval v0 v0)))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval (p (p (p H1 v0) v0) x) (eval v0 (eval v0 v0))) := congrArg (fun q => (eval q (eval v0 (eval v0 v0)))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval (p (p (p H1 v0) v0) x) (eval v0 (p v0 v0))) := congrArg (fun q => (eval (p (p (p H1 v0) v0) x) (eval v0 q))) (eval_raw (nr3 x v0 v1))
      _ = (eval (p (p (p H1 v0) v0) x) (p v0 (p v0 v0))) := congrArg (fun q => (eval (p (p (p H1 v0) v0) x) q)) (eval_raw (nr4 x v0 v1))
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
