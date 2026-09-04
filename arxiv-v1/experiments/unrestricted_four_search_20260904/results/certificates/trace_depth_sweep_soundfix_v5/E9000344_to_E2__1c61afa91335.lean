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
      (s0 : Step v1 x H0)
      (s1 : Step v0 H0 H1) :
      Code (p (p (p H1 v0) v0) (p x x)) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v1 q_x q_H0 ∧ Step q_v0 q_H0 q_H1 ∧ a = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R a))
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
      change v = (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) := (let peq0 : v = (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_x)) (sz_lt_p_left (p q_v0 (p q_v1 q_x)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H1 q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H1 q_v0) q_v0) := (let peq0 : v = (p (p q_H1 q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_H1 q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H1 q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) q_v0) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p q_v0 q_H0) q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p (p q_v0 q_H0) q_v0) q_v0) := (let peq0 : v = (p (p (p q_v0 q_H0) q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p (p q_v0 q_H0) q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_H0) q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p (p q_v0 q_H0) q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_H0) q_v0) q_v0) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p q_H1 q_v0) q_v0) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v0 at e2
      have cyc : q_v0 = (p (p q_H1 q_v0) q_v0) := (let peq0 : v = (p (p q_H1 q_v0) q_v0) := e0; let peq2 : v = q_v0 := e2; let pst0 : (p (p q_H1 q_v0) q_v0) = v := Eq.symm (peq0); let pst1 : (p (p q_H1 q_v0) q_v0) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_H1 q_v0) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_H1 q_v0) q_v0) := Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)
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
theorem nr0 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code H1 v0 o := by
  exact step_no_first s1

theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p H1 v0) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
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
        change v0 = (p (p q_v0 (p q_v1 q_x)) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_x = (p q_v0 (p q_v1 q_x)) := (let peq0 : v0 = (p (p q_v0 (p q_v1 q_x)) q_v0) := e0; let peq2 : v0 = (p q_x q_x) := e2; let pst0 : (p (p q_v0 (p q_v1 q_x)) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 (p q_v1 q_x)) q_v0) = (p q_x q_x) := Eq.trans (pst0) (peq2); let pst2 : (p q_v0 (p q_v1 q_x)) = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = (p q_v0 (p q_v1 q_x)) := Eq.symm (pst2); pst3)
        have hlt : sz q_x < sz (p q_v0 (p q_v1 q_x)) := Nat.lt_trans (sz_lt_p_right q_v1 q_x) (sz_lt_p_right q_v0 (p q_v1 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_x = (p q_x q_x) := (let peq0 : v0 = (p q_H1 q_v0) := e0; let peq2 : v0 = (p q_x q_x) := e2; let peq3 : v0 = q_v0 := e3; let pst0 : (p q_H1 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = (p q_x q_x) := Eq.trans (pst0) (peq2); let pst2 : q_H1 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = q_v0 := Eq.trans (pst8) (peq3); let pst10 : (p q_x q_x) = q_x := Eq.trans (pst9) (pst4); let pst11 : q_x = (p q_x q_x) := Eq.symm (pst10); pst11)
        have hlt : sz q_x < sz (p q_x q_x) := sz_lt_p_left q_x q_x
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p q_v0 q_H0) q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_v0 = (p q_v0 q_H0) := (let peq0 : v0 = (p (p q_v0 q_H0) q_v0) := e0; let peq2 : v0 = (p q_x q_x) := e2; let pst0 : (p (p q_v0 q_H0) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_H0) q_v0) = (p q_x q_x) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_H0) = q_x := congrArg (fun q => L q) (pst1); let pst4 : q_x = (p q_v0 q_H0) := Eq.symm (pst3); let pst5 : q_v0 = (p q_v0 q_H0) := Eq.trans (pst2) (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_H0) := sz_lt_p_left q_v0 q_H0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p q_H1 q_v0) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change H0 = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = q_v0 at e3
        have cyc : q_x = (p q_x q_x) := (let peq0 : v0 = (p q_H1 q_v0) := e0; let peq2 : v0 = (p q_x q_x) := e2; let peq3 : v0 = q_v0 := e3; let pst0 : (p q_H1 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = (p q_x q_x) := Eq.trans (pst0) (peq2); let pst2 : q_H1 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_H1 q_v0) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = q_v0 := Eq.trans (pst8) (peq3); let pst10 : (p q_x q_x) = q_x := Eq.trans (pst9) (pst4); let pst11 : q_x = (p q_x q_x) := Eq.symm (pst10); pst11)
        have hlt : sz q_x < sz (p q_x q_x) := sz_lt_p_left q_x q_x
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
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p q_x q_x) < sz (p (p (p (p q_x q_x) (p q_v1 q_x)) (p q_x q_x)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left (p q_x q_x) (p q_v1 q_x)) (sz_lt_p_left (p (p q_x q_x) (p q_v1 q_x)) (p q_x q_x))) (sz_lt_p_left (p (p (p q_x q_x) (p q_v1 q_x)) (p q_x q_x)) (p q_x q_x))
          have large_eq : sz v0 = sz (p q_x q_x) := congrArg sz (p1)
          have small_eq : sz H1 = sz (p (p (p (p q_x q_x) (p q_v1 q_x)) (p q_x q_x)) (p q_x q_x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q (p q_v1 q_x)) (Eq.trans (p2.symm) (p1)))) (congrArg (fun q => p (p (p q_x q_x) (p q_v1 q_x)) q) (Eq.trans (p2.symm) (p1))))) (congrArg (fun q => p (p (p (p q_x q_x) (p q_v1 q_x)) (p q_x q_x)) q) (Eq.trans (p2.symm) (p1)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p q_H1 q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p q_x q_x) < sz (p (p q_H1 (p q_x q_x)) (p q_x q_x)) := Nat.lt_trans (sz_lt_p_right q_H1 (p q_x q_x)) (sz_lt_p_left (p q_H1 (p q_x q_x)) (p q_x q_x))
          have large_eq : sz v0 = sz (p q_x q_x) := congrArg sz (p1)
          have small_eq : sz H1 = sz (p (p q_H1 (p q_x q_x)) (p q_x q_x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q_H1 q) (Eq.trans (p2.symm) (p1)))) (congrArg (fun q => p (p q_H1 (p q_x q_x)) q) (Eq.trans (p2.symm) (p1)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p (p q_v0 q_H0) q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p q_x q_x) < sz (p (p (p (p q_x q_x) q_H0) (p q_x q_x)) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left (p q_x q_x) q_H0) (sz_lt_p_left (p (p q_x q_x) q_H0) (p q_x q_x))) (sz_lt_p_left (p (p (p q_x q_x) q_H0) (p q_x q_x)) (p q_x q_x))
          have large_eq : sz v0 = sz (p q_x q_x) := congrArg sz (p1)
          have small_eq : sz H1 = sz (p (p (p (p q_x q_x) q_H0) (p q_x q_x)) (p q_x q_x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_H0) (Eq.trans (p2.symm) (p1)))) (congrArg (fun q => p (p (p q_x q_x) q_H0) q) (Eq.trans (p2.symm) (p1))))) (congrArg (fun q => p (p (p (p q_x q_x) q_H0) (p q_x q_x)) q) (Eq.trans (p2.symm) (p1)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H1 = (p (p q_H1 q_v0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p q_x q_x) < sz (p (p q_H1 (p q_x q_x)) (p q_x q_x)) := Nat.lt_trans (sz_lt_p_right q_H1 (p q_x q_x)) (sz_lt_p_left (p q_H1 (p q_x q_x)) (p q_x q_x))
          have large_eq : sz v0 = sz (p q_x q_x) := congrArg sz (p1)
          have small_eq : sz H1 = sz (p (p q_H1 (p q_x q_x)) (p q_x q_x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q_H1 q) (Eq.trans (p2.symm) (p1)))) (congrArg (fun q => p (p q_H1 (p q_x q_x)) q) (Eq.trans (p2.symm) (p1)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) := (let peq0 : x = (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v1 q_x)) (sz_lt_p_left (p q_v0 (p q_v1 q_x)) q_v0)) (sz_lt_p_left (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0)) (sz_lt_p_left (p (p (p q_v0 (p q_v1 q_x)) q_v0) q_v0) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := (let peq0 : x = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)) (sz_lt_p_left (p (p q_H1 q_v0) q_v0) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) := (let peq0 : x = (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_H0) (sz_lt_p_left (p q_v0 q_H0) q_v0)) (sz_lt_p_left (p (p q_v0 q_H0) q_v0) q_v0)) (sz_lt_p_left (p (p (p q_v0 q_H0) q_v0) q_v0) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := (let peq0 : x = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p (p q_H1 q_v0) q_v0) (p q_x q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H1 q_v0) (sz_lt_p_left (p q_H1 q_v0) q_v0)) (sz_lt_p_left (p (p q_H1 q_v0) q_v0) (p q_x q_x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step v0 H0 H1) :
    ¬ ∃ o, Code (p (p H1 v0) v0) (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq3 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = q_v0 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_v0 := Eq.trans (peq0) (pst1); let pst3 : q_v0 = v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_x q_x) := Eq.trans (pst3) (peq3); let pst5 : q_H1 = (p q_x q_x) := Eq.trans (pst1) (pst4); let pst6 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst7 : q_H1 = q_v0 := Eq.trans (pst5) (pst6); pst7)
      exact step_ne_first (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_H1 := congrArg (fun q => (L (L (L q)))) (ha); let peq2 : v0 = q_v0 := congrArg (fun q => (R (L q))) (ha); let peq3 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let pst0 : q_H1 = v0 := Eq.symm (peq0); let pst1 : q_H1 = q_v0 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_v0 := Eq.trans (peq0) (pst1); let pst3 : q_v0 = v0 := Eq.symm (pst2); let pst4 : q_v0 = (p q_x q_x) := Eq.trans (pst3) (peq3); let pst5 : q_H1 = (p q_x q_x) := Eq.trans (pst1) (pst4); let pst6 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst7 : q_H1 = q_v0 := Eq.trans (pst5) (pst6); pst7)
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
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p (p q_v0 (p q_v1 q_x)) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change (p x x) = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p x x) < sz (p (p (p x x) (p q_v1 q_x)) (p x x)) := Nat.lt_trans (sz_lt_p_left (p x x) (p q_v1 q_x)) (sz_lt_p_left (p (p x x) (p q_v1 q_x)) (p x x))
          have large_eq : sz v0 = sz (p x x) := congrArg sz (Eq.trans (p1) (p3.symm))
          have small_eq : sz H1 = sz (p (p (p x x) (p q_v1 q_x)) (p x x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q (p q_v1 q_x)) (p3.symm))) (congrArg (fun q => p (p (p x x) (p q_v1 q_x)) q) (p3.symm))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change (p x x) = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p x x) < sz (p q_H1 (p x x)) := sz_lt_p_right q_H1 (p x x)
          have large_eq : sz v0 = sz (p x x) := congrArg sz (Eq.trans (p1) (p3.symm))
          have small_eq : sz H1 = sz (p q_H1 (p x x)) := congrArg sz (Eq.trans (p0) (congrArg (fun q => p q_H1 q) (p3.symm)))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p (p q_v0 q_H0) q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change (p x x) = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p x x) < sz (p (p (p x x) q_H0) (p x x)) := Nat.lt_trans (sz_lt_p_left (p x x) q_H0) (sz_lt_p_left (p (p x x) q_H0) (p x x))
          have large_eq : sz v0 = sz (p x x) := congrArg sz (Eq.trans (p1) (p3.symm))
          have small_eq : sz H1 = sz (p (p (p x x) q_H0) (p x x)) := congrArg sz (Eq.trans (p0) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => p q q_H0) (p3.symm))) (congrArg (fun q => p (p (p x x) q_H0) q) (p3.symm))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H1 = (p q_H1 q_v0) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v0 = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = (p q_x q_x) at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change (p x x) = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz v0 < sz H1 := by
          have structural : sz (p x x) < sz (p q_H1 (p x x)) := sz_lt_p_right q_H1 (p x x)
          have large_eq : sz v0 = sz (p x x) := congrArg sz (Eq.trans (p1) (p3.symm))
          have small_eq : sz H1 = sz (p q_H1 (p x x)) := congrArg sz (Eq.trans (p0) (congrArg (fun q => p q_H1 q) (p3.symm)))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s1hB.2).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval (eval v0 (eval v1 x)) v0) v0) (eval x x)) v0) := by
  let H0 := eval v1 x
  have e0a : v1 = v1 := by
    change v1 = v1
    rfl
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step v1 x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v1 x
  let H1 := eval v0 (eval v1 x)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval v1 x) = H0 := by
    change H0 = H0
    rfl
  have s1 : Step v0 H0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval v1 x)
  change x = (eval (eval (eval (eval H1 v0) v0) (eval x x)) v0)
  have rawEq : (eval (eval (eval (eval H1 v0) v0) (eval x x)) v0) = (eval (p (p (p H1 v0) v0) (p x x)) v0) := by
    calc
      (eval (eval (eval (eval H1 v0) v0) (eval x x)) v0) = (eval (eval (eval (p H1 v0) v0) (eval x x)) v0) := congrArg (fun q => (eval (eval (eval q v0) (eval x x)) v0)) (eval_raw (nr0 x v0 v1 H1 s1))
      _ = (eval (eval (p (p H1 v0) v0) (eval x x)) v0) := congrArg (fun q => (eval (eval q (eval x x)) v0)) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval (eval (p (p H1 v0) v0) (p x x)) v0) := congrArg (fun q => (eval (eval (p (p H1 v0) v0) q) v0)) (eval_raw (nr2 x v0 v1))
      _ = (eval (p (p (p H1 v0) v0) (p x x)) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr3 x v0 v1 H1 s1))
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
