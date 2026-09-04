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
      (s1 : Step v1 x H1) :
      Code (p (p (p (p (p H0 v0) v2) H1) v1) v1) v1 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_v1 q_x q_H1 ∧ a = (p (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) q_v1) ∧ b = q_v1 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 s0 s1 => ⟨x, v0, v1, v2, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (R (L c))
theorem code_key {a b o : CM} (h : Code a b o) : getKey a = b := by
  cases h <;> rfl
theorem code_key_unique {a b q o : CM} (h : Code a b o) (k : Code a q o) : b = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz b < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  exact Nat.lt_trans (sz_lt_p_right (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) (sz_lt_p_left (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) q_v1)
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact Nat.lt_trans (sz_lt_p_right (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) (sz_lt_p_left (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) q_v1)
  ·
    cases s1 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v1 q_x) (sz_lt_p_right (p (p q_H0 q_v0) q_v2) (p q_v1 q_x))) (sz_lt_p_left (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1)) (sz_lt_p_left (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) q_v1)
    | hit h1 =>
      exact Nat.lt_trans (code_key_small h1) (Nat.lt_trans (sz_lt_p_right (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) (sz_lt_p_left (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) q_v1))
theorem step_second_unique {a b q o : CM} (h : Step a b o) (k : Step a q o) : b = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := code_bounds hc
      have hp := sz_lt_p_left a b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
  | hit hc =>
    cases k with
    | raw =>
      have hb := code_bounds hc
      have hp := sz_lt_p_left a q
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
    | hit hk => exact code_key_unique hc hk
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, hs0, hs1, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_v2, r_q_H0, r_q_H1, rs0, rs1, ka, kb, ko⟩
  have et := congrArg (fun z => (R (L (L z)))) (ha.symm.trans ka)
  have eo := congrArg (fun z => (R (L z))) (ha.symm.trans ka)
  change q_H1 = r_q_H1 at et
  change q_v1 = r_q_v1 at eo
  rw [eo.symm, et.symm] at rs1
  have er := step_second_unique hs1 rs1
  have ex : q_x = r_q_x := er
  exact ho.trans (ex.trans ko.symm)
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v1 at e2
      have cyc : q_v1 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) := (let peq0 : v = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) := e0; let peq2 : v = q_v1 := e2; let pst0 : (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) = v := Eq.symm (peq0); let pst1 : (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x))) (sz_lt_p_left (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v1 at e2
      have cyc : q_v1 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) := (let peq0 : v = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) := e0; let peq2 : v = q_v1 := e2; let pst0 : (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) = v := Eq.symm (peq0); let pst1 : (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1)) (sz_lt_p_left (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v1 at e2
      have cyc : q_v1 = (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) := (let peq0 : v = (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) := e0; let peq2 : v = q_v1 := e2; let pst0 : (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) = v := Eq.symm (peq0); let pst1 : (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_x) (sz_lt_p_right (p (p q_H0 q_v0) q_v2) (p q_v1 q_x))) (sz_lt_p_left (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = q_v1 at e1
      have e2 := congrArg (fun q => q) hb
      change v = q_v1 at e2
      have cyc : q_v1 = (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) := (let peq0 : v = (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) := e0; let peq2 : v = q_v1 := e2; let pst0 : (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) = v := Eq.symm (peq0); let pst1 : (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) := sz_lt_p_right (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1
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
theorem nr0 (x v0 v1 v2 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code H0 v0 o := by
  exact step_no_first s0

theorem nr1 (x v0 v1 v2 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code (p H0 v0) v2 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
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
        change v0 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v1 at e2
        have e3 := congrArg (fun q => q) hb
        change v2 = q_v1 at e3
        have cyc : q_v1 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) := (let peq0 : v0 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v1 < sz (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v1 at e2
        have e3 := congrArg (fun q => q) hb
        change v2 = q_v1 at e3
        have cyc : q_v1 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) := (let peq0 : v0 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) = v0 := Eq.symm (peq0); let pst1 : (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v1 < sz (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v1 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change v0 = q_v1 at e2
        have e3 := congrArg (fun q => q) hb
        change v2 = q_v1 at e3
        have cyc : q_v1 = (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) := (let peq0 : v0 = (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v1 < sz (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) := Nat.lt_trans (sz_lt_p_left q_v1 q_x) (sz_lt_p_right (p (p q_H0 q_v0) q_v2) (p q_v1 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change v0 = (p (p (p q_H0 q_v0) q_v2) q_H1) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change v1 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v1 at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v2 = q_v1 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz q_v0 < sz q_v1 := by
          have structural : sz q_v0 < sz (p (p (p q_H0 q_v0) q_v2) q_H1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v2)) (sz_lt_p_left (p (p q_H0 q_v0) q_v2) q_H1)
          have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
          have small_eq : sz q_v1 = sz (p (p (p q_H0 q_v0) q_v2) q_H1) := congrArg sz (Eq.trans (p2.symm) (p0))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs0hB.1).elim
  | hit s0h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H0 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v2 = q_v1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H0 := by
          have structural : sz q_v1 < sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x))) (sz_lt_p_left (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1)
          have large_eq : sz v0 = sz q_v1 := congrArg sz (p1)
          have small_eq : sz H0 = sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) (p q_v1 q_x)) q_v1) := congrArg sz (p0)
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H0 = (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v2 = q_v1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H0 := by
          have structural : sz q_v1 < sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)) (sz_lt_p_left (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1)) (sz_lt_p_left (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1)
          have large_eq : sz v0 = sz q_v1 := congrArg sz (p1)
          have small_eq : sz H0 = sz (p (p (p (p (p q_v0 q_v1) q_v0) q_v2) q_H1) q_v1) := congrArg sz (p0)
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H0 = (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v2 = q_v1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H0 := by
          have structural : sz q_v1 < sz (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_x) (sz_lt_p_right (p (p q_H0 q_v0) q_v2) (p q_v1 q_x))) (sz_lt_p_left (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1)
          have large_eq : sz v0 = sz q_v1 := congrArg sz (p1)
          have small_eq : sz H0 = sz (p (p (p (p q_H0 q_v0) q_v2) (p q_v1 q_x)) q_v1) := congrArg sz (p0)
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change H0 = (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change v0 = q_v1 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v2 = q_v1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz v0 < sz H0 := by
          have structural : sz q_v1 < sz (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) := sz_lt_p_right (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1
          have large_eq : sz v0 = sz q_v1 := congrArg sz (p1)
          have small_eq : sz H0 = sz (p (p (p (p q_H0 q_v0) q_v2) q_H1) q_v1) := congrArg sz (p0)
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) s0hB.2).elim
theorem nr2 (x v0 v1 v2 H0 H1 : CM)
    (s0 : Step v0 v1 H0)
    (s1 : Step v1 x H1) :
    ¬ ∃ o, Code (p (p H0 v0) v2) H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
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
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = (p q_v1 q_x) at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v1 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v2 = q_v1 at e3
          have e4 := congrArg (fun q => q) hb
          change (p v1 x) = q_v1 at e4
          have cyc : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := (let peq0 : v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_v0 q_v1) q_v0) q_v2) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) q_v2) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := Eq.symm (pst1); pst2)
          have hlt : sz q_v1 < sz (p (p (p q_v0 q_v1) q_v0) q_v2) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = q_H1 at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v1 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v2 = q_v1 at e3
          have e4 := congrArg (fun q => q) hb
          change (p v1 x) = q_v1 at e4
          have cyc : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := (let peq0 : v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_v0 q_v1) q_v0) q_v2) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) q_v2) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := Eq.symm (pst1); pst2)
          have hlt : sz q_v1 < sz (p (p (p q_v0 q_v1) q_v0) q_v2) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p (p q_H0 q_v0) q_v2) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = (p q_v1 q_x) at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v1 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v2 = q_v1 at e3
          have e4 := congrArg (fun q => q) hb
          change (p v1 x) = q_v1 at e4
          have cyc : q_H0 = (p (p q_H0 q_v0) q_v2) := (let peq0 : v0 = (p (p q_H0 q_v0) q_v2) := e0; let peq1 : v1 = (p q_v1 q_x) := e1; let peq2 : v0 = q_v1 := e2; let peq4 : (p v1 x) = q_v1 := e4; let pst0 : (p (p q_H0 q_v0) q_v2) = v0 := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) q_v2) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p q_H0 q_v0) q_v2) := Eq.symm (pst1); let pst3 : (p q_v1 q_x) = (p (p (p q_H0 q_v0) q_v2) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : v1 = (p (p (p q_H0 q_v0) q_v2) q_x) := Eq.trans (peq1) (pst3); let pst5 : (p v1 x) = (p (p (p (p q_H0 q_v0) q_v2) q_x) x) := congrArg (fun q => p q x) (pst4); let pst6 : (p (p (p (p q_H0 q_v0) q_v2) q_x) x) = (p v1 x) := Eq.symm (pst5); let pst7 : (p (p (p (p q_H0 q_v0) q_v2) q_x) x) = q_v1 := Eq.trans (pst6) (peq4); let pst8 : (p (p (p (p q_H0 q_v0) q_v2) q_x) x) = (p (p q_H0 q_v0) q_v2) := Eq.trans (pst7) (pst2); let pst9 : (p (p (p q_H0 q_v0) q_v2) q_x) = (p q_H0 q_v0) := congrArg (fun q => L q) (pst8); let pst10 : (p (p q_H0 q_v0) q_v2) = q_H0 := congrArg (fun q => L q) (pst9); let pst11 : q_H0 = (p (p q_H0 q_v0) q_v2) := Eq.symm (pst10); pst11)
          have hlt : sz q_H0 < sz (p (p q_H0 q_v0) q_v2) := Nat.lt_trans (sz_lt_p_left q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have hcB := code_bounds hc
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L (L q)))) (ha)
          change v0 = (p (p q_H0 q_v0) q_v2) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L (L q)))) (ha)
          change v1 = q_H1 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R (L q))) (ha)
          change v0 = q_v1 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R q)) (ha)
          change v2 = q_v1 at p3
          have z3 := congrArg sz p3
          have p4 := hb
          change (p v1 x) = q_v1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          have badlt : sz q_v0 < sz q_v1 := by
            have structural : sz q_v0 < sz (p (p q_H0 q_v0) q_v2) := Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v2)
            have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
            have small_eq : sz q_v1 = sz (p (p q_H0 q_v0) q_v2) := congrArg sz (Eq.trans (p2.symm) (p0))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs0hB.1).elim
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = (p q_v1 q_x) at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v1 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v2 = q_v1 at e3
          have e4 := congrArg (fun q => q) hb
          change H1 = q_v1 at e4
          have cyc : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := (let peq0 : v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_v0 q_v1) q_v0) q_v2) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) q_v2) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := Eq.symm (pst1); pst2)
          have hlt : sz q_v1 < sz (p (p (p q_v0 q_v1) q_v0) q_v2) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit qs1h =>
          have e0 := congrArg (fun q => (L (L (L q)))) ha
          change v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) at e0
          have e1 := congrArg (fun q => (R (L (L q)))) ha
          change v1 = q_H1 at e1
          have e2 := congrArg (fun q => (R (L q))) ha
          change v0 = q_v1 at e2
          have e3 := congrArg (fun q => (R q)) ha
          change v2 = q_v1 at e3
          have e4 := congrArg (fun q => q) hb
          change H1 = q_v1 at e4
          have cyc : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := (let peq0 : v0 = (p (p (p q_v0 q_v1) q_v0) q_v2) := e0; let peq2 : v0 = q_v1 := e2; let pst0 : (p (p (p q_v0 q_v1) q_v0) q_v2) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) q_v2) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p (p (p q_v0 q_v1) q_v0) q_v2) := Eq.symm (pst1); pst2)
          have hlt : sz q_v1 < sz (p (p (p q_v0 q_v1) q_v0) q_v2) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)) (sz_lt_p_left (p (p q_v0 q_v1) q_v0) q_v2)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have hcB := code_bounds hc
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L (L q)))) (ha)
          change v0 = (p (p q_H0 q_v0) q_v2) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L (L q)))) (ha)
          change v1 = (p q_v1 q_x) at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R (L q))) (ha)
          change v0 = q_v1 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R q)) (ha)
          change v2 = q_v1 at p3
          have z3 := congrArg sz p3
          have p4 := hb
          change H1 = q_v1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          have badlt : sz q_v0 < sz q_v1 := by
            have structural : sz q_v0 < sz (p (p q_H0 q_v0) q_v2) := Nat.lt_trans (sz_lt_p_right q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) q_v2)
            have large_eq : sz q_v0 = sz q_v0 := congrArg sz (rfl)
            have small_eq : sz q_v1 = sz (p (p q_H0 q_v0) q_v2) := congrArg sz (Eq.trans (p2.symm) (p0))
            exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
          exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs0hB.1).elim
        | hit qs1h =>
          have hcB := code_bounds hc
          have s1hB := code_bounds s1h
          have qs0hB := code_bounds qs0h
          have qs1hB := code_bounds qs1h
          have s0B := s0B
          have s1B := s1B
          have qs0B := qs0B
          have qs1B := qs1B
          have p0 := congrArg (fun q => (L (L (L q)))) (ha)
          change v0 = (p (p q_H0 q_v0) q_v2) at p0
          have z0 := congrArg sz p0
          have p1 := congrArg (fun q => (R (L (L q)))) (ha)
          change v1 = q_H1 at p1
          have z1 := congrArg sz p1
          have p2 := congrArg (fun q => (R (L q))) (ha)
          change v0 = q_v1 at p2
          have z2 := congrArg sz p2
          have p3 := congrArg (fun q => (R q)) (ha)
          change v2 = q_v1 at p3
          have z3 := congrArg sz p3
          have p4 := hb
          change H1 = q_v1 at p4
          have z4 := congrArg sz p4
          have p5 := ho
          change o = q_x at p5
          have z5 := congrArg sz p5
          have hx : sz (p (p q_H0 q_v0) q_v2) < sz q_H1 := by
            have q := s1hB.2
            have eu : sz H1 = sz (p (p q_H0 q_v0) q_v2) := congrArg sz (Eq.trans (p4) (Eq.trans (p2.symm) (p0)))
            have ev : sz v1 = sz q_H1 := congrArg sz (p1)
            have q1 : sz (p (p q_H0 q_v0) q_v2) < sz v1 := lt_of_eq_of_lt eu.symm q
            exact lt_of_lt_of_eq q1 ev
          have hy : sz q_H1 < sz (p (p q_H0 q_v0) q_v2) := by
            have q := qs1hB.2
            have ev : sz q_H1 = sz q_H1 := congrArg sz (rfl)
            have eu : sz q_v1 = sz (p (p q_H0 q_v0) q_v2) := congrArg sz (Eq.trans (p2.symm) (p0))
            have q1 : sz q_H1 < sz q_v1 := lt_of_eq_of_lt ev.symm q
            exact lt_of_lt_of_eq q1 eu
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
  | hit s0h =>
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
          have ena : v0 = (p v1 x) := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : (p v1 x) = q_v1 := hb; let pst0 : q_v1 = (p v1 x) := Eq.symm (peq3); let pst1 : v0 = (p v1 x) := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : v0 = (p v1 x) := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : (p v1 x) = q_v1 := hb; let pst0 : q_v1 = (p v1 x) := Eq.symm (peq3); let pst1 : v0 = (p v1 x) := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : v0 = (p v1 x) := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : (p v1 x) = q_v1 := hb; let pst0 : q_v1 = (p v1 x) := Eq.symm (peq3); let pst1 : v0 = (p v1 x) := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : v0 = (p v1 x) := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : (p v1 x) = q_v1 := hb; let pst0 : q_v1 = (p v1 x) := Eq.symm (peq3); let pst1 : v0 = (p v1 x) := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
    | hit s1h =>
      have qs0B := step_bound qs0
      have qs0N := step_no_first qs0
      cases qs0 with
      | raw =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : v0 = H1 := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : H1 = q_v1 := hb; let pst0 : q_v1 = H1 := Eq.symm (peq3); let pst1 : v0 = H1 := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : v0 = H1 := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : H1 = q_v1 := hb; let pst0 : q_v1 = H1 := Eq.symm (peq3); let pst1 : v0 = H1 := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
      | hit qs0h =>
        have qs1B := step_bound qs1
        have qs1N := step_no_first qs1
        cases qs1 with
        | raw =>
          have ena : v0 = H1 := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : H1 = q_v1 := hb; let pst0 : q_v1 = H1 := Eq.symm (peq3); let pst1 : v0 = H1 := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
        | hit qs1h =>
          have ena : v0 = H1 := (let peq1 : v0 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq3 : H1 = q_v1 := hb; let pst0 : q_v1 = H1 := Eq.symm (peq3); let pst1 : v0 = H1 := Eq.trans (peq1) (pst0); pst1)
          have enb : v1 = v1 := (rfl)
          apply s1N
          refine ⟨H0, ?_⟩
          simpa only [ena, enb] using s0h
theorem nr3 (x v0 v1 v2 H0 H1 : CM)
    (s0 : Step v0 v1 H0)
    (s1 : Step v1 x H1) :
    ¬ ∃ o, Code (p (p (p H0 v0) v2) H1) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have he : H1 = v1 := (let peq1 : v1 = q_v2 := congrArg (fun q => (R (L (L (L q))))) (ha); let peq4 : H1 = q_v1 := congrArg (fun q => (R q)) (ha); let peq5 : v1 = q_v1 := hb; let pst0 : q_v2 = v1 := Eq.symm (peq1); let pst1 : q_v2 = q_v1 := Eq.trans (pst0) (peq5); let pst2 : v1 = q_v1 := Eq.trans (peq1) (pst1); let pst3 : q_v1 = v1 := Eq.symm (pst2); let pst4 : H1 = v1 := Eq.trans (peq4) (pst3); pst4)
    exact step_ne_first (by simpa only [he] using s1)
  | hit s0h =>
    have he : H1 = v1 := (let peq3 : H1 = q_v1 := congrArg (fun q => (R q)) (ha); let peq4 : v1 = q_v1 := hb; let pst0 : q_v1 = v1 := Eq.symm (peq4); let pst1 : H1 = v1 := Eq.trans (peq3) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
theorem nr4 (x v0 v1 v2 H0 H1 : CM)
    (s0 : Step v0 v1 H0)
    (s1 : Step v1 x H1) :
    ¬ ∃ o, Code (p (p (p (p H0 v0) v2) H1) v1) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have he : H1 = v1 := (let peq1 : v1 = q_v0 := congrArg (fun q => (R (L (L (L (L q)))))) (ha); let peq4 : H1 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq5 : v1 = q_v1 := congrArg (fun q => (R q)) (ha); let pst0 : q_v0 = v1 := Eq.symm (peq1); let pst1 : q_v0 = q_v1 := Eq.trans (pst0) (peq5); let pst2 : v1 = q_v1 := Eq.trans (peq1) (pst1); let pst3 : q_v1 = v1 := Eq.symm (pst2); let pst4 : H1 = v1 := Eq.trans (peq4) (pst3); pst4)
    exact step_ne_first (by simpa only [he] using s1)
  | hit s0h =>
    have he : H1 = v1 := (let peq3 : H1 = q_v1 := congrArg (fun q => (R (L q))) (ha); let peq4 : v1 = q_v1 := congrArg (fun q => (R q)) (ha); let pst0 : q_v1 = v1 := Eq.symm (peq4); let pst1 : H1 = v1 := Eq.trans (peq3) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval (eval (eval (eval (eval (eval v0 v1) v0) v2) (eval v1 x)) v1) v1) v1) := by
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
  let H1 := eval v1 x
  have e1a : v1 = v1 := by
    change v1 = v1
    rfl
  have e1b : x = x := by
    change x = x
    rfl
  have s1 : Step v1 x H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v1 x
  change x = (eval (eval (eval (eval (eval (eval H0 v0) v2) H1) v1) v1) v1)
  have rawEq : (eval (eval (eval (eval (eval (eval H0 v0) v2) H1) v1) v1) v1) = (eval (p (p (p (p (p H0 v0) v2) H1) v1) v1) v1) := by
    calc
      (eval (eval (eval (eval (eval (eval H0 v0) v2) H1) v1) v1) v1) = (eval (eval (eval (eval (eval (p H0 v0) v2) H1) v1) v1) v1) := congrArg (fun q => (eval (eval (eval (eval (eval q v2) H1) v1) v1) v1)) (eval_raw (nr0 x v0 v1 v2 H0 s0))
      _ = (eval (eval (eval (eval (p (p H0 v0) v2) H1) v1) v1) v1) := congrArg (fun q => (eval (eval (eval (eval q H1) v1) v1) v1)) (eval_raw (nr1 x v0 v1 v2 H0 s0))
      _ = (eval (eval (eval (p (p (p H0 v0) v2) H1) v1) v1) v1) := congrArg (fun q => (eval (eval (eval q v1) v1) v1)) (eval_raw (nr2 x v0 v1 v2 H0 H1 s0 s1))
      _ = (eval (eval (p (p (p (p H0 v0) v2) H1) v1) v1) v1) := congrArg (fun q => (eval (eval q v1) v1)) (eval_raw (nr3 x v0 v1 v2 H0 H1 s0 s1))
      _ = (eval (p (p (p (p (p H0 v0) v2) H1) v1) v1) v1) := congrArg (fun q => (eval q v1)) (eval_raw (nr4 x v0 v1 v2 H0 H1 s0 s1))
  exact (eval_hit (Code.law x v0 v1 v2 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op a b := eval b a
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro q0 q1 q2 q3
    exact CM.source_holds q0 q3 q1 q2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
