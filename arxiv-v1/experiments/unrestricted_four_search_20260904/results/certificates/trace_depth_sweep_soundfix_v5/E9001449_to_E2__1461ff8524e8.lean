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
      (s0 : Step x v0 H0)
      (s1 : Step v0 (p (p (p H0 x) (p x x)) v1) H1) :
      Code (p H1 v0) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_x q_v0 q_H0 ∧ Step q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) q_H1 ∧ a = (p q_H1 q_v0) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (R c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey a = b := by
  cases h <;> rfl
theorem code_key_unique {a b q o : CM} (h : Code a b o) (k : Code a q o) : b = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz b < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_right q_H1 q_v0
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_right q_H1 q_v0
  ·
    cases s1 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_x) (sz_lt_p_left (p q_H0 q_x) (p q_x q_x))) (sz_lt_p_left (p (p q_H0 q_x) (p q_x q_x)) q_v1)) (sz_lt_p_right q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1))) (sz_lt_p_left (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0)
    | hit h1 =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_x) (sz_lt_p_left (p q_H0 q_x) (p q_x q_x))) (sz_lt_p_left (p (p q_H0 q_x) (p q_x q_x)) q_v1)) (code_key_small h1)) (sz_lt_p_right q_H1 q_v0)
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
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, hs0, hs1, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_H0, r_q_H1, rs0, rs1, ka, kb, ko⟩
  have et := congrArg (fun z => (L z)) (ha.symm.trans ka)
  have eo := congrArg (fun z => (R z)) (ha.symm.trans ka)
  change q_H1 = r_q_H1 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs1
  have er := step_second_unique hs1 rs1
  have ex : q_x = r_q_x := congrArg (fun z => (R (L (L z)))) er
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have he : q_H1 = q_v0 := (let peq0 : v = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H1 = v := Eq.symm (peq0); let pst1 : q_H1 = q_v0 := Eq.trans (pst0) (peq2); pst1)
    exact step_ne_first (by simpa only [he] using qs1)
  | hit qs0h =>
    have he : q_H1 = q_v0 := (let peq0 : v = q_H1 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H1 = v := Eq.symm (peq0); let pst1 : q_H1 = q_v0 := Eq.trans (pst0) (peq2); pst1)
    exact step_ne_first (by simpa only [he] using qs1)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw => exact code_no_pair_left a b
  | hit sh =>
    rintro ⟨u, hk⟩
    have ho := (code_bounds sh).2
    have ha := (code_bounds hk).1
    omega
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step x v0 H0) :
    ¬ ∃ o, Code H0 x o := by
  exact step_no_first s0

theorem nr1 (x v0 v1 : CM)
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
      change x = (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) := (let peq0 : x = (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) (sz_lt_p_left (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_H1 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : x = (p q_H1 q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p q_H1 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) := (let peq0 : x = (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) = x := Eq.symm (peq0); let pst1 : (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0) := Nat.lt_trans (sz_lt_p_left q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) (sz_lt_p_left (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_H1 q_v0) at e0
      have e1 := congrArg (fun q => q) hb
      change x = q_v0 at e1
      have cyc : q_v0 = (p q_H1 q_v0) := (let peq0 : x = (p q_H1 q_v0) := e0; let peq1 : x = q_v0 := e1; let pst0 : (p q_H1 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_H1 q_v0) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_H1 q_v0) := Eq.symm (pst1); pst2)
      have hlt : sz q_v0 < sz (p q_H1 q_v0) := sz_lt_p_right q_H1 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step x v0 H0) :
    ¬ ∃ o, Code (p H0 x) (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
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
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e3
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = q_v0 := e0; let peq3 : (p x x) = q_v0 := e3; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq0); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq0); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq3); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change (p x v0) = q_H1 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq1); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq1); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change x = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e3
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = q_v0 := e0; let peq3 : (p x x) = q_v0 := e3; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq0); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq0); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq3); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change (p x v0) = q_H1 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq1); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq1); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change H0 = (p q_v0 (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq1); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq1); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change H0 = q_H1 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq1); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq1); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change H0 = (p q_v0 (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq1); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq1); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change H0 = q_H1 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change x = q_v0 at e1
        have e2 := congrArg (fun q => q) hb
        change (p x x) = q_v0 at e2
        have cyc : q_v0 = (p q_v0 q_v0) := (let peq1 : x = q_v0 := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq1); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq1); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p q_v0 q_v0) = (p x x) := Eq.symm (pst2); let pst4 : (p q_v0 q_v0) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p q_v0 q_v0) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step x v0 H0) :
    ¬ ∃ o, Code (p (p H0 x) (p x x)) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
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
        change (p x v0) = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change x = (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change (p x x) = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change v1 = q_v0 at e3
        have cyc : x = (p (p (p (p q_x (p x v0)) q_x) (p q_x q_x)) q_v1) := (let peq0 : (p x v0) = q_v0 := e0; let peq1 : x = (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) := e1; let pst0 : q_v0 = (p x v0) := Eq.symm (peq0); let pst1 : (p q_x q_v0) = (p q_x (p x v0)) := congrArg (fun q => p q_x q) (pst0); let pst2 : (p (p q_x q_v0) q_x) = (p (p q_x (p x v0)) q_x) := congrArg (fun q => p q q_x) (pst1); let pst3 : (p (p (p q_x q_v0) q_x) (p q_x q_x)) = (p (p (p q_x (p x v0)) q_x) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst2); let pst4 : (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) = (p (p (p (p q_x (p x v0)) q_x) (p q_x q_x)) q_v1) := congrArg (fun q => p q q_v1) (pst3); let pst5 : x = (p (p (p (p q_x (p x v0)) q_x) (p q_x q_x)) q_v1) := Eq.trans (peq1) (pst4); pst5)
        have hlt : sz x < sz (p (p (p (p q_x (p x v0)) q_x) (p q_x q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x v0) (sz_lt_p_right q_x (p x v0))) (sz_lt_p_left (p q_x (p x v0)) q_x)) (sz_lt_p_left (p (p q_x (p x v0)) q_x) (p q_x q_x))) (sz_lt_p_left (p (p (p q_x (p x v0)) q_x) (p q_x q_x)) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p (p x v0) x) = q_H1 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v1 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz q_v0 < sz (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) := by
          have structural : sz (p x x) < sz (p (p (p (p q_x (p x x)) q_x) (p q_x q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x (p x x)) (sz_lt_p_left (p q_x (p x x)) q_x)) (sz_lt_p_left (p (p q_x (p x x)) q_x) (p q_x q_x))) (sz_lt_p_left (p (p (p q_x (p x x)) q_x) (p q_x q_x)) q_v1)
          have large_eq : sz q_v0 = sz (p x x) := congrArg sz (p1.symm)
          have small_eq : sz (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) = sz (p (p (p (p q_x (p x x)) q_x) (p q_x q_x)) q_v1) := congrArg sz (congrArg (fun q => p q q_v1) (congrArg (fun q => p q (p q_x q_x)) (congrArg (fun q => p q q_x) (congrArg (fun q => p q_x q) (p1.symm)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.1).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change (p x v0) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change x = (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change (p x x) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v1 = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz q_x < sz q_v0 := by
          have structural : sz q_x < sz (p (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H0 q_x) (sz_lt_p_left (p q_H0 q_x) (p q_x q_x))) (sz_lt_p_left (p (p q_H0 q_x) (p q_x q_x)) q_v1)) (sz_lt_p_left (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) v0)
          have large_eq : sz q_x = sz q_x := congrArg sz (rfl)
          have small_eq : sz q_v0 = sz (p (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) v0) := congrArg sz (Eq.trans (p0.symm) (congrArg (fun q => p q v0) (p1)))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs0hB.1).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p (p x v0) x) = q_H1 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v1 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3
        omega
  | hit s0h =>
    have qs0B := step_bound qs0
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change H0 = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change x = (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) at e1
        have e2 := congrArg (fun q => (R q)) ha
        change (p x x) = q_v0 at e2
        have e3 := congrArg (fun q => q) hb
        change v1 = q_v0 at e3
        have cyc : q_v0 = (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) := (let peq1 : x = (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) := e1; let peq2 : (p x x) = q_v0 := e2; let pst0 : (p x x) = (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) x) := congrArg (fun q => p q x) (peq1); let pst1 : (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) x) = (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) := congrArg (fun q => p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) q) (peq1); let pst2 : (p x x) = (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) := Eq.trans (pst0) (pst1); let pst3 : (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) = (p x x) := Eq.symm (pst2); let pst4 : (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) = q_v0 := Eq.trans (pst3) (peq2); let pst5 : q_v0 = (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) := Eq.symm (pst4); pst5)
        have hlt : sz q_v0 < sz (p (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x q_v0) (sz_lt_p_left (p q_x q_v0) q_x)) (sz_lt_p_left (p (p q_x q_v0) q_x) (p q_x q_x))) (sz_lt_p_left (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1)) (sz_lt_p_left (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p H0 x) = q_H1 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v1 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        have badlt : sz q_v0 < sz (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) := by
          have structural : sz (p x x) < sz (p (p (p (p q_x (p x x)) q_x) (p q_x q_x)) q_v1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_x (p x x)) (sz_lt_p_left (p q_x (p x x)) q_x)) (sz_lt_p_left (p (p q_x (p x x)) q_x) (p q_x q_x))) (sz_lt_p_left (p (p (p q_x (p x x)) q_x) (p q_x q_x)) q_v1)
          have large_eq : sz q_v0 = sz (p x x) := congrArg sz (p1.symm)
          have small_eq : sz (p (p (p (p q_x q_v0) q_x) (p q_x q_x)) q_v1) = sz (p (p (p (p q_x (p x x)) q_x) (p q_x q_x)) q_v1) := congrArg sz (congrArg (fun q => p q q_v1) (congrArg (fun q => p q (p q_x q_x)) (congrArg (fun q => p q q_x) (congrArg (fun q => p q_x q) (p1.symm)))))
          exact lt_of_lt_of_eq (lt_of_eq_of_lt large_eq structural) small_eq.symm
        exact (Nat.not_lt_of_ge (Nat.le_of_lt badlt) qs1hB.1).elim
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
        have p0 := congrArg (fun q => (L (L q))) (ha)
        change H0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R (L q))) (ha)
        change x = (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (ha)
        change (p x x) = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v1 = q_v0 at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        have badlt : sz x < sz H0 := by
          have structural : sz (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) < sz (p (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) := sz_lt_p_left (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)
          have large_eq : sz x = sz (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) := congrArg sz (p1)
          have small_eq : sz H0 = sz (p (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) (p (p (p q_H0 q_x) (p q_x q_x)) q_v1)) := congrArg sz (Eq.trans (p0) (Eq.trans (p2.symm) (Eq.trans (congrArg (fun q => p q x) (p1)) (congrArg (fun q => p (p (p (p q_H0 q_x) (p q_x q_x)) q_v1) q) (p1)))))
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
        change (p H0 x) = q_H1 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v1 = q_v0 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [L, R, U, sz] at hcB s0hB qs0hB qs1hB z0 z1 z2 z3
        omega
theorem nr4 (x v0 v1 H1 : CM)
    (s1 : Step v0 (p (p (p H0 x) (p x x)) v1) H1) :
    ¬ ∃ o, Code H1 v0 o := by
  exact step_no_first s1

theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 (eval (eval (eval (eval x v0) x) (eval x x)) v1)) v0) v0) := by
  let H0 := eval x v0
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v0 = v0 := by
    change v0 = v0
    rfl
  have s0 : Step x v0 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v0
  let H1 := eval v0 (eval (eval (eval (eval x v0) x) (eval x x)) v1)
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : (eval (eval (eval (eval x v0) x) (eval x x)) v1) = (p (p (p H0 x) (p x x)) v1) := by
    change (eval (eval (eval H0 x) (eval x x)) v1) = (p (p (p H0 x) (p x x)) v1)
    calc
      (eval (eval (eval H0 x) (eval x x)) v1) = (eval (eval (p H0 x) (eval x x)) v1) := congrArg (fun q => (eval (eval q (eval x x)) v1)) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval (eval (p H0 x) (p x x)) v1) := congrArg (fun q => (eval (eval (p H0 x) q) v1)) (eval_raw (nr1 x v0 v1))
      _ = (eval (p (p H0 x) (p x x)) v1) := congrArg (fun q => (eval q v1)) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (p (p (p H0 x) (p x x)) v1) := (eval_raw (nr3 x v0 v1 H0 s0))
  have s1 : Step v0 (p (p (p H0 x) (p x x)) v1) H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 (eval (eval (eval (eval x v0) x) (eval x x)) v1)
  change x = (eval (eval H1 v0) v0)
  have rawEq : (eval (eval H1 v0) v0) = (eval (p H1 v0) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr4 x v0 v1 H1 s1))
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
