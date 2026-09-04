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
      (s1 : Step (p H0 (p (p x x) x)) v0 H1) :
      Code v0 (p v0 H1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v1 q_v0 q_H0 ∧ Step (p q_H0 (p (p q_x q_x) q_x)) q_v0 q_H1 ∧ a = q_v0 ∧ b = (p q_v0 q_H1) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (L c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey b = a := by
  cases h <;> rfl
theorem code_key_unique {a q b o : CM} (h : Code a b o) (k : Code q b o) : a = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz a < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_left q_v0 q_H1
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_left q_v0 q_H1
  ·
    cases s1 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_x)) (sz_lt_p_right q_H0 (p (p q_x q_x) q_x))) (sz_lt_p_left (p q_H0 (p (p q_x q_x) q_x)) q_v0)) (sz_lt_p_right q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0))
    | hit h1 =>
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_x)) (sz_lt_p_right q_H0 (p (p q_x q_x) q_x))) (code_key_small h1)) (sz_lt_p_left q_v0 q_H1)
theorem step_first_unique {a q b o : CM} (h : Step a b o) (k : Step q b o) : a = q := by
  cases h with
  | raw =>
    cases k with
    | raw => rfl
    | hit hc =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right a b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
  | hit hc =>
    cases k with
    | raw =>
      have hb := code_bounds hc
      have hp := sz_lt_p_right q b
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hp) hb.2).elim
    | hit hk => exact code_key_unique hc hk
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, hs0, hs1, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_H0, r_q_H1, rs0, rs1, ka, kb, ko⟩
  have et := congrArg (fun z => (R z)) (hb.symm.trans kb)
  have eo := congrArg (fun z => (L z)) (hb.symm.trans kb)
  change q_H1 = r_q_H1 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs1
  have er := step_first_unique hs1 rs1
  have ex : q_x = r_q_x := congrArg (fun z => (L (L (R z)))) er
  exact ho.trans (ex.trans ko.symm)
theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz a < sz (p o b) := by
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
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) at e1
      have cyc : v = (p (p v k) (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) = (p (p v k) (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) := congrArg (fun q => p q (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) (pst0); let pst2 : (p q_v1 q_v0) = (p q_v1 (p v k)) := congrArg (fun q => p q_v1 q) (pst0); let pst3 : (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) = (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) := congrArg (fun q => p q (p (p q_x q_x) q_x)) (pst2); let pst4 : (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k)) := congrArg (fun q => p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) q) (pst0); let pst6 : (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k)) := Eq.trans (pst4) (pst5); let pst7 : (p (p v k) (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) = (p (p v k) (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst6); let pst8 : (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) = (p (p v k) (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k))) := Eq.trans (pst1) (pst7); let pst9 : v = (p (p v k) (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k))) := Eq.trans (peq1) (pst8); pst9)
      have hlt : sz v < sz (p (p v k) (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p (p q_v1 (p v k)) (p (p q_x q_x) q_x)) (p v k)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 q_H1) at e1
      have cyc : v = (p (p v k) q_H1) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H1) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = (p (p v k) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst2 : v = (p (p v k) q_H1) := Eq.trans (peq1) (pst1); pst2)
      have hlt : sz v < sz (p (p v k) q_H1) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) at e1
      have cyc : v = (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) (p v k))) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) = (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) := congrArg (fun q => p q (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) (pst0); let pst2 : (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) = (p (p q_H0 (p (p q_x q_x) q_x)) (p v k)) := congrArg (fun q => p (p q_H0 (p (p q_x q_x) q_x)) q) (pst0); let pst3 : (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) = (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) (p v k))) := congrArg (fun q => p (p v k) q) (pst2); let pst4 : (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) = (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) (p v k))) := Eq.trans (pst1) (pst3); let pst5 : v = (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) (p v k))) := Eq.trans (peq1) (pst4); pst5)
      have hlt : sz v < sz (p (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) (p v k))) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) (p (p q_H0 (p (p q_x q_x) q_x)) (p v k)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change (p v k) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v = (p q_v0 q_H1) at e1
      have cyc : v = (p (p v k) q_H1) := (let peq0 : (p v k) = q_v0 := e0; let peq1 : v = (p q_v0 q_H1) := e1; let pst0 : q_v0 = (p v k) := Eq.symm (peq0); let pst1 : (p q_v0 q_H1) = (p (p v k) q_H1) := congrArg (fun q => p q q_H1) (pst0); let pst2 : v = (p (p v k) q_H1) := Eq.trans (peq1) (pst1); pst2)
      have hlt : sz v < sz (p (p v k) q_H1) := Nat.lt_trans (sz_lt_p_left v k) (sz_lt_p_left (p v k) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) at e1
      have cyc : q_v0 = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) := sz_lt_p_left q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 q_H1) at e1
      have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 q_H1) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_H1) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) at e1
      have cyc : q_v0 = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) := sz_lt_p_left q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p q_v0 q_H1) at e1
      have cyc : q_v0 = (p q_v0 q_H1) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p q_v0 q_H1) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_H1) := Eq.trans (pst0) (peq1); pst1)
      have hlt : sz q_v0 < sz (p q_v0 q_H1) := sz_lt_p_left q_v0 q_H1
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p x x) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      apply code_no_pair_left x x
      exact ⟨_, hc⟩
    | hit qs1h =>
      apply code_no_pair_left x x
      exact ⟨_, hc⟩
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      apply code_no_pair_left x x
      exact ⟨_, hc⟩
    | hit qs1h =>
      apply code_no_pair_left x x
      exact ⟨_, hc⟩
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step v1 v0 H0) :
    ¬ ∃ o, Code H0 (p (p x x) x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v1 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) at e2
        have cyc : v0 = (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) (p v0 v0)) := (let peq0 : (p v1 v0) = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq2 : x = (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) := e2; let pst0 : q_v0 = (p v1 v0) := Eq.symm (peq0); let pst1 : (p x x) = (p v1 v0) := Eq.trans (peq1) (pst0); let pst2 : x = v1 := congrArg (fun q => L q) (pst1); let pst3 : v1 = x := Eq.symm (pst2); let pst4 : x = v0 := congrArg (fun q => R q) (pst1); let pst5 : v1 = v0 := Eq.trans (pst3) (pst4); let pst6 : x = v0 := Eq.trans (pst2) (pst5); let pst7 : v0 = x := Eq.symm (pst6); let pst8 : v0 = (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) := Eq.trans (pst7) (peq2); let pst9 : (p v1 v0) = (p v0 v0) := congrArg (fun q => p q v0) (pst5); let pst10 : q_v0 = (p v0 v0) := Eq.trans (pst0) (pst9); let pst11 : (p q_v1 q_v0) = (p q_v1 (p v0 v0)) := congrArg (fun q => p q_v1 q) (pst10); let pst12 : (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) = (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) := congrArg (fun q => p q (p (p q_x q_x) q_x)) (pst11); let pst13 : (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst12); let pst14 : (p v1 v0) = (p v0 v0) := congrArg (fun q => p q v0) (pst5); let pst15 : q_v0 = (p v0 v0) := Eq.trans (pst0) (pst14); let pst16 : (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) (p v0 v0)) := congrArg (fun q => p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) q) (pst15); let pst17 : (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) (p v0 v0)) := Eq.trans (pst13) (pst16); let pst18 : v0 = (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) (p v0 v0)) := Eq.trans (pst8) (pst17); pst18)
        have hlt : sz v0 < sz (p (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) (p v0 v0)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_right q_v1 (p v0 v0))) (sz_lt_p_left (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x))) (sz_lt_p_left (p (p q_v1 (p v0 v0)) (p (p q_x q_x) q_x)) (p v0 v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change (p v1 v0) = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change x = q_H1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [L, R, U, sz] at hcB qs1hB s0B qs0B qs1B z0 z1 z2 z3
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change (p v1 v0) = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) at e2
        have cyc : v0 = (p (p q_H0 (p (p q_x q_x) q_x)) (p v0 v0)) := (let peq0 : (p v1 v0) = q_v0 := e0; let peq1 : (p x x) = q_v0 := e1; let peq2 : x = (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) := e2; let pst0 : q_v0 = (p v1 v0) := Eq.symm (peq0); let pst1 : (p x x) = (p v1 v0) := Eq.trans (peq1) (pst0); let pst2 : x = v1 := congrArg (fun q => L q) (pst1); let pst3 : v1 = x := Eq.symm (pst2); let pst4 : x = v0 := congrArg (fun q => R q) (pst1); let pst5 : v1 = v0 := Eq.trans (pst3) (pst4); let pst6 : x = v0 := Eq.trans (pst2) (pst5); let pst7 : v0 = x := Eq.symm (pst6); let pst8 : v0 = (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) := Eq.trans (pst7) (peq2); let pst9 : (p v1 v0) = (p v0 v0) := congrArg (fun q => p q v0) (pst5); let pst10 : q_v0 = (p v0 v0) := Eq.trans (pst0) (pst9); let pst11 : (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) = (p (p q_H0 (p (p q_x q_x) q_x)) (p v0 v0)) := congrArg (fun q => p (p q_H0 (p (p q_x q_x) q_x)) q) (pst10); let pst12 : v0 = (p (p q_H0 (p (p q_x q_x) q_x)) (p v0 v0)) := Eq.trans (pst8) (pst11); pst12)
        have hlt : sz v0 < sz (p (p q_H0 (p (p q_x q_x) q_x)) (p v0 v0)) := Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_right (p q_H0 (p (p q_x q_x) q_x)) (p v0 v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have he : u0_H1 = u0_v0 := (let peq0 : (p v1 v0) = q_v0 := ha; let peq1 : (p x x) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : x = q_H1 := congrArg (fun q => (R q)) (hb); let peq5 : q_v0 = (p u0_v0 u0_H1) := u0b; let pst0 : q_v0 = (p v1 v0) := Eq.symm (peq0); let pst1 : (p x x) = (p v1 v0) := Eq.trans (peq1) (pst0); let pst2 : x = v1 := congrArg (fun q => L q) (pst1); let pst3 : v1 = x := Eq.symm (pst2); let pst4 : x = v0 := congrArg (fun q => R q) (pst1); let pst5 : v1 = v0 := Eq.trans (pst3) (pst4); let pst6 : x = v0 := Eq.trans (pst2) (pst5); let pst7 : v0 = x := Eq.symm (pst6); let pst8 : v0 = q_H1 := Eq.trans (pst7) (peq2); let pst9 : v1 = q_H1 := Eq.trans (pst5) (pst8); let pst10 : (p v1 v0) = (p q_H1 v0) := congrArg (fun q => p q v0) (pst9); let pst11 : (p q_H1 v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst8); let pst12 : (p v1 v0) = (p q_H1 q_H1) := Eq.trans (pst10) (pst11); let pst13 : q_v0 = (p q_H1 q_H1) := Eq.trans (pst0) (pst12); let pst14 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst13); let pst15 : (p q_H1 q_H1) = (p u0_v0 u0_H1) := Eq.trans (pst14) (peq5); let pst16 : q_H1 = u0_v0 := congrArg (fun q => L q) (pst15); let pst17 : u0_v0 = q_H1 := Eq.symm (pst16); let pst18 : q_H1 = u0_H1 := congrArg (fun q => R q) (pst15); let pst19 : u0_v0 = u0_H1 := Eq.trans (pst17) (pst18); let pst20 : u0_H1 = u0_v0 := Eq.symm (pst19); pst20)
        exact step_ne_second (by simpa only [he] using u0s1)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) at e2
        have cyc : x = (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) (p x x)) := (let peq1 : (p x x) = q_v0 := e1; let peq2 : x = (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : (p q_v1 q_v0) = (p q_v1 (p x x)) := congrArg (fun q => p q_v1 q) (pst0); let pst2 : (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) = (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) := congrArg (fun q => p q (p (p q_x q_x) q_x)) (pst1); let pst3 : (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) (p x x)) := congrArg (fun q => p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) q) (pst0); let pst5 : (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0) = (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) (p x x)) := Eq.trans (pst3) (pst4); let pst6 : x = (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) (p x x)) := Eq.trans (peq2) (pst5); pst6)
        have hlt : sz x < sz (p (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) (p x x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_right q_v1 (p x x))) (sz_lt_p_left (p q_v1 (p x x)) (p (p q_x q_x) q_x))) (sz_lt_p_left (p (p q_v1 (p x x)) (p (p q_x q_x) q_x)) (p x x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s0hB := code_bounds s0h
        have qs1hB := code_bounds qs1h
        have s0B := s0B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change (p x x) = q_v0 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change x = q_H1 at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [L, R, U, sz] at hcB s0hB qs1hB s0B qs0B qs1B z0 z1 z2 z3
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H0 = q_v0 at e0
        have e1 := congrArg (fun q => (L q)) hb
        change (p x x) = q_v0 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) at e2
        have cyc : x = (p (p q_H0 (p (p q_x q_x) q_x)) (p x x)) := (let peq1 : (p x x) = q_v0 := e1; let peq2 : x = (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) := e2; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : (p (p q_H0 (p (p q_x q_x) q_x)) q_v0) = (p (p q_H0 (p (p q_x q_x) q_x)) (p x x)) := congrArg (fun q => p (p q_H0 (p (p q_x q_x) q_x)) q) (pst0); let pst2 : x = (p (p q_H0 (p (p q_x q_x) q_x)) (p x x)) := Eq.trans (peq2) (pst1); pst2)
        have hlt : sz x < sz (p (p q_H0 (p (p q_x q_x) q_x)) (p x x)) := Nat.lt_trans (sz_lt_p_left x x) (sz_lt_p_right (p q_H0 (p (p q_x q_x) q_x)) (p x x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0B := step_bound u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1B := step_bound u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq1 : (p x x) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : x = q_H1 := congrArg (fun q => (R q)) (hb); let peq11 : q_v0 = (p u1_v0 u1_H1) := u1b; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : (p x x) = (p q_H1 x) := congrArg (fun q => p q x) (peq2); let pst2 : (p q_H1 x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst3 : (p x x) = (p q_H1 q_H1) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H1 q_H1) := Eq.trans (pst0) (pst3); let pst5 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = (p u1_v0 u1_H1) := Eq.trans (pst5) (peq11); let pst7 : q_H1 = u1_v0 := congrArg (fun q => L q) (pst6); let pst8 : u1_v0 = q_H1 := Eq.symm (pst7); let pst9 : q_H1 = u1_H1 := congrArg (fun q => R q) (pst6); let pst10 : u1_v0 = u1_H1 := Eq.trans (pst8) (pst9); let pst11 : u1_H1 = u1_v0 := Eq.symm (pst10); pst11)
            exact step_ne_second (by simpa only [he] using u1s1)
          | hit u0s1h =>
            have hcB := code_bounds hc
            have s0hB := code_bounds s0h
            have qs0hB := code_bounds qs0h
            have qs1hB := code_bounds qs1h
            have u0s1hB := code_bounds u0s1h
            have s0B := s0B
            have qs0B := qs0B
            have qs1B := qs1B
            have u0s0B := u0s0B
            have u0s1B := u0s1B
            have p0 := ha
            change H0 = q_v0 at p0
            have z0 := congrArg sz p0
            have p1 := congrArg (fun q => (L q)) (hb)
            change (p x x) = q_v0 at p1
            have z1 := congrArg sz p1
            have p2 := congrArg (fun q => (R q)) (hb)
            change x = q_H1 at p2
            have z2 := congrArg sz p2
            have p3 := ho
            change o = q_x at p3
            have z3 := congrArg sz p3
            have p4 := u0a
            change v1 = u0_v0 at p4
            have z4 := congrArg sz p4
            have p5 := u0b
            change v0 = (p u0_v0 u0s1out) at p5
            have z5 := congrArg sz p5
            have p6 := u0o
            change H0 = u0_x at p6
            have z6 := congrArg sz p6
            simp only [L, R, U, sz] at hcB s0hB qs0hB qs1hB u0s1hB s0B qs0B qs1B u0s0B u0s1B z0 z1 z2 z3 z4 z5 z6
            omega
        | hit u0s0h =>
          have u0s1B := step_bound u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq1 : (p x x) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : x = q_H1 := congrArg (fun q => (R q)) (hb); let peq11 : q_v0 = (p u1_v0 u1_H1) := u1b; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : (p x x) = (p q_H1 x) := congrArg (fun q => p q x) (peq2); let pst2 : (p q_H1 x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst3 : (p x x) = (p q_H1 q_H1) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H1 q_H1) := Eq.trans (pst0) (pst3); let pst5 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = (p u1_v0 u1_H1) := Eq.trans (pst5) (peq11); let pst7 : q_H1 = u1_v0 := congrArg (fun q => L q) (pst6); let pst8 : u1_v0 = q_H1 := Eq.symm (pst7); let pst9 : q_H1 = u1_H1 := congrArg (fun q => R q) (pst6); let pst10 : u1_v0 = u1_H1 := Eq.trans (pst8) (pst9); let pst11 : u1_H1 = u1_v0 := Eq.symm (pst10); pst11)
            exact step_ne_second (by simpa only [he] using u1s1)
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have he : u1_H1 = u1_v0 := (let peq1 : (p x x) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : x = q_H1 := congrArg (fun q => (R q)) (hb); let peq11 : q_v0 = (p u1_v0 u1_H1) := u1b; let pst0 : q_v0 = (p x x) := Eq.symm (peq1); let pst1 : (p x x) = (p q_H1 x) := congrArg (fun q => p q x) (peq2); let pst2 : (p q_H1 x) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (peq2); let pst3 : (p x x) = (p q_H1 q_H1) := Eq.trans (pst1) (pst2); let pst4 : q_v0 = (p q_H1 q_H1) := Eq.trans (pst0) (pst3); let pst5 : (p q_H1 q_H1) = q_v0 := Eq.symm (pst4); let pst6 : (p q_H1 q_H1) = (p u1_v0 u1_H1) := Eq.trans (pst5) (peq11); let pst7 : q_H1 = u1_v0 := congrArg (fun q => L q) (pst6); let pst8 : u1_v0 = q_H1 := Eq.symm (pst7); let pst9 : q_H1 = u1_H1 := congrArg (fun q => R q) (pst6); let pst10 : u1_v0 = u1_H1 := Eq.trans (pst8) (pst9); let pst11 : u1_H1 = u1_v0 := Eq.symm (pst10); pst11)
            exact step_ne_second (by simpa only [he] using u1s1)
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step (p H0 (p (p x x) x)) v0 H1) :
    ¬ ∃ o, Code v0 H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p H0 (p (p x x) x)) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p H0 (p (p x x) x)) := Eq.symm (peq1); let pst1 : v0 = (p H0 (p (p x x) x)) := Eq.trans (peq0) (pst0); let pst2 : (p H0 (p (p x x) x)) = v0 := Eq.symm (pst1); let pst3 : (p H0 (p (p x x) x)) = q_H1 := Eq.trans (pst2) (peq2); let pst4 : q_H1 = (p H0 (p (p x x) x)) := Eq.symm (pst3); let pst5 : (p H0 (p (p x x) x)) = q_v0 := Eq.symm (pst0); let pst6 : q_H1 = q_v0 := Eq.trans (pst4) (pst5); pst6)
      exact step_ne_second (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_v0 := (let peq0 : v0 = q_v0 := ha; let peq1 : (p H0 (p (p x x) x)) = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : v0 = q_H1 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = (p H0 (p (p x x) x)) := Eq.symm (peq1); let pst1 : v0 = (p H0 (p (p x x) x)) := Eq.trans (peq0) (pst0); let pst2 : (p H0 (p (p x x) x)) = v0 := Eq.symm (pst1); let pst3 : (p H0 (p (p x x) x)) = q_H1 := Eq.trans (pst2) (peq2); let pst4 : q_H1 = (p H0 (p (p x x) x)) := Eq.symm (pst3); let pst5 : (p H0 (p (p x x) x)) = q_v0 := Eq.symm (pst0); let pst6 : q_H1 = q_v0 := Eq.trans (pst4) (pst5); pst6)
      exact step_ne_second (by simpa only [he] using qs1)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 (p (p (p q_v1 q_v0) (p (p q_x q_x) q_x)) q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s1hB s1B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s1hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 (p (p q_H0 (p (p q_x q_x) q_x)) q_v0)) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s1hB qs0hB s1B qs0B qs1B z0 z1 z2
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change v0 = q_v0 at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change H1 = (p q_v0 q_H1) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        simp only [L, R, U, sz] at hcB s1hB qs0hB qs1hB s1B qs0B qs1B z0 z1 z2
        omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval (eval v1 v0) (eval (eval x x) x)) v0))) := by
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
  let H1 := eval (eval (eval v1 v0) (eval (eval x x) x)) v0
  have e1a : (eval (eval v1 v0) (eval (eval x x) x)) = (p H0 (p (p x x) x)) := by
    change (eval H0 (eval (eval x x) x)) = (p H0 (p (p x x) x))
    calc
      (eval H0 (eval (eval x x) x)) = (eval H0 (eval (p x x) x)) := congrArg (fun q => (eval H0 (eval q x))) (eval_raw (nr0 x v0 v1))
      _ = (eval H0 (p (p x x) x)) := congrArg (fun q => (eval H0 q)) (eval_raw (nr1 x v0 v1))
      _ = (p H0 (p (p x x) x)) := (eval_raw (nr2 x v0 v1 H0 s0))
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step (p H0 (p (p x x) x)) v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval (eval v1 v0) (eval (eval x x) x)) v0
  change x = (eval v0 (eval v0 H1))
  have rawEq : (eval v0 (eval v0 H1)) = (eval v0 (p v0 H1)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H1 s1))
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
