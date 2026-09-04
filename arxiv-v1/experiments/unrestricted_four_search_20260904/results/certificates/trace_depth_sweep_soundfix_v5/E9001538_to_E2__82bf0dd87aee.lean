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
  | law (x v0 v1 H0 H1 H2 H3 : CM)
      (s0 : Step v0 x H0)
      (s1 : Step H0 v1 H1)
      (s2 : Step x H1 H2)
      (s3 : Step v0 (p H2 x) H3) :
      Code (p H3 v0) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 q_H2 q_H3 : CM, Step q_v0 q_x q_H0 ∧ Step q_H0 q_v1 q_H1 ∧ Step q_x q_H1 q_H2 ∧ Step q_v0 (p q_H2 q_x) q_H3 ∧ a = (p q_H3 q_v0) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 H2 H3 s0 s1 s2 s3 => ⟨x, v0, v1, H0, H1, H2, H3, s0, s1, s2, s3, rfl, rfl, rfl⟩
def getKey (c : CM) : CM := (R c)
theorem code_key {a b o : CM} (h : Code a b o) : getKey a = b := by
  cases h <;> rfl
theorem code_key_unique {a b q o : CM} (h : Code a b o) (k : Code a q o) : b = q :=
  (code_key h).symm.trans (code_key k)
theorem code_key_small {a b o : CM} (h : Code a b o) : sz b < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, q_H3, s0, s1, s2, s3, ha, hb, ho⟩
  subst a
  subst b
  exact sz_lt_p_right q_H3 q_v0
theorem code_bounds {a b o : CM} (h : Code a b o) :
    sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, q_H3, s0, s1, s2, s3, ha, hb, ho⟩
  subst a
  subst b
  subst o
  constructor
  · exact sz_lt_p_right q_H3 q_v0
  ·
    cases s3 with
    | raw =>
      exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_x) (sz_lt_p_right q_v0 (p q_H2 q_x))) (sz_lt_p_left (p q_v0 (p q_H2 q_x)) q_v0)
    | hit h3 =>
      exact Nat.lt_trans (Nat.lt_trans (sz_lt_p_right q_H2 q_x) (code_key_small h3)) (sz_lt_p_right q_H3 q_v0)
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
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, q_H3, hs0, hs1, hs2, hs3, ha, hb, ho⟩
  rcases code_shape k with ⟨r_q_x, r_q_v0, r_q_v1, r_q_H0, r_q_H1, r_q_H2, r_q_H3, rs0, rs1, rs2, rs3, ka, kb, ko⟩
  have et := congrArg (fun z => (L z)) (ha.symm.trans ka)
  have eo := congrArg (fun z => (R z)) (ha.symm.trans ka)
  change q_H3 = r_q_H3 at et
  change q_v0 = r_q_v0 at eo
  rw [eo.symm, et.symm] at rs3
  have er := step_second_unique hs3 rs3
  have ex : q_x = r_q_x := congrArg (fun z => (R z)) er
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, q_H2, q_H3, qs0, qs1, qs2, qs3, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
      | hit qs2h =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
      | hit qs2h =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
  | hit qs0h =>
    have qs1B := step_bound qs1
    cases qs1 with
    | raw =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
      | hit qs2h =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
    | hit qs1h =>
      have qs2B := step_bound qs2
      cases qs2 with
      | raw =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
      | hit qs2h =>
        have he : q_H3 = q_v0 := (let peq0 : v = q_H3 := congrArg (fun q => (L q)) (ha); let peq2 : v = q_v0 := hb; let pst0 : q_H3 = v := Eq.symm (peq0); let pst1 : q_H3 = q_v0 := Eq.trans (pst0) (peq2); pst1)
        exact step_ne_first (by simpa only [he] using qs3)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw => exact code_no_pair_left a b
  | hit sh =>
    rintro ⟨u, hk⟩
    have ho := (code_bounds sh).2
    have ha := (code_bounds hk).1
    omega
theorem nr0 (x v0 v1 H2 : CM)
    (s2 : Step x H1 H2) :
    ¬ ∃ o, Code H2 x o := by
  exact step_no_first s2

theorem nr1 (x v0 v1 H3 : CM)
    (s3 : Step v0 (p H2 x) H3) :
    ¬ ∃ o, Code H3 v0 o := by
  exact step_no_first s3

theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 (eval (eval x (eval (eval v0 x) v1)) x)) v0) v0) := by
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
  let H1 := eval (eval v0 x) v1
  have e1a : (eval v0 x) = H0 := by
    change H0 = H0
    rfl
  have e1b : v1 = v1 := by
    change v1 = v1
    rfl
  have s1 : Step H0 v1 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step (eval v0 x) v1
  let H2 := eval x (eval (eval v0 x) v1)
  have e2a : x = x := by
    change x = x
    rfl
  have e2b : (eval (eval v0 x) v1) = H1 := by
    change H1 = H1
    rfl
  have s2 : Step x H1 H2 := by
    rw [← e2a, ← e2b]
    exact eval_step x (eval (eval v0 x) v1)
  let H3 := eval v0 (eval (eval x (eval (eval v0 x) v1)) x)
  have e3a : v0 = v0 := by
    change v0 = v0
    rfl
  have e3b : (eval (eval x (eval (eval v0 x) v1)) x) = (p H2 x) := by
    change (eval H2 x) = (p H2 x)
    exact (eval_raw (nr0 x v0 v1 H2 s2))
  have s3 : Step v0 (p H2 x) H3 := by
    rw [← e3a, ← e3b]
    exact eval_step v0 (eval (eval x (eval (eval v0 x) v1)) x)
  change x = (eval (eval H3 v0) v0)
  have rawEq : (eval (eval H3 v0) v0) = (eval (p H3 v0) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr1 x v0 v1 H3 s3))
  exact (eval_hit (Code.law x v0 v1 H0 H1 H2 H3 s0 s1 s2 s3)).symm.trans rawEq.symm
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
