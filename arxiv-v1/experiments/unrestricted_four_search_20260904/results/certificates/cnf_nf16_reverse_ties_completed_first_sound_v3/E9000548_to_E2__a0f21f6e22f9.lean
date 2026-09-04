import JudgeProblem
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace submission
inductive CM where | e : CM | k : CM → CM | p : CM → CM → CM
namespace CM
def L : CM → CM | .p a _ => a | _ => .e
def R : CM → CM | .p _ b => b | _ => .e
def U : CM → CM | .k a => a | _ => .e
def sz : CM → Nat | .e => 0 | .k a => sz a + 1 | .p a b => sz a + sz b + 2
inductive Code : CM → CM → CM → Prop
  | r0 (v0 v1 : CM) : Code (p (p (p e v0) v1) v1) (p v0 e) v1
  | r1 (v0 : CM) : Code v0 v0 e
  | r2 (v0 : CM) : Code (p (p e v0) v0) e v0
  | r3 (v0 : CM) : Code (p e (p e v0)) (p v0 e) (p e v0)
  | r4 (v0 : CM) : Code (p e (p e (p (p e v0) v0))) v0 (p e (p (p e v0) v0))
  | r5 (v0 : CM) : Code (p (p e v0) (p v0 e)) (p (p e v0) e) (p v0 e)
  | r6 (v0 v1 : CM) : Code (p (p (p e (p (p e v0) v0)) v1) v1) v0 v1
  | r7 (v0 : CM) : Code (p (p e (p (p e v0) v0)) v0) (p (p e (p (p e v0) v0)) e) v0
def CodeCases (a b o : CM) : Prop := (∃ v0 v1 : CM, a = (p (p (p e v0) v1) v1) ∧ b = (p v0 e) ∧ o = v1 ∧ sz a = sz (p (p (p e v0) v1) v1) ∧ sz b = sz (p v0 e) ∧ sz o = sz v1) ∨ (∃ v0 : CM, a = v0 ∧ b = v0 ∧ o = e ∧ sz a = sz v0 ∧ sz b = sz v0 ∧ sz o = sz e) ∨ (∃ v0 : CM, a = (p (p e v0) v0) ∧ b = e ∧ o = v0 ∧ sz a = sz (p (p e v0) v0) ∧ sz b = sz e ∧ sz o = sz v0) ∨ (∃ v0 : CM, a = (p e (p e v0)) ∧ b = (p v0 e) ∧ o = (p e v0) ∧ sz a = sz (p e (p e v0)) ∧ sz b = sz (p v0 e) ∧ sz o = sz (p e v0)) ∨ (∃ v0 : CM, a = (p e (p e (p (p e v0) v0))) ∧ b = v0 ∧ o = (p e (p (p e v0) v0)) ∧ sz a = sz (p e (p e (p (p e v0) v0))) ∧ sz b = sz v0 ∧ sz o = sz (p e (p (p e v0) v0))) ∨ (∃ v0 : CM, a = (p (p e v0) (p v0 e)) ∧ b = (p (p e v0) e) ∧ o = (p v0 e) ∧ sz a = sz (p (p e v0) (p v0 e)) ∧ sz b = sz (p (p e v0) e) ∧ sz o = sz (p v0 e)) ∨ (∃ v0 v1 : CM, a = (p (p (p e (p (p e v0) v0)) v1) v1) ∧ b = v0 ∧ o = v1 ∧ sz a = sz (p (p (p e (p (p e v0) v0)) v1) v1) ∧ sz b = sz v0 ∧ sz o = sz v1) ∨ (∃ v0 : CM, a = (p (p e (p (p e v0) v0)) v0) ∧ b = (p (p e (p (p e v0) v0)) e) ∧ o = v0 ∧ sz a = sz (p (p e (p (p e v0) v0)) v0) ∧ sz b = sz (p (p e (p (p e v0) v0)) e) ∧ sz o = sz v0) ∨ False
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  cases h with
  | r0 => exact Or.inl ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | r2 => exact Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  | r3 => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩)))
  | r4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩))))
  | r5 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩)))))
  | r6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩))))))
  | r7 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩)))))))
def NF : CM → Prop
  | .e => True
  | .k a => NF a
  | .p a b => NF a ∧ NF b ∧ ¬ ∃ o, Code a b o
@[grind →] theorem nf_p_left {a b : CM} (h : NF (p a b)) : NF a := h.1
@[grind →] theorem nf_p_right {a b : CM} (h : NF (p a b)) : NF b := h.2.1
@[grind →] theorem nf_p_no {a b : CM} (h : NF (p a b)) : ¬ ∃ o, Code a b o := h.2.2
theorem eq_sz {a b : CM} (h : a = b) : sz a = sz b := congrArg sz h
theorem ne_p_left (a b : CM) : a ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q <;> omega
theorem ne_p_right (a b : CM) : b ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q <;> omega
theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact ha.1.2.1
  | r1 => exact by trivial
  | r2 => exact ha.1.2.1
  | r3 => exact ha.2.1
  | r4 => exact ha.2.1
  | r5 => exact ha.2.1
  | r6 => exact ha.1.2.1
  | r7 => exact ha.1.2.1.1.2.1
theorem redex0_not_nf (v0 v1 : CM) :
    ¬ NF (p (p (p (p e v0) v1) v1) (p v0 e)) := by
  intro h
  exact h.2.2 ⟨v1, Code.r0 v0 v1⟩
theorem redex1_not_nf (v0 : CM) :
    ¬ NF (p v0 v0) := by
  intro h
  exact h.2.2 ⟨e, Code.r1 v0⟩
theorem redex2_not_nf (v0 : CM) :
    ¬ NF (p (p (p e v0) v0) e) := by
  intro h
  exact h.2.2 ⟨v0, Code.r2 v0⟩
theorem redex3_not_nf (v0 : CM) :
    ¬ NF (p (p e (p e v0)) (p v0 e)) := by
  intro h
  exact h.2.2 ⟨(p e v0), Code.r3 v0⟩
theorem redex4_not_nf (v0 : CM) :
    ¬ NF (p (p e (p e (p (p e v0) v0))) v0) := by
  intro h
  exact h.2.2 ⟨(p e (p (p e v0) v0)), Code.r4 v0⟩
theorem redex5_not_nf (v0 : CM) :
    ¬ NF (p (p (p e v0) (p v0 e)) (p (p e v0) e)) := by
  intro h
  exact h.2.2 ⟨(p v0 e), Code.r5 v0⟩
theorem redex6_not_nf (v0 v1 : CM) :
    ¬ NF (p (p (p (p e (p (p e v0) v0)) v1) v1) v0) := by
  intro h
  exact h.2.2 ⟨v1, Code.r6 v0 v1⟩
theorem redex7_not_nf (v0 : CM) :
    ¬ NF (p (p (p e (p (p e v0) v0)) v0) (p (p e (p (p e v0) v0)) e)) := by
  intro h
  exact h.2.2 ⟨v0, Code.r7 v0⟩
noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_raw {a b : CM} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by simp [eval, h]
theorem eval_nf {a b : CM} (ha : NF a) (hb : NF b) : NF (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact code_nf ha hb (Classical.choose_spec h)
  · rw [eval_raw h]
    exact ⟨ha, hb, h⟩
@[grind unfold] abbrev C0 (v0 v1 : CM) (a b o : CM) : Prop := a = (p (p (p e v0) v1) v1) ∧ b = (p v0 e) ∧ o = v1 ∧ sz a = sz (p (p (p e v0) v1) v1) ∧ sz b = sz (p v0 e) ∧ sz o = sz v1
@[grind unfold] abbrev C1 (v0 : CM) (a b o : CM) : Prop := a = v0 ∧ b = v0 ∧ o = e ∧ sz a = sz v0 ∧ sz b = sz v0 ∧ sz o = sz e
@[grind unfold] abbrev C2 (v0 : CM) (a b o : CM) : Prop := a = (p (p e v0) v0) ∧ b = e ∧ o = v0 ∧ sz a = sz (p (p e v0) v0) ∧ sz b = sz e ∧ sz o = sz v0
@[grind unfold] abbrev C3 (v0 : CM) (a b o : CM) : Prop := a = (p e (p e v0)) ∧ b = (p v0 e) ∧ o = (p e v0) ∧ sz a = sz (p e (p e v0)) ∧ sz b = sz (p v0 e) ∧ sz o = sz (p e v0)
@[grind unfold] abbrev C4 (v0 : CM) (a b o : CM) : Prop := a = (p e (p e (p (p e v0) v0))) ∧ b = v0 ∧ o = (p e (p (p e v0) v0)) ∧ sz a = sz (p e (p e (p (p e v0) v0))) ∧ sz b = sz v0 ∧ sz o = sz (p e (p (p e v0) v0))
@[grind unfold] abbrev C5 (v0 : CM) (a b o : CM) : Prop := a = (p (p e v0) (p v0 e)) ∧ b = (p (p e v0) e) ∧ o = (p v0 e) ∧ sz a = sz (p (p e v0) (p v0 e)) ∧ sz b = sz (p (p e v0) e) ∧ sz o = sz (p v0 e)
@[grind unfold] abbrev C6 (v0 v1 : CM) (a b o : CM) : Prop := a = (p (p (p e (p (p e v0) v0)) v1) v1) ∧ b = v0 ∧ o = v1 ∧ sz a = sz (p (p (p e (p (p e v0) v0)) v1) v1) ∧ sz b = sz v0 ∧ sz o = sz v1
@[grind unfold] abbrev C7 (v0 : CM) (a b o : CM) : Prop := a = (p (p e (p (p e v0) v0)) v0) ∧ b = (p (p e (p (p e v0) v0)) e) ∧ o = v0 ∧ sz a = sz (p (p e (p (p e v0) v0)) v0) ∧ sz b = sz (p (p e (p (p e v0) v0)) e) ∧ sz o = sz v0
inductive EvalCases (a b o : CM) : Prop
  | r0 (v0 v1 : CM) (h : C0 v0 v1 a b o) : EvalCases a b o
  | r1 (v0 : CM) (h : C1 v0 a b o) : EvalCases a b o
  | r2 (v0 : CM) (h : C2 v0 a b o) : EvalCases a b o
  | r3 (v0 : CM) (h : C3 v0 a b o) : EvalCases a b o
  | r4 (v0 : CM) (h : C4 v0 a b o) : EvalCases a b o
  | r5 (v0 : CM) (h : C5 v0 a b o) : EvalCases a b o
  | r6 (v0 v1 : CM) (h : C6 v0 v1 a b o) : EvalCases a b o
  | r7 (v0 : CM) (h : C7 v0 a b o) : EvalCases a b o
  | raw (h : o = p a b ∧ sz o = sz a + sz b + 2) (n : ¬ ∃ q, Code a b q) : EvalCases a b o
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with cc0 | cc1 | cc2 | cc3 | cc4 | cc5 | cc6 | cc7 | impossible
    · rcases cc0 with ⟨v0, v1, hc0⟩
      exact .r0 v0 v1 hc0
    · rcases cc1 with ⟨v0, hc1⟩
      exact .r1 v0 hc1
    · rcases cc2 with ⟨v0, hc2⟩
      exact .r2 v0 hc2
    · rcases cc3 with ⟨v0, hc3⟩
      exact .r3 v0 hc3
    · rcases cc4 with ⟨v0, hc4⟩
      exact .r4 v0 hc4
    · rcases cc5 with ⟨v0, hc5⟩
      exact .r5 v0 hc5
    · rcases cc6 with ⟨v0, v1, hc6⟩
      exact .r6 v0 v1 hc6
    · rcases cc7 with ⟨v0, hc7⟩
      exact .r7 v0 hc7
    · contradiction
  · exact .raw ⟨eval_raw h, eq_sz (eval_raw h)⟩ h

theorem source_raw (q0 q1 q2 : CM)
    (hq0 : NF q0) (hq1 : NF q1) (hq2 : NF q2) :
    q0 = (eval (eval (eval (eval (eval q1 q1) q2) q0) q0) (eval q2 (eval q2 q2))) := by
  classical
  generalize H0 : eval q1 q1 = T0
  generalize H1 : eval T0 q2 = T1
  generalize H2 : eval T1 q0 = T2
  generalize H3 : eval T2 q0 = T3
  generalize H4 : eval q2 q2 = T4
  generalize H5 : eval q2 T4 = T5
  generalize H6 : eval T3 T5 = T6
  change q0 = T6
  have B0 : EvalCases q1 q1 T0 := by
    rw [← H0]
    exact eval_cases q1 q1
  have B1 : EvalCases T0 q2 T1 := by
    rw [← H1]
    exact eval_cases T0 q2
  have B2 : EvalCases T1 q0 T2 := by
    rw [← H2]
    exact eval_cases T1 q0
  have B3 : EvalCases T2 q0 T3 := by
    rw [← H3]
    exact eval_cases T2 q0
  have B4 : EvalCases q2 q2 T4 := by
    rw [← H4]
    exact eval_cases q2 q2
  have B5 : EvalCases q2 T4 T5 := by
    rw [← H5]
    exact eval_cases q2 T4
  have B6 : EvalCases T3 T5 T6 := by
    rw [← H6]
    exact eval_cases T3 T5
  have N0 : NF T0 := by
    rw [← H0]
    exact eval_nf hq1 hq1
  have N1 : NF T1 := by
    rw [← H1]
    exact eval_nf N0 hq2
  have N2 : NF T2 := by
    rw [← H2]
    exact eval_nf N1 hq0
  have N3 : NF T3 := by
    rw [← H3]
    exact eval_nf N2 hq0
  have N4 : NF T4 := by
    rw [← H4]
    exact eval_nf hq2 hq2
  have N5 : NF T5 := by
    rw [← H5]
    exact eval_nf hq2 N4
  have N6 : NF T6 := by
    rw [← H6]
    exact eval_nf N3 N5
  all_goals rcases B4 with ⟨v4_0_0, v4_0_1, hc4_0⟩ | ⟨v4_1_0, hc4_1⟩ | ⟨v4_2_0, hc4_2⟩ | ⟨v4_3_0, hc4_3⟩ | ⟨v4_4_0, hc4_4⟩ | ⟨v4_5_0, hc4_5⟩ | ⟨v4_6_0, v4_6_1, hc4_6⟩ | ⟨v4_7_0, hc4_7⟩ | ⟨hr4, n4⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals rcases B0 with ⟨v0_0_0, v0_0_1, hc0_0⟩ | ⟨v0_1_0, hc0_1⟩ | ⟨v0_2_0, hc0_2⟩ | ⟨v0_3_0, hc0_3⟩ | ⟨v0_4_0, hc0_4⟩ | ⟨v0_5_0, hc0_5⟩ | ⟨v0_6_0, v0_6_1, hc0_6⟩ | ⟨v0_7_0, hc0_7⟩ | ⟨hr0, n0⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals rcases B1 with ⟨v1_0_0, v1_0_1, hc1_0⟩ | ⟨v1_1_0, hc1_1⟩ | ⟨v1_2_0, hc1_2⟩ | ⟨v1_3_0, hc1_3⟩ | ⟨v1_4_0, hc1_4⟩ | ⟨v1_5_0, hc1_5⟩ | ⟨v1_6_0, v1_6_1, hc1_6⟩ | ⟨v1_7_0, hc1_7⟩ | ⟨hr1, n1⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals rcases B5 with ⟨v5_0_0, v5_0_1, hc5_0⟩ | ⟨v5_1_0, hc5_1⟩ | ⟨v5_2_0, hc5_2⟩ | ⟨v5_3_0, hc5_3⟩ | ⟨v5_4_0, hc5_4⟩ | ⟨v5_5_0, hc5_5⟩ | ⟨v5_6_0, v5_6_1, hc5_6⟩ | ⟨v5_7_0, hc5_7⟩ | ⟨hr5, n5⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals rcases B2 with ⟨v2_0_0, v2_0_1, hc2_0⟩ | ⟨v2_1_0, hc2_1⟩ | ⟨v2_2_0, hc2_2⟩ | ⟨v2_3_0, hc2_3⟩ | ⟨v2_4_0, hc2_4⟩ | ⟨v2_5_0, hc2_5⟩ | ⟨v2_6_0, v2_6_1, hc2_6⟩ | ⟨v2_7_0, hc2_7⟩ | ⟨hr2, n2⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals rcases B3 with ⟨v3_0_0, v3_0_1, hc3_0⟩ | ⟨v3_1_0, hc3_1⟩ | ⟨v3_2_0, hc3_2⟩ | ⟨v3_3_0, hc3_3⟩ | ⟨v3_4_0, hc3_4⟩ | ⟨v3_5_0, hc3_5⟩ | ⟨v3_6_0, v3_6_1, hc3_6⟩ | ⟨v3_7_0, hc3_7⟩ | ⟨hr3, n3⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals rcases B6 with ⟨v6_0_0, v6_0_1, hc6_0⟩ | ⟨v6_1_0, hc6_1⟩ | ⟨v6_2_0, hc6_2⟩ | ⟨v6_3_0, hc6_3⟩ | ⟨v6_4_0, hc6_4⟩ | ⟨v6_5_0, hc6_5⟩ | ⟨v6_6_0, v6_6_1, hc6_6⟩ | ⟨v6_7_0, hc6_7⟩ | ⟨hr6, n6⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz])
  all_goals first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, Code.r2, Code.r3, Code.r4, Code.r5, Code.r6, Code.r7, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, redex4_not_nf, redex5_not_nf, redex6_not_nf, redex7_not_nf, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagma : Magma Carrier where op := op
theorem source_holds (q0 q1 q2 : Carrier) :
    q0 = (op (op (op (op (op q1 q1) q2) q0) q0) (op q2 (op q2 q2))) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q2.1 q0.2 q1.2 q2.2
def ce : Carrier := ⟨e, by trivial⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, a.2⟩
def tower : Nat → Carrier | 0 => ce | n+1 => ck (tower n)
theorem tower_sz (n : Nat) : sz (tower n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tower, ck, sz, ih]
theorem tower_injective : Function.Injective tower := by
  intro a b h
  have q := congrArg (fun x : Carrier => sz x.1) h
  simpa only [tower_sz] using q
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagma, CM.source_holds, ?_⟩
  intro target
  have bad := congrArg Subtype.val (target ce (ck ce))
  change e = (k e) at bad
  have hl : e = e := rfl
  have hr : (k e) = (k e) := rfl
  have bad := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => false | k _ => true | p _ _ => false) bad)
