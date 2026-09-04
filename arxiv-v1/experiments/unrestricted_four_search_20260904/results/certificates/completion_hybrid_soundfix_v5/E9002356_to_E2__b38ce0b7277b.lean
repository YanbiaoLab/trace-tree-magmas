import JudgeProblem
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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
inductive Code : CM → CM → CM → Prop
  | r0 (v00 v01 v02 v03 : CM) : Code (p v00 (p v01 v00)) (p (p (p (p v02 v02) v03) v02) v00) v02
  | r1 (v10 v11 v12 v13 v14 : CM) : Code (p (p (p (p (p v10 v10) v11) v10) v12) v10) (p (p (p (p v13 v13) v14) v13) (p (p (p (p v10 v10) v11) v10) v12)) v13
def CodeCases (a b o : CM) : Prop := (∃ v00 v01 v02 v03, a = (p v00 (p v01 v00)) ∧ b = (p (p (p (p v02 v02) v03) v02) v00) ∧ o = v02 ∧ sz a = ((sz v00 + 1) + (((sz v01 + 1) + (sz v00 + 1)) + 1)) ∧ sz b = ((((((((sz v02 + 1) + (sz v02 + 1)) + 1) + (sz v03 + 1)) + 1) + (sz v02 + 1)) + 1) + (sz v00 + 1)) ∧ sz o = sz v02) ∨ (∃ v10 v11 v12 v13 v14, a = (p (p (p (p (p v10 v10) v11) v10) v12) v10) ∧ b = (p (p (p (p v13 v13) v14) v13) (p (p (p (p v10 v10) v11) v10) v12)) ∧ o = v13 ∧ sz a = ((((((((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1)) + 1) + (sz v10 + 1)) + 1) + (sz v12 + 1)) + 1) + (sz v10 + 1)) ∧ sz b = ((((((((sz v13 + 1) + (sz v13 + 1)) + 1) + (sz v14 + 1)) + 1) + (sz v13 + 1)) + 1) + (((((((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1)) + 1) + (sz v10 + 1)) + 1) + (sz v12 + 1)) + 1)) ∧ sz o = sz v13)
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  unfold CodeCases
  cases h with
  | r0 => exact Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)
def NF : CM → Prop
  | e => True
  | k a => NF a
  | p a b => NF a ∧ NF b ∧ ¬ ∃ o, Code a b o
theorem nf_p_no {a b : CM} (h : NF (p a b)) : ¬ ∃ o, Code a b o := h.2.2
theorem nf_p_left {a b : CM} (h : NF (p a b)) : NF a := h.1
theorem nf_p_right {a b : CM} (h : NF (p a b)) : NF b := h.2.1
theorem eq_sz {a b : CM} (h : a = b) : sz a = sz b := congrArg sz h
theorem ne_p_left (a b : CM) : a ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q
  omega
theorem ne_p_right (a b : CM) : b ≠ p a b := by
  intro h
  have q := congrArg sz h
  simp [sz] at q
  omega
theorem redex0_not_nf (v00 v01 v02 v03 : CM) :
    ¬ NF (p (p v00 (p v01 v00)) (p (p (p (p v02 v02) v03) v02) v00)) := by
  intro h
  exact h.2.2 ⟨v02, Code.r0 v00 v01 v02 v03⟩

theorem redex1_not_nf (v10 v11 v12 v13 v14 : CM) :
    ¬ NF (p (p (p (p (p (p v10 v10) v11) v10) v12) v10) (p (p (p (p v13 v13) v14) v13) (p (p (p (p v10 v10) v11) v10) v12))) := by
  intro h
  exact h.2.2 ⟨v13, Code.r1 v10 v11 v12 v13 v14⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact hb.1.2.1
  | r1 => exact hb.1.2.1
noncomputable def eval (a b : CM) : CM := by
  classical
  exact if h : ∃ o, Code a b o then Classical.choose h else p a b
theorem eval_raw {a b : CM} (h : ¬ ∃ o, Code a b o) : eval a b = p a b := by
  rw [eval, dif_neg h]
theorem eval_nf {a b : CM} (ha : NF a) (hb : NF b) : NF (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact code_nf ha hb (Classical.choose_spec h)
  · rw [eval_raw h]
    exact ⟨ha, hb, h⟩
def EvalCases (a b o : CM) : Prop := (∃ v00 v01 v02 v03, a = (p v00 (p v01 v00)) ∧ b = (p (p (p (p v02 v02) v03) v02) v00) ∧ o = v02 ∧ sz a = ((sz v00 + 1) + (((sz v01 + 1) + (sz v00 + 1)) + 1)) ∧ sz b = ((((((((sz v02 + 1) + (sz v02 + 1)) + 1) + (sz v03 + 1)) + 1) + (sz v02 + 1)) + 1) + (sz v00 + 1)) ∧ sz o = sz v02) ∨ (∃ v10 v11 v12 v13 v14, a = (p (p (p (p (p v10 v10) v11) v10) v12) v10) ∧ b = (p (p (p (p v13 v13) v14) v13) (p (p (p (p v10 v10) v11) v10) v12)) ∧ o = v13 ∧ sz a = ((((((((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1)) + 1) + (sz v10 + 1)) + 1) + (sz v12 + 1)) + 1) + (sz v10 + 1)) ∧ sz b = ((((((((sz v13 + 1) + (sz v13 + 1)) + 1) + (sz v14 + 1)) + 1) + (sz v13 + 1)) + 1) + (((((((((sz v10 + 1) + (sz v10 + 1)) + 1) + (sz v11 + 1)) + 1) + (sz v10 + 1)) + 1) + (sz v12 + 1)) + 1)) ∧ sz o = sz v13) ∨ (o = p a b ∧ sz o = ((sz a + 1) + (sz b + 1)) ∧ ¬ ∃ q, Code a b q)
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with c0 | c1
    · exact Or.inl c0
    · exact Or.inr (Or.inl c1)
  · exact Or.inr (Or.inr (⟨eval_raw h, eq_sz (eval_raw h), h⟩))

theorem source_raw (q0 q1 q2 z : CM) (hq0 : NF q0) (hq1 : NF q1) (hq2 : NF q2) (hz : NF z) :
    q0 = (eval (eval q1 (eval q2 q1)) (eval (eval (eval (eval q0 q0) z) q0) q1)) := by
  classical
  have B0 := eval_cases q2 q1
  have B1 := eval_cases q1 (eval q2 q1)
  have B2 := eval_cases q0 q0
  have B3 := eval_cases (eval q0 q0) z
  have B4 := eval_cases (eval (eval q0 q0) z) q0
  have B5 := eval_cases (eval (eval (eval q0 q0) z) q0) q1
  have B6 := eval_cases (eval q1 (eval q2 q1)) (eval (eval (eval (eval q0 q0) z) q0) q1)
  have Hsrc : Code (p q1 (p q2 q1)) (p (p (p (p q0 q0) z) q0) q1) q0 := .r0 q1 q2 q0 z
  have N0 : NF (eval q2 q1) := eval_nf (hq2) (hq1)
  have N1 : NF (eval q1 (eval q2 q1)) := eval_nf (hq1) (eval_nf (hq2) (hq1))
  have N2 : NF (eval q0 q0) := eval_nf (hq0) (hq0)
  have N3 : NF (eval (eval q0 q0) z) := eval_nf (eval_nf (hq0) (hq0)) (hz)
  have N4 : NF (eval (eval (eval q0 q0) z) q0) := eval_nf (eval_nf (eval_nf (hq0) (hq0)) (hz)) (hq0)
  have N5 : NF (eval (eval (eval (eval q0 q0) z) q0) q1) := eval_nf (eval_nf (eval_nf (eval_nf (hq0) (hq0)) (hz)) (hq0)) (hq1)
  have N6 : NF (eval (eval q1 (eval q2 q1)) (eval (eval (eval (eval q0 q0) z) q0) q1)) := eval_nf (eval_nf (hq1) (eval_nf (hq2) (hq1))) (eval_nf (eval_nf (eval_nf (eval_nf (hq0) (hq0)) (hz)) (hq0)) (hq1))
  all_goals rcases B0 with ⟨b0_0_v00, b0_0_v01, b0_0_v02, b0_0_v03, b0_0_a, b0_0_b, b0_0_o, b0_0_sa, b0_0_sb, b0_0_so⟩ | ⟨b0_1_v10, b0_1_v11, b0_1_v12, b0_1_v13, b0_1_v14, b0_1_a, b0_1_b, b0_1_o, b0_1_sa, b0_1_sb, b0_1_so⟩ | ⟨b0_raw_o, b0_raw_so, b0_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals rcases B1 with ⟨b1_0_v00, b1_0_v01, b1_0_v02, b1_0_v03, b1_0_a, b1_0_b, b1_0_o, b1_0_sa, b1_0_sb, b1_0_so⟩ | ⟨b1_1_v10, b1_1_v11, b1_1_v12, b1_1_v13, b1_1_v14, b1_1_a, b1_1_b, b1_1_o, b1_1_sa, b1_1_sb, b1_1_so⟩ | ⟨b1_raw_o, b1_raw_so, b1_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals rcases B2 with ⟨b2_0_v00, b2_0_v01, b2_0_v02, b2_0_v03, b2_0_a, b2_0_b, b2_0_o, b2_0_sa, b2_0_sb, b2_0_so⟩ | ⟨b2_1_v10, b2_1_v11, b2_1_v12, b2_1_v13, b2_1_v14, b2_1_a, b2_1_b, b2_1_o, b2_1_sa, b2_1_sb, b2_1_so⟩ | ⟨b2_raw_o, b2_raw_so, b2_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals rcases B3 with ⟨b3_0_v00, b3_0_v01, b3_0_v02, b3_0_v03, b3_0_a, b3_0_b, b3_0_o, b3_0_sa, b3_0_sb, b3_0_so⟩ | ⟨b3_1_v10, b3_1_v11, b3_1_v12, b3_1_v13, b3_1_v14, b3_1_a, b3_1_b, b3_1_o, b3_1_sa, b3_1_sb, b3_1_so⟩ | ⟨b3_raw_o, b3_raw_so, b3_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals rcases B4 with ⟨b4_0_v00, b4_0_v01, b4_0_v02, b4_0_v03, b4_0_a, b4_0_b, b4_0_o, b4_0_sa, b4_0_sb, b4_0_so⟩ | ⟨b4_1_v10, b4_1_v11, b4_1_v12, b4_1_v13, b4_1_v14, b4_1_a, b4_1_b, b4_1_o, b4_1_sa, b4_1_sb, b4_1_so⟩ | ⟨b4_raw_o, b4_raw_so, b4_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals rcases B5 with ⟨b5_0_v00, b5_0_v01, b5_0_v02, b5_0_v03, b5_0_a, b5_0_b, b5_0_o, b5_0_sa, b5_0_sb, b5_0_so⟩ | ⟨b5_1_v10, b5_1_v11, b5_1_v12, b5_1_v13, b5_1_v14, b5_1_a, b5_1_b, b5_1_o, b5_1_sa, b5_1_sb, b5_1_so⟩ | ⟨b5_raw_o, b5_raw_so, b5_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals rcases B6 with ⟨b6_0_v00, b6_0_v01, b6_0_v02, b6_0_v03, b6_0_a, b6_0_b, b6_0_o, b6_0_sa, b6_0_sb, b6_0_so⟩ | ⟨b6_1_v10, b6_1_v11, b6_1_v12, b6_1_v13, b6_1_v14, b6_1_a, b6_1_b, b6_1_o, b6_1_sa, b6_1_sb, b6_1_so⟩ | ⟨b6_raw_o, b6_raw_so, b6_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 1, gen := 6 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
  all_goals grind (config := { splits := 10, gen := 10 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, Code.r0, Code.r1, L, R, U, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op := op
theorem source_holds (q0 q1 q2 z : Carrier) : q0 = (op (op q1 (op q2 q1)) (op (op (op (op q0 q0) z) q0) q1)) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q2.1 z.1 q0.2 q1.2 q2.2 z.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, (fun q0 q1 q2 => CM.source_holds q0 q1 q2 (op q0 q1)), ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = CM.e at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : CM.e = CM.e := rfl
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) nb)
