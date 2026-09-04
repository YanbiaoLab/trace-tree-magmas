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
  | r0 (v00 v01 v02 v03 : CM) : Code (p (p (p v00 v01) v02) v01) (p v03 (p v01 (p v01 (p v01 v01)))) v03
  | r1 (v10 v11 v12 : CM) : Code v10 (p v11 (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p v10 (p v12 (p v12 (p v12 v12)))))))) v11
  | r2 (v20 v21 v22 : CM) : Code (p v20 v21) (p v22 (p v21 (p v21 (p v21 v21)))) v22
def CodeCases (a b o : CM) : Prop := (∃ v00 v01 v02 v03, a = (p (p (p v00 v01) v02) v01) ∧ b = (p v03 (p v01 (p v01 (p v01 v01)))) ∧ o = v03 ∧ sz a = ((((((sz v00 + 1) + (sz v01 + 1)) + 1) + (sz v02 + 1)) + 1) + (sz v01 + 1)) ∧ sz b = ((sz v03 + 1) + (((sz v01 + 1) + (((sz v01 + 1) + (((sz v01 + 1) + (sz v01 + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v03) ∨ (∃ v10 v11 v12, a = v10 ∧ b = (p v11 (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p v10 (p v12 (p v12 (p v12 v12)))))))) ∧ o = v11 ∧ sz a = sz v10 ∧ sz b = ((sz v11 + 1) + (((((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1) + (((((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1) + (((((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1) + (((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v11) ∨ (∃ v20 v21 v22, a = (p v20 v21) ∧ b = (p v22 (p v21 (p v21 (p v21 v21)))) ∧ o = v22 ∧ sz a = ((sz v20 + 1) + (sz v21 + 1)) ∧ sz b = ((sz v22 + 1) + (((sz v21 + 1) + (((sz v21 + 1) + (((sz v21 + 1) + (sz v21 + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v22)
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  unfold CodeCases
  cases h with
  | r0 => exact Or.inl ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | r2 => exact Or.inr (Or.inr (⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩))
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
    ¬ NF (p (p (p (p v00 v01) v02) v01) (p v03 (p v01 (p v01 (p v01 v01))))) := by
  intro h
  exact h.2.2 ⟨v03, Code.r0 v00 v01 v02 v03⟩

theorem redex1_not_nf (v10 v11 v12 : CM) :
    ¬ NF (p v10 (p v11 (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p v10 (p v12 (p v12 (p v12 v12))))))))) := by
  intro h
  exact h.2.2 ⟨v11, Code.r1 v10 v11 v12⟩

theorem redex2_not_nf (v20 v21 v22 : CM) :
    ¬ NF (p (p v20 v21) (p v22 (p v21 (p v21 (p v21 v21))))) := by
  intro h
  exact h.2.2 ⟨v22, Code.r2 v20 v21 v22⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact hb.1
  | r1 => exact hb.1
  | r2 => exact hb.1
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
def EvalCases (a b o : CM) : Prop := (∃ v00 v01 v02 v03, a = (p (p (p v00 v01) v02) v01) ∧ b = (p v03 (p v01 (p v01 (p v01 v01)))) ∧ o = v03 ∧ sz a = ((((((sz v00 + 1) + (sz v01 + 1)) + 1) + (sz v02 + 1)) + 1) + (sz v01 + 1)) ∧ sz b = ((sz v03 + 1) + (((sz v01 + 1) + (((sz v01 + 1) + (((sz v01 + 1) + (sz v01 + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v03) ∨ (∃ v10 v11 v12, a = v10 ∧ b = (p v11 (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p (p v10 (p v12 (p v12 (p v12 v12)))) (p v10 (p v12 (p v12 (p v12 v12)))))))) ∧ o = v11 ∧ sz a = sz v10 ∧ sz b = ((sz v11 + 1) + (((((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1) + (((((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1) + (((((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1) + (((sz v10 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (((sz v12 + 1) + (sz v12 + 1)) + 1)) + 1)) + 1)) + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v11) ∨ (∃ v20 v21 v22, a = (p v20 v21) ∧ b = (p v22 (p v21 (p v21 (p v21 v21)))) ∧ o = v22 ∧ sz a = ((sz v20 + 1) + (sz v21 + 1)) ∧ sz b = ((sz v22 + 1) + (((sz v21 + 1) + (((sz v21 + 1) + (((sz v21 + 1) + (sz v21 + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v22) ∨ (o = p a b ∧ sz o = ((sz a + 1) + (sz b + 1)) ∧ ¬ ∃ q, Code a b q)
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with c0 | c1 | c2
    · exact Or.inl c0
    · exact Or.inr (Or.inl c1)
    · exact Or.inr (Or.inr (Or.inl c2))
  · exact Or.inr (Or.inr (Or.inr (⟨eval_raw h, eq_sz (eval_raw h), h⟩)))

theorem source_raw (q0 q2 q1 z : CM) (hq0 : NF q0) (hq2 : NF q2) (hq1 : NF q1) (hz : NF z) :
    q0 = (eval (eval (eval (eval q2 q1) z) q1) (eval q0 (eval q1 (eval q1 (eval q1 q1))))) := by
  classical
  have B0 := eval_cases q2 q1
  have B1 := eval_cases (eval q2 q1) z
  have B2 := eval_cases (eval (eval q2 q1) z) q1
  have B3 := eval_cases q1 q1
  have B4 := eval_cases q1 (eval q1 q1)
  have B5 := eval_cases q1 (eval q1 (eval q1 q1))
  have B6 := eval_cases q0 (eval q1 (eval q1 (eval q1 q1)))
  have B7 := eval_cases (eval (eval (eval q2 q1) z) q1) (eval q0 (eval q1 (eval q1 (eval q1 q1))))
  have Hsrc : Code (p (p (p q2 q1) z) q1) (p q0 (p q1 (p q1 (p q1 q1)))) q0 := .r0 q2 q1 z q0
  have N0 : NF (eval q2 q1) := eval_nf (hq2) (hq1)
  have N1 : NF (eval (eval q2 q1) z) := eval_nf (eval_nf (hq2) (hq1)) (hz)
  have N2 : NF (eval (eval (eval q2 q1) z) q1) := eval_nf (eval_nf (eval_nf (hq2) (hq1)) (hz)) (hq1)
  have N3 : NF (eval q1 q1) := eval_nf (hq1) (hq1)
  have N4 : NF (eval q1 (eval q1 q1)) := eval_nf (hq1) (eval_nf (hq1) (hq1))
  have N5 : NF (eval q1 (eval q1 (eval q1 q1))) := eval_nf (hq1) (eval_nf (hq1) (eval_nf (hq1) (hq1)))
  have N6 : NF (eval q0 (eval q1 (eval q1 (eval q1 q1)))) := eval_nf (hq0) (eval_nf (hq1) (eval_nf (hq1) (eval_nf (hq1) (hq1))))
  have N7 : NF (eval (eval (eval (eval q2 q1) z) q1) (eval q0 (eval q1 (eval q1 (eval q1 q1))))) := eval_nf (eval_nf (eval_nf (eval_nf (hq2) (hq1)) (hz)) (hq1)) (eval_nf (hq0) (eval_nf (hq1) (eval_nf (hq1) (eval_nf (hq1) (hq1)))))
  all_goals rcases B7 with ⟨b7_0_v00, b7_0_v01, b7_0_v02, b7_0_v03, b7_0_a, b7_0_b, b7_0_o, b7_0_sa, b7_0_sb, b7_0_so⟩ | ⟨b7_1_v10, b7_1_v11, b7_1_v12, b7_1_a, b7_1_b, b7_1_o, b7_1_sa, b7_1_sb, b7_1_so⟩ | ⟨b7_2_v20, b7_2_v21, b7_2_v22, b7_2_a, b7_2_b, b7_2_o, b7_2_sa, b7_2_sb, b7_2_so⟩ | ⟨b7_raw_o, b7_raw_so, b7_raw_no⟩
  all_goals try omega
  all_goals rcases B6 with ⟨b6_0_v00, b6_0_v01, b6_0_v02, b6_0_v03, b6_0_a, b6_0_b, b6_0_o, b6_0_sa, b6_0_sb, b6_0_so⟩ | ⟨b6_1_v10, b6_1_v11, b6_1_v12, b6_1_a, b6_1_b, b6_1_o, b6_1_sa, b6_1_sb, b6_1_so⟩ | ⟨b6_2_v20, b6_2_v21, b6_2_v22, b6_2_a, b6_2_b, b6_2_o, b6_2_sa, b6_2_sb, b6_2_so⟩ | ⟨b6_raw_o, b6_raw_so, b6_raw_no⟩
  all_goals try omega
  all_goals rcases B5 with ⟨b5_0_v00, b5_0_v01, b5_0_v02, b5_0_v03, b5_0_a, b5_0_b, b5_0_o, b5_0_sa, b5_0_sb, b5_0_so⟩ | ⟨b5_1_v10, b5_1_v11, b5_1_v12, b5_1_a, b5_1_b, b5_1_o, b5_1_sa, b5_1_sb, b5_1_so⟩ | ⟨b5_2_v20, b5_2_v21, b5_2_v22, b5_2_a, b5_2_b, b5_2_o, b5_2_sa, b5_2_sb, b5_2_so⟩ | ⟨b5_raw_o, b5_raw_so, b5_raw_no⟩
  all_goals try omega
  all_goals rcases B4 with ⟨b4_0_v00, b4_0_v01, b4_0_v02, b4_0_v03, b4_0_a, b4_0_b, b4_0_o, b4_0_sa, b4_0_sb, b4_0_so⟩ | ⟨b4_1_v10, b4_1_v11, b4_1_v12, b4_1_a, b4_1_b, b4_1_o, b4_1_sa, b4_1_sb, b4_1_so⟩ | ⟨b4_2_v20, b4_2_v21, b4_2_v22, b4_2_a, b4_2_b, b4_2_o, b4_2_sa, b4_2_sb, b4_2_so⟩ | ⟨b4_raw_o, b4_raw_so, b4_raw_no⟩
  all_goals try omega
  all_goals rcases B3 with ⟨b3_0_v00, b3_0_v01, b3_0_v02, b3_0_v03, b3_0_a, b3_0_b, b3_0_o, b3_0_sa, b3_0_sb, b3_0_so⟩ | ⟨b3_1_v10, b3_1_v11, b3_1_v12, b3_1_a, b3_1_b, b3_1_o, b3_1_sa, b3_1_sb, b3_1_so⟩ | ⟨b3_2_v20, b3_2_v21, b3_2_v22, b3_2_a, b3_2_b, b3_2_o, b3_2_sa, b3_2_sb, b3_2_so⟩ | ⟨b3_raw_o, b3_raw_so, b3_raw_no⟩
  all_goals try omega
  all_goals rcases B2 with ⟨b2_0_v00, b2_0_v01, b2_0_v02, b2_0_v03, b2_0_a, b2_0_b, b2_0_o, b2_0_sa, b2_0_sb, b2_0_so⟩ | ⟨b2_1_v10, b2_1_v11, b2_1_v12, b2_1_a, b2_1_b, b2_1_o, b2_1_sa, b2_1_sb, b2_1_so⟩ | ⟨b2_2_v20, b2_2_v21, b2_2_v22, b2_2_a, b2_2_b, b2_2_o, b2_2_sa, b2_2_sb, b2_2_so⟩ | ⟨b2_raw_o, b2_raw_so, b2_raw_no⟩
  all_goals try omega
  all_goals rcases B1 with ⟨b1_0_v00, b1_0_v01, b1_0_v02, b1_0_v03, b1_0_a, b1_0_b, b1_0_o, b1_0_sa, b1_0_sb, b1_0_so⟩ | ⟨b1_1_v10, b1_1_v11, b1_1_v12, b1_1_a, b1_1_b, b1_1_o, b1_1_sa, b1_1_sb, b1_1_so⟩ | ⟨b1_2_v20, b1_2_v21, b1_2_v22, b1_2_a, b1_2_b, b1_2_o, b1_2_sa, b1_2_sb, b1_2_so⟩ | ⟨b1_raw_o, b1_raw_so, b1_raw_no⟩
  all_goals try omega
  all_goals rcases B0 with ⟨b0_0_v00, b0_0_v01, b0_0_v02, b0_0_v03, b0_0_a, b0_0_b, b0_0_o, b0_0_sa, b0_0_sb, b0_0_so⟩ | ⟨b0_1_v10, b0_1_v11, b0_1_v12, b0_1_a, b0_1_b, b0_1_o, b0_1_sa, b0_1_sb, b0_1_so⟩ | ⟨b0_2_v20, b0_2_v21, b0_2_v22, b0_2_a, b0_2_b, b0_2_o, b0_2_sa, b0_2_sb, b0_2_so⟩ | ⟨b0_raw_o, b0_raw_so, b0_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 4, gen := 12 }) [eq_sz, ne_p_left, ne_p_right, L, R, U, sz]
  all_goals grind (config := { splits := 20, gen := 14 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, Code.r0, Code.r1, Code.r2, L, R, U, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op a b := op b a
theorem source_holds (q0 q2 q1 z : Carrier) : q0 = (op (op (op (op q2 q1) z) q1) (op q0 (op q1 (op q1 (op q1 q1))))) := by
  apply Subtype.ext
  exact source_raw q0.1 q2.1 q1.1 z.1 q0.2 q2.2 q1.2 z.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, (fun q0 q1 q2 => ((fun q0 q2 q1 => CM.source_holds q0 q2 q1 q1)) q0 q2 q1), ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = CM.e at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : CM.e = CM.e := rfl
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) nb)
