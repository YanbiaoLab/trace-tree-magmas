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
  | r0 (v00 v01 v02 : CM) : Code v00 (p v01 (p v01 (p v00 (p v02 v02)))) v01
  | r1 (v10 : CM) : Code (p v10 v10) (p v10 v10) (p v10 v10)
  | r2 (v20 v21 : CM) : Code (p v20 (p v21 v21)) (p v20 (p v20 (p v21 v21))) v20
  | r3 (v30 v31 : CM) : Code (p v30 v30) (p v31 (p v31 (p v30 v30))) v31
def CodeCases (a b o : CM) : Prop := (∃ v00 v01 v02, a = v00 ∧ b = (p v01 (p v01 (p v00 (p v02 v02)))) ∧ o = v01 ∧ sz a = sz v00 ∧ sz b = ((sz v01 + 1) + (((sz v01 + 1) + (((sz v00 + 1) + (((sz v02 + 1) + (sz v02 + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v01) ∨ (∃ v10, a = (p v10 v10) ∧ b = (p v10 v10) ∧ o = (p v10 v10) ∧ sz a = ((sz v10 + 1) + (sz v10 + 1)) ∧ sz b = ((sz v10 + 1) + (sz v10 + 1)) ∧ sz o = ((sz v10 + 1) + (sz v10 + 1))) ∨ (∃ v20 v21, a = (p v20 (p v21 v21)) ∧ b = (p v20 (p v20 (p v21 v21))) ∧ o = v20 ∧ sz a = ((sz v20 + 1) + (((sz v21 + 1) + (sz v21 + 1)) + 1)) ∧ sz b = ((sz v20 + 1) + (((sz v20 + 1) + (((sz v21 + 1) + (sz v21 + 1)) + 1)) + 1)) ∧ sz o = sz v20) ∨ (∃ v30 v31, a = (p v30 v30) ∧ b = (p v31 (p v31 (p v30 v30))) ∧ o = v31 ∧ sz a = ((sz v30 + 1) + (sz v30 + 1)) ∧ sz b = ((sz v31 + 1) + (((sz v31 + 1) + (((sz v30 + 1) + (sz v30 + 1)) + 1)) + 1)) ∧ sz o = sz v31)
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  unfold CodeCases
  cases h with
  | r0 => exact Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (Or.inl ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | r2 => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩))
  | r3 => exact Or.inr (Or.inr (Or.inr (⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)))
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
theorem redex0_not_nf (v00 v01 v02 : CM) :
    ¬ NF (p v00 (p v01 (p v01 (p v00 (p v02 v02))))) := by
  intro h
  exact h.2.2 ⟨v01, Code.r0 v00 v01 v02⟩

theorem redex1_not_nf (v10 : CM) :
    ¬ NF (p (p v10 v10) (p v10 v10)) := by
  intro h
  exact h.2.2 ⟨(p v10 v10), Code.r1 v10⟩

theorem redex2_not_nf (v20 v21 : CM) :
    ¬ NF (p (p v20 (p v21 v21)) (p v20 (p v20 (p v21 v21)))) := by
  intro h
  exact h.2.2 ⟨v20, Code.r2 v20 v21⟩

theorem redex3_not_nf (v30 v31 : CM) :
    ¬ NF (p (p v30 v30) (p v31 (p v31 (p v30 v30)))) := by
  intro h
  exact h.2.2 ⟨v31, Code.r3 v30 v31⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact hb.1
  | r1 => exact ha
  | r2 => exact ha.1
  | r3 => exact hb.1
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
def EvalCases (a b o : CM) : Prop := (∃ v00 v01 v02, a = v00 ∧ b = (p v01 (p v01 (p v00 (p v02 v02)))) ∧ o = v01 ∧ sz a = sz v00 ∧ sz b = ((sz v01 + 1) + (((sz v01 + 1) + (((sz v00 + 1) + (((sz v02 + 1) + (sz v02 + 1)) + 1)) + 1)) + 1)) ∧ sz o = sz v01) ∨ (∃ v10, a = (p v10 v10) ∧ b = (p v10 v10) ∧ o = (p v10 v10) ∧ sz a = ((sz v10 + 1) + (sz v10 + 1)) ∧ sz b = ((sz v10 + 1) + (sz v10 + 1)) ∧ sz o = ((sz v10 + 1) + (sz v10 + 1))) ∨ (∃ v20 v21, a = (p v20 (p v21 v21)) ∧ b = (p v20 (p v20 (p v21 v21))) ∧ o = v20 ∧ sz a = ((sz v20 + 1) + (((sz v21 + 1) + (sz v21 + 1)) + 1)) ∧ sz b = ((sz v20 + 1) + (((sz v20 + 1) + (((sz v21 + 1) + (sz v21 + 1)) + 1)) + 1)) ∧ sz o = sz v20) ∨ (∃ v30 v31, a = (p v30 v30) ∧ b = (p v31 (p v31 (p v30 v30))) ∧ o = v31 ∧ sz a = ((sz v30 + 1) + (sz v30 + 1)) ∧ sz b = ((sz v31 + 1) + (((sz v31 + 1) + (((sz v30 + 1) + (sz v30 + 1)) + 1)) + 1)) ∧ sz o = sz v31) ∨ (o = p a b ∧ sz o = ((sz a + 1) + (sz b + 1)) ∧ ¬ ∃ q, Code a b q)
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with c0 | c1 | c2 | c3
    · exact Or.inl c0
    · exact Or.inr (Or.inl c1)
    · exact Or.inr (Or.inr (Or.inl c2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl c3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨eval_raw h, eq_sz (eval_raw h), h⟩))))

theorem source_raw (q0 q1 q2 : CM) (hq0 : NF q0) (hq1 : NF q1) (hq2 : NF q2) :
    q0 = (eval q1 (eval q0 (eval q0 (eval q1 (eval q2 q2))))) := by
  classical
  have B0 := eval_cases q2 q2
  have B1 := eval_cases q1 (eval q2 q2)
  have B2 := eval_cases q0 (eval q1 (eval q2 q2))
  have B3 := eval_cases q0 (eval q0 (eval q1 (eval q2 q2)))
  have B4 := eval_cases q1 (eval q0 (eval q0 (eval q1 (eval q2 q2))))
  have Hsrc : Code q1 (p q0 (p q0 (p q1 (p q2 q2)))) q0 := .r0 q1 q0 q2
  have N0 : NF (eval q2 q2) := eval_nf (hq2) (hq2)
  have N1 : NF (eval q1 (eval q2 q2)) := eval_nf (hq1) (eval_nf (hq2) (hq2))
  have N2 : NF (eval q0 (eval q1 (eval q2 q2))) := eval_nf (hq0) (eval_nf (hq1) (eval_nf (hq2) (hq2)))
  have N3 : NF (eval q0 (eval q0 (eval q1 (eval q2 q2)))) := eval_nf (hq0) (eval_nf (hq0) (eval_nf (hq1) (eval_nf (hq2) (hq2))))
  have N4 : NF (eval q1 (eval q0 (eval q0 (eval q1 (eval q2 q2))))) := eval_nf (hq1) (eval_nf (hq0) (eval_nf (hq0) (eval_nf (hq1) (eval_nf (hq2) (hq2)))))
  all_goals rcases B4 with ⟨b4_0_v00, b4_0_v01, b4_0_v02, b4_0_a, b4_0_b, b4_0_o, b4_0_sa, b4_0_sb, b4_0_so⟩ | ⟨b4_1_v10, b4_1_a, b4_1_b, b4_1_o, b4_1_sa, b4_1_sb, b4_1_so⟩ | ⟨b4_2_v20, b4_2_v21, b4_2_a, b4_2_b, b4_2_o, b4_2_sa, b4_2_sb, b4_2_so⟩ | ⟨b4_3_v30, b4_3_v31, b4_3_a, b4_3_b, b4_3_o, b4_3_sa, b4_3_sb, b4_3_so⟩ | ⟨b4_raw_o, b4_raw_so, b4_raw_no⟩
  all_goals try omega
  all_goals rcases B3 with ⟨b3_0_v00, b3_0_v01, b3_0_v02, b3_0_a, b3_0_b, b3_0_o, b3_0_sa, b3_0_sb, b3_0_so⟩ | ⟨b3_1_v10, b3_1_a, b3_1_b, b3_1_o, b3_1_sa, b3_1_sb, b3_1_so⟩ | ⟨b3_2_v20, b3_2_v21, b3_2_a, b3_2_b, b3_2_o, b3_2_sa, b3_2_sb, b3_2_so⟩ | ⟨b3_3_v30, b3_3_v31, b3_3_a, b3_3_b, b3_3_o, b3_3_sa, b3_3_sb, b3_3_so⟩ | ⟨b3_raw_o, b3_raw_so, b3_raw_no⟩
  all_goals try omega
  all_goals rcases B2 with ⟨b2_0_v00, b2_0_v01, b2_0_v02, b2_0_a, b2_0_b, b2_0_o, b2_0_sa, b2_0_sb, b2_0_so⟩ | ⟨b2_1_v10, b2_1_a, b2_1_b, b2_1_o, b2_1_sa, b2_1_sb, b2_1_so⟩ | ⟨b2_2_v20, b2_2_v21, b2_2_a, b2_2_b, b2_2_o, b2_2_sa, b2_2_sb, b2_2_so⟩ | ⟨b2_3_v30, b2_3_v31, b2_3_a, b2_3_b, b2_3_o, b2_3_sa, b2_3_sb, b2_3_so⟩ | ⟨b2_raw_o, b2_raw_so, b2_raw_no⟩
  all_goals try omega
  all_goals rcases B1 with ⟨b1_0_v00, b1_0_v01, b1_0_v02, b1_0_a, b1_0_b, b1_0_o, b1_0_sa, b1_0_sb, b1_0_so⟩ | ⟨b1_1_v10, b1_1_a, b1_1_b, b1_1_o, b1_1_sa, b1_1_sb, b1_1_so⟩ | ⟨b1_2_v20, b1_2_v21, b1_2_a, b1_2_b, b1_2_o, b1_2_sa, b1_2_sb, b1_2_so⟩ | ⟨b1_3_v30, b1_3_v31, b1_3_a, b1_3_b, b1_3_o, b1_3_sa, b1_3_sb, b1_3_so⟩ | ⟨b1_raw_o, b1_raw_so, b1_raw_no⟩
  all_goals try omega
  all_goals rcases B0 with ⟨b0_0_v00, b0_0_v01, b0_0_v02, b0_0_a, b0_0_b, b0_0_o, b0_0_sa, b0_0_sb, b0_0_so⟩ | ⟨b0_1_v10, b0_1_a, b0_1_b, b0_1_o, b0_1_sa, b0_1_sb, b0_1_so⟩ | ⟨b0_2_v20, b0_2_v21, b0_2_a, b0_2_b, b0_2_o, b0_2_sa, b0_2_sb, b0_2_so⟩ | ⟨b0_3_v30, b0_3_v31, b0_3_a, b0_3_b, b0_3_o, b0_3_sa, b0_3_sb, b0_3_so⟩ | ⟨b0_raw_o, b0_raw_so, b0_raw_no⟩
  all_goals try omega
  all_goals try grind (config := { splits := 4, gen := 12 }) [eq_sz, ne_p_left, ne_p_right, L, R, U, sz]
  all_goals grind (config := { splits := 20, gen := 14 }) [NF, nf_p_no, nf_p_left, nf_p_right, ne_p_left, ne_p_right, eq_sz, redex0_not_nf, redex1_not_nf, redex2_not_nf, redex3_not_nf, Code.r0, Code.r1, Code.r2, Code.r3, L, R, U, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op := op
theorem source_holds (q0 q1 q2 : Carrier) : q0 = (op q1 (op q0 (op q0 (op q1 (op q2 q2))))) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q2.1 q0.2 q1.2 q2.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, CM.source_holds, ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = CM.e at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : CM.e = CM.e := rfl
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) nb)
