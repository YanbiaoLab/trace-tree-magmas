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
  | r0 (v00 v01 v02 v03 v04 : CM) : Code (p v00 (p (p v01 v02) (p v00 (p v03 v00)))) (p (p v04 v04) v00) v04
  | r1 (v10 v11 : CM) : Code (p (p v10 v10) v10) (p (p v11 v11) (p v10 v10)) v11
  | r2 (v20 v21 v22 v23 : CM) : Code (p v20 (p v21 (p v20 (p v22 v20)))) (p (p v23 v23) v20) v23
  | r3 (v30 v31 v32 v33 v34 : CM) : Code (p (p (p v30 v30) v31) (p (p v32 v33) (p (p (p v30 v30) v31) v30))) (p (p v34 v34) (p (p v30 v30) v31)) v34
  | r4 (v40 v41 v42 v43 : CM) : Code (p (p (p v40 v40) v41) (p v42 (p (p (p v40 v40) v41) v40))) (p (p v43 v43) (p (p v40 v40) v41)) v43
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
theorem redex0_not_nf (v00 v01 v02 v03 v04 : CM) :
    ¬ NF (p (p v00 (p (p v01 v02) (p v00 (p v03 v00)))) (p (p v04 v04) v00)) := by
  intro h
  exact h.2.2 ⟨v04, Code.r0 v00 v01 v02 v03 v04⟩

theorem redex1_not_nf (v10 v11 : CM) :
    ¬ NF (p (p (p v10 v10) v10) (p (p v11 v11) (p v10 v10))) := by
  intro h
  exact h.2.2 ⟨v11, Code.r1 v10 v11⟩

theorem redex2_not_nf (v20 v21 v22 v23 : CM) :
    ¬ NF (p (p v20 (p v21 (p v20 (p v22 v20)))) (p (p v23 v23) v20)) := by
  intro h
  exact h.2.2 ⟨v23, Code.r2 v20 v21 v22 v23⟩

theorem redex3_not_nf (v30 v31 v32 v33 v34 : CM) :
    ¬ NF (p (p (p (p v30 v30) v31) (p (p v32 v33) (p (p (p v30 v30) v31) v30))) (p (p v34 v34) (p (p v30 v30) v31))) := by
  intro h
  exact h.2.2 ⟨v34, Code.r3 v30 v31 v32 v33 v34⟩

theorem redex4_not_nf (v40 v41 v42 v43 : CM) :
    ¬ NF (p (p (p (p v40 v40) v41) (p v42 (p (p (p v40 v40) v41) v40))) (p (p v43 v43) (p (p v40 v40) v41))) := by
  intro h
  exact h.2.2 ⟨v43, Code.r4 v40 v41 v42 v43⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact hb.1.1
  | r1 => exact hb.1.1
  | r2 => exact hb.1.1
  | r3 => exact hb.1.1
  | r4 => exact hb.1.1
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
inductive EvalCases : CM → CM → CM → Prop
  | r0 (v00 v01 v02 v03 v04 : CM) : EvalCases (p v00 (p (p v01 v02) (p v00 (p v03 v00)))) (p (p v04 v04) v00) v04
  | r1 (v10 v11 : CM) : EvalCases (p (p v10 v10) v10) (p (p v11 v11) (p v10 v10)) v11
  | r2 (v20 v21 v22 v23 : CM) : EvalCases (p v20 (p v21 (p v20 (p v22 v20)))) (p (p v23 v23) v20) v23
  | r3 (v30 v31 v32 v33 v34 : CM) : EvalCases (p (p (p v30 v30) v31) (p (p v32 v33) (p (p (p v30 v30) v31) v30))) (p (p v34 v34) (p (p v30 v30) v31)) v34
  | r4 (v40 v41 v42 v43 : CM) : EvalCases (p (p (p v40 v40) v41) (p v42 (p (p (p v40 v40) v41) v40))) (p (p v43 v43) (p (p v40 v40) v41)) v43
  | raw {a b : CM} (n : ¬ ∃ q, Code a b q) : EvalCases a b (p a b)
theorem no_code_r0 {v00 v01 v02 v03 v04 : CM} (n : ¬ ∃ q, Code (p v00 (p (p v01 v02) (p v00 (p v03 v00)))) (p (p v04 v04) v00) q) : False := n ⟨_, Code.r0 v00 v01 v02 v03 v04⟩
theorem no_code_r1 {v10 v11 : CM} (n : ¬ ∃ q, Code (p (p v10 v10) v10) (p (p v11 v11) (p v10 v10)) q) : False := n ⟨_, Code.r1 v10 v11⟩
theorem no_code_r2 {v20 v21 v22 v23 : CM} (n : ¬ ∃ q, Code (p v20 (p v21 (p v20 (p v22 v20)))) (p (p v23 v23) v20) q) : False := n ⟨_, Code.r2 v20 v21 v22 v23⟩
theorem no_code_r3 {v30 v31 v32 v33 v34 : CM} (n : ¬ ∃ q, Code (p (p (p v30 v30) v31) (p (p v32 v33) (p (p (p v30 v30) v31) v30))) (p (p v34 v34) (p (p v30 v30) v31)) q) : False := n ⟨_, Code.r3 v30 v31 v32 v33 v34⟩
theorem no_code_r4 {v40 v41 v42 v43 : CM} (n : ¬ ∃ q, Code (p (p (p v40 v40) v41) (p v42 (p (p (p v40 v40) v41) v40))) (p (p v43 v43) (p (p v40 v40) v41)) q) : False := n ⟨_, Code.r4 v40 v41 v42 v43⟩
theorem nf_code_r0 {v00 v01 v02 v03 v04 : CM} (h : NF (p (p v00 (p (p v01 v02) (p v00 (p v03 v00)))) (p (p v04 v04) v00))) : False := redex0_not_nf v00 v01 v02 v03 v04 h
theorem nf_code_r1 {v10 v11 : CM} (h : NF (p (p (p v10 v10) v10) (p (p v11 v11) (p v10 v10)))) : False := redex1_not_nf v10 v11 h
theorem nf_code_r2 {v20 v21 v22 v23 : CM} (h : NF (p (p v20 (p v21 (p v20 (p v22 v20)))) (p (p v23 v23) v20))) : False := redex2_not_nf v20 v21 v22 v23 h
theorem nf_code_r3 {v30 v31 v32 v33 v34 : CM} (h : NF (p (p (p (p v30 v30) v31) (p (p v32 v33) (p (p (p v30 v30) v31) v30))) (p (p v34 v34) (p (p v30 v30) v31)))) : False := redex3_not_nf v30 v31 v32 v33 v34 h
theorem nf_code_r4 {v40 v41 v42 v43 : CM} (h : NF (p (p (p (p v40 v40) v41) (p v42 (p (p (p v40 v40) v41) v40))) (p (p v43 v43) (p (p v40 v40) v41)))) : False := redex4_not_nf v40 v41 v42 v43 h
theorem eval_cases_of_code {a b o : CM} (h : Code a b o) : EvalCases a b o := by
  cases h with
  | r0 => exact .r0 _ _ _ _ _
  | r1 => exact .r1 _ _
  | r2 => exact .r2 _ _ _ _
  | r3 => exact .r3 _ _ _ _ _
  | r4 => exact .r4 _ _ _ _
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact eval_cases_of_code (Classical.choose_spec h)
  · rw [eval_raw h]
    exact .raw h

theorem source_raw (q0 q1 q3 q2 z : CM) (hq0 : NF q0) (hq1 : NF q1) (hq3 : NF q3) (hq2 : NF q2) (hz : NF z) :
    q0 = (eval (eval q1 (eval (eval q3 q2) (eval q1 (eval z q1)))) (eval (eval q0 q0) q1)) := by
  classical
  generalize hE0 : (eval q3 q2) = E0
  generalize hE1 : (eval z q1) = E1
  generalize hE2 : (eval q1 E1) = E2
  generalize hE3 : (eval E0 E2) = E3
  generalize hE4 : (eval q1 E3) = E4
  generalize hE5 : (eval q0 q0) = E5
  generalize hE6 : (eval E5 q1) = E6
  generalize hE7 : (eval E4 E6) = E7
  have B0 : EvalCases q3 q2 E0 := by rw [← hE0]; exact eval_cases q3 q2
  have B1 : EvalCases z q1 E1 := by rw [← hE1]; exact eval_cases z q1
  have B2 : EvalCases q1 E1 E2 := by rw [← hE2]; exact eval_cases q1 E1
  have B3 : EvalCases E0 E2 E3 := by rw [← hE3]; exact eval_cases E0 E2
  have B4 : EvalCases q1 E3 E4 := by rw [← hE4]; exact eval_cases q1 E3
  have B5 : EvalCases q0 q0 E5 := by rw [← hE5]; exact eval_cases q0 q0
  have B6 : EvalCases E5 q1 E6 := by rw [← hE6]; exact eval_cases E5 q1
  have B7 : EvalCases E4 E6 E7 := by rw [← hE7]; exact eval_cases E4 E6
  have Hsrc : Code (p q1 (p (p q3 q2) (p q1 (p z q1)))) (p (p q0 q0) q1) q0 := .r0 q1 q3 q2 z q0
  have N0 : NF E0 := by rw [← hE0]; exact eval_nf (hq3) (hq2)
  have N1 : NF E1 := by rw [← hE1]; exact eval_nf (hz) (hq1)
  have N2 : NF E2 := by rw [← hE2]; exact eval_nf (hq1) (N1)
  have N3 : NF E3 := by rw [← hE3]; exact eval_nf (N0) (N2)
  have N4 : NF E4 := by rw [← hE4]; exact eval_nf (hq1) (N3)
  have N5 : NF E5 := by rw [← hE5]; exact eval_nf (hq0) (hq0)
  have N6 : NF E6 := by rw [← hE6]; exact eval_nf (N5) (hq1)
  have N7 : NF E7 := by rw [← hE7]; exact eval_nf (N4) (N6)
  all_goals cases B7
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B6
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B5
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B4
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B3
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B2
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B1
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals cases B0
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals first | rfl | (simp_all [sz] <;> omega) | omega | grind
  all_goals done
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op a b := op b a
theorem source_holds (q0 q1 q3 q2 z : Carrier) : q0 = (op (op q1 (op (op q3 q2) (op q1 (op z q1)))) (op (op q0 q0) q1)) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q3.1 q2.1 z.1 q0.2 q1.2 q3.2 q2.2 z.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, (fun q0 q1 q2 q3 => ((fun q0 q1 q3 q2 => CM.source_holds q0 q1 q3 q2 q0)) q0 q1 q3 q2), ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = CM.e at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : CM.e = CM.e := rfl
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) nb)
