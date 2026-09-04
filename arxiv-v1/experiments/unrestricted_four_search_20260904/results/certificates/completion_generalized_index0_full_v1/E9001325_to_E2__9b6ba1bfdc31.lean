import JudgeProblem
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
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
  | r0 (v00 v01 v02 v03 v04 : CM) : Code (p (p v00 (p v01 v02)) (p v03 v03)) (p v04 (p v03 (p v03 v03))) v04
  | r1 (v10 v11 : CM) : Code (p v10 (p v10 v10)) (p v11 (p (p v10 (p v10 v10)) (p (p v10 (p v10 v10)) (p v10 (p v10 v10))))) v11
  | r2 (v20 v21 v22 : CM) : Code (p v20 (p v21 v21)) (p v22 (p v21 (p v21 v21))) v22
  | r3 (v30 v31 v32 v33 v34 : CM) : Code (p (p v30 (p v31 v32)) (p (p v33 (p v33 v33)) (p v33 (p v33 v33)))) (p v34 (p v33 (p v33 v33))) v34
  | r4 (v40 v41 v42 v43 v44 : CM) : Code (p (p v40 (p v41 v42)) (p (p v40 (p v41 v42)) (p v40 (p v41 v42)))) (p v43 (p v44 (p v44 v44))) v43
  | r5 (v50 v51 v52 : CM) : Code (p v50 (p (p v51 (p v51 v51)) (p v51 (p v51 v51)))) (p v52 (p v51 (p v51 v51))) v52
  | r6 (v60 v61 v62 : CM) : Code (p v60 (p v60 v60)) (p v61 (p v62 (p v62 v62))) v61
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
    ¬ NF (p (p (p v00 (p v01 v02)) (p v03 v03)) (p v04 (p v03 (p v03 v03)))) := by
  intro h
  exact h.2.2 ⟨v04, Code.r0 v00 v01 v02 v03 v04⟩

theorem redex1_not_nf (v10 v11 : CM) :
    ¬ NF (p (p v10 (p v10 v10)) (p v11 (p (p v10 (p v10 v10)) (p (p v10 (p v10 v10)) (p v10 (p v10 v10)))))) := by
  intro h
  exact h.2.2 ⟨v11, Code.r1 v10 v11⟩

theorem redex2_not_nf (v20 v21 v22 : CM) :
    ¬ NF (p (p v20 (p v21 v21)) (p v22 (p v21 (p v21 v21)))) := by
  intro h
  exact h.2.2 ⟨v22, Code.r2 v20 v21 v22⟩

theorem redex3_not_nf (v30 v31 v32 v33 v34 : CM) :
    ¬ NF (p (p (p v30 (p v31 v32)) (p (p v33 (p v33 v33)) (p v33 (p v33 v33)))) (p v34 (p v33 (p v33 v33)))) := by
  intro h
  exact h.2.2 ⟨v34, Code.r3 v30 v31 v32 v33 v34⟩

theorem redex4_not_nf (v40 v41 v42 v43 v44 : CM) :
    ¬ NF (p (p (p v40 (p v41 v42)) (p (p v40 (p v41 v42)) (p v40 (p v41 v42)))) (p v43 (p v44 (p v44 v44)))) := by
  intro h
  exact h.2.2 ⟨v43, Code.r4 v40 v41 v42 v43 v44⟩

theorem redex5_not_nf (v50 v51 v52 : CM) :
    ¬ NF (p (p v50 (p (p v51 (p v51 v51)) (p v51 (p v51 v51)))) (p v52 (p v51 (p v51 v51)))) := by
  intro h
  exact h.2.2 ⟨v52, Code.r5 v50 v51 v52⟩

theorem redex6_not_nf (v60 v61 v62 : CM) :
    ¬ NF (p (p v60 (p v60 v60)) (p v61 (p v62 (p v62 v62)))) := by
  intro h
  exact h.2.2 ⟨v61, Code.r6 v60 v61 v62⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact hb.1
  | r1 => exact hb.1
  | r2 => exact hb.1
  | r3 => exact hb.1
  | r4 => exact hb.1
  | r5 => exact hb.1
  | r6 => exact hb.1
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
  | r0 (v00 v01 v02 v03 v04 : CM) : EvalCases (p (p v00 (p v01 v02)) (p v03 v03)) (p v04 (p v03 (p v03 v03))) v04
  | r1 (v10 v11 : CM) : EvalCases (p v10 (p v10 v10)) (p v11 (p (p v10 (p v10 v10)) (p (p v10 (p v10 v10)) (p v10 (p v10 v10))))) v11
  | r2 (v20 v21 v22 : CM) : EvalCases (p v20 (p v21 v21)) (p v22 (p v21 (p v21 v21))) v22
  | r3 (v30 v31 v32 v33 v34 : CM) : EvalCases (p (p v30 (p v31 v32)) (p (p v33 (p v33 v33)) (p v33 (p v33 v33)))) (p v34 (p v33 (p v33 v33))) v34
  | r4 (v40 v41 v42 v43 v44 : CM) : EvalCases (p (p v40 (p v41 v42)) (p (p v40 (p v41 v42)) (p v40 (p v41 v42)))) (p v43 (p v44 (p v44 v44))) v43
  | r5 (v50 v51 v52 : CM) : EvalCases (p v50 (p (p v51 (p v51 v51)) (p v51 (p v51 v51)))) (p v52 (p v51 (p v51 v51))) v52
  | r6 (v60 v61 v62 : CM) : EvalCases (p v60 (p v60 v60)) (p v61 (p v62 (p v62 v62))) v61
  | raw {a b : CM} (n : ¬ ∃ q, Code a b q) : EvalCases a b (p a b)
theorem no_code_r0 {v00 v01 v02 v03 v04 : CM} (n : ¬ ∃ q, Code (p (p v00 (p v01 v02)) (p v03 v03)) (p v04 (p v03 (p v03 v03))) q) : False := n ⟨_, Code.r0 v00 v01 v02 v03 v04⟩
theorem no_code_r1 {v10 v11 : CM} (n : ¬ ∃ q, Code (p v10 (p v10 v10)) (p v11 (p (p v10 (p v10 v10)) (p (p v10 (p v10 v10)) (p v10 (p v10 v10))))) q) : False := n ⟨_, Code.r1 v10 v11⟩
theorem no_code_r2 {v20 v21 v22 : CM} (n : ¬ ∃ q, Code (p v20 (p v21 v21)) (p v22 (p v21 (p v21 v21))) q) : False := n ⟨_, Code.r2 v20 v21 v22⟩
theorem no_code_r3 {v30 v31 v32 v33 v34 : CM} (n : ¬ ∃ q, Code (p (p v30 (p v31 v32)) (p (p v33 (p v33 v33)) (p v33 (p v33 v33)))) (p v34 (p v33 (p v33 v33))) q) : False := n ⟨_, Code.r3 v30 v31 v32 v33 v34⟩
theorem no_code_r4 {v40 v41 v42 v43 v44 : CM} (n : ¬ ∃ q, Code (p (p v40 (p v41 v42)) (p (p v40 (p v41 v42)) (p v40 (p v41 v42)))) (p v43 (p v44 (p v44 v44))) q) : False := n ⟨_, Code.r4 v40 v41 v42 v43 v44⟩
theorem no_code_r5 {v50 v51 v52 : CM} (n : ¬ ∃ q, Code (p v50 (p (p v51 (p v51 v51)) (p v51 (p v51 v51)))) (p v52 (p v51 (p v51 v51))) q) : False := n ⟨_, Code.r5 v50 v51 v52⟩
theorem no_code_r6 {v60 v61 v62 : CM} (n : ¬ ∃ q, Code (p v60 (p v60 v60)) (p v61 (p v62 (p v62 v62))) q) : False := n ⟨_, Code.r6 v60 v61 v62⟩
theorem nf_code_r0 {v00 v01 v02 v03 v04 : CM} (h : NF (p (p (p v00 (p v01 v02)) (p v03 v03)) (p v04 (p v03 (p v03 v03))))) : False := redex0_not_nf v00 v01 v02 v03 v04 h
theorem nf_code_r1 {v10 v11 : CM} (h : NF (p (p v10 (p v10 v10)) (p v11 (p (p v10 (p v10 v10)) (p (p v10 (p v10 v10)) (p v10 (p v10 v10))))))) : False := redex1_not_nf v10 v11 h
theorem nf_code_r2 {v20 v21 v22 : CM} (h : NF (p (p v20 (p v21 v21)) (p v22 (p v21 (p v21 v21))))) : False := redex2_not_nf v20 v21 v22 h
theorem nf_code_r3 {v30 v31 v32 v33 v34 : CM} (h : NF (p (p (p v30 (p v31 v32)) (p (p v33 (p v33 v33)) (p v33 (p v33 v33)))) (p v34 (p v33 (p v33 v33))))) : False := redex3_not_nf v30 v31 v32 v33 v34 h
theorem nf_code_r4 {v40 v41 v42 v43 v44 : CM} (h : NF (p (p (p v40 (p v41 v42)) (p (p v40 (p v41 v42)) (p v40 (p v41 v42)))) (p v43 (p v44 (p v44 v44))))) : False := redex4_not_nf v40 v41 v42 v43 v44 h
theorem nf_code_r5 {v50 v51 v52 : CM} (h : NF (p (p v50 (p (p v51 (p v51 v51)) (p v51 (p v51 v51)))) (p v52 (p v51 (p v51 v51))))) : False := redex5_not_nf v50 v51 v52 h
theorem nf_code_r6 {v60 v61 v62 : CM} (h : NF (p (p v60 (p v60 v60)) (p v61 (p v62 (p v62 v62))))) : False := redex6_not_nf v60 v61 v62 h
theorem eval_cases_of_code {a b o : CM} (h : Code a b o) : EvalCases a b o := by
  cases h with
  | r0 => exact .r0 _ _ _ _ _
  | r1 => exact .r1 _ _
  | r2 => exact .r2 _ _ _
  | r3 => exact .r3 _ _ _ _ _
  | r4 => exact .r4 _ _ _ _ _
  | r5 => exact .r5 _ _ _
  | r6 => exact .r6 _ _ _
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact eval_cases_of_code (Classical.choose_spec h)
  · rw [eval_raw h]
    exact .raw h

theorem source_raw (q0 z q3 q2 q1 : CM) (hq0 : NF q0) (hz : NF z) (hq3 : NF q3) (hq2 : NF q2) (hq1 : NF q1) :
    q0 = (eval (eval (eval z (eval q3 q2)) (eval q1 q1)) (eval q0 (eval q1 (eval q1 q1)))) := by
  classical
  generalize hE0 : (eval q3 q2) = E0
  generalize hE1 : (eval z E0) = E1
  generalize hE2 : (eval q1 q1) = E2
  generalize hE3 : (eval E1 E2) = E3
  generalize hE4 : (eval q1 q1) = E4
  generalize hE5 : (eval q1 E2) = E5
  generalize hE6 : (eval q0 E5) = E6
  generalize hE7 : (eval E3 E6) = E7
  have B0 : EvalCases q3 q2 E0 := by rw [← hE0]; exact eval_cases q3 q2
  have B1 : EvalCases z E0 E1 := by rw [← hE1]; exact eval_cases z E0
  have B2 : EvalCases q1 q1 E2 := by rw [← hE2]; exact eval_cases q1 q1
  have B3 : EvalCases E1 E2 E3 := by rw [← hE3]; exact eval_cases E1 E2
  have B4 : EvalCases q1 q1 E4 := by rw [← hE4]; exact eval_cases q1 q1
  have B5 : EvalCases q1 E2 E5 := by rw [← hE5]; exact eval_cases q1 E2
  have B6 : EvalCases q0 E5 E6 := by rw [← hE6]; exact eval_cases q0 E5
  have B7 : EvalCases E3 E6 E7 := by rw [← hE7]; exact eval_cases E3 E6
  have Hsrc : Code (p (p z (p q3 q2)) (p q1 q1)) (p q0 (p q1 (p q1 q1))) q0 := .r0 z q3 q2 q1 q0
  have N0 : NF E0 := by rw [← hE0]; exact eval_nf (hq3) (hq2)
  have N1 : NF E1 := by rw [← hE1]; exact eval_nf (hz) (N0)
  have N2 : NF E2 := by rw [← hE2]; exact eval_nf (hq1) (hq1)
  have N3 : NF E3 := by rw [← hE3]; exact eval_nf (N1) (N2)
  have N4 : NF E4 := by rw [← hE4]; exact eval_nf (hq1) (hq1)
  have N5 : NF E5 := by rw [← hE5]; exact eval_nf (hq1) (N2)
  have N6 : NF E6 := by rw [← hE6]; exact eval_nf (hq0) (N5)
  have N7 : NF E7 := by rw [← hE7]; exact eval_nf (N3) (N6)
  all_goals cases B6
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B7
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B5
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B4
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B3
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B2
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B1
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals cases B0
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply no_code_r6 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | exfalso; apply nf_code_r6 <;> assumption
  | rfl
  | omega
  | skip
  all_goals first | rfl | omega | grind
  all_goals done
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op a b := op b a
theorem source_holds (q0 z q3 q2 q1 : Carrier) : q0 = (op (op (op z (op q3 q2)) (op q1 q1)) (op q0 (op q1 (op q1 q1)))) := by
  apply Subtype.ext
  exact source_raw q0.1 z.1 q3.1 q2.1 q1.1 q0.2 z.2 q3.2 q2.2 q1.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, (fun q0 q1 q2 q3 => ((fun q0 q1 q3 q2 => CM.source_holds q0 q1 q3 q2 q1)) q0 q1 q3 q2), ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = CM.e at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : CM.e = CM.e := rfl
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) nb)
