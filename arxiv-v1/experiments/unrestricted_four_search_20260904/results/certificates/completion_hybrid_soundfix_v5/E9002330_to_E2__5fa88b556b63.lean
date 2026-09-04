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
  | r0 (v00 v01 v02 v03 v04 : CM) : Code (p v00 (p v01 v01)) (p (p v00 (p (p v01 v02) (p v03 v04))) v00) v01
  | r1 (v10 v11 v12 : CM) : Code (p (p (p v10 v11) (p v12 v12)) (p (p v10 v11) (p v10 v11))) (p v12 (p (p v10 v11) (p v12 v12))) (p v10 v11)
  | r2 (v20 v21 v22 : CM) : Code (p v20 (p v21 v21)) (p (p v20 v22) v20) v21
  | r3 (v30 v31 : CM) : Code (p (p v30 (p v31 v31)) (p v30 v30)) (p v31 (p v30 (p v31 v31))) v30
  | r4 (v40 v41 v42 v43 : CM) : Code (p (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41))) (p v42 v42)) (p (p v40 v41) (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41)))) v42
  | r5 (v50 v51 v52 : CM) : Code (p (p v50 (p v51 v51)) (p v52 v52)) (p v51 (p v50 (p v51 v51))) v52
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
    ¬ NF (p (p v00 (p v01 v01)) (p (p v00 (p (p v01 v02) (p v03 v04))) v00)) := by
  intro h
  exact h.2.2 ⟨v01, Code.r0 v00 v01 v02 v03 v04⟩

theorem redex1_not_nf (v10 v11 v12 : CM) :
    ¬ NF (p (p (p (p v10 v11) (p v12 v12)) (p (p v10 v11) (p v10 v11))) (p v12 (p (p v10 v11) (p v12 v12)))) := by
  intro h
  exact h.2.2 ⟨(p v10 v11), Code.r1 v10 v11 v12⟩

theorem redex2_not_nf (v20 v21 v22 : CM) :
    ¬ NF (p (p v20 (p v21 v21)) (p (p v20 v22) v20)) := by
  intro h
  exact h.2.2 ⟨v21, Code.r2 v20 v21 v22⟩

theorem redex3_not_nf (v30 v31 : CM) :
    ¬ NF (p (p (p v30 (p v31 v31)) (p v30 v30)) (p v31 (p v30 (p v31 v31)))) := by
  intro h
  exact h.2.2 ⟨v30, Code.r3 v30 v31⟩

theorem redex4_not_nf (v40 v41 v42 v43 : CM) :
    ¬ NF (p (p (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41))) (p v42 v42)) (p (p v40 v41) (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41))))) := by
  intro h
  exact h.2.2 ⟨v42, Code.r4 v40 v41 v42 v43⟩

theorem redex5_not_nf (v50 v51 v52 : CM) :
    ¬ NF (p (p (p v50 (p v51 v51)) (p v52 v52)) (p v51 (p v50 (p v51 v51)))) := by
  intro h
  exact h.2.2 ⟨v52, Code.r5 v50 v51 v52⟩


theorem code_nf {a b o : CM} (ha : NF a) (hb : NF b) (h : Code a b o) : NF o := by
  cases h with
  | r0 => exact ha.2.1.1
  | r1 => exact ha.1.1
  | r2 => exact ha.2.1.1
  | r3 => exact ha.1.1
  | r4 => exact ha.2.1.1
  | r5 => exact ha.2.1.1
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
  | r0 (v00 v01 v02 v03 v04 : CM) : EvalCases (p v00 (p v01 v01)) (p (p v00 (p (p v01 v02) (p v03 v04))) v00) v01
  | r1 (v10 v11 v12 : CM) : EvalCases (p (p (p v10 v11) (p v12 v12)) (p (p v10 v11) (p v10 v11))) (p v12 (p (p v10 v11) (p v12 v12))) (p v10 v11)
  | r2 (v20 v21 v22 : CM) : EvalCases (p v20 (p v21 v21)) (p (p v20 v22) v20) v21
  | r3 (v30 v31 : CM) : EvalCases (p (p v30 (p v31 v31)) (p v30 v30)) (p v31 (p v30 (p v31 v31))) v30
  | r4 (v40 v41 v42 v43 : CM) : EvalCases (p (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41))) (p v42 v42)) (p (p v40 v41) (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41)))) v42
  | r5 (v50 v51 v52 : CM) : EvalCases (p (p v50 (p v51 v51)) (p v52 v52)) (p v51 (p v50 (p v51 v51))) v52
  | raw {a b : CM} (n : ¬ ∃ q, Code a b q) : EvalCases a b (p a b)
theorem no_code_r0 {v00 v01 v02 v03 v04 : CM} (n : ¬ ∃ q, Code (p v00 (p v01 v01)) (p (p v00 (p (p v01 v02) (p v03 v04))) v00) q) : False := n ⟨_, Code.r0 v00 v01 v02 v03 v04⟩
theorem no_code_r1 {v10 v11 v12 : CM} (n : ¬ ∃ q, Code (p (p (p v10 v11) (p v12 v12)) (p (p v10 v11) (p v10 v11))) (p v12 (p (p v10 v11) (p v12 v12))) q) : False := n ⟨_, Code.r1 v10 v11 v12⟩
theorem no_code_r2 {v20 v21 v22 : CM} (n : ¬ ∃ q, Code (p v20 (p v21 v21)) (p (p v20 v22) v20) q) : False := n ⟨_, Code.r2 v20 v21 v22⟩
theorem no_code_r3 {v30 v31 : CM} (n : ¬ ∃ q, Code (p (p v30 (p v31 v31)) (p v30 v30)) (p v31 (p v30 (p v31 v31))) q) : False := n ⟨_, Code.r3 v30 v31⟩
theorem no_code_r4 {v40 v41 v42 v43 : CM} (n : ¬ ∃ q, Code (p (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41))) (p v42 v42)) (p (p v40 v41) (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41)))) q) : False := n ⟨_, Code.r4 v40 v41 v42 v43⟩
theorem no_code_r5 {v50 v51 v52 : CM} (n : ¬ ∃ q, Code (p (p v50 (p v51 v51)) (p v52 v52)) (p v51 (p v50 (p v51 v51))) q) : False := n ⟨_, Code.r5 v50 v51 v52⟩
theorem nf_code_r0 {v00 v01 v02 v03 v04 : CM} (h : NF (p (p v00 (p v01 v01)) (p (p v00 (p (p v01 v02) (p v03 v04))) v00))) : False := redex0_not_nf v00 v01 v02 v03 v04 h
theorem nf_code_r1 {v10 v11 v12 : CM} (h : NF (p (p (p (p v10 v11) (p v12 v12)) (p (p v10 v11) (p v10 v11))) (p v12 (p (p v10 v11) (p v12 v12))))) : False := redex1_not_nf v10 v11 v12 h
theorem nf_code_r2 {v20 v21 v22 : CM} (h : NF (p (p v20 (p v21 v21)) (p (p v20 v22) v20))) : False := redex2_not_nf v20 v21 v22 h
theorem nf_code_r3 {v30 v31 : CM} (h : NF (p (p (p v30 (p v31 v31)) (p v30 v30)) (p v31 (p v30 (p v31 v31))))) : False := redex3_not_nf v30 v31 h
theorem nf_code_r4 {v40 v41 v42 v43 : CM} (h : NF (p (p (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41))) (p v42 v42)) (p (p v40 v41) (p (p (p v40 v41) (p (p v42 v43) (p v42 v43))) (p (p v40 v41) (p v40 v41)))))) : False := redex4_not_nf v40 v41 v42 v43 h
theorem nf_code_r5 {v50 v51 v52 : CM} (h : NF (p (p (p v50 (p v51 v51)) (p v52 v52)) (p v51 (p v50 (p v51 v51))))) : False := redex5_not_nf v50 v51 v52 h
theorem eval_cases_of_code {a b o : CM} (h : Code a b o) : EvalCases a b o := by
  cases h with
  | r0 => exact .r0 _ _ _ _ _
  | r1 => exact .r1 _ _ _
  | r2 => exact .r2 _ _ _
  | r3 => exact .r3 _ _
  | r4 => exact .r4 _ _ _ _
  | r5 => exact .r5 _ _ _
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · rw [eval, dif_pos h]
    exact eval_cases_of_code (Classical.choose_spec h)
  · rw [eval_raw h]
    exact .raw h

theorem source_raw (q0 q1 q2 z q3 : CM) (hq0 : NF q0) (hq1 : NF q1) (hq2 : NF q2) (hz : NF z) (hq3 : NF q3) :
    q0 = (eval (eval q1 (eval q0 q0)) (eval (eval q1 (eval (eval q0 q2) (eval z q3))) q1)) := by
  classical
  generalize hE0 : (eval q0 q0) = E0
  generalize hE1 : (eval q1 E0) = E1
  generalize hE2 : (eval q0 q2) = E2
  generalize hE3 : (eval z q3) = E3
  generalize hE4 : (eval E2 E3) = E4
  generalize hE5 : (eval q1 E4) = E5
  generalize hE6 : (eval E5 q1) = E6
  generalize hE7 : (eval E1 E6) = E7
  have B0 : EvalCases q0 q0 E0 := by rw [← hE0]; exact eval_cases q0 q0
  have B1 : EvalCases q1 E0 E1 := by rw [← hE1]; exact eval_cases q1 E0
  have B2 : EvalCases q0 q2 E2 := by rw [← hE2]; exact eval_cases q0 q2
  have B3 : EvalCases z q3 E3 := by rw [← hE3]; exact eval_cases z q3
  have B4 : EvalCases E2 E3 E4 := by rw [← hE4]; exact eval_cases E2 E3
  have B5 : EvalCases q1 E4 E5 := by rw [← hE5]; exact eval_cases q1 E4
  have B6 : EvalCases E5 q1 E6 := by rw [← hE6]; exact eval_cases E5 q1
  have B7 : EvalCases E1 E6 E7 := by rw [← hE7]; exact eval_cases E1 E6
  have Hsrc : Code (p q1 (p q0 q0)) (p (p q1 (p (p q0 q2) (p z q3))) q1) q0 := .r0 q1 q0 q2 z q3
  have N0 : NF E0 := by rw [← hE0]; exact eval_nf (hq0) (hq0)
  have N1 : NF E1 := by rw [← hE1]; exact eval_nf (hq1) (N0)
  have N2 : NF E2 := by rw [← hE2]; exact eval_nf (hq0) (hq2)
  have N3 : NF E3 := by rw [← hE3]; exact eval_nf (hz) (hq3)
  have N4 : NF E4 := by rw [← hE4]; exact eval_nf (N2) (N3)
  have N5 : NF E5 := by rw [← hE5]; exact eval_nf (hq1) (N4)
  have N6 : NF E6 := by rw [← hE6]; exact eval_nf (N5) (hq1)
  have N7 : NF E7 := by rw [← hE7]; exact eval_nf (N1) (N6)
  all_goals cases B7
  all_goals first
  | exfalso; apply no_code_r0 <;> assumption
  | exfalso; apply no_code_r1 <;> assumption
  | exfalso; apply no_code_r2 <;> assumption
  | exfalso; apply no_code_r3 <;> assumption
  | exfalso; apply no_code_r4 <;> assumption
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
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
  | exfalso; apply no_code_r5 <;> assumption
  | exfalso; apply nf_code_r0 <;> assumption
  | exfalso; apply nf_code_r1 <;> assumption
  | exfalso; apply nf_code_r2 <;> assumption
  | exfalso; apply nf_code_r3 <;> assumption
  | exfalso; apply nf_code_r4 <;> assumption
  | exfalso; apply nf_code_r5 <;> assumption
  | rfl
  | (simp_all [sz] <;> omega)
  | omega
  | skip
  all_goals first | rfl | (simp_all [sz] <;> omega) | omega | grind
  all_goals done
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagmaNF : Magma Carrier where op := op
theorem source_holds (q0 q1 q2 z q3 : Carrier) : q0 = (op (op q1 (op q0 q0)) (op (op q1 (op (op q0 q2) (op z q3))) q1)) := by
  apply Subtype.ext
  exact source_raw q0.1 q1.1 q2.1 z.1 q3.1 q0.2 q1.2 q2.2 z.2 q3.2
def ce : Carrier := ⟨e, by simp [NF]⟩
def ck (a : Carrier) : Carrier := ⟨k a.1, by simpa [NF] using a.2⟩
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM.Carrier, CM.instMagmaNF, (fun q0 q1 q2 q3 => CM.source_holds q0 q1 q2 q0 q3), ?_⟩
  intro target
  have bad := congrArg Subtype.val (target (ck ce) ce)
  change (CM.k CM.e) = CM.e at bad
  have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
  have hr : CM.e = CM.e := rfl
  have nb := hl.symm.trans (bad.trans hr)
  exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) nb)
