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
  | r0 (v0 v1 v2 : CM) : Code (p v0 (p v1 v0)) (p (p v2 v2) v0) v2
  | r1 (v0 v1 v2 : CM) : Code (p (p (p v0 v0) v1) v0) (p (p v2 v2) (p (p v0 v0) v1)) v2
def CodeCases (a b o : CM) : Prop := (∃ v0 v1 v2 : CM, a = (p v0 (p v1 v0)) ∧ b = (p (p v2 v2) v0) ∧ o = v2 ∧ sz a = sz (p v0 (p v1 v0)) ∧ sz b = sz (p (p v2 v2) v0) ∧ sz o = sz v2) ∨ (∃ v0 v1 v2 : CM, a = (p (p (p v0 v0) v1) v0) ∧ b = (p (p v2 v2) (p (p v0 v0) v1)) ∧ o = v2 ∧ sz a = sz (p (p (p v0 v0) v1) v0) ∧ sz b = sz (p (p v2 v2) (p (p v0 v0) v1)) ∧ sz o = sz v2) ∨ False
theorem code_cases {a b o : CM} (h : Code a b o) : CodeCases a b o := by
  cases h with
  | r0 => exact Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | r1 => exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩)
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
  | r0 => exact hb.1.1
  | r1 => exact hb.1.1
theorem redex0_not_nf (v0 v1 v2 : CM) :
    ¬ NF (p (p v0 (p v1 v0)) (p (p v2 v2) v0)) := by
  intro h
  exact h.2.2 ⟨v2, Code.r0 v0 v1 v2⟩
theorem redex1_not_nf (v0 v1 v2 : CM) :
    ¬ NF (p (p (p (p v0 v0) v1) v0) (p (p v2 v2) (p (p v0 v0) v1))) := by
  intro h
  exact h.2.2 ⟨v2, Code.r1 v0 v1 v2⟩
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
@[grind unfold] abbrev C0 (v0 v1 v2 : CM) (a b o : CM) : Prop := a = (p v0 (p v1 v0)) ∧ b = (p (p v2 v2) v0) ∧ o = v2 ∧ sz a = sz (p v0 (p v1 v0)) ∧ sz b = sz (p (p v2 v2) v0) ∧ sz o = sz v2
@[grind unfold] abbrev C1 (v0 v1 v2 : CM) (a b o : CM) : Prop := a = (p (p (p v0 v0) v1) v0) ∧ b = (p (p v2 v2) (p (p v0 v0) v1)) ∧ o = v2 ∧ sz a = sz (p (p (p v0 v0) v1) v0) ∧ sz b = sz (p (p v2 v2) (p (p v0 v0) v1)) ∧ sz o = sz v2
inductive EvalCases (a b o : CM) : Prop
  | r0 (v0 v1 v2 : CM) (h : C0 v0 v1 v2 a b o) : EvalCases a b o
  | r1 (v0 v1 v2 : CM) (h : C1 v0 v1 v2 a b o) : EvalCases a b o
  | raw (h : o = p a b ∧ sz o = sz a + sz b + 2) (n : ¬ ∃ q, Code a b q) : EvalCases a b o
theorem eval_cases (a b : CM) : EvalCases a b (eval a b) := by
  by_cases h : ∃ o, Code a b o
  · let o := Classical.choose h
    have hc : Code a b o := Classical.choose_spec h
    have cc := code_cases hc
    have hv : eval a b = o := by rw [eval, dif_pos h]
    rw [hv]
    unfold CodeCases at cc
    rcases cc with cc0 | cc1 | impossible
    · rcases cc0 with ⟨v0, v1, v2, hc0⟩
      exact .r0 v0 v1 v2 hc0
    · rcases cc1 with ⟨v0, v1, v2, hc1⟩
      exact .r1 v0 v1 v2 hc1
    · contradiction
  · exact .raw ⟨eval_raw h, eq_sz (eval_raw h)⟩ h

theorem source_raw (q0 q1 q2 : CM)
    (hq0 : NF q0) (hq1 : NF q1) (hq2 : NF q2) :
    q0 = (eval (eval q1 (eval q2 q1)) (eval (eval q0 q0) q1)) := by
  classical
  generalize H0 : eval q2 q1 = T0
  generalize H1 : eval q1 T0 = T1
  generalize H2 : eval q0 q0 = T2
  generalize H3 : eval T2 q1 = T3
  generalize H4 : eval T1 T3 = T4
  change q0 = T4
  have B0 : EvalCases q2 q1 T0 := by
    rw [← H0]
    exact eval_cases q2 q1
  have B1 : EvalCases q1 T0 T1 := by
    rw [← H1]
    exact eval_cases q1 T0
  have B2 : EvalCases q0 q0 T2 := by
    rw [← H2]
    exact eval_cases q0 q0
  have B3 : EvalCases T2 q1 T3 := by
    rw [← H3]
    exact eval_cases T2 q1
  have B4 : EvalCases T1 T3 T4 := by
    rw [← H4]
    exact eval_cases T1 T3
  have N0 : NF T0 := by
    rw [← H0]
    exact eval_nf hq2 hq1
  have N1 : NF T1 := by
    rw [← H1]
    exact eval_nf hq1 N0
  have N2 : NF T2 := by
    rw [← H2]
    exact eval_nf hq0 hq0
  have N3 : NF T3 := by
    rw [← H3]
    exact eval_nf N2 hq1
  have N4 : NF T4 := by
    rw [← H4]
    exact eval_nf N1 N3
  all_goals rcases B2 with ⟨v2_0_0, v2_0_1, v2_0_2, hc2_0⟩ | ⟨v2_1_0, v2_1_1, v2_1_2, hc2_1⟩ | ⟨hr2, n2⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals rcases B3 with ⟨v3_0_0, v3_0_1, v3_0_2, hc3_0⟩ | ⟨v3_1_0, v3_1_1, v3_1_2, hc3_1⟩ | ⟨hr3, n3⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals rcases B4 with ⟨v4_0_0, v4_0_1, v4_0_2, hc4_0⟩ | ⟨v4_1_0, v4_1_1, v4_1_2, hc4_1⟩ | ⟨hr4, n4⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals rcases B1 with ⟨v1_0_0, v1_0_1, v1_0_2, hc1_0⟩ | ⟨v1_1_0, v1_1_1, v1_1_2, hc1_1⟩ | ⟨hr1, n1⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals rcases B0 with ⟨v0_0_0, v0_0_1, v0_0_2, hc0_0⟩ | ⟨v0_1_0, v0_1_1, v0_1_2, hc0_1⟩ | ⟨hr0, n0⟩
  all_goals try (first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz])
  all_goals first | omega | contradiction | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, sz] | grind (config := { splits := 1, gen := 6 }) [Code.r0, Code.r1, sz] | grind (config := { splits := 1, gen := 6 }) [nf_p_left, nf_p_right, nf_p_no, redex0_not_nf, redex1_not_nf, sz]
def Carrier := {t : CM // NF t}
noncomputable def op (a b : Carrier) : Carrier := ⟨eval a.1 b.1, eval_nf a.2 b.2⟩
noncomputable instance instMagma : Magma Carrier where op := op
theorem source_holds (q0 q1 q2 : Carrier) :
    q0 = (op (op q1 (op q2 q1)) (op (op q0 q0) q1)) := by
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
