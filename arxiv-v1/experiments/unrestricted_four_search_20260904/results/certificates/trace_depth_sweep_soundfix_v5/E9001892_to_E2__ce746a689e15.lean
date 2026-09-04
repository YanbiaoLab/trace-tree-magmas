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
  | law (x v0 v1 v2 H0 H1 : CM)
      (s0 : Step v0 v1 H0)
      (s1 : Step v2 v0 H1) :
      Code (p H0 (p x x)) (p (p (p v0 v0) H1) v0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_v2 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_v2 q_v0 q_H1 ∧ a = (p q_H0 (p q_x q_x)) ∧ b = (p (p (p q_v0 q_v0) q_H1) q_v0) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 v2 H0 H1 s0 s1 => ⟨x, v0, v1, v2, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc)
    omega

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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p q_v0 q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at e2
      have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := (let peq0 : v = (p q_v0 q_v1) := e0; let peq2 : v = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := e2; let pst0 : (p q_v0 q_v1) = v := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v2 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v2 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = (p q_v0 q_v1) at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_x) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p (p q_v0 q_v0) q_H1) q_v0) at e2
      have cyc : q_v0 = (p (p q_v0 q_v0) q_H1) := (let peq0 : v = (p q_v0 q_v1) := e0; let peq2 : v = (p (p (p q_v0 q_v0) q_H1) q_v0) := e2; let pst0 : (p q_v0 q_v1) = v := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); pst2)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H1)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have p0 := congrArg (fun q => (L q)) (ha)
      change v = q_H0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change k = (p q_x q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3
      omega
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have p0 := congrArg (fun q => (L q)) (ha)
      change v = q_H0 at p0
      have z0 := congrArg sz p0
      have p1 := congrArg (fun q => (R q)) (ha)
      change k = (p q_x q_x) at p1
      have z1 := congrArg sz p1
      have p2 := hb
      change v = (p (p (p q_v0 q_v0) q_H1) q_v0) at p2
      have z2 := congrArg sz p2
      have p3 := ho
      change o = q_x at p3
      have z3 := congrArg sz p3
      simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3
      omega
theorem nr0 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_v0 q_v1) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at e1
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = (p (p q_v0 q_v1) (p q_x q_x)) := e0; let peq1 : x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := e1; let pst0 : (p (p q_v0 q_v1) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v1) (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v1) = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => L q) (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change x = (p (p q_v0 q_v1) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change x = (p (p (p q_v0 q_v0) q_H1) q_v0) at e1
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : x = (p (p q_v0 q_v1) (p q_x q_x)) := e0; let peq1 : x = (p (p (p q_v0 q_v0) q_H1) q_v0) := e1; let pst0 : (p (p q_v0 q_v1) (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v1) (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v1) = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => L q) (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst39); let pst41 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst42 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst43 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst41) (pst42); let pst44 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst43); let pst45 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst44); let pst46 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst47 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst48 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst46) (pst47); let pst49 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst48); let pst50 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst49); let pst51 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst45) (pst50); let pst52 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst51); let pst53 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst52); let pst54 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst53); let pst55 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst40) (pst54); let pst56 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst55); let pst57 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst56); let pst58 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst57) (peq5); let pst59 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst58); pst59)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst39); let pst41 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst42 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst43 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst41) (pst42); let pst44 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst43); let pst45 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst44); let pst46 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst47 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst48 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst46) (pst47); let pst49 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst48); let pst50 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst49); let pst51 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst45) (pst50); let pst52 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst51); let pst53 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst52); let pst54 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst53); let pst55 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst40) (pst54); let pst56 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst55); let pst57 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst56); let pst58 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst57) (peq5); let pst59 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst58); pst59)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst25); let pst27 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst28 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst30 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst29); let pst31 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst28) (pst30); let pst32 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst31); let pst33 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst32); let pst34 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst33); let pst35 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst26) (pst34); let pst36 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst35); let pst37 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst36); let pst38 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst37) (peq5); let pst39 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst38); pst39)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst25); let pst27 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst28 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst30 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst29); let pst31 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst28) (pst30); let pst32 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst31); let pst33 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst32); let pst34 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst33); let pst35 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst26) (pst34); let pst36 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst35); let pst37 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst36); let pst38 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst37) (peq5); let pst39 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst38); pst39)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst39); let pst41 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst40); let pst42 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst41); let pst43 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst42) (peq5); let pst44 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst43); pst44)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst39); let pst41 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst40); let pst42 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst41); let pst43 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst42) (peq5); let pst44 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst43); pst44)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst25); let pst27 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst26); let pst28 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst27); let pst29 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst28) (peq5); let pst30 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst29); pst30)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : x = (p q_H0 (p q_x q_x)) := ha; let peq1 : x = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = x := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst25); let pst27 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst26); let pst28 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst27); let pst29 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst28) (peq5); let pst30 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst29); pst30)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 v2 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code H0 (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p q_v0 q_v1) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x q_x) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) (p q_v2 q_v0)) at e2
        have e3 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := (let peq2 : x = (p (p q_v0 q_v0) (p q_v2 q_v0)) := e2; let peq3 : x = q_v0 := e3; let pst0 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = x := Eq.symm (peq2); let pst1 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v2 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v2 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = (p q_v0 q_v1) at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x q_x) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) q_H1) at e2
        have e3 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 q_v0) q_H1) := (let peq2 : x = (p (p q_v0 q_v0) q_H1) := e2; let peq3 : x = q_v0 := e3; let pst0 : (p (p q_v0 q_v0) q_H1) = x := Eq.symm (peq2); let pst1 : (p (p q_v0 q_v0) q_H1) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p q_v0 q_v0) q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_H0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x q_x) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) (p q_v2 q_v0)) at e2
        have e3 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := (let peq2 : x = (p (p q_v0 q_v0) (p q_v2 q_v0)) := e2; let peq3 : x = q_v0 := e3; let pst0 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = x := Eq.symm (peq2); let pst1 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v2 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v2 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_H0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x q_x) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) q_H1) at e2
        have e3 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p (p q_v0 q_v0) q_H1) := (let peq2 : x = (p (p q_v0 q_v0) q_H1) := e2; let peq3 : x = q_v0 := e3; let pst0 : (p (p q_v0 q_v0) q_H1) = x := Eq.symm (peq2); let pst1 : (p (p q_v0 q_v0) q_H1) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p (p q_v0 q_v0) q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H0 = (p (p q_v0 q_v1) (p q_x q_x)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) (p q_v2 q_v0)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := (let peq1 : x = (p (p q_v0 q_v0) (p q_v2 q_v0)) := e1; let peq2 : x = q_v0 := e2; let pst0 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = x := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v2 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v2 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H0 = (p (p q_v0 q_v1) (p q_x q_x)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) q_H1) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_v0) q_H1) := (let peq1 : x = (p (p q_v0 q_v0) q_H1) := e1; let peq2 : x = q_v0 := e2; let pst0 : (p (p q_v0 q_v0) q_H1) = x := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v0) q_H1) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_v0) q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change H0 = (p q_H0 (p q_x q_x)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) (p q_v2 q_v0)) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := (let peq1 : x = (p (p q_v0 q_v0) (p q_v2 q_v0)) := e1; let peq2 : x = q_v0 := e2; let pst0 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = x := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) (p q_v2 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v2 q_v0))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change H0 = (p q_H0 (p q_x q_x)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = (p (p q_v0 q_v0) q_H1) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = q_v0 at e2
        have cyc : q_v0 = (p (p q_v0 q_v0) q_H1) := (let peq1 : x = (p (p q_v0 q_v0) q_H1) := e1; let peq2 : x = q_v0 := e2; let pst0 : (p (p q_v0 q_v0) q_H1) = x := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v0) q_H1) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p (p q_v0 q_v0) q_H1) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_H1) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 v2 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p q_v0 q_v1) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at e1
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p (p q_v0 q_v1) (p q_x q_x)) := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := e1; let pst0 : (p (p q_v0 q_v1) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v1) (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v1) = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => L q) (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = (p (p q_v0 q_v1) (p q_x q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) at e1
      have cyc : q_v0 = (p q_v0 q_v0) := (let peq0 : v0 = (p (p q_v0 q_v1) (p q_x q_x)) := e0; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := e1; let pst0 : (p (p q_v0 q_v1) (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v1) (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : (p q_v0 q_v1) = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = (p q_v0 q_v0) := congrArg (fun q => L q) (pst2); pst3)
      have hlt : sz q_v0 < sz (p q_v0 q_v0) := sz_lt_p_left q_v0 q_v0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst39); let pst41 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst42 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst43 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst41) (pst42); let pst44 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst43); let pst45 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst44); let pst46 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst47 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst48 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst46) (pst47); let pst49 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst48); let pst50 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst49); let pst51 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst45) (pst50); let pst52 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst51); let pst53 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst52); let pst54 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst53); let pst55 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst40) (pst54); let pst56 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst55); let pst57 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst56); let pst58 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst57) (peq5); let pst59 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst58); pst59)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst39); let pst41 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst42 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst43 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst41) (pst42); let pst44 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst43); let pst45 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst44); let pst46 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst47 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst48 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst46) (pst47); let pst49 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst48); let pst50 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst49); let pst51 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst45) (pst50); let pst52 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst51); let pst53 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst52); let pst54 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst53); let pst55 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst40) (pst54); let pst56 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst55); let pst57 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst56); let pst58 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst57) (peq5); let pst59 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst58); pst59)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst25); let pst27 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst28 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst30 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst29); let pst31 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst28) (pst30); let pst32 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst31); let pst33 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst32); let pst34 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst33); let pst35 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst26) (pst34); let pst36 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst35); let pst37 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst36); let pst38 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst37) (peq5); let pst39 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst38); pst39)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) (p q_v2 q_v0)) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst25); let pst27 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst28 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst30 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst29); let pst31 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst28) (pst30); let pst32 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst31); let pst33 : (p q_v2 q_v0) = (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p q_v2 q) (pst32); let pst34 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := congrArg (fun q => p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q) (pst33); let pst35 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst26) (pst34); let pst36 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.trans (pst2) (pst35); let pst37 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = q_H0 := Eq.symm (pst36); let pst38 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) = u0_x := Eq.trans (pst37) (peq5); let pst39 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Eq.symm (pst38); pst39)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) (p q_v2 (p (p u0_x u0_x) (p u0_x u0_x))))
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst39); let pst41 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst40); let pst42 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst41); let pst43 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst42) (peq5); let pst44 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst43); pst44)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p (p u0_v0 u0_v1) (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst6); let pst8 : (p u0_v0 u0_v1) = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : u0_v0 = u0_x := congrArg (fun q => L q) (pst10); let pst12 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : u0_v1 = u0_x := congrArg (fun q => R q) (pst10); let pst14 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst15 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst12) (pst14); let pst16 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst15); let pst17 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst16); let pst18 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst19 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst20 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst18) (pst19); let pst21 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst20); let pst22 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst21); let pst23 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst17) (pst22); let pst24 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst24); let pst26 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst27 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst28 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst26) (pst27); let pst29 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst28); let pst30 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst29); let pst31 : (p u0_v0 u0_v1) = (p u0_x u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst32 : (p u0_x u0_v1) = (p u0_x u0_x) := congrArg (fun q => p u0_x q) (pst13); let pst33 : (p u0_v0 u0_v1) = (p u0_x u0_x) := Eq.trans (pst31) (pst32); let pst34 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst33); let pst35 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst34); let pst36 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst30) (pst35); let pst37 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst36); let pst38 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst25) (pst38); let pst40 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst39); let pst41 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst40); let pst42 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst41); let pst43 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst42) (peq5); let pst44 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst43); pst44)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        let u0s1out := u0_H1
        cases u0s1 with
        | raw =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst25); let pst27 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst26); let pst28 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst27); let pst29 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst28) (peq5); let pst30 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst29); pst30)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s1h =>
          have cyc : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := (let peq0 : v0 = (p q_H0 (p q_x q_x)) := ha; let peq1 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := hb; let peq3 : q_v0 = (p u0s0out (p u0_x u0_x)) := u0a; let peq5 : q_H0 = u0_x := u0o; let pst0 : (p q_H0 (p q_x q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_x q_x)) = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = (p (p q_v0 q_v0) q_H1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_x q_x) := Eq.symm (pst3); let pst5 : (p q_x q_x) = q_v0 := Eq.symm (pst4); let pst6 : (p q_x q_x) = (p u0s0out (p u0_x u0_x)) := Eq.trans (pst5) (peq3); let pst7 : q_x = u0s0out := congrArg (fun q => L q) (pst6); let pst8 : u0s0out = q_x := Eq.symm (pst7); let pst9 : q_x = (p u0_x u0_x) := congrArg (fun q => R q) (pst6); let pst10 : u0s0out = (p u0_x u0_x) := Eq.trans (pst8) (pst9); let pst11 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst12 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst14 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst13); let pst15 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst12) (pst14); let pst16 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst15); let pst17 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst19 : (p q_x q_x) = (p (p u0_x u0_x) q_x) := congrArg (fun q => p q q_x) (pst18); let pst20 : q_x = (p u0_x u0_x) := Eq.trans (pst7) (pst10); let pst21 : (p (p u0_x u0_x) q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := congrArg (fun q => p (p u0_x u0_x) q) (pst20); let pst22 : (p q_x q_x) = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p (p u0_x u0_x) (p u0_x u0_x)) := Eq.trans (pst4) (pst22); let pst24 : (p (p (p u0_x u0_x) (p u0_x u0_x)) q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := congrArg (fun q => p (p (p u0_x u0_x) (p u0_x u0_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) := Eq.trans (pst17) (pst24); let pst26 : (p (p q_v0 q_v0) q_H1) = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := congrArg (fun q => p q q_H1) (pst25); let pst27 : q_H0 = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.trans (pst2) (pst26); let pst28 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = q_H0 := Eq.symm (pst27); let pst29 : (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) = u0_x := Eq.trans (pst28) (peq5); let pst30 : u0_x = (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Eq.symm (pst29); pst30)
          have hlt : sz u0_x < sz (p (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_x u0_x) (sz_lt_p_left (p u0_x u0_x) (p u0_x u0_x))) (sz_lt_p_left (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x)))) (sz_lt_p_left (p (p (p u0_x u0_x) (p u0_x u0_x)) (p (p u0_x u0_x) (p u0_x u0_x))) q_H1)
          exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 v2 H1 : CM)
    (s1 : Step v2 v0 H1) :
    ¬ ∃ o, Code (p v0 v0) H1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s1 with
  | raw =>
    have he : q_H0 = q_v0 := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq3 : v0 = q_v0 := congrArg (fun q => (R q)) (hb); let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = q_v0 := Eq.trans (pst3) (peq3); let pst5 : q_v0 = (p q_x q_x) := Eq.symm (pst4); let pst6 : (p q_x q_x) = q_v0 := Eq.symm (pst5); let pst7 : q_H0 = q_v0 := Eq.trans (pst1) (pst6); pst7)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s1h =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_x q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : q_v1 = q_x := congrArg (fun q => R q) (pst1); let pst5 : (p q_x q_v1) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst4); let pst6 : (p q_v0 q_v1) = (p q_x q_x) := Eq.trans (pst3) (pst5); let pst7 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst6); let pst8 : (p q_x q_x) = v0 := Eq.symm (pst7); let pst9 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst8) (peq5); let pst10 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst9); let pst11 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst10); let pst12 : q_x = u0_v0 := congrArg (fun q => R q) (pst9); let pst13 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst11) (pst12); let pst14 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst13); pst14)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_v2, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) (p u0_v2 u0_v0)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) (p u0_v2 u0_v0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := (let peq0 : v0 = q_H0 := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_x q_x) := congrArg (fun q => (R q)) (ha); let peq5 : v0 = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := u0b; let pst0 : q_H0 = v0 := Eq.symm (peq0); let pst1 : q_H0 = (p q_x q_x) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_x) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_x) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_x) = (p (p (p u0_v0 u0_v0) u0s1out) u0_v0) := Eq.trans (pst3) (peq5); let pst5 : q_x = (p (p u0_v0 u0_v0) u0s1out) := congrArg (fun q => L q) (pst4); let pst6 : (p (p u0_v0 u0_v0) u0s1out) = q_x := Eq.symm (pst5); let pst7 : q_x = u0_v0 := congrArg (fun q => R q) (pst4); let pst8 : (p (p u0_v0 u0_v0) u0s1out) = u0_v0 := Eq.trans (pst6) (pst7); let pst9 : u0_v0 = (p (p u0_v0 u0_v0) u0s1out) := Eq.symm (pst8); pst9)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v0) u0s1out) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v0) (sz_lt_p_left (p u0_v0 u0_v0) u0s1out)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 v2 H1 : CM)
    (s1 : Step v2 v0 H1) :
    ¬ ∃ o, Code (p (p v0 v0) H1) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_v2, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases s1 with
  | raw =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v1 at e1
        have e2 := congrArg (fun q => (L (R q))) ha
        change v2 = q_x at e2
        have e3 := congrArg (fun q => (R (R q))) ha
        change v0 = q_x at e3
        have e4 := congrArg (fun q => q) hb
        change v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at e4
        have cyc : q_x = (p (p (p q_x q_x) (p q_v2 q_x)) q_x) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = q_v1 := e1; let peq3 : v0 = q_x := e3; let peq4 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_v1 := Eq.trans (pst0) (peq1); let pst2 : v0 = q_v1 := Eq.trans (peq0) (pst1); let pst3 : q_v1 = v0 := Eq.symm (pst2); let pst4 : q_v1 = q_x := Eq.trans (pst3) (peq3); let pst5 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst6 : v0 = q_x := Eq.trans (peq0) (pst5); let pst7 : q_x = v0 := Eq.symm (pst6); let pst8 : q_x = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst7) (peq4); let pst9 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst10 : (p q_v0 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst9); let pst11 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst12 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst11); let pst13 : (p q_v0 q_v0) = (p q_x q_x) := Eq.trans (pst10) (pst12); let pst14 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p q_x q_x) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst13); let pst15 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst16 : (p q_v2 q_v0) = (p q_v2 q_x) := congrArg (fun q => p q_v2 q) (pst15); let pst17 : (p (p q_x q_x) (p q_v2 q_v0)) = (p (p q_x q_x) (p q_v2 q_x)) := congrArg (fun q => p (p q_x q_x) q) (pst16); let pst18 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p q_x q_x) (p q_v2 q_x)) := Eq.trans (pst14) (pst17); let pst19 : (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) = (p (p (p q_x q_x) (p q_v2 q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst18); let pst20 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst21 : (p (p (p q_x q_x) (p q_v2 q_x)) q_v0) = (p (p (p q_x q_x) (p q_v2 q_x)) q_x) := congrArg (fun q => p (p (p q_x q_x) (p q_v2 q_x)) q) (pst20); let pst22 : (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) = (p (p (p q_x q_x) (p q_v2 q_x)) q_x) := Eq.trans (pst19) (pst21); let pst23 : q_x = (p (p (p q_x q_x) (p q_v2 q_x)) q_x) := Eq.trans (pst8) (pst22); pst23)
        have hlt : sz q_x < sz (p (p (p q_x q_x) (p q_v2 q_x)) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) (p q_v2 q_x))) (sz_lt_p_left (p (p q_x q_x) (p q_v2 q_x)) q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v1 at e1
        have e2 := congrArg (fun q => (L (R q))) ha
        change v2 = q_x at e2
        have e3 := congrArg (fun q => (R (R q))) ha
        change v0 = q_x at e3
        have e4 := congrArg (fun q => q) hb
        change v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) at e4
        have cyc : q_x = (p (p (p q_x q_x) q_H1) q_x) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = q_v1 := e1; let peq3 : v0 = q_x := e3; let peq4 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := e4; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_v1 := Eq.trans (pst0) (peq1); let pst2 : v0 = q_v1 := Eq.trans (peq0) (pst1); let pst3 : q_v1 = v0 := Eq.symm (pst2); let pst4 : q_v1 = q_x := Eq.trans (pst3) (peq3); let pst5 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst6 : v0 = q_x := Eq.trans (peq0) (pst5); let pst7 : q_x = v0 := Eq.symm (pst6); let pst8 : q_x = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst7) (peq4); let pst9 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst10 : (p q_v0 q_v0) = (p q_x q_v0) := congrArg (fun q => p q q_v0) (pst9); let pst11 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst12 : (p q_x q_v0) = (p q_x q_x) := congrArg (fun q => p q_x q) (pst11); let pst13 : (p q_v0 q_v0) = (p q_x q_x) := Eq.trans (pst10) (pst12); let pst14 : (p (p q_v0 q_v0) q_H1) = (p (p q_x q_x) q_H1) := congrArg (fun q => p q q_H1) (pst13); let pst15 : (p (p (p q_v0 q_v0) q_H1) q_v0) = (p (p (p q_x q_x) q_H1) q_v0) := congrArg (fun q => p q q_v0) (pst14); let pst16 : q_v0 = q_x := Eq.trans (pst1) (pst4); let pst17 : (p (p (p q_x q_x) q_H1) q_v0) = (p (p (p q_x q_x) q_H1) q_x) := congrArg (fun q => p (p (p q_x q_x) q_H1) q) (pst16); let pst18 : (p (p (p q_v0 q_v0) q_H1) q_v0) = (p (p (p q_x q_x) q_H1) q_x) := Eq.trans (pst15) (pst17); let pst19 : q_x = (p (p (p q_x q_x) q_H1) q_x) := Eq.trans (pst8) (pst18); pst19)
        have hlt : sz q_x < sz (p (p (p q_x q_x) q_H1) q_x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_left (p q_x q_x) q_H1)) (sz_lt_p_left (p (p q_x q_x) q_H1) q_x)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L (R q))) (ha)
        change v2 = q_x at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R (R q))) (ha)
        change v0 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs0hB z0 z1 z2 z3 z4
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L (R q))) (ha)
        change v2 = q_x at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R (R q))) (ha)
        change v0 = q_x at p2
        have z2 := congrArg sz p2
        have p3 := hb
        change v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) at p3
        have z3 := congrArg sz p3
        have p4 := ho
        change o = q_x at p4
        have z4 := congrArg sz p4
        simp only [getOut, L, R, U, sz] at hcB qs0hB qs1hB z0 z1 z2 z3 z4
        omega
  | hit s1h =>
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change H1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at e3
        have cyc : q_v1 = (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v1) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = q_v1 := e1; let peq3 : v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_v1 := Eq.trans (pst0) (peq1); let pst2 : v0 = q_v1 := Eq.trans (peq0) (pst1); let pst3 : q_v1 = v0 := Eq.symm (pst2); let pst4 : q_v1 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst5) (pst6); let pst8 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p q_v1 q_v1) (p q_v2 q_v0)) := congrArg (fun q => p q (p q_v2 q_v0)) (pst7); let pst9 : (p q_v2 q_v0) = (p q_v2 q_v1) := congrArg (fun q => p q_v2 q) (pst1); let pst10 : (p (p q_v1 q_v1) (p q_v2 q_v0)) = (p (p q_v1 q_v1) (p q_v2 q_v1)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst9); let pst11 : (p (p q_v0 q_v0) (p q_v2 q_v0)) = (p (p q_v1 q_v1) (p q_v2 q_v1)) := Eq.trans (pst8) (pst10); let pst12 : (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) = (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v0) := congrArg (fun q => p q q_v0) (pst11); let pst13 : (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v0) = (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v1) := congrArg (fun q => p (p (p q_v1 q_v1) (p q_v2 q_v1)) q) (pst1); let pst14 : (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) = (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v1) := Eq.trans (pst12) (pst13); let pst15 : q_v1 = (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v1) := Eq.trans (pst4) (pst14); pst15)
        have hlt : sz q_v1 < sz (p (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_left (p q_v1 q_v1) (p q_v2 q_v1))) (sz_lt_p_left (p (p q_v1 q_v1) (p q_v2 q_v1)) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L (L q))) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R (L q))) ha
        change v0 = q_v1 at e1
        have e2 := congrArg (fun q => (R q)) ha
        change H1 = (p q_x q_x) at e2
        have e3 := congrArg (fun q => q) hb
        change v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) at e3
        have cyc : q_v1 = (p (p (p q_v1 q_v1) q_H1) q_v1) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = q_v1 := e1; let peq3 : v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_v1 := Eq.trans (pst0) (peq1); let pst2 : v0 = q_v1 := Eq.trans (peq0) (pst1); let pst3 : q_v1 = v0 := Eq.symm (pst2); let pst4 : q_v1 = (p (p (p q_v0 q_v0) q_H1) q_v0) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst5) (pst6); let pst8 : (p (p q_v0 q_v0) q_H1) = (p (p q_v1 q_v1) q_H1) := congrArg (fun q => p q q_H1) (pst7); let pst9 : (p (p (p q_v0 q_v0) q_H1) q_v0) = (p (p (p q_v1 q_v1) q_H1) q_v0) := congrArg (fun q => p q q_v0) (pst8); let pst10 : (p (p (p q_v1 q_v1) q_H1) q_v0) = (p (p (p q_v1 q_v1) q_H1) q_v1) := congrArg (fun q => p (p (p q_v1 q_v1) q_H1) q) (pst1); let pst11 : (p (p (p q_v0 q_v0) q_H1) q_v0) = (p (p (p q_v1 q_v1) q_H1) q_v1) := Eq.trans (pst9) (pst10); let pst12 : q_v1 = (p (p (p q_v1 q_v1) q_H1) q_v1) := Eq.trans (pst4) (pst11); pst12)
        have hlt : sz q_v1 < sz (p (p (p q_v1 q_v1) q_H1) q_v1) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_left (p q_v1 q_v1) q_H1)) (sz_lt_p_left (p (p q_v1 q_v1) q_H1) q_v1)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H1 = (p q_x q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = (p (p (p q_v0 q_v0) (p q_v2 q_v0)) q_v0) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := congrArg (fun q => (L q)) (ha)
        change (p v0 v0) = q_H0 at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (R q)) (ha)
        change H1 = (p q_x q_x) at p1
        have z1 := congrArg sz p1
        have p2 := hb
        change v0 = (p (p (p q_v0 q_v0) q_H1) q_v0) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB z0 z1 z2 z3
        omega
theorem source_holds (x v0 v1 v2 : CM) :
    x = (eval (eval (eval v0 v1) (eval x x)) (eval (eval (eval v0 v0) (eval v2 v0)) v0)) := by
  let H0 := eval v0 v1
  have e0a : v0 = v0 := by
    change v0 = v0
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step v0 v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v0 v1
  let H1 := eval v2 v0
  have e1a : v2 = v2 := by
    change v2 = v2
    rfl
  have e1b : v0 = v0 := by
    change v0 = v0
    rfl
  have s1 : Step v2 v0 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v2 v0
  change x = (eval (eval H0 (eval x x)) (eval (eval (eval v0 v0) H1) v0))
  have rawEq : (eval (eval H0 (eval x x)) (eval (eval (eval v0 v0) H1) v0)) = (eval (p H0 (p x x)) (p (p (p v0 v0) H1) v0)) := by
    calc
      (eval (eval H0 (eval x x)) (eval (eval (eval v0 v0) H1) v0)) = (eval (eval H0 (p x x)) (eval (eval (eval v0 v0) H1) v0)) := congrArg (fun q => (eval (eval H0 q) (eval (eval (eval v0 v0) H1) v0))) (eval_raw (nr0 x v0 v1 v2))
      _ = (eval (p H0 (p x x)) (eval (eval (eval v0 v0) H1) v0)) := congrArg (fun q => (eval q (eval (eval (eval v0 v0) H1) v0))) (eval_raw (nr1 x v0 v1 v2 H0 s0))
      _ = (eval (p H0 (p x x)) (eval (eval (p v0 v0) H1) v0)) := congrArg (fun q => (eval (p H0 (p x x)) (eval (eval q H1) v0))) (eval_raw (nr2 x v0 v1 v2))
      _ = (eval (p H0 (p x x)) (eval (p (p v0 v0) H1) v0)) := congrArg (fun q => (eval (p H0 (p x x)) (eval q v0))) (eval_raw (nr3 x v0 v1 v2 H1 s1))
      _ = (eval (p H0 (p x x)) (p (p (p v0 v0) H1) v0)) := congrArg (fun q => (eval (p H0 (p x x)) q)) (eval_raw (nr4 x v0 v1 v2 H1 s1))
  exact (eval_hit (Code.law x v0 v1 v2 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op := eval
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro x v0 v1 v2
    exact CM.source_holds x v0 v1 v2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
