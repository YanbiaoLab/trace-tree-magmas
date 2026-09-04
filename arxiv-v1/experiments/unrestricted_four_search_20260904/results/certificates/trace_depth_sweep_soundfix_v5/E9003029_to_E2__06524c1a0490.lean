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
  | law (x v0 v1 H0 : CM)
      (s0 : Step v1 x H0) :
      Code v0 (p (p x (p H0 (p (p v0 v0) (p x x)))) v0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v1 q_x q_H0 ∧ a = q_v0 ∧ b = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L b))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz a < sz b ∧ sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz a < sz (p o b) := by
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
    have cyc : q_v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) (sz_lt_p_right q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))))) (sz_lt_p_left (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
    have cyc : q_v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) (sz_lt_p_right q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))))) (sz_lt_p_left (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
    have cyc : q_v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) (sz_lt_p_right q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))))) (sz_lt_p_left (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
    have cyc : q_v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := (let peq0 : x = q_v0 := e0; let peq1 : x = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) (sz_lt_p_right q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))))) (sz_lt_p_left (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p v0 v0) (p x x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change (p v0 v0) = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change x = (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change x = q_v0 at e2
    have cyc : v0 = (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : x = (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) := e1; let peq2 : x = q_v0 := e2; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst3); let pst5 : (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) = (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) := congrArg (fun q => p (p q_v1 q_x) q) (pst4); let pst6 : (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) = (p q_x (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : x = (p q_x (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) := Eq.trans (peq1) (pst6); let pst8 : (p q_x (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) = x := Eq.symm (pst7); let pst9 : (p q_x (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) = q_v0 := Eq.trans (pst8) (peq2); let pst10 : (p q_x (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) = (p v0 v0) := Eq.trans (pst9) (pst0); let pst11 : q_x = v0 := congrArg (fun q => L q) (pst10); let pst12 : (p q_v1 q_x) = (p q_v1 v0) := congrArg (fun q => p q_v1 q) (pst11); let pst13 : (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) = (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) := congrArg (fun q => p q (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) (pst12); let pst14 : (p q_x q_x) = (p v0 q_x) := congrArg (fun q => p q q_x) (pst11); let pst15 : (p v0 q_x) = (p v0 v0) := congrArg (fun q => p v0 q) (pst11); let pst16 : (p q_x q_x) = (p v0 v0) := Eq.trans (pst14) (pst15); let pst17 : (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)) = (p (p (p v0 v0) (p v0 v0)) (p v0 v0)) := congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (pst16); let pst18 : (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) = (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := congrArg (fun q => p (p q_v1 v0) q) (pst17); let pst19 : (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) = (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := Eq.trans (pst13) (pst18); let pst20 : (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) = (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) := Eq.symm (pst19); let pst21 : (p (p q_v1 q_x) (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) = v0 := congrArg (fun q => R q) (pst10); let pst22 : (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) = v0 := Eq.trans (pst20) (pst21); let pst23 : v0 = (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := Eq.symm (pst22); pst23)
    have hlt : sz v0 < sz (p (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := Nat.lt_trans (sz_lt_p_right q_v1 v0) (sz_lt_p_left (p q_v1 v0) (p (p (p v0 v0) (p v0 v0)) (p v0 v0)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change (p v0 v0) = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change x = (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change x = q_v0 at e2
    have cyc : v0 = (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := (let peq0 : (p v0 v0) = q_v0 := e0; let peq1 : x = (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) := e1; let peq2 : x = q_v0 := e2; let pst0 : q_v0 = (p v0 v0) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p v0 v0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p v0 v0) q_v0) = (p (p v0 v0) (p v0 v0)) := congrArg (fun q => p (p v0 v0) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p v0 v0) (p v0 v0)) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst3); let pst5 : (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) = (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) := congrArg (fun q => p q_H0 q) (pst4); let pst6 : (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) = (p q_x (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : x = (p q_x (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) := Eq.trans (peq1) (pst6); let pst8 : (p q_x (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) = x := Eq.symm (pst7); let pst9 : (p q_x (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) = q_v0 := Eq.trans (pst8) (peq2); let pst10 : (p q_x (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)))) = (p v0 v0) := Eq.trans (pst9) (pst0); let pst11 : q_x = v0 := congrArg (fun q => L q) (pst10); let pst12 : (p q_x q_x) = (p v0 q_x) := congrArg (fun q => p q q_x) (pst11); let pst13 : (p v0 q_x) = (p v0 v0) := congrArg (fun q => p v0 q) (pst11); let pst14 : (p q_x q_x) = (p v0 v0) := Eq.trans (pst12) (pst13); let pst15 : (p (p (p v0 v0) (p v0 v0)) (p q_x q_x)) = (p (p (p v0 v0) (p v0 v0)) (p v0 v0)) := congrArg (fun q => p (p (p v0 v0) (p v0 v0)) q) (pst14); let pst16 : (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) = (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := congrArg (fun q => p q_H0 q) (pst15); let pst17 : (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) = (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) := Eq.symm (pst16); let pst18 : (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p q_x q_x))) = v0 := congrArg (fun q => R q) (pst10); let pst19 : (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) = v0 := Eq.trans (pst17) (pst18); let pst20 : v0 = (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := Eq.symm (pst19); pst20)
    have hlt : sz v0 < sz (p q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p v0 v0))) (sz_lt_p_left (p (p v0 v0) (p v0 v0)) (p v0 v0))) (sz_lt_p_right q_H0 (p (p (p v0 v0) (p v0 v0)) (p v0 v0)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v1 x H0) :
    ¬ ∃ o, Code H0 (p (p v0 v0) (p x x)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p v1 x) = q_v0 at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change v0 = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change v0 = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p x x) = q_v0 at e3
      have cyc : q_x = (p (p q_v1 q_x) (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := (let peq0 : (p v1 x) = q_v0 := e0; let peq1 : v0 = q_x := e1; let peq2 : v0 = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := e2; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p v1 x) := Eq.symm (peq0); let pst3 : (p q_v0 q_v0) = (p (p v1 x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p v1 x) q_v0) = (p (p v1 x) (p v1 x)) := congrArg (fun q => p (p v1 x) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p v1 x) (p v1 x)) := Eq.trans (pst3) (pst4); let pst6 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p v1 x) (p v1 x)) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst5); let pst7 : (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) = (p (p q_v1 q_x) (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := congrArg (fun q => p (p q_v1 q_x) q) (pst6); let pst8 : q_x = (p (p q_v1 q_x) (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := Eq.trans (pst1) (pst7); pst8)
      have hlt : sz q_x < sz (p (p q_v1 q_x) (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := Nat.lt_trans (sz_lt_p_right q_v1 q_x) (sz_lt_p_left (p q_v1 q_x) (p (p (p v1 x) (p v1 x)) (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p v1 x) = q_v0 at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change v0 = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change v0 = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p x x) = q_v0 at e3
      have cyc : q_x = (p q_H0 (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := (let peq0 : (p v1 x) = q_v0 := e0; let peq1 : v0 = q_x := e1; let peq2 : v0 = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := e2; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p v1 x) := Eq.symm (peq0); let pst3 : (p q_v0 q_v0) = (p (p v1 x) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst4 : (p (p v1 x) q_v0) = (p (p v1 x) (p v1 x)) := congrArg (fun q => p (p v1 x) q) (pst2); let pst5 : (p q_v0 q_v0) = (p (p v1 x) (p v1 x)) := Eq.trans (pst3) (pst4); let pst6 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p v1 x) (p v1 x)) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst5); let pst7 : (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) = (p q_H0 (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := congrArg (fun q => p q_H0 q) (pst6); let pst8 : q_x = (p q_H0 (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := Eq.trans (pst1) (pst7); pst8)
      have hlt : sz q_x < sz (p q_H0 (p (p (p v1 x) (p v1 x)) (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right (p (p v1 x) (p v1 x)) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p (p v1 x) (p v1 x)) (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change H0 = q_v0 at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change v0 = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change v0 = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p x x) = q_v0 at e3
      have cyc : q_x = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := (let peq1 : v0 = q_x := e1; let peq2 : v0 = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := e2; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_x < sz (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := Nat.lt_trans (sz_lt_p_right q_v1 q_x) (sz_lt_p_left (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change H0 = q_v0 at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change v0 = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change v0 = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p x x) = q_v0 at e3
      have cyc : q_x = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := (let peq1 : v0 = q_x := e1; let peq2 : v0 = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := e2; let pst0 : q_x = v0 := Eq.symm (peq1); let pst1 : q_x = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_x < sz (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_x q_x) (sz_lt_p_right (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p q_v0 q_v0) (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step v1 x H0) :
    ¬ ∃ o, Code x (p H0 (p (p v0 v0) (p x x))) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change x = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p (p v0 v0) (p x x)) = q_v0 at e3
      have cyc : q_v0 = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change v1 = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change x = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p (p v0 v0) (p x x)) = q_v0 at e3
      have cyc : q_v0 = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p q_v0 q_v0) (p q_x q_x)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change H0 = (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change (p (p v0 v0) (p x x)) = q_v0 at e2
      have cyc : q_v0 = (p (p v0 v0) (p q_v0 q_v0)) := (let peq0 : x = q_v0 := e0; let peq2 : (p (p v0 v0) (p x x)) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq0); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq0); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) (p x x)) = (p (p v0 v0) (p q_v0 q_v0)) := congrArg (fun q => p (p v0 v0) q) (pst2); let pst4 : (p (p v0 v0) (p q_v0 q_v0)) = (p (p v0 v0) (p x x)) := Eq.symm (pst3); let pst5 : (p (p v0 v0) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst4) (peq2); let pst6 : q_v0 = (p (p v0 v0) (p q_v0 q_v0)) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p v0 v0) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p v0 v0) (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change H0 = (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change (p (p v0 v0) (p x x)) = q_v0 at e2
      have cyc : q_v0 = (p (p v0 v0) (p q_v0 q_v0)) := (let peq0 : x = q_v0 := e0; let peq2 : (p (p v0 v0) (p x x)) = q_v0 := e2; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq0); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq0); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) (p x x)) = (p (p v0 v0) (p q_v0 q_v0)) := congrArg (fun q => p (p v0 v0) q) (pst2); let pst4 : (p (p v0 v0) (p q_v0 q_v0)) = (p (p v0 v0) (p x x)) := Eq.symm (pst3); let pst5 : (p (p v0 v0) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst4) (peq2); let pst6 : q_v0 = (p (p v0 v0) (p q_v0 q_v0)) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p v0 v0) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p v0 v0) (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr5 (x v0 v1 H0 : CM)
    (s0 : Step v1 x H0) :
    ¬ ∃ o, Code (p x (p H0 (p (p v0 v0) (p x x)))) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p (p v1 x) (p (p v0 v0) (p x x)))) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
      have cyc : v0 = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := (let peq0 : (p x (p (p v1 x) (p (p v0 v0) (p x x)))) = q_v0 := e0; let peq1 : v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = (p x (p (p v1 x) (p (p v0 v0) (p x x)))) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) q_v0) = (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst3); let pst5 : (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) = (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x))) := congrArg (fun q => p (p q_v1 q_x) q) (pst4); let pst6 : (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) = (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) q) (pst0); let pst9 : (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Eq.trans (pst7) (pst8); let pst10 : v0 = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Eq.trans (peq1) (pst9); pst10)
      have hlt : sz v0 < sz (p (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p x x))) (sz_lt_p_right (p v1 x) (p (p v0 v0) (p x x)))) (sz_lt_p_right x (p (p v1 x) (p (p v0 v0) (p x x))))) (sz_lt_p_left (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x)))))) (sz_lt_p_left (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x))) (sz_lt_p_right (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (sz_lt_p_right q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x))))) (sz_lt_p_left (p q_x (p (p q_v1 q_x) (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p (p v1 x) (p (p v0 v0) (p x x)))) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
      have cyc : v0 = (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := (let peq0 : (p x (p (p v1 x) (p (p v0 v0) (p x x)))) = q_v0 := e0; let peq1 : v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = (p x (p (p v1 x) (p (p v0 v0) (p x x)))) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) q_v0) = (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst3); let pst5 : (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) = (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x))) := congrArg (fun q => p q_H0 q) (pst4); let pst6 : (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) = (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) = (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) q) (pst0); let pst9 : (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Eq.trans (pst7) (pst8); let pst10 : v0 = (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Eq.trans (peq1) (pst9); pst10)
      have hlt : sz v0 < sz (p (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p x x))) (sz_lt_p_right (p v1 x) (p (p v0 v0) (p x x)))) (sz_lt_p_right x (p (p v1 x) (p (p v0 v0) (p x x))))) (sz_lt_p_left (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x)))))) (sz_lt_p_left (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (sz_lt_p_right q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x))))) (sz_lt_p_left (p q_x (p q_H0 (p (p (p x (p (p v1 x) (p (p v0 v0) (p x x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p (p v1 x) (p (p v0 v0) (p x x)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p H0 (p (p v0 v0) (p x x)))) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
      have cyc : v0 = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := (let peq0 : (p x (p H0 (p (p v0 v0) (p x x)))) = q_v0 := e0; let peq1 : v0 = (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = (p x (p H0 (p (p v0 v0) (p x x)))) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p x (p H0 (p (p v0 v0) (p x x)))) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x (p H0 (p (p v0 v0) (p x x)))) q_v0) = (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p x (p H0 (p (p v0 v0) (p x x)))) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst3); let pst5 : (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x))) = (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x))) := congrArg (fun q => p (p q_v1 q_x) q) (pst4); let pst6 : (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) = (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) q) (pst0); let pst9 : (p (p q_x (p (p q_v1 q_x) (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Eq.trans (pst7) (pst8); let pst10 : v0 = (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Eq.trans (peq1) (pst9); pst10)
      have hlt : sz v0 < sz (p (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p x x))) (sz_lt_p_right H0 (p (p v0 v0) (p x x)))) (sz_lt_p_right x (p H0 (p (p v0 v0) (p x x))))) (sz_lt_p_left (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x)))))) (sz_lt_p_left (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x))) (sz_lt_p_right (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (sz_lt_p_right q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x))))) (sz_lt_p_left (p q_x (p (p q_v1 q_x) (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p H0 (p (p v0 v0) (p x x)))) = q_v0 at e0
      have e1 := congrArg (fun q => q) hb
      change v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) at e1
      have cyc : v0 = (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := (let peq0 : (p x (p H0 (p (p v0 v0) (p x x)))) = q_v0 := e0; let peq1 : v0 = (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) := e1; let pst0 : q_v0 = (p x (p H0 (p (p v0 v0) (p x x)))) := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p x (p H0 (p (p v0 v0) (p x x)))) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst2 : (p (p x (p H0 (p (p v0 v0) (p x x)))) q_v0) = (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p x (p H0 (p (p v0 v0) (p x x)))) q) (pst0); let pst3 : (p q_v0 q_v0) = (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Eq.trans (pst1) (pst2); let pst4 : (p (p q_v0 q_v0) (p q_x q_x)) = (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)) := congrArg (fun q => p q (p q_x q_x)) (pst3); let pst5 : (p q_H0 (p (p q_v0 q_v0) (p q_x q_x))) = (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x))) := congrArg (fun q => p q_H0 q) (pst4); let pst6 : (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) = (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) := congrArg (fun q => p q_x q) (pst5); let pst7 : (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) q_v0) = (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := congrArg (fun q => p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) q) (pst0); let pst9 : (p (p q_x (p q_H0 (p (p q_v0 q_v0) (p q_x q_x)))) q_v0) = (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Eq.trans (pst7) (pst8); let pst10 : v0 = (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Eq.trans (peq1) (pst9); pst10)
      have hlt : sz v0 < sz (p (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v0 v0) (sz_lt_p_left (p v0 v0) (p x x))) (sz_lt_p_right H0 (p (p v0 v0) (p x x)))) (sz_lt_p_right x (p H0 (p (p v0 v0) (p x x))))) (sz_lt_p_left (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x)))))) (sz_lt_p_left (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x))) (sz_lt_p_right q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (sz_lt_p_right q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x))))) (sz_lt_p_left (p q_x (p q_H0 (p (p (p x (p H0 (p (p v0 v0) (p x x)))) (p x (p H0 (p (p v0 v0) (p x x))))) (p q_x q_x)))) (p x (p H0 (p (p v0 v0) (p x x)))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval (eval x (eval (eval v1 x) (eval (eval v0 v0) (eval x x)))) v0)) := by
  let H0 := eval v1 x
  have e0a : v1 = v1 := by
    change v1 = v1
    rfl
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step v1 x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v1 x
  change x = (eval v0 (eval (eval x (eval H0 (eval (eval v0 v0) (eval x x)))) v0))
  have rawEq : (eval v0 (eval (eval x (eval H0 (eval (eval v0 v0) (eval x x)))) v0)) = (eval v0 (p (p x (p H0 (p (p v0 v0) (p x x)))) v0)) := by
    calc
      (eval v0 (eval (eval x (eval H0 (eval (eval v0 v0) (eval x x)))) v0)) = (eval v0 (eval (eval x (eval H0 (eval (p v0 v0) (eval x x)))) v0)) := congrArg (fun q => (eval v0 (eval (eval x (eval H0 (eval q (eval x x)))) v0))) (eval_raw (nr0 x v0 v1))
      _ = (eval v0 (eval (eval x (eval H0 (eval (p v0 v0) (p x x)))) v0)) := congrArg (fun q => (eval v0 (eval (eval x (eval H0 (eval (p v0 v0) q))) v0))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval (eval x (eval H0 (p (p v0 v0) (p x x)))) v0)) := congrArg (fun q => (eval v0 (eval (eval x (eval H0 q)) v0))) (eval_raw (nr2 x v0 v1))
      _ = (eval v0 (eval (eval x (p H0 (p (p v0 v0) (p x x)))) v0)) := congrArg (fun q => (eval v0 (eval (eval x q) v0))) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval v0 (eval (p x (p H0 (p (p v0 v0) (p x x)))) v0)) := congrArg (fun q => (eval v0 (eval q v0))) (eval_raw (nr4 x v0 v1 H0 s0))
      _ = (eval v0 (p (p x (p H0 (p (p v0 v0) (p x x)))) v0)) := congrArg (fun q => (eval v0 q)) (eval_raw (nr5 x v0 v1 H0 s0))
  exact (eval_hit (Code.law x v0 v1 H0 s0)).symm.trans rawEq.symm
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
