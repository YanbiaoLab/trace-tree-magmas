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
      (s0 : Step (p x x) x H0) :
      Code (p v0 v0) (p (p x (p H0 (p v1 v1))) v1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step (p q_x q_x) q_x q_H0 ∧ a = (p q_v0 q_v0) ∧ b = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L b))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz b := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

theorem step_ne_second {a b : CM} : ¬ Step a b b := by
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) at e1
    have cyc : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Eq.symm (pst5); pst6)
    have hlt : sz q_v1 < sz (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p (p q_x q_x) q_x) (p q_v1 q_v1))) (sz_lt_p_right q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) at e1
    have cyc : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := e1; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_H0 (p q_v1 q_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.symm (pst5); pst6)
    have hlt : sz q_v1 < sz (p q_x (p q_H0 (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right q_H0 (p q_v1 q_v1))) (sz_lt_p_right q_x (p q_H0 (p q_v1 q_v1)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code x x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change x = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) at e1
    have cyc : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := (let peq0 : x = (p q_v0 q_v0) := e0; let peq1 : x = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := e1; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Eq.symm (pst5); pst6)
    have hlt : sz q_v1 < sz (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p (p q_x q_x) q_x) (p q_v1 q_v1))) (sz_lt_p_right q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change x = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change x = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) at e1
    have cyc : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := (let peq0 : x = (p q_v0 q_v0) := e0; let peq1 : x = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := e1; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_H0 (p q_v1 q_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.symm (pst5); pst6)
    have hlt : sz q_v1 < sz (p q_x (p q_H0 (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right q_H0 (p q_v1 q_v1))) (sz_lt_p_right q_x (p q_H0 (p q_v1 q_v1)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) at e1
    have cyc : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := (let peq0 : v1 = (p q_v0 q_v0) := e0; let peq1 : v1 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := e1; let pst0 : (p q_v0 q_v0) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Eq.symm (pst5); pst6)
    have hlt : sz q_v1 < sz (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p (p q_x q_x) q_x) (p q_v1 q_v1))) (sz_lt_p_right q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v1 = (p q_v0 q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) at e1
    have cyc : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := (let peq0 : v1 = (p q_v0 q_v0) := e0; let peq1 : v1 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := e1; let pst0 : (p q_v0 q_v0) = v1 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p q_x (p q_H0 (p q_v1 q_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.symm (pst5); pst6)
    have hlt : sz q_v1 < sz (p q_x (p q_H0 (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right q_H0 (p q_v1 q_v1))) (sz_lt_p_right q_x (p q_H0 (p q_v1 q_v1)))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step (p x x) x H0) :
    ¬ ∃ o, Code H0 (p v1 v1) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change (p x x) = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change v1 = q_v1 at e3
      have cyc : x = (p x x) := (let peq0 : (p x x) = q_v0 := e0; let peq1 : x = q_v0 := e1; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : x = (p x x) := Eq.trans (peq1) (pst0); pst1)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change (p x x) = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change x = q_v0 at e1
      have e2 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x (p q_H0 (p q_v1 q_v1))) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change v1 = q_v1 at e3
      have cyc : x = (p x x) := (let peq0 : (p x x) = q_v0 := e0; let peq1 : x = q_v0 := e1; let pst0 : q_v0 = (p x x) := Eq.symm (peq0); let pst1 : x = (p x x) := Eq.trans (peq1) (pst0); pst1)
      have hlt : sz x < sz (p x x) := sz_lt_p_left x x
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change H0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = q_v1 at e2
      have cyc : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := (let peq1 : v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := e1; let peq2 : v1 = q_v1 := e2; let pst0 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = v1 := Eq.symm (peq1); let pst1 : (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right (p (p q_x q_x) q_x) (p q_v1 q_v1))) (sz_lt_p_right q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change H0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x (p q_H0 (p q_v1 q_v1))) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v1 = q_v1 at e2
      have cyc : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := (let peq1 : v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := e1; let peq2 : v1 = q_v1 := e2; let pst0 : (p q_x (p q_H0 (p q_v1 q_v1))) = v1 := Eq.symm (peq1); let pst1 : (p q_x (p q_H0 (p q_v1 q_v1))) = q_v1 := Eq.trans (pst0) (peq2); let pst2 : q_v1 = (p q_x (p q_H0 (p q_v1 q_v1))) := Eq.symm (pst1); pst2)
      have hlt : sz q_v1 < sz (p q_x (p q_H0 (p q_v1 q_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right q_H0 (p q_v1 q_v1))) (sz_lt_p_right q_x (p q_H0 (p q_v1 q_v1)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step (p x x) x H0) :
    ¬ ∃ o, Code x (p H0 (p v1 v1)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change x = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (L (L q))) hb
      change (p x x) = q_x at e1
      have e2 := congrArg (fun q => (R (L q))) hb
      change x = (p (p (p q_x q_x) q_x) (p q_v1 q_v1)) at e2
      have e3 := congrArg (fun q => (R q)) hb
      change (p v1 v1) = q_v1 at e3
      have cyc : q_v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) := (let peq0 : x = (p q_v0 q_v0) := e0; let peq1 : (p x x) = q_x := e1; let peq2 : x = (p (p (p q_x q_x) q_x) (p q_v1 q_v1)) := e2; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p (p q_x q_x) q_x) (p q_v1 q_v1)) := Eq.trans (pst0) (peq2); let pst2 : (p x x) = (p (p q_v0 q_v0) x) := congrArg (fun q => p q x) (peq0); let pst3 : (p (p q_v0 q_v0) x) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst4 : (p x x) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst2) (pst3); let pst5 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p x x) := Eq.symm (pst4); let pst6 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = q_x := Eq.trans (pst5) (peq1); let pst7 : q_x = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.symm (pst6); let pst8 : (p q_x q_x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) q_x) := congrArg (fun q => p q q_x) (pst7); let pst9 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) q_x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) := congrArg (fun q => p (p (p q_v0 q_v0) (p q_v0 q_v0)) q) (pst7); let pst10 : (p q_x q_x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) := Eq.trans (pst8) (pst9); let pst11 : (p (p q_x q_x) q_x) = (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) q_x) := congrArg (fun q => p q q_x) (pst10); let pst12 : (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) q_x) = (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) := congrArg (fun q => p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) q) (pst7); let pst13 : (p (p q_x q_x) q_x) = (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) := Eq.trans (pst11) (pst12); let pst14 : (p (p (p q_x q_x) q_x) (p q_v1 q_v1)) = (p (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p q_v1 q_v1)) := congrArg (fun q => p q (p q_v1 q_v1)) (pst13); let pst15 : (p q_v0 q_v0) = (p (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p q_v1 q_v1)) := Eq.trans (pst1) (pst14); let pst16 : q_v0 = (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) := congrArg (fun q => L q) (pst15); pst16)
      have hlt : sz q_v0 < sz (p (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0)))) (sz_lt_p_left (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p (p q_v0 q_v0) (p q_v0 q_v0))) (p (p q_v0 q_v0) (p q_v0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape qs0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : v1 = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := (let peq0 : x = (p q_v0 q_v0) := ha; let peq1 : (p x x) = q_x := congrArg (fun q => (L (L q))) (hb); let peq2 : x = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R (L q))) (hb); let peq3 : (p v1 v1) = q_v1 := congrArg (fun q => (R q)) (hb); let peq7 : q_x = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := u0b; let pst0 : (p x x) = (p (p q_v0 q_v0) x) := congrArg (fun q => p q x) (peq0); let pst1 : (p (p q_v0 q_v0) x) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst2 : (p x x) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (pst1); let pst3 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p x x) := Eq.symm (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = q_x := Eq.trans (pst3) (peq1); let pst5 : q_x = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst7 : (p q_v0 q_v0) = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst6) (peq2); let pst8 : q_v0 = q_H0 := congrArg (fun q => L q) (pst7); let pst9 : q_H0 = q_v0 := Eq.symm (pst8); let pst10 : q_v0 = (p q_v1 q_v1) := congrArg (fun q => R q) (pst7); let pst11 : q_H0 = (p q_v1 q_v1) := Eq.trans (pst9) (pst10); let pst12 : q_v1 = (p v1 v1) := Eq.symm (peq3); let pst13 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst14 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst15 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst13) (pst14); let pst16 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst15); let pst17 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst16); let pst18 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) q_v0) := congrArg (fun q => p q q_v0) (pst17); let pst19 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst20 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst21 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst19) (pst20); let pst22 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst21); let pst23 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst22); let pst24 : (p (p (p v1 v1) (p v1 v1)) q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p (p (p v1 v1) (p v1 v1)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Eq.trans (pst18) (pst24); let pst26 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst25); let pst27 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst28 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst29 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst27) (pst28); let pst30 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst29); let pst31 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst30); let pst32 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) q_v0) := congrArg (fun q => p q q_v0) (pst31); let pst33 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst34 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst35 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst33) (pst34); let pst36 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst35); let pst37 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst36); let pst38 : (p (p (p v1 v1) (p v1 v1)) q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p (p (p v1 v1) (p v1 v1)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Eq.trans (pst32) (pst38); let pst40 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p q_v0 q_v0)) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) := congrArg (fun q => p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) q) (pst39); let pst41 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) := Eq.trans (pst26) (pst40); let pst42 : q_x = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) := Eq.trans (pst5) (pst41); let pst43 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) = q_x := Eq.symm (pst42); let pst44 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst43) (peq7); let pst45 : (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst44); let pst46 : (p (p v1 v1) (p v1 v1)) = (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst45); let pst47 : (p (p v1 v1) (p v1 v1)) = u0_x := congrArg (fun q => L q) (pst45); let pst48 : u0_x = (p (p v1 v1) (p v1 v1)) := Eq.symm (pst47); let pst49 : (p u0_x u0_x) = (p (p (p v1 v1) (p v1 v1)) u0_x) := congrArg (fun q => p q u0_x) (pst48); let pst50 : (p (p (p v1 v1) (p v1 v1)) u0_x) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p (p (p v1 v1) (p v1 v1)) q) (pst48); let pst51 : (p u0_x u0_x) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Eq.trans (pst49) (pst50); let pst52 : (p (p u0_x u0_x) u0_x) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) u0_x) := congrArg (fun q => p q u0_x) (pst51); let pst53 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) u0_x) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) q) (pst48); let pst54 : (p (p u0_x u0_x) u0_x) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p v1 v1) (p v1 v1))) := Eq.trans (pst52) (pst53); let pst55 : (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1)) = (p (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p v1 v1) (p v1 v1))) (p u0_v1 u0_v1)) := congrArg (fun q => p q (p u0_v1 u0_v1)) (pst54); let pst56 : (p (p v1 v1) (p v1 v1)) = (p (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p v1 v1) (p v1 v1))) (p u0_v1 u0_v1)) := Eq.trans (pst46) (pst55); let pst57 : (p v1 v1) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => L q) (pst56); let pst58 : v1 = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => L q) (pst57); pst58)
        have hlt : sz v1 < sz (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left v1 v1) (sz_lt_p_left (p v1 v1) (p v1 v1))) (sz_lt_p_left (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v1 = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := (let peq0 : x = (p q_v0 q_v0) := ha; let peq1 : (p x x) = q_x := congrArg (fun q => (L (L q))) (hb); let peq2 : x = (p q_H0 (p q_v1 q_v1)) := congrArg (fun q => (R (L q))) (hb); let peq3 : (p v1 v1) = q_v1 := congrArg (fun q => (R q)) (hb); let peq7 : q_x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := u0b; let pst0 : (p x x) = (p (p q_v0 q_v0) x) := congrArg (fun q => p q x) (peq0); let pst1 : (p (p q_v0 q_v0) x) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst2 : (p x x) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (pst1); let pst3 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p x x) := Eq.symm (pst2); let pst4 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = q_x := Eq.trans (pst3) (peq1); let pst5 : q_x = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst7 : (p q_v0 q_v0) = (p q_H0 (p q_v1 q_v1)) := Eq.trans (pst6) (peq2); let pst8 : q_v0 = q_H0 := congrArg (fun q => L q) (pst7); let pst9 : q_H0 = q_v0 := Eq.symm (pst8); let pst10 : q_v0 = (p q_v1 q_v1) := congrArg (fun q => R q) (pst7); let pst11 : q_H0 = (p q_v1 q_v1) := Eq.trans (pst9) (pst10); let pst12 : q_v1 = (p v1 v1) := Eq.symm (peq3); let pst13 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst14 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst15 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst13) (pst14); let pst16 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst15); let pst17 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst16); let pst18 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) q_v0) := congrArg (fun q => p q q_v0) (pst17); let pst19 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst20 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst21 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst19) (pst20); let pst22 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst21); let pst23 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst22); let pst24 : (p (p (p v1 v1) (p v1 v1)) q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p (p (p v1 v1) (p v1 v1)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Eq.trans (pst18) (pst24); let pst26 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst25); let pst27 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst28 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst29 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst27) (pst28); let pst30 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst29); let pst31 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst30); let pst32 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) q_v0) := congrArg (fun q => p q q_v0) (pst31); let pst33 : (p q_v1 q_v1) = (p (p v1 v1) q_v1) := congrArg (fun q => p q q_v1) (pst12); let pst34 : (p (p v1 v1) q_v1) = (p (p v1 v1) (p v1 v1)) := congrArg (fun q => p (p v1 v1) q) (pst12); let pst35 : (p q_v1 q_v1) = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst33) (pst34); let pst36 : q_H0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst11) (pst35); let pst37 : q_v0 = (p (p v1 v1) (p v1 v1)) := Eq.trans (pst8) (pst36); let pst38 : (p (p (p v1 v1) (p v1 v1)) q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p (p (p v1 v1) (p v1 v1)) q) (pst37); let pst39 : (p q_v0 q_v0) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Eq.trans (pst32) (pst38); let pst40 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p q_v0 q_v0)) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) := congrArg (fun q => p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) q) (pst39); let pst41 : (p (p q_v0 q_v0) (p q_v0 q_v0)) = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) := Eq.trans (pst26) (pst40); let pst42 : q_x = (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) := Eq.trans (pst5) (pst41); let pst43 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) = q_x := Eq.symm (pst42); let pst44 : (p (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1)))) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst43) (peq7); let pst45 : (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst44); let pst46 : (p (p v1 v1) (p v1 v1)) = (p u0s0out (p u0_v1 u0_v1)) := congrArg (fun q => R q) (pst45); let pst47 : (p v1 v1) = (p u0_v1 u0_v1) := congrArg (fun q => R q) (pst46); let pst48 : v1 = u0_v1 := congrArg (fun q => L q) (pst47); let pst49 : (p v1 v1) = (p u0_v1 v1) := congrArg (fun q => p q v1) (pst48); let pst50 : (p u0_v1 v1) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst48); let pst51 : (p v1 v1) = (p u0_v1 u0_v1) := Eq.trans (pst49) (pst50); let pst52 : (p (p v1 v1) (p v1 v1)) = (p (p u0_v1 u0_v1) (p v1 v1)) := congrArg (fun q => p q (p v1 v1)) (pst51); let pst53 : (p v1 v1) = (p u0_v1 v1) := congrArg (fun q => p q v1) (pst48); let pst54 : (p u0_v1 v1) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst48); let pst55 : (p v1 v1) = (p u0_v1 u0_v1) := Eq.trans (pst53) (pst54); let pst56 : (p (p u0_v1 u0_v1) (p v1 v1)) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst55); let pst57 : (p (p v1 v1) (p v1 v1)) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst52) (pst56); let pst58 : (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p v1 v1) (p v1 v1))) := congrArg (fun q => p q (p (p v1 v1) (p v1 v1))) (pst57); let pst59 : (p v1 v1) = (p u0_v1 v1) := congrArg (fun q => p q v1) (pst48); let pst60 : (p u0_v1 v1) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst48); let pst61 : (p v1 v1) = (p u0_v1 u0_v1) := Eq.trans (pst59) (pst60); let pst62 : (p (p v1 v1) (p v1 v1)) = (p (p u0_v1 u0_v1) (p v1 v1)) := congrArg (fun q => p q (p v1 v1)) (pst61); let pst63 : (p v1 v1) = (p u0_v1 v1) := congrArg (fun q => p q v1) (pst48); let pst64 : (p u0_v1 v1) = (p u0_v1 u0_v1) := congrArg (fun q => p u0_v1 q) (pst48); let pst65 : (p v1 v1) = (p u0_v1 u0_v1) := Eq.trans (pst63) (pst64); let pst66 : (p (p u0_v1 u0_v1) (p v1 v1)) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := congrArg (fun q => p (p u0_v1 u0_v1) q) (pst65); let pst67 : (p (p v1 v1) (p v1 v1)) = (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) := Eq.trans (pst62) (pst66); let pst68 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p v1 v1) (p v1 v1))) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := congrArg (fun q => p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) q) (pst67); let pst69 : (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.trans (pst58) (pst68); let pst70 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) := Eq.symm (pst69); let pst71 : (p (p (p v1 v1) (p v1 v1)) (p (p v1 v1) (p v1 v1))) = u0_v1 := congrArg (fun q => R q) (pst44); let pst72 : (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst70) (pst71); let pst73 : u0_v1 = (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Eq.symm (pst72); pst73)
        have hlt : sz u0_v1 < sz (p (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_left (p u0_v1 u0_v1) (p u0_v1 u0_v1))) (sz_lt_p_left (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)) (p (p u0_v1 u0_v1) (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v1 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := (let peq0 : x = (p q_v0 q_v0) := ha; let peq6 : x = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := u0b; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst0) (peq6); let pst2 : q_v0 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_right (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) (sz_lt_p_right u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := (let peq0 : x = (p q_v0 q_v0) := ha; let peq6 : x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := u0b; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst0) (peq6); let pst2 : q_v0 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p u0_x (p u0s0out (p u0_v1 u0_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p u0_x (p u0s0out (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_right u0s0out (p u0_v1 u0_v1))) (sz_lt_p_right u0_x (p u0s0out (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_v1 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := (let peq0 : x = (p q_v0 q_v0) := ha; let peq6 : x = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := u0b; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst0) (peq6); let pst2 : q_v0 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_right (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) (sz_lt_p_right u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := (let peq0 : x = (p q_v0 q_v0) := ha; let peq6 : x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := u0b; let pst0 : (p q_v0 q_v0) = x := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst0) (peq6); let pst2 : q_v0 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst1); let pst3 : (p u0_x (p u0s0out (p u0_v1 u0_v1))) = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = u0_v1 := congrArg (fun q => R q) (pst1); let pst5 : (p u0_x (p u0s0out (p u0_v1 u0_v1))) = u0_v1 := Eq.trans (pst3) (pst4); let pst6 : u0_v1 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Eq.symm (pst5); pst6)
        have hlt : sz u0_v1 < sz (p u0_x (p u0s0out (p u0_v1 u0_v1))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u0_v1 u0_v1) (sz_lt_p_right u0s0out (p u0_v1 u0_v1))) (sz_lt_p_right u0_x (p u0s0out (p u0_v1 u0_v1)))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr5 (x v0 v1 H0 : CM)
    (s0 : Step (p x x) x H0) :
    ¬ ∃ o, Code (p x (p H0 (p v1 v1))) v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases s0 with
  | raw =>
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change (p (p (p x x) x) (p v1 v1)) = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := (let peq0 : x = q_v0 := e0; let peq1 : (p (p (p x x) x) (p v1 v1)) = q_v0 := e1; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq0); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq0); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p (p x x) x) = (p (p q_v0 q_v0) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p q_v0 q_v0) x) = (p (p q_v0 q_v0) q_v0) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst5 : (p (p x x) x) = (p (p q_v0 q_v0) q_v0) := Eq.trans (pst3) (pst4); let pst6 : (p (p (p x x) x) (p v1 v1)) = (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := congrArg (fun q => p q (p v1 v1)) (pst5); let pst7 : (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) = (p (p (p x x) x) (p v1 v1)) := Eq.symm (pst6); let pst8 : (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) = q_v0 := Eq.trans (pst7) (peq1); let pst9 : q_v0 = (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := Eq.symm (pst8); pst9)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v0)) (sz_lt_p_left (p (p q_v0 q_v0) q_v0) (p v1 v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L q)) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change (p (p (p x x) x) (p v1 v1)) = q_v0 at e1
      have e2 := congrArg (fun q => q) hb
      change v1 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) at e2
      have cyc : q_v0 = (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := (let peq0 : x = q_v0 := e0; let peq1 : (p (p (p x x) x) (p v1 v1)) = q_v0 := e1; let pst0 : (p x x) = (p q_v0 x) := congrArg (fun q => p q x) (peq0); let pst1 : (p q_v0 x) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (peq0); let pst2 : (p x x) = (p q_v0 q_v0) := Eq.trans (pst0) (pst1); let pst3 : (p (p x x) x) = (p (p q_v0 q_v0) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p q_v0 q_v0) x) = (p (p q_v0 q_v0) q_v0) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst5 : (p (p x x) x) = (p (p q_v0 q_v0) q_v0) := Eq.trans (pst3) (pst4); let pst6 : (p (p (p x x) x) (p v1 v1)) = (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := congrArg (fun q => p q (p v1 v1)) (pst5); let pst7 : (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) = (p (p (p x x) x) (p v1 v1)) := Eq.symm (pst6); let pst8 : (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) = q_v0 := Eq.trans (pst7) (peq1); let pst9 : q_v0 = (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := Eq.symm (pst8); pst9)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_v0) (p v1 v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_v0)) (sz_lt_p_left (p (p q_v0 q_v0) q_v0) (p v1 v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    cases qs0 with
    | raw =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_x = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := (let peq0 : x = q_v0 := congrArg (fun q => (L q)) (ha); let peq1 : (p H0 (p v1 v1)) = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : v1 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := hb; let peq6 : x = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := u0b; let peq7 : H0 = u0_x := u0o; let pst0 : q_v0 = (p H0 (p v1 v1)) := Eq.symm (peq1); let pst1 : (p v1 v1) = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) v1) := congrArg (fun q => p q v1) (peq2); let pst2 : (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) v1) = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) := congrArg (fun q => p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) q) (peq2); let pst3 : (p v1 v1) = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) := Eq.trans (pst1) (pst2); let pst4 : (p H0 (p v1 v1)) = (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p H0 q) (pst3); let pst5 : q_v0 = (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := Eq.trans (pst0) (pst4); let pst6 : x = (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := Eq.trans (peq0) (pst5); let pst7 : (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) = x := Eq.symm (pst6); let pst8 : (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst7) (peq6); let pst9 : H0 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst8); let pst10 : (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) = u0_v1 := congrArg (fun q => R q) (pst8); let pst11 : u0_v1 = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) := Eq.symm (pst10); let pst12 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) u0_v1) = (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) q) (pst11); let pst14 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := Eq.trans (pst12) (pst13); let pst15 : (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1)) = (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)))) := congrArg (fun q => p (p (p u0_x u0_x) u0_x) q) (pst14); let pst16 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := congrArg (fun q => p u0_x q) (pst15); let pst17 : H0 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := Eq.trans (pst9) (pst16); let pst18 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) = H0 := Eq.symm (pst17); let pst19 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) = u0_x := Eq.trans (pst18) (peq7); let pst20 : u0_x = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := Eq.symm (pst19); pst20)
        have hlt : sz u0_x < sz (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := sz_lt_p_left u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_x = (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := (let peq0 : x = q_v0 := congrArg (fun q => (L q)) (ha); let peq1 : (p H0 (p v1 v1)) = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : v1 = (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) := hb; let peq6 : x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := u0b; let peq7 : H0 = u0_x := u0o; let pst0 : q_v0 = (p H0 (p v1 v1)) := Eq.symm (peq1); let pst1 : (p v1 v1) = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) v1) := congrArg (fun q => p q v1) (peq2); let pst2 : (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) v1) = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) := congrArg (fun q => p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) q) (peq2); let pst3 : (p v1 v1) = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) := Eq.trans (pst1) (pst2); let pst4 : (p H0 (p v1 v1)) = (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p H0 q) (pst3); let pst5 : q_v0 = (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := Eq.trans (pst0) (pst4); let pst6 : x = (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := Eq.trans (peq0) (pst5); let pst7 : (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) = x := Eq.symm (pst6); let pst8 : (p H0 (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst7) (peq6); let pst9 : H0 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst8); let pst10 : (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) = u0_v1 := congrArg (fun q => R q) (pst8); let pst11 : u0_v1 = (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) := Eq.symm (pst10); let pst12 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) u0_v1) = (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) q) (pst11); let pst14 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))) := Eq.trans (pst12) (pst13); let pst15 : (p u0s0out (p u0_v1 u0_v1)) = (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)))) := congrArg (fun q => p u0s0out q) (pst14); let pst16 : (p u0_x (p u0s0out (p u0_v1 u0_v1))) = (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := congrArg (fun q => p u0_x q) (pst15); let pst17 : H0 = (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := Eq.trans (pst9) (pst16); let pst18 : (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) = H0 := Eq.symm (pst17); let pst19 : (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) = u0_x := Eq.trans (pst18) (peq7); let pst20 : u0_x = (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := Eq.symm (pst19); pst20)
        have hlt : sz u0_x < sz (p u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))) := sz_lt_p_left u0_x (p u0s0out (p (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1) (p (p q_x (p (p (p q_x q_x) q_x) (p q_v1 q_v1))) q_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0s0, u0a, u0b, u0o⟩
      let u0s0out := u0_H0
      cases u0s0 with
      | raw =>
        have cyc : u0_x = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := (let peq0 : x = q_v0 := congrArg (fun q => (L q)) (ha); let peq1 : (p H0 (p v1 v1)) = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : v1 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := hb; let peq6 : x = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := u0b; let peq7 : H0 = u0_x := u0o; let pst0 : q_v0 = (p H0 (p v1 v1)) := Eq.symm (peq1); let pst1 : (p v1 v1) = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) v1) := congrArg (fun q => p q v1) (peq2); let pst2 : (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) v1) = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) := congrArg (fun q => p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) q) (peq2); let pst3 : (p v1 v1) = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) := Eq.trans (pst1) (pst2); let pst4 : (p H0 (p v1 v1)) = (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p H0 q) (pst3); let pst5 : q_v0 = (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := Eq.trans (pst0) (pst4); let pst6 : x = (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := Eq.trans (peq0) (pst5); let pst7 : (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) = x := Eq.symm (pst6); let pst8 : (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) = (p (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst7) (peq6); let pst9 : H0 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst8); let pst10 : (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) = u0_v1 := congrArg (fun q => R q) (pst8); let pst11 : u0_v1 = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) := Eq.symm (pst10); let pst12 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) u0_v1) = (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) q) (pst11); let pst14 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := Eq.trans (pst12) (pst13); let pst15 : (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1)) = (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)))) := congrArg (fun q => p (p (p u0_x u0_x) u0_x) q) (pst14); let pst16 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p u0_v1 u0_v1))) = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := congrArg (fun q => p u0_x q) (pst15); let pst17 : H0 = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := Eq.trans (pst9) (pst16); let pst18 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) = H0 := Eq.symm (pst17); let pst19 : (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) = u0_x := Eq.trans (pst18) (peq7); let pst20 : u0_x = (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := Eq.symm (pst19); pst20)
        have hlt : sz u0_x < sz (p u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := sz_lt_p_left u0_x (p (p (p u0_x u0_x) u0_x) (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit u0s0h =>
        have cyc : u0_x = (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := (let peq0 : x = q_v0 := congrArg (fun q => (L q)) (ha); let peq1 : (p H0 (p v1 v1)) = q_v0 := congrArg (fun q => (R q)) (ha); let peq2 : v1 = (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) := hb; let peq6 : x = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := u0b; let peq7 : H0 = u0_x := u0o; let pst0 : q_v0 = (p H0 (p v1 v1)) := Eq.symm (peq1); let pst1 : (p v1 v1) = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) v1) := congrArg (fun q => p q v1) (peq2); let pst2 : (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) v1) = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) := congrArg (fun q => p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) q) (peq2); let pst3 : (p v1 v1) = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) := Eq.trans (pst1) (pst2); let pst4 : (p H0 (p v1 v1)) = (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p H0 q) (pst3); let pst5 : q_v0 = (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := Eq.trans (pst0) (pst4); let pst6 : x = (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := Eq.trans (peq0) (pst5); let pst7 : (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) = x := Eq.symm (pst6); let pst8 : (p H0 (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) = (p (p u0_x (p u0s0out (p u0_v1 u0_v1))) u0_v1) := Eq.trans (pst7) (peq6); let pst9 : H0 = (p u0_x (p u0s0out (p u0_v1 u0_v1))) := congrArg (fun q => L q) (pst8); let pst10 : (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) = u0_v1 := congrArg (fun q => R q) (pst8); let pst11 : u0_v1 = (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) := Eq.symm (pst10); let pst12 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) u0_v1) := congrArg (fun q => p q u0_v1) (pst11); let pst13 : (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) u0_v1) = (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := congrArg (fun q => p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) q) (pst11); let pst14 : (p u0_v1 u0_v1) = (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))) := Eq.trans (pst12) (pst13); let pst15 : (p u0s0out (p u0_v1 u0_v1)) = (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)))) := congrArg (fun q => p u0s0out q) (pst14); let pst16 : (p u0_x (p u0s0out (p u0_v1 u0_v1))) = (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := congrArg (fun q => p u0_x q) (pst15); let pst17 : H0 = (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := Eq.trans (pst9) (pst16); let pst18 : (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) = H0 := Eq.symm (pst17); let pst19 : (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) = u0_x := Eq.trans (pst18) (peq7); let pst20 : u0_x = (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := Eq.symm (pst19); pst20)
        have hlt : sz u0_x < sz (p u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))) := sz_lt_p_left u0_x (p u0s0out (p (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1)) (p (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1) (p (p q_x (p q_H0 (p q_v1 q_v1))) q_v1))))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 v0) (eval (eval x (eval (eval (eval x x) x) (eval v1 v1))) v1)) := by
  let H0 := eval (eval x x) x
  have e0a : (eval x x) = (p x x) := by
    change (eval x x) = (p x x)
    exact (eval_raw (nr1 x v0 v1))
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step (p x x) x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step (eval x x) x
  change x = (eval (eval v0 v0) (eval (eval x (eval H0 (eval v1 v1))) v1))
  have rawEq : (eval (eval v0 v0) (eval (eval x (eval H0 (eval v1 v1))) v1)) = (eval (p v0 v0) (p (p x (p H0 (p v1 v1))) v1)) := by
    calc
      (eval (eval v0 v0) (eval (eval x (eval H0 (eval v1 v1))) v1)) = (eval (p v0 v0) (eval (eval x (eval H0 (eval v1 v1))) v1)) := congrArg (fun q => (eval q (eval (eval x (eval H0 (eval v1 v1))) v1))) (eval_raw (nr0 x v0 v1))
      _ = (eval (p v0 v0) (eval (eval x (eval H0 (p v1 v1))) v1)) := congrArg (fun q => (eval (p v0 v0) (eval (eval x (eval H0 q)) v1))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p v0 v0) (eval (eval x (p H0 (p v1 v1))) v1)) := congrArg (fun q => (eval (p v0 v0) (eval (eval x q) v1))) (eval_raw (nr3 x v0 v1 H0 s0))
      _ = (eval (p v0 v0) (eval (p x (p H0 (p v1 v1))) v1)) := congrArg (fun q => (eval (p v0 v0) (eval q v1))) (eval_raw (nr4 x v0 v1 H0 s0))
      _ = (eval (p v0 v0) (p (p x (p H0 (p v1 v1))) v1)) := congrArg (fun q => (eval (p v0 v0) q)) (eval_raw (nr5 x v0 v1 H0 s0))
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
