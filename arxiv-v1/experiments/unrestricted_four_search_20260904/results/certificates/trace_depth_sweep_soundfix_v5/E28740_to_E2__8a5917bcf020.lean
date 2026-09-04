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
      (s0 : Step x v1 H0) :
      Code (p (p (p v0 v0) x) v0) H0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_x q_v1 q_H0 ∧ a = (p (p (p q_v0 q_v0) q_x) q_v0) ∧ b = q_H0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (L a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
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
theorem nr0 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p q_v0 q_v0) q_x) q_v0) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p q_x q_v1) at e1
    have cyc : q_x = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_x) q_v0) := e0; let peq1 : v0 = (p q_x q_v1) := e1; let pst0 : (p (p (p q_v0 q_v0) q_x) q_v0) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_x) q_v0) = (p q_x q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v0) q_x) = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = (p (p q_v0 q_v0) q_x) := Eq.symm (pst2); pst3)
    have hlt : sz q_x < sz (p (p q_v0 q_v0) q_x) := sz_lt_p_right (p q_v0 q_v0) q_x
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have hcB := code_bounds hc
    have qs0hB := code_bounds qs0h
    have p0 := ha
    change v0 = (p (p (p q_v0 q_v0) q_x) q_v0) at p0
    have z0 := congrArg sz p0
    have p1 := hb
    change v0 = q_H0 at p1
    have z1 := congrArg sz p1
    have p2 := ho
    change o = q_x at p2
    have z2 := congrArg sz p2
    have hx : sz q_x < sz (p (p (p q_v0 q_v0) q_x) q_v0) := by
      have q := hcB
      have eu : sz o = sz q_x := congrArg sz (ho)
      have ev : sz v0 = sz (p (p (p q_v0 q_v0) q_x) q_v0) := congrArg sz (p0)
      have q1 : sz q_x < sz v0 := lt_of_eq_of_lt eu.symm q
      exact lt_of_lt_of_eq q1 ev
    have hy : sz (p (p (p q_v0 q_v0) q_x) q_v0) < sz q_x := by
      have q := qs0hB
      have ev : sz q_H0 = sz (p (p (p q_v0 q_v0) q_x) q_v0) := congrArg sz (Eq.trans (p1.symm) (p0))
      have eu : sz q_x = sz q_x := congrArg sz (rfl)
      have q1 : sz (p (p (p q_v0 q_v0) q_x) q_v0) < sz q_x := lt_of_eq_of_lt ev.symm q
      exact lt_of_lt_of_eq q1 eu
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p v0 v0) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => (L q)) ha
    change v0 = (p (p q_v0 q_v0) q_x) at e0
    have e1 := congrArg (fun q => (R q)) ha
    change v0 = q_v0 at e1
    have e2 := congrArg (fun q => q) hb
    change x = (p q_x q_v1) at e2
    have cyc : q_v0 = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p (p q_v0 q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_v0 q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_v0 q_v0) q_x) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_x)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => (L q)) ha
    change v0 = (p (p q_v0 q_v0) q_x) at e0
    have e1 := congrArg (fun q => (R q)) ha
    change v0 = q_v0 at e1
    have e2 := congrArg (fun q => q) hb
    change x = q_H0 at e2
    have cyc : q_v0 = (p (p q_v0 q_v0) q_x) := (let peq0 : v0 = (p (p q_v0 q_v0) q_x) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p q_v0 q_v0) q_x) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_x) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p q_v0 q_v0) q_x) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p q_v0 q_v0) q_x) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_x)
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p (p v0 v0) x) v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have he : q_H0 = q_x := (let peq0 : v0 = (p q_v0 q_v0) := congrArg (fun q => (L (L q))) (ha); let peq1 : v0 = q_x := congrArg (fun q => (R (L q))) (ha); let peq3 : v0 = q_H0 := hb; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = q_H0 := Eq.trans (pst0) (peq3); let pst2 : q_H0 = (p q_v0 q_v0) := Eq.symm (pst1); let pst3 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst4 : (p q_v0 q_v0) = q_x := Eq.trans (pst3) (peq1); let pst5 : q_x = (p q_v0 q_v0) := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = q_x := Eq.symm (pst5); let pst7 : q_H0 = q_x := Eq.trans (pst2) (pst6); pst7)
  exact step_ne_first (by simpa only [he] using qs0)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 v0) x) v0) (eval x v1)) := by
  let H0 := eval x v1
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : v1 = v1 := by
    change v1 = v1
    rfl
  have s0 : Step x v1 H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x v1
  change x = (eval (eval (eval (eval v0 v0) x) v0) H0)
  have rawEq : (eval (eval (eval (eval v0 v0) x) v0) H0) = (eval (p (p (p v0 v0) x) v0) H0) := by
    calc
      (eval (eval (eval (eval v0 v0) x) v0) H0) = (eval (eval (eval (p v0 v0) x) v0) H0) := congrArg (fun q => (eval (eval (eval q x) v0) H0)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval (p (p v0 v0) x) v0) H0) := congrArg (fun q => (eval (eval q v0) H0)) (eval_raw (nr1 x v0 v1))
      _ = (eval (p (p (p v0 v0) x) v0) H0) := congrArg (fun q => (eval q H0)) (eval_raw (nr2 x v0 v1))
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
