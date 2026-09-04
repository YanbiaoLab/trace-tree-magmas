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
      (s0 : Step x (p v1 v1) H0) :
      Code (p (p v0 v0) (p H0 x)) v1 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_x (p q_v1 q_v1) q_H0 ∧ a = (p (p q_v0 q_v0) (p q_H0 q_x)) ∧ b = q_v1 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
def CodeArg :=
  PSigma fun a : CM => PSigma fun b : CM => PSigma fun o : CM => Code a b o
theorem code_bounds_core (q : CodeArg) : sz q.2.1 < sz q.1 ∧ sz q.2.2.1 < sz q.1 := by
  rcases q with ⟨a, b, o, h⟩
  rcases code_shape h with ⟨x, v0, v1, H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst x
  cases s0 with
  | raw =>
    simp only [getOut, L, R, U, sz] <;> omega
  | hit s0h =>
    have s0hB := code_bounds_core ⟨_, _, _, s0h⟩
    simp only [getOut, L, R, U, sz] at s0hB ⊢ <;> omega
termination_by sz q.1
decreasing_by
  all_goals try subst a
  all_goals try subst b
  all_goals try subst o
  all_goals simp_all [sz] <;> omega
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a :=
  code_bounds_core ⟨a, b, o, h⟩
theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
    omega
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz b < sz (p o a) := by
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
    change v0 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v1 at e1
    have cyc : q_v1 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := (let peq0 : v0 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := e0; let peq1 : v0 = q_v1 := e1; let pst0 : (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = q_v1 := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v1 < sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right q_x (p q_v1 q_v1))) (sz_lt_p_left (p q_x (p q_v1 q_v1)) q_x)) (sz_lt_p_right (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have hcB := code_bounds hc
    have qs0hB := code_bounds qs0h
    have qs0B := qs0B
    have p0 := ha
    change v0 = (p (p q_v0 q_v0) (p q_H0 q_x)) at p0
    have z0 := congrArg sz p0
    have p1 := hb
    change v0 = q_v1 at p1
    have z1 := congrArg sz p1
    have p2 := ho
    change o = q_x at p2
    have z2 := congrArg sz p2
    have hx := hcB.1
    rw [p0] at hx
    have selflt : sz (p (p q_v0 q_v0) (p q_H0 q_x)) < sz (p (p q_v0 q_v0) (p q_H0 q_x)) := hx
    exact (Nat.lt_irrefl _ selflt).elim
theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v1 = q_v1 at e1
    have cyc : q_v1 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := (let peq0 : v1 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := e0; let peq1 : v1 = q_v1 := e1; let pst0 : (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = q_v1 := Eq.trans (pst0) (peq1); let pst2 : q_v1 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v1 < sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_right q_x (p q_v1 q_v1))) (sz_lt_p_left (p q_x (p q_v1 q_v1)) q_x)) (sz_lt_p_right (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have hcB := code_bounds hc
    have qs0hB := code_bounds qs0h
    have qs0B := qs0B
    have p0 := ha
    change v1 = (p (p q_v0 q_v0) (p q_H0 q_x)) at p0
    have z0 := congrArg sz p0
    have p1 := hb
    change v1 = q_v1 at p1
    have z1 := congrArg sz p1
    have p2 := ho
    change o = q_x at p2
    have z2 := congrArg sz p2
    have hx := hcB.1
    rw [p0] at hx
    have selflt : sz (p (p q_v0 q_v0) (p q_H0 q_x)) < sz (p (p q_v0 q_v0) (p q_H0 q_x)) := hx
    exact (Nat.lt_irrefl _ selflt).elim
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step x (p v1 v1) H0) :
    ¬ ∃ o, Code H0 x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_x := (let peq1 : v1 = q_H0 := congrArg (fun q => (L (R q))) (ha); let peq2 : v1 = q_x := congrArg (fun q => (R (R q))) (ha); let pst0 : q_H0 = v1 := Eq.symm (peq1); let pst1 : q_H0 = q_x := Eq.trans (pst0) (peq2); pst1)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change H0 = (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change x = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v1 < sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := by
        have q := hcB.1
        have eu : sz x = sz q_v1 := congrArg sz (p1)
        have ev : sz H0 = sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := congrArg sz (p0)
        have q1 : sz q_v1 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) < sz q_v1 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := congrArg sz (p0)
        have eu : sz x = sz q_v1 := congrArg sz (p1)
        have q1 : sz (p (p q_v0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) < sz x := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change H0 = (p (p q_v0 q_v0) (p q_H0 q_x)) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change x = q_v1 at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v1 < sz (p (p q_v0 q_v0) (p q_H0 q_x)) := by
        have q := hcB.1
        have eu : sz x = sz q_v1 := congrArg sz (p1)
        have ev : sz H0 = sz (p (p q_v0 q_v0) (p q_H0 q_x)) := congrArg sz (p0)
        have q1 : sz q_v1 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p q_v0 q_v0) (p q_H0 q_x)) < sz q_v1 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p (p q_v0 q_v0) (p q_H0 q_x)) := congrArg sz (p0)
        have eu : sz x = sz q_v1 := congrArg sz (p1)
        have q1 : sz (p (p q_v0 q_v0) (p q_H0 q_x)) < sz x := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step x (p v1 v1) H0) :
    ¬ ∃ o, Code (p v0 v0) (p H0 x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_x := (let peq0 : v0 = (p q_v0 q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_H0 q_x) := congrArg (fun q => (R q)) (ha); let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_H0 q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_H0 := congrArg (fun q => L q) (pst1); let pst3 : q_H0 = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst5 : q_H0 = q_x := Eq.trans (pst3) (pst4); pst5)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have he : q_H0 = q_x := (let peq0 : v0 = (p q_v0 q_v0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p q_H0 q_x) := congrArg (fun q => (R q)) (ha); let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_H0 q_x) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_H0 := congrArg (fun q => L q) (pst1); let pst3 : q_H0 = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_x := congrArg (fun q => R q) (pst1); let pst5 : q_H0 = q_x := Eq.trans (pst3) (pst4); pst5)
    exact step_ne_first (by simpa only [he] using qs0)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 v0) (eval (eval x (eval v1 v1)) x)) v1) := by
  let H0 := eval x (eval v1 v1)
  have e0a : x = x := by
    change x = x
    rfl
  have e0b : (eval v1 v1) = (p v1 v1) := by
    change (eval v1 v1) = (p v1 v1)
    exact (eval_raw (nr1 x v0 v1))
  have s0 : Step x (p v1 v1) H0 := by
    rw [← e0a, ← e0b]
    exact eval_step x (eval v1 v1)
  change x = (eval (eval (eval v0 v0) (eval H0 x)) v1)
  have rawEq : (eval (eval (eval v0 v0) (eval H0 x)) v1) = (eval (p (p v0 v0) (p H0 x)) v1) := by
    calc
      (eval (eval (eval v0 v0) (eval H0 x)) v1) = (eval (eval (p v0 v0) (eval H0 x)) v1) := congrArg (fun q => (eval (eval q (eval H0 x)) v1)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval (p v0 v0) (p H0 x)) v1) := congrArg (fun q => (eval (eval (p v0 v0) q) v1)) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval (p (p v0 v0) (p H0 x)) v1) := congrArg (fun q => (eval q v1)) (eval_raw (nr3 x v0 v1 H0 s0))
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
