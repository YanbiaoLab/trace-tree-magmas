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
  | law (x v0 v1 H0 H1 : CM)
      (s0 : Step v0 v1 H0)
      (s1 : Step x (p v0 v0) H1) :
      Code (p H0 (p H1 x)) (p v0 v0) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_x (p q_v0 q_v0) q_H1 ∧ a = (p q_H0 (p q_H1 q_x)) ∧ b = (p q_v0 q_v0) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
def CodeArg := (a : CM) ×' (b : CM) ×' (o : CM) ×' Code a b o
def StepArg := (a : CM) ×' (b : CM) ×' (o : CM) ×' Step a b o
mutual
theorem code_bounds_core (q : CodeArg) :
    sz q.2.1 < sz q.1 ∧ sz q.2.2.1 < sz q.1 := by
  rcases q with ⟨a, b, o, h⟩
  rcases code_shape h with ⟨x, v0, v1, H0, H1, s0, s1, ha, hb, ho⟩
  subst a
  subst b
  subst x
  exact ⟨Nat.lt_trans (step_bound_core ⟨_, _, _, s1⟩) (sz_lt_p_right H0 (p H1 o)), Nat.lt_trans (sz_lt_p_right H1 o) (sz_lt_p_right H0 (p H1 o))⟩
termination_by sz q.1
decreasing_by simp_all [sz] <;> omega
theorem step_bound_core (q : StepArg) :
    sz q.2.1 < sz (p q.2.2.1 q.1) := by
  rcases q with ⟨a, b, o, h⟩
  cases h with
  | raw => simp only [sz] <;> omega
  | hit hc => exact Nat.lt_trans ((code_bounds_core ⟨_, _, _, hc⟩).1) (sz_lt_p_right o a)
termination_by sz (p q.2.2.1 q.1)
decreasing_by simp_all only [sz] <;> omega
end
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a :=
  code_bounds_core ⟨a, b, o, h⟩
theorem step_bound {a b o : CM} (h : Step a b o) :
    sz b < sz (p o a) :=
  step_bound_core ⟨a, b, o, h⟩
theorem step_ne_first {a b : CM} : ¬ Step a b a := by
  intro h
  cases h with
  | hit hc =>
    have hb := (code_bounds hc).2
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have he : q_H0 = q_v0 := (let peq0 : v0 = (p q_H0 (p q_H1 q_x)) := ha; let peq1 : v0 = (p q_v0 q_v0) := hb; let pst0 : (p q_H0 (p q_H1 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_H1 q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_H1 q_x) := Eq.symm (pst3); let pst5 : q_H0 = (p q_H1 q_x) := Eq.trans (pst2) (pst4); let pst6 : (p q_H1 q_x) = q_v0 := Eq.symm (pst4); let pst7 : q_H0 = q_v0 := Eq.trans (pst5) (pst6); pst7)
  exact step_ne_first (by simpa only [he] using qs0)
theorem nr1 (x v0 v1 H1 : CM)
    (s1 : Step x (p v0 v0) H1) :
    ¬ ∃ o, Code H1 x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1B := step_bound s1
  cases s1 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have he : q_H1 = q_x := (let peq1 : v0 = q_H1 := congrArg (fun q => (L (R q))) (ha); let peq2 : v0 = q_x := congrArg (fun q => (R (R q))) (ha); let pst0 : q_H1 = v0 := Eq.symm (peq1); let pst1 : q_H1 = q_x := Eq.trans (pst0) (peq2); pst1)
      exact step_ne_first (by simpa only [he] using qs1)
    | hit qs0h =>
      have he : q_H1 = q_x := (let peq1 : v0 = q_H1 := congrArg (fun q => (L (R q))) (ha); let peq2 : v0 = q_x := congrArg (fun q => (R (R q))) (ha); let pst0 : q_H1 = v0 := Eq.symm (peq1); let pst1 : q_H1 = q_x := Eq.trans (pst0) (peq2); pst1)
      exact step_ne_first (by simpa only [he] using qs1)
  | hit s1h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p (p q_v0 q_v1) (p (p q_x (p q_v0 q_v0)) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change x = (p q_v0 q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz (p q_v0 q_v0) < sz (p (p q_v0 q_v1) (p (p q_x (p q_v0 q_v0)) q_x)) := by
          have q := hcB.1
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have ev : sz H1 = sz (p (p q_v0 q_v1) (p (p q_x (p q_v0 q_v0)) q_x)) := congrArg sz (p0)
          have q1 : sz (p q_v0 q_v0) < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p (p q_v0 q_v1) (p (p q_x (p q_v0 q_v0)) q_x)) < sz (p q_v0 q_v0) := by
          have q := s1hB.2
          have ev : sz H1 = sz (p (p q_v0 q_v1) (p (p q_x (p q_v0 q_v0)) q_x)) := congrArg sz (p0)
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have q1 : sz (p (p q_v0 q_v1) (p (p q_x (p q_v0 q_v0)) q_x)) < sz x := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p (p q_v0 q_v1) (p q_H1 q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change x = (p q_v0 q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz (p q_v0 q_v0) < sz (p (p q_v0 q_v1) (p q_H1 q_x)) := by
          have q := hcB.1
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have ev : sz H1 = sz (p (p q_v0 q_v1) (p q_H1 q_x)) := congrArg sz (p0)
          have q1 : sz (p q_v0 q_v0) < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p (p q_v0 q_v1) (p q_H1 q_x)) < sz (p q_v0 q_v0) := by
          have q := s1hB.2
          have ev : sz H1 = sz (p (p q_v0 q_v1) (p q_H1 q_x)) := congrArg sz (p0)
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have q1 : sz (p (p q_v0 q_v1) (p q_H1 q_x)) < sz x := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have qs1B := step_bound qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p q_H0 (p (p q_x (p q_v0 q_v0)) q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change x = (p q_v0 q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz (p q_v0 q_v0) < sz (p q_H0 (p (p q_x (p q_v0 q_v0)) q_x)) := by
          have q := hcB.1
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have ev : sz H1 = sz (p q_H0 (p (p q_x (p q_v0 q_v0)) q_x)) := congrArg sz (p0)
          have q1 : sz (p q_v0 q_v0) < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_H0 (p (p q_x (p q_v0 q_v0)) q_x)) < sz (p q_v0 q_v0) := by
          have q := s1hB.2
          have ev : sz H1 = sz (p q_H0 (p (p q_x (p q_v0 q_v0)) q_x)) := congrArg sz (p0)
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have q1 : sz (p q_H0 (p (p q_x (p q_v0 q_v0)) q_x)) < sz x := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have s1B := s1B
        have qs0B := qs0B
        have qs1B := qs1B
        have p0 := ha
        change H1 = (p q_H0 (p q_H1 q_x)) at p0
        have z0 := congrArg sz p0
        have p1 := hb
        change x = (p q_v0 q_v0) at p1
        have z1 := congrArg sz p1
        have p2 := ho
        change o = q_x at p2
        have z2 := congrArg sz p2
        have hx : sz (p q_v0 q_v0) < sz (p q_H0 (p q_H1 q_x)) := by
          have q := hcB.1
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have ev : sz H1 = sz (p q_H0 (p q_H1 q_x)) := congrArg sz (p0)
          have q1 : sz (p q_v0 q_v0) < sz H1 := lt_of_eq_of_lt eu.symm q
          exact lt_of_lt_of_eq q1 ev
        have hy : sz (p q_H0 (p q_H1 q_x)) < sz (p q_v0 q_v0) := by
          have q := s1hB.2
          have ev : sz H1 = sz (p q_H0 (p q_H1 q_x)) := congrArg sz (p0)
          have eu : sz x = sz (p q_v0 q_v0) := congrArg sz (p1)
          have q1 : sz (p q_H0 (p q_H1 q_x)) < sz x := lt_of_eq_of_lt ev.symm q
          exact lt_of_lt_of_eq q1 eu
        exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr2 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 v1 H0)
    (s1 : Step x (p v0 v0) H1) :
    ¬ ∃ o, Code H0 (p H1 x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : H1 = x := (let peq2 : H1 = q_v0 := congrArg (fun q => (L q)) (hb); let peq3 : x = q_v0 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq3); let pst1 : H1 = x := Eq.trans (peq2) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
  | hit s0h =>
    have he : H1 = x := (let peq1 : H1 = q_v0 := congrArg (fun q => (L q)) (hb); let peq2 : x = q_v0 := congrArg (fun q => (R q)) (hb); let pst0 : q_v0 = x := Eq.symm (peq2); let pst1 : H1 = x := Eq.trans (peq1) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have he : q_H0 = q_v0 := (let peq0 : v0 = (p q_H0 (p q_H1 q_x)) := ha; let peq1 : v0 = (p q_v0 q_v0) := hb; let pst0 : (p q_H0 (p q_H1 q_x)) = v0 := Eq.symm (peq0); let pst1 : (p q_H0 (p q_H1 q_x)) = (p q_v0 q_v0) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_H1 q_x) = q_v0 := congrArg (fun q => R q) (pst1); let pst4 : q_v0 = (p q_H1 q_x) := Eq.symm (pst3); let pst5 : q_H0 = (p q_H1 q_x) := Eq.trans (pst2) (pst4); let pst6 : (p q_H1 q_x) = q_v0 := Eq.symm (pst4); let pst7 : q_H0 = q_v0 := Eq.trans (pst5) (pst6); pst7)
  exact step_ne_first (by simpa only [he] using qs0)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval v0 v1) (eval (eval x (eval v0 v0)) x)) (eval v0 v0)) := by
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
  let H1 := eval x (eval v0 v0)
  have e1a : x = x := by
    change x = x
    rfl
  have e1b : (eval v0 v0) = (p v0 v0) := by
    change (eval v0 v0) = (p v0 v0)
    exact (eval_raw (nr0 x v0 v1))
  have s1 : Step x (p v0 v0) H1 := by
    rw [← e1a, ← e1b]
    exact eval_step x (eval v0 v0)
  change x = (eval (eval H0 (eval H1 x)) (eval v0 v0))
  have rawEq : (eval (eval H0 (eval H1 x)) (eval v0 v0)) = (eval (p H0 (p H1 x)) (p v0 v0)) := by
    calc
      (eval (eval H0 (eval H1 x)) (eval v0 v0)) = (eval (eval H0 (p H1 x)) (eval v0 v0)) := congrArg (fun q => (eval (eval H0 q) (eval v0 v0))) (eval_raw (nr1 x v0 v1 H1 s1))
      _ = (eval (p H0 (p H1 x)) (eval v0 v0)) := congrArg (fun q => (eval q (eval v0 v0))) (eval_raw (nr2 x v0 v1 H0 H1 s0 s1))
      _ = (eval (p H0 (p H1 x)) (p v0 v0)) := congrArg (fun q => (eval (p H0 (p H1 x)) q)) (eval_raw (nr3 x v0 v1))
  exact (eval_hit (Code.law x v0 v1 H0 H1 s0 s1)).symm.trans rawEq.symm
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
