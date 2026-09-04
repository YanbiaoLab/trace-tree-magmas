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
      (s1 : Step x (p v1 v1) H1) :
      Code (p (p H0 v0) (p H1 x)) (p v1 v1) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_v1 q_H0 ∧ Step q_x (p q_v1 q_v1) q_H1 ∧ a = (p (p q_H0 q_v0) (p q_H1 q_x)) ∧ b = (p q_v1 q_v1) ∧ o = q_x := by
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
  exact ⟨Nat.lt_trans (step_bound_core ⟨_, _, _, s1⟩) (sz_lt_p_right (p H0 v0) (p H1 o)), Nat.lt_trans (sz_lt_p_right H1 o) (sz_lt_p_right (p H0 v0) (p H1 o))⟩
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
theorem code_no_pair_left (v k : CM) :
    ¬ ∃ o, Code (p v k) v o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have he : q_H0 = q_v0 := (let peq0 : v = (p q_H0 q_v0) := congrArg (fun q => (L q)) (ha); let peq2 : v = (p q_v1 q_v1) := hb; let pst0 : (p q_H0 q_v0) = v := Eq.symm (peq0); let pst1 : (p q_H0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst0) (peq2); let pst2 : q_H0 = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst4 : q_v1 = q_v0 := Eq.symm (pst3); let pst5 : q_H0 = q_v0 := Eq.trans (pst2) (pst4); pst5)
  exact step_ne_first (by simpa only [he] using qs0)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw => exact code_no_pair_left a b
  | hit sh =>
    rintro ⟨u, hk⟩
    have ho := (code_bounds sh).2
    have ha := (code_bounds hk).1
    omega
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step v0 v1 H0) :
    ¬ ∃ o, Code H0 v0 o := by
  exact step_no_first s0

theorem nr1 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 q_v1) at e1
      have cyc : q_v1 = (p (p q_v0 q_v1) q_v0) := (let peq0 : v1 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v1) q_v0) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p (p q_v0 q_v1) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p (p q_v0 q_v1) q_v0) := Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 q_v1) at e1
      have cyc : q_v1 = (p (p q_v0 q_v1) q_v0) := (let peq0 : v1 = (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v1) q_v0) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p (p q_v0 q_v1) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p (p q_v0 q_v1) q_v0) := Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 q_v1) at e1
      have cyc : q_H0 = (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := (let peq0 : v1 = (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_H0 q_v0) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p q_H0 q_v0) := Eq.symm (pst2); let pst4 : (p q_v1 q_v1) = (p (p q_H0 q_v0) q_v1) := congrArg (fun q => p q q_v1) (pst3); let pst5 : (p (p q_H0 q_v0) q_v1) = (p (p q_H0 q_v0) (p q_H0 q_v0)) := congrArg (fun q => p (p q_H0 q_v0) q) (pst3); let pst6 : (p q_v1 q_v1) = (p (p q_H0 q_v0) (p q_H0 q_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p q_x (p q_v1 q_v1)) = (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p (p q_x (p q_v1 q_v1)) q_x) = (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) := congrArg (fun q => p q q_x) (pst7); let pst9 : (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) = (p (p q_x (p q_v1 q_v1)) q_x) := Eq.symm (pst8); let pst10 : (p (p q_x (p q_v1 q_v1)) q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst11 : (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) = q_v1 := Eq.trans (pst9) (pst10); let pst12 : (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) = (p q_H0 q_v0) := Eq.trans (pst11) (pst3); let pst13 : (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) = q_H0 := congrArg (fun q => L q) (pst12); let pst14 : q_H0 = (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := Eq.symm (pst13); pst14)
      have hlt : sz q_H0 < sz (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p q_H0 q_v0))) (sz_lt_p_right q_x (p (p q_H0 q_v0) (p q_H0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v1 = (p (p q_H0 q_v0) (p q_H1 q_x)) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v1 = (p q_v1 q_v1) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p (p q_H0 q_v0) (p q_H1 q_x)) < sz (p (p q_H0 q_v0) (p q_H1 q_x)) := hx
      exact (Nat.lt_irrefl _ selflt).elim
theorem nr2 (x v0 v1 H1 : CM)
    (s1 : Step x (p v1 v1) H1) :
    ¬ ∃ o, Code H1 x o := by
  exact step_no_first s1

theorem nr3 (x v0 v1 H0 H1 : CM)
    (s0 : Step v0 v1 H0)
    (s1 : Step x (p v1 v1) H1) :
    ¬ ∃ o, Code (p H0 v0) (p H1 x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0B := step_bound s0
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have he : H1 = x := (let peq3 : H1 = q_v1 := congrArg (fun q => (L q)) (hb); let peq4 : x = q_v1 := congrArg (fun q => (R q)) (hb); let pst0 : q_v1 = x := Eq.symm (peq4); let pst1 : H1 = x := Eq.trans (peq3) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
  | hit s0h =>
    have he : H1 = x := (let peq2 : H1 = q_v1 := congrArg (fun q => (L q)) (hb); let peq3 : x = q_v1 := congrArg (fun q => (R q)) (hb); let pst0 : q_v1 = x := Eq.symm (peq3); let pst1 : H1 = x := Eq.trans (peq2) (pst0); pst1)
    exact step_ne_first (by simpa only [he] using s1)
theorem nr4 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 v1 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have qs0B := step_bound qs0
  have qs0N := step_no_first qs0
  cases qs0 with
  | raw =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 q_v1) at e1
      have cyc : q_v1 = (p (p q_v0 q_v1) q_v0) := (let peq0 : v1 = (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v1) q_v0) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p (p q_v0 q_v1) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p (p q_v0 q_v1) q_v0) := Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 q_v1) at e1
      have cyc : q_v1 = (p (p q_v0 q_v1) q_v0) := (let peq0 : v1 = (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v1) q_v0) (p q_H1 q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p (p q_v0 q_v1) q_v0) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p (p q_v0 q_v1) q_v0) := Eq.symm (pst2); pst3)
      have hlt : sz q_v1 < sz (p (p q_v0 q_v1) q_v0) := Nat.lt_trans (sz_lt_p_right q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) q_v0)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have qs1B := step_bound qs1
    have qs1N := step_no_first qs1
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v1 = (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) at e0
      have e1 := congrArg (fun q => q) hb
      change v1 = (p q_v1 q_v1) at e1
      have cyc : q_H0 = (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := (let peq0 : v1 = (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) := e0; let peq1 : v1 = (p q_v1 q_v1) := e1; let pst0 : (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = v1 := Eq.symm (peq0); let pst1 : (p (p q_H0 q_v0) (p (p q_x (p q_v1 q_v1)) q_x)) = (p q_v1 q_v1) := Eq.trans (pst0) (peq1); let pst2 : (p q_H0 q_v0) = q_v1 := congrArg (fun q => L q) (pst1); let pst3 : q_v1 = (p q_H0 q_v0) := Eq.symm (pst2); let pst4 : (p q_v1 q_v1) = (p (p q_H0 q_v0) q_v1) := congrArg (fun q => p q q_v1) (pst3); let pst5 : (p (p q_H0 q_v0) q_v1) = (p (p q_H0 q_v0) (p q_H0 q_v0)) := congrArg (fun q => p (p q_H0 q_v0) q) (pst3); let pst6 : (p q_v1 q_v1) = (p (p q_H0 q_v0) (p q_H0 q_v0)) := Eq.trans (pst4) (pst5); let pst7 : (p q_x (p q_v1 q_v1)) = (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p (p q_x (p q_v1 q_v1)) q_x) = (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) := congrArg (fun q => p q q_x) (pst7); let pst9 : (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) = (p (p q_x (p q_v1 q_v1)) q_x) := Eq.symm (pst8); let pst10 : (p (p q_x (p q_v1 q_v1)) q_x) = q_v1 := congrArg (fun q => R q) (pst1); let pst11 : (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) = q_v1 := Eq.trans (pst9) (pst10); let pst12 : (p (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) q_x) = (p q_H0 q_v0) := Eq.trans (pst11) (pst3); let pst13 : (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) = q_H0 := congrArg (fun q => L q) (pst12); let pst14 : q_H0 = (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := Eq.symm (pst13); pst14)
      have hlt : sz q_H0 < sz (p q_x (p (p q_H0 q_v0) (p q_H0 q_v0))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_H0 q_v0) (sz_lt_p_left (p q_H0 q_v0) (p q_H0 q_v0))) (sz_lt_p_right q_x (p (p q_H0 q_v0) (p q_H0 q_v0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have hcB := code_bounds hc
      have qs0hB := code_bounds qs0h
      have qs1hB := code_bounds qs1h
      have qs0B := qs0B
      have qs1B := qs1B
      have p0 := ha
      change v1 = (p (p q_H0 q_v0) (p q_H1 q_x)) at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change v1 = (p q_v1 q_v1) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx := hcB.1
      rw [p0] at hx
      have selflt : sz (p (p q_H0 q_v0) (p q_H1 q_x)) < sz (p (p q_H0 q_v0) (p q_H1 q_x)) := hx
      exact (Nat.lt_irrefl _ selflt).elim
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 v1) v0) (eval (eval x (eval v1 v1)) x)) (eval v1 v1)) := by
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
  let H1 := eval x (eval v1 v1)
  have e1a : x = x := by
    change x = x
    rfl
  have e1b : (eval v1 v1) = (p v1 v1) := by
    change (eval v1 v1) = (p v1 v1)
    exact (eval_raw (nr1 x v0 v1))
  have s1 : Step x (p v1 v1) H1 := by
    rw [← e1a, ← e1b]
    exact eval_step x (eval v1 v1)
  change x = (eval (eval (eval H0 v0) (eval H1 x)) (eval v1 v1))
  have rawEq : (eval (eval (eval H0 v0) (eval H1 x)) (eval v1 v1)) = (eval (p (p H0 v0) (p H1 x)) (p v1 v1)) := by
    calc
      (eval (eval (eval H0 v0) (eval H1 x)) (eval v1 v1)) = (eval (eval (p H0 v0) (eval H1 x)) (eval v1 v1)) := congrArg (fun q => (eval (eval q (eval H1 x)) (eval v1 v1))) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval (eval (p H0 v0) (p H1 x)) (eval v1 v1)) := congrArg (fun q => (eval (eval (p H0 v0) q) (eval v1 v1))) (eval_raw (nr2 x v0 v1 H1 s1))
      _ = (eval (p (p H0 v0) (p H1 x)) (eval v1 v1)) := congrArg (fun q => (eval q (eval v1 v1))) (eval_raw (nr3 x v0 v1 H0 H1 s0 s1))
      _ = (eval (p (p H0 v0) (p H1 x)) (p v1 v1)) := congrArg (fun q => (eval (p (p H0 v0) (p H1 x)) q)) (eval_raw (nr4 x v0 v1))
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
