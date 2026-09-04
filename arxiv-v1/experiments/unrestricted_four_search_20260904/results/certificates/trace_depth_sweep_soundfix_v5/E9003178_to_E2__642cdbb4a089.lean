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
      (s0 : Step v0 x H0) :
      Code v0 (p (p x H0) (p v1 (p v0 (p v0 (p v0 v0))))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v0 q_x q_H0 ∧ a = q_v0 ∧ b = (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) ∧ o = q_x := by
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
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code x H0 o := by
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
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x (p q_v0 q_x)) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) at e2
      have cyc : q_v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 (p q_v0 q_v0))) (sz_lt_p_right q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = (p q_x q_H0) at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) at e2
      have cyc : q_v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 (p q_v0 q_v0))) (sz_lt_p_right q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v0 < sz (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := by
        have q := hcB.1
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have ev : sz H0 = sz (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := congrArg sz (p1)
        have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) < sz q_v0 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := congrArg sz (p1)
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have q1 : sz (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) < sz x := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
    | hit qs0h =>
      have hcB := code_bounds hc
      have s0hB := code_bounds s0h
      have qs0hB := code_bounds qs0h
      have s0B := s0B
      have qs0B := qs0B
      have p0 := ha
      change x = q_v0 at p0
      have z0 := congrArg sz p0
      have p1 := hb
      change H0 = (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v0 < sz (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := by
        have q := hcB.1
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have ev : sz H0 = sz (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := congrArg sz (p1)
        have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) < sz q_v0 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := congrArg sz (p1)
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have q1 : sz (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) < sz x := lt_of_eq_of_lt ev.symm q
        exact lt_of_lt_of_eq q1 eu
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hx) hy).elim
theorem nr1 (x v0 v1 : CM)
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
    change v0 = (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) at e1
    have cyc : q_v0 = (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))) (sz_lt_p_left (p q_x (p q_v0 q_x)) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) at e1
    have cyc : q_v0 = (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 (p q_v0 (p q_v0 q_v0))) (sz_lt_p_right q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0))))) (sz_lt_p_right (p q_x q_H0) (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x (p q_v0 q_x)) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) at e2
    have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 q_x)) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x q_H0) at e1
    have e2 := congrArg (fun q => (R q)) hb
    change v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) at e2
    have cyc : q_H0 = (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0)))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_x q_H0) := e1; let peq2 : v0 = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_H0) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_H0) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_H0) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_H0) = (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) := Eq.trans (pst3) (peq2); let pst5 : (p q_v0 (p q_v0 (p q_v0 q_v0))) = (p (p q_x q_H0) (p q_v0 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v0 q_v0))) (pst1); let pst6 : (p q_v0 (p q_v0 q_v0)) = (p (p q_x q_H0) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst8 : (p (p q_x q_H0) q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := congrArg (fun q => p (p q_x q_H0) q) (pst1); let pst9 : (p q_v0 q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := Eq.trans (pst7) (pst8); let pst10 : (p (p q_x q_H0) (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := congrArg (fun q => p (p q_x q_H0) q) (pst9); let pst11 : (p q_v0 (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := Eq.trans (pst6) (pst10); let pst12 : (p (p q_x q_H0) (p q_v0 (p q_v0 q_v0))) = (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := congrArg (fun q => p (p q_x q_H0) q) (pst11); let pst13 : (p q_v0 (p q_v0 (p q_v0 q_v0))) = (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := Eq.trans (pst5) (pst12); let pst14 : (p q_v1 (p q_v0 (p q_v0 (p q_v0 q_v0)))) = (p q_v1 (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))))) := congrArg (fun q => p q_v1 q) (pst13); let pst15 : (p q_x q_H0) = (p q_v1 (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))))) := Eq.trans (pst4) (pst14); let pst16 : q_H0 = (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := congrArg (fun q => R q) (pst15); let pst17 : q_x = q_v1 := congrArg (fun q => L q) (pst15); let pst18 : (p q_x q_H0) = (p q_v1 q_H0) := congrArg (fun q => p q q_H0) (pst17); let pst19 : (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) = (p (p q_v1 q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := congrArg (fun q => p q (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) (pst18); let pst20 : (p q_x q_H0) = (p q_v1 q_H0) := congrArg (fun q => p q q_H0) (pst17); let pst21 : (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) = (p (p q_v1 q_H0) (p (p q_x q_H0) (p q_x q_H0))) := congrArg (fun q => p q (p (p q_x q_H0) (p q_x q_H0))) (pst20); let pst22 : (p q_x q_H0) = (p q_v1 q_H0) := congrArg (fun q => p q q_H0) (pst17); let pst23 : (p (p q_x q_H0) (p q_x q_H0)) = (p (p q_v1 q_H0) (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst22); let pst24 : (p q_x q_H0) = (p q_v1 q_H0) := congrArg (fun q => p q q_H0) (pst17); let pst25 : (p (p q_v1 q_H0) (p q_x q_H0)) = (p (p q_v1 q_H0) (p q_v1 q_H0)) := congrArg (fun q => p (p q_v1 q_H0) q) (pst24); let pst26 : (p (p q_x q_H0) (p q_x q_H0)) = (p (p q_v1 q_H0) (p q_v1 q_H0)) := Eq.trans (pst23) (pst25); let pst27 : (p (p q_v1 q_H0) (p (p q_x q_H0) (p q_x q_H0))) = (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0))) := congrArg (fun q => p (p q_v1 q_H0) q) (pst26); let pst28 : (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) = (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0))) := Eq.trans (pst21) (pst27); let pst29 : (p (p q_v1 q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) = (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0)))) := congrArg (fun q => p (p q_v1 q_H0) q) (pst28); let pst30 : (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) = (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0)))) := Eq.trans (pst19) (pst29); let pst31 : q_H0 = (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0)))) := Eq.trans (pst16) (pst30); pst31)
    have hlt : sz q_H0 < sz (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0)))) := Nat.lt_trans (sz_lt_p_right q_v1 q_H0) (sz_lt_p_left (p q_v1 q_H0) (p (p q_v1 q_H0) (p (p q_v1 q_H0) (p q_v1 q_H0))))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 (p v0 (p v0 v0)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x (p q_v0 q_x)) at e1
    have e2 := congrArg (fun q => (L (R q))) hb
    change v0 = q_v1 at e2
    have e3 := congrArg (fun q => (R (R q))) hb
    change v0 = (p q_v0 (p q_v0 (p q_v0 q_v0))) at e3
    have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x (p q_v0 q_x)) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x q_H0) at e1
    have e2 := congrArg (fun q => (L (R q))) hb
    change v0 = q_v1 at e2
    have e3 := congrArg (fun q => (R (R q))) hb
    change v0 = (p q_v0 (p q_v0 (p q_v0 q_v0))) at e3
    have cyc : q_x = (p q_x q_H0) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_x q_H0) := e1; let peq3 : v0 = (p q_v0 (p q_v0 (p q_v0 q_v0))) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_x q_H0) := Eq.trans (pst0) (peq1); let pst2 : v0 = (p q_x q_H0) := Eq.trans (peq0) (pst1); let pst3 : (p q_x q_H0) = v0 := Eq.symm (pst2); let pst4 : (p q_x q_H0) = (p q_v0 (p q_v0 (p q_v0 q_v0))) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 (p q_v0 (p q_v0 q_v0))) = (p (p q_x q_H0) (p q_v0 (p q_v0 q_v0))) := congrArg (fun q => p q (p q_v0 (p q_v0 q_v0))) (pst1); let pst6 : (p q_v0 (p q_v0 q_v0)) = (p (p q_x q_H0) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst1); let pst7 : (p q_v0 q_v0) = (p (p q_x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst8 : (p (p q_x q_H0) q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := congrArg (fun q => p (p q_x q_H0) q) (pst1); let pst9 : (p q_v0 q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := Eq.trans (pst7) (pst8); let pst10 : (p (p q_x q_H0) (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := congrArg (fun q => p (p q_x q_H0) q) (pst9); let pst11 : (p q_v0 (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := Eq.trans (pst6) (pst10); let pst12 : (p (p q_x q_H0) (p q_v0 (p q_v0 q_v0))) = (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := congrArg (fun q => p (p q_x q_H0) q) (pst11); let pst13 : (p q_v0 (p q_v0 (p q_v0 q_v0))) = (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := Eq.trans (pst5) (pst12); let pst14 : (p q_x q_H0) = (p (p q_x q_H0) (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0)))) := Eq.trans (pst4) (pst13); let pst15 : q_x = (p q_x q_H0) := congrArg (fun q => L q) (pst14); pst15)
    have hlt : sz q_x < sz (p q_x q_H0) := sz_lt_p_left q_x q_H0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr4 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v1 (p v0 (p v0 (p v0 v0))) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x (p q_v0 q_x)) at e1
    have e2 := congrArg (fun q => (L (R q))) hb
    change v0 = q_v1 at e2
    have e3 := congrArg (fun q => (L (R (R q)))) hb
    change v0 = q_v0 at e3
    have e4 := congrArg (fun q => (R (R (R q)))) hb
    change v0 = (p q_v0 (p q_v0 q_v0)) at e4
    have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq1 : v0 = (p q_x (p q_v0 q_x)) := e1; let peq3 : v0 = q_v0 := e3; let pst0 : (p q_x (p q_v0 q_x)) = v0 := Eq.symm (peq1); let pst1 : (p q_x (p q_v0 q_x)) = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p q_x (p q_v0 q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v1 = q_v0 at e0
    have e1 := congrArg (fun q => (L q)) hb
    change v0 = (p q_x q_H0) at e1
    have e2 := congrArg (fun q => (L (R q))) hb
    change v0 = q_v1 at e2
    have e3 := congrArg (fun q => (L (R (R q)))) hb
    change v0 = q_v0 at e3
    have e4 := congrArg (fun q => (R (R (R q)))) hb
    change v0 = (p q_v0 (p q_v0 q_v0)) at e4
    have cyc : q_x = (p q_x q_H0) := (let peq1 : v0 = (p q_x q_H0) := e1; let peq3 : v0 = q_v0 := e3; let peq4 : v0 = (p q_v0 (p q_v0 q_v0)) := e4; let pst0 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst1 : (p q_x q_H0) = (p q_v0 (p q_v0 q_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = v0 := Eq.symm (peq1); let pst3 : (p q_x q_H0) = q_v0 := Eq.trans (pst2) (peq3); let pst4 : q_v0 = (p q_x q_H0) := Eq.symm (pst3); let pst5 : (p q_v0 (p q_v0 q_v0)) = (p (p q_x q_H0) (p q_v0 q_v0)) := congrArg (fun q => p q (p q_v0 q_v0)) (pst4); let pst6 : (p q_v0 q_v0) = (p (p q_x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst7 : (p (p q_x q_H0) q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := congrArg (fun q => p (p q_x q_H0) q) (pst4); let pst8 : (p q_v0 q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := Eq.trans (pst6) (pst7); let pst9 : (p (p q_x q_H0) (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := congrArg (fun q => p (p q_x q_H0) q) (pst8); let pst10 : (p q_v0 (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := Eq.trans (pst5) (pst9); let pst11 : (p q_x q_H0) = (p (p q_x q_H0) (p (p q_x q_H0) (p q_x q_H0))) := Eq.trans (pst1) (pst10); let pst12 : q_x = (p q_x q_H0) := congrArg (fun q => L q) (pst11); pst12)
    have hlt : sz q_x < sz (p q_x q_H0) := sz_lt_p_left q_x q_H0
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr5 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code (p x H0) (p v1 (p v0 (p v0 (p v0 v0)))) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p v0 x)) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x (p q_v0 q_x)) at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => (L (R (R q)))) hb
      change v0 = q_v0 at e3
      have e4 := congrArg (fun q => (L (R (R (R q))))) hb
      change v0 = q_v0 at e4
      have e5 := congrArg (fun q => (R (R (R (R q))))) hb
      change v0 = (p q_v0 q_v0) at e5
      have cyc : q_v1 = (p x (p q_v1 x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq2 : v0 = q_v1 := e2; let peq3 : v0 = q_v0 := e3; let pst0 : q_v1 = v0 := Eq.symm (peq2); let pst1 : q_v1 = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst3 : (p v0 x) = (p q_v1 x) := congrArg (fun q => p q x) (peq2); let pst4 : (p x (p v0 x)) = (p x (p q_v1 x)) := congrArg (fun q => p x q) (pst3); let pst5 : q_v0 = (p x (p q_v1 x)) := Eq.trans (pst2) (pst4); let pst6 : q_v1 = (p x (p q_v1 x)) := Eq.trans (pst1) (pst5); pst6)
      have hlt : sz q_v1 < sz (p x (p q_v1 x)) := Nat.lt_trans (sz_lt_p_left q_v1 x) (sz_lt_p_right x (p q_v1 x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p v0 x)) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x q_H0) at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => (L (R (R q)))) hb
      change v0 = q_v0 at e3
      have e4 := congrArg (fun q => (L (R (R (R q))))) hb
      change v0 = q_v0 at e4
      have e5 := congrArg (fun q => (R (R (R (R q))))) hb
      change v0 = (p q_v0 q_v0) at e5
      have cyc : q_v1 = (p x (p q_v1 x)) := (let peq0 : (p x (p v0 x)) = q_v0 := e0; let peq2 : v0 = q_v1 := e2; let peq3 : v0 = q_v0 := e3; let pst0 : q_v1 = v0 := Eq.symm (peq2); let pst1 : q_v1 = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x (p v0 x)) := Eq.symm (peq0); let pst3 : (p v0 x) = (p q_v1 x) := congrArg (fun q => p q x) (peq2); let pst4 : (p x (p v0 x)) = (p x (p q_v1 x)) := congrArg (fun q => p x q) (pst3); let pst5 : q_v0 = (p x (p q_v1 x)) := Eq.trans (pst2) (pst4); let pst6 : q_v1 = (p x (p q_v1 x)) := Eq.trans (pst1) (pst5); pst6)
      have hlt : sz q_v1 < sz (p x (p q_v1 x)) := Nat.lt_trans (sz_lt_p_left q_v1 x) (sz_lt_p_right x (p q_v1 x))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x H0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x (p q_v0 q_x)) at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => (L (R (R q)))) hb
      change v0 = q_v0 at e3
      have e4 := congrArg (fun q => (L (R (R (R q))))) hb
      change v0 = q_v0 at e4
      have e5 := congrArg (fun q => (R (R (R (R q))))) hb
      change v0 = (p q_v0 q_v0) at e5
      have cyc : x = (p x H0) := (let peq0 : (p x H0) = q_v0 := e0; let peq2 : v0 = q_v1 := e2; let peq3 : v0 = q_v0 := e3; let peq5 : v0 = (p q_v0 q_v0) := e5; let pst0 : q_v1 = v0 := Eq.symm (peq2); let pst1 : q_v1 = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x H0) := Eq.symm (peq0); let pst3 : q_v1 = (p x H0) := Eq.trans (pst1) (pst2); let pst4 : v0 = (p x H0) := Eq.trans (peq2) (pst3); let pst5 : (p x H0) = v0 := Eq.symm (pst4); let pst6 : (p x H0) = (p q_v0 q_v0) := Eq.trans (pst5) (peq5); let pst7 : (p q_v0 q_v0) = (p (p x H0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst8 : (p (p x H0) q_v0) = (p (p x H0) (p x H0)) := congrArg (fun q => p (p x H0) q) (pst2); let pst9 : (p q_v0 q_v0) = (p (p x H0) (p x H0)) := Eq.trans (pst7) (pst8); let pst10 : (p x H0) = (p (p x H0) (p x H0)) := Eq.trans (pst6) (pst9); let pst11 : x = (p x H0) := congrArg (fun q => L q) (pst10); pst11)
      have hlt : sz x < sz (p x H0) := sz_lt_p_left x H0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x H0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = (p q_x q_H0) at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = q_v1 at e2
      have e3 := congrArg (fun q => (L (R (R q)))) hb
      change v0 = q_v0 at e3
      have e4 := congrArg (fun q => (L (R (R (R q))))) hb
      change v0 = q_v0 at e4
      have e5 := congrArg (fun q => (R (R (R (R q))))) hb
      change v0 = (p q_v0 q_v0) at e5
      have cyc : x = (p x H0) := (let peq0 : (p x H0) = q_v0 := e0; let peq2 : v0 = q_v1 := e2; let peq3 : v0 = q_v0 := e3; let peq5 : v0 = (p q_v0 q_v0) := e5; let pst0 : q_v1 = v0 := Eq.symm (peq2); let pst1 : q_v1 = q_v0 := Eq.trans (pst0) (peq3); let pst2 : q_v0 = (p x H0) := Eq.symm (peq0); let pst3 : q_v1 = (p x H0) := Eq.trans (pst1) (pst2); let pst4 : v0 = (p x H0) := Eq.trans (peq2) (pst3); let pst5 : (p x H0) = v0 := Eq.symm (pst4); let pst6 : (p x H0) = (p q_v0 q_v0) := Eq.trans (pst5) (peq5); let pst7 : (p q_v0 q_v0) = (p (p x H0) q_v0) := congrArg (fun q => p q q_v0) (pst2); let pst8 : (p (p x H0) q_v0) = (p (p x H0) (p x H0)) := congrArg (fun q => p (p x H0) q) (pst2); let pst9 : (p q_v0 q_v0) = (p (p x H0) (p x H0)) := Eq.trans (pst7) (pst8); let pst10 : (p x H0) = (p (p x H0) (p x H0)) := Eq.trans (pst6) (pst9); let pst11 : x = (p x H0) := congrArg (fun q => L q) (pst10); pst11)
      have hlt : sz x < sz (p x H0) := sz_lt_p_left x H0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval (eval x (eval v0 x)) (eval v1 (eval v0 (eval v0 (eval v0 v0)))))) := by
  let H0 := eval v0 x
  have e0a : v0 = v0 := by
    change v0 = v0
    rfl
  have e0b : x = x := by
    change x = x
    rfl
  have s0 : Step v0 x H0 := by
    rw [← e0a, ← e0b]
    exact eval_step v0 x
  change x = (eval v0 (eval (eval x H0) (eval v1 (eval v0 (eval v0 (eval v0 v0))))))
  have rawEq : (eval v0 (eval (eval x H0) (eval v1 (eval v0 (eval v0 (eval v0 v0)))))) = (eval v0 (p (p x H0) (p v1 (p v0 (p v0 (p v0 v0)))))) := by
    calc
      (eval v0 (eval (eval x H0) (eval v1 (eval v0 (eval v0 (eval v0 v0)))))) = (eval v0 (eval (p x H0) (eval v1 (eval v0 (eval v0 (eval v0 v0)))))) := congrArg (fun q => (eval v0 (eval q (eval v1 (eval v0 (eval v0 (eval v0 v0))))))) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval v0 (eval (p x H0) (eval v1 (eval v0 (eval v0 (p v0 v0)))))) := congrArg (fun q => (eval v0 (eval (p x H0) (eval v1 (eval v0 (eval v0 q)))))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval (p x H0) (eval v1 (eval v0 (p v0 (p v0 v0)))))) := congrArg (fun q => (eval v0 (eval (p x H0) (eval v1 (eval v0 q))))) (eval_raw (nr2 x v0 v1))
      _ = (eval v0 (eval (p x H0) (eval v1 (p v0 (p v0 (p v0 v0)))))) := congrArg (fun q => (eval v0 (eval (p x H0) (eval v1 q)))) (eval_raw (nr3 x v0 v1))
      _ = (eval v0 (eval (p x H0) (p v1 (p v0 (p v0 (p v0 v0)))))) := congrArg (fun q => (eval v0 (eval (p x H0) q))) (eval_raw (nr4 x v0 v1))
      _ = (eval v0 (p (p x H0) (p v1 (p v0 (p v0 (p v0 v0)))))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr5 x v0 v1 H0 s0))
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
