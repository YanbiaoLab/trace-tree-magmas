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
      Code v0 (p v0 (p (p x H0) (p v0 v0))) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_v1 q_x q_H0 ∧ a = q_v0 ∧ b = (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (L (R b)))
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
    (s0 : Step v1 x H0) :
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
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p q_x (p q_v1 q_x)) (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change x = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v1 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change x = (p (p q_x q_H0) (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p (p q_x q_H0) (p q_v0 q_v0)) := (let peq0 : x = q_v0 := e0; let peq2 : x = (p (p q_x q_H0) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = x := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_x q_H0) (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_x q_H0) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right (p q_x q_H0) (p q_v0 q_v0))
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
      change H0 = (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v0 < sz (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := by
        have q := hcB.1
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have ev : sz H0 = sz (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := congrArg sz (p1)
        have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) < sz q_v0 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := congrArg sz (p1)
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have q1 : sz (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) < sz x := lt_of_eq_of_lt ev.symm q
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
      change H0 = (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) at p1
      have z1 := congrArg sz p1
      have p2 := ho
      change o = q_x at p2
      have z2 := congrArg sz p2
      have hx : sz q_v0 < sz (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := by
        have q := hcB.1
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have ev : sz H0 = sz (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := congrArg sz (p1)
        have q1 : sz q_v0 < sz H0 := lt_of_eq_of_lt eu.symm q
        exact lt_of_lt_of_eq q1 ev
      have hy : sz (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) < sz q_v0 := by
        have q := s0hB.2
        have ev : sz H0 = sz (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := congrArg sz (p1)
        have eu : sz x = sz q_v0 := congrArg sz (p0)
        have q1 : sz (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) < sz x := lt_of_eq_of_lt ev.symm q
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
    change v0 = (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) at e1
    have cyc : q_v0 = (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))) := sz_lt_p_left q_v0 (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = q_v0 at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) at e1
    have cyc : q_v0 = (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := (let peq0 : v0 = q_v0 := e0; let peq1 : v0 = (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := e1; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := Eq.trans (pst0) (peq1); pst1)
    have hlt : sz q_v0 < sz (p q_v0 (p (p q_x q_H0) (p q_v0 q_v0))) := sz_lt_p_left q_v0 (p (p q_x q_H0) (p q_v0 q_v0))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr2 (x v0 v1 H0 : CM)
    (s0 : Step v1 x H0) :
    ¬ ∃ o, Code (p x H0) (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p v1 x)) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) at e2
      have cyc : v1 = (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := (let peq0 : (p x (p v1 x)) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = (p x (p v1 x)) := Eq.symm (peq0); let pst1 : v0 = (p x (p v1 x)) := Eq.trans (peq1) (pst0); let pst2 : (p x (p v1 x)) = v0 := Eq.symm (pst1); let pst3 : (p x (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p x (p v1 x)) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x (p v1 x)) q_v0) = (p (p x (p v1 x)) (p x (p v1 x))) := congrArg (fun q => p (p x (p v1 x)) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x (p v1 x)) (p x (p v1 x))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) = (p (p q_x (p q_v1 q_x)) (p (p x (p v1 x)) (p x (p v1 x)))) := congrArg (fun q => p (p q_x (p q_v1 q_x)) q) (pst6); let pst8 : (p x (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p (p x (p v1 x)) (p x (p v1 x)))) := Eq.trans (pst3) (pst7); let pst9 : x = (p q_x (p q_v1 q_x)) := congrArg (fun q => L q) (pst8); let pst10 : (p v1 x) = (p v1 (p q_x (p q_v1 q_x))) := congrArg (fun q => p v1 q) (pst9); let pst11 : (p v1 (p q_x (p q_v1 q_x))) = (p v1 x) := Eq.symm (pst10); let pst12 : (p v1 x) = (p (p x (p v1 x)) (p x (p v1 x))) := congrArg (fun q => R q) (pst8); let pst13 : (p v1 (p q_x (p q_v1 q_x))) = (p (p x (p v1 x)) (p x (p v1 x))) := Eq.trans (pst11) (pst12); let pst14 : (p x (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst9); let pst15 : (p v1 x) = (p v1 (p q_x (p q_v1 q_x))) := congrArg (fun q => p v1 q) (pst9); let pst16 : (p (p q_x (p q_v1 q_x)) (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := congrArg (fun q => p (p q_x (p q_v1 q_x)) q) (pst15); let pst17 : (p x (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := Eq.trans (pst14) (pst16); let pst18 : (p (p x (p v1 x)) (p x (p v1 x))) = (p (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) (p x (p v1 x))) := congrArg (fun q => p q (p x (p v1 x))) (pst17); let pst19 : (p x (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst9); let pst20 : (p v1 x) = (p v1 (p q_x (p q_v1 q_x))) := congrArg (fun q => p v1 q) (pst9); let pst21 : (p (p q_x (p q_v1 q_x)) (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := congrArg (fun q => p (p q_x (p q_v1 q_x)) q) (pst20); let pst22 : (p x (p v1 x)) = (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := Eq.trans (pst19) (pst21); let pst23 : (p (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) (p x (p v1 x))) = (p (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x))))) := congrArg (fun q => p (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) q) (pst22); let pst24 : (p (p x (p v1 x)) (p x (p v1 x))) = (p (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x))))) := Eq.trans (pst18) (pst23); let pst25 : (p v1 (p q_x (p q_v1 q_x))) = (p (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x))))) := Eq.trans (pst13) (pst24); let pst26 : v1 = (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := congrArg (fun q => L q) (pst25); pst26)
      have hlt : sz v1 < sz (p (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x)))) := Nat.lt_trans (sz_lt_p_left v1 (p q_x (p q_v1 q_x))) (sz_lt_p_right (p q_x (p q_v1 q_x)) (p v1 (p q_x (p q_v1 q_x))))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x (p v1 x)) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_x q_H0) (p q_v0 q_v0)) at e2
      have cyc : v1 = (p (p q_x q_H0) (p v1 (p q_x q_H0))) := (let peq0 : (p x (p v1 x)) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_H0) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = (p x (p v1 x)) := Eq.symm (peq0); let pst1 : v0 = (p x (p v1 x)) := Eq.trans (peq1) (pst0); let pst2 : (p x (p v1 x)) = v0 := Eq.symm (pst1); let pst3 : (p x (p v1 x)) = (p (p q_x q_H0) (p q_v0 q_v0)) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p x (p v1 x)) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x (p v1 x)) q_v0) = (p (p x (p v1 x)) (p x (p v1 x))) := congrArg (fun q => p (p x (p v1 x)) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x (p v1 x)) (p x (p v1 x))) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_H0) (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p x (p v1 x)) (p x (p v1 x)))) := congrArg (fun q => p (p q_x q_H0) q) (pst6); let pst8 : (p x (p v1 x)) = (p (p q_x q_H0) (p (p x (p v1 x)) (p x (p v1 x)))) := Eq.trans (pst3) (pst7); let pst9 : x = (p q_x q_H0) := congrArg (fun q => L q) (pst8); let pst10 : (p v1 x) = (p v1 (p q_x q_H0)) := congrArg (fun q => p v1 q) (pst9); let pst11 : (p v1 (p q_x q_H0)) = (p v1 x) := Eq.symm (pst10); let pst12 : (p v1 x) = (p (p x (p v1 x)) (p x (p v1 x))) := congrArg (fun q => R q) (pst8); let pst13 : (p v1 (p q_x q_H0)) = (p (p x (p v1 x)) (p x (p v1 x))) := Eq.trans (pst11) (pst12); let pst14 : (p x (p v1 x)) = (p (p q_x q_H0) (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst9); let pst15 : (p v1 x) = (p v1 (p q_x q_H0)) := congrArg (fun q => p v1 q) (pst9); let pst16 : (p (p q_x q_H0) (p v1 x)) = (p (p q_x q_H0) (p v1 (p q_x q_H0))) := congrArg (fun q => p (p q_x q_H0) q) (pst15); let pst17 : (p x (p v1 x)) = (p (p q_x q_H0) (p v1 (p q_x q_H0))) := Eq.trans (pst14) (pst16); let pst18 : (p (p x (p v1 x)) (p x (p v1 x))) = (p (p (p q_x q_H0) (p v1 (p q_x q_H0))) (p x (p v1 x))) := congrArg (fun q => p q (p x (p v1 x))) (pst17); let pst19 : (p x (p v1 x)) = (p (p q_x q_H0) (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst9); let pst20 : (p v1 x) = (p v1 (p q_x q_H0)) := congrArg (fun q => p v1 q) (pst9); let pst21 : (p (p q_x q_H0) (p v1 x)) = (p (p q_x q_H0) (p v1 (p q_x q_H0))) := congrArg (fun q => p (p q_x q_H0) q) (pst20); let pst22 : (p x (p v1 x)) = (p (p q_x q_H0) (p v1 (p q_x q_H0))) := Eq.trans (pst19) (pst21); let pst23 : (p (p (p q_x q_H0) (p v1 (p q_x q_H0))) (p x (p v1 x))) = (p (p (p q_x q_H0) (p v1 (p q_x q_H0))) (p (p q_x q_H0) (p v1 (p q_x q_H0)))) := congrArg (fun q => p (p (p q_x q_H0) (p v1 (p q_x q_H0))) q) (pst22); let pst24 : (p (p x (p v1 x)) (p x (p v1 x))) = (p (p (p q_x q_H0) (p v1 (p q_x q_H0))) (p (p q_x q_H0) (p v1 (p q_x q_H0)))) := Eq.trans (pst18) (pst23); let pst25 : (p v1 (p q_x q_H0)) = (p (p (p q_x q_H0) (p v1 (p q_x q_H0))) (p (p q_x q_H0) (p v1 (p q_x q_H0)))) := Eq.trans (pst13) (pst24); let pst26 : v1 = (p (p q_x q_H0) (p v1 (p q_x q_H0))) := congrArg (fun q => L q) (pst25); pst26)
      have hlt : sz v1 < sz (p (p q_x q_H0) (p v1 (p q_x q_H0))) := Nat.lt_trans (sz_lt_p_left v1 (p q_x q_H0)) (sz_lt_p_right (p q_x q_H0) (p v1 (p q_x q_H0)))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change (p x H0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) at e2
      have cyc : H0 = (p (p (p q_x (p q_v1 q_x)) H0) (p (p q_x (p q_v1 q_x)) H0)) := (let peq0 : (p x H0) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = (p x H0) := Eq.symm (peq0); let pst1 : v0 = (p x H0) := Eq.trans (peq1) (pst0); let pst2 : (p x H0) = v0 := Eq.symm (pst1); let pst3 : (p x H0) = (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p x H0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x H0) q_v0) = (p (p x H0) (p x H0)) := congrArg (fun q => p (p x H0) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x H0) (p x H0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x (p q_v1 q_x)) (p q_v0 q_v0)) = (p (p q_x (p q_v1 q_x)) (p (p x H0) (p x H0))) := congrArg (fun q => p (p q_x (p q_v1 q_x)) q) (pst6); let pst8 : (p x H0) = (p (p q_x (p q_v1 q_x)) (p (p x H0) (p x H0))) := Eq.trans (pst3) (pst7); let pst9 : H0 = (p (p x H0) (p x H0)) := congrArg (fun q => R q) (pst8); let pst10 : x = (p q_x (p q_v1 q_x)) := congrArg (fun q => L q) (pst8); let pst11 : (p x H0) = (p (p q_x (p q_v1 q_x)) H0) := congrArg (fun q => p q H0) (pst10); let pst12 : (p (p x H0) (p x H0)) = (p (p (p q_x (p q_v1 q_x)) H0) (p x H0)) := congrArg (fun q => p q (p x H0)) (pst11); let pst13 : (p x H0) = (p (p q_x (p q_v1 q_x)) H0) := congrArg (fun q => p q H0) (pst10); let pst14 : (p (p (p q_x (p q_v1 q_x)) H0) (p x H0)) = (p (p (p q_x (p q_v1 q_x)) H0) (p (p q_x (p q_v1 q_x)) H0)) := congrArg (fun q => p (p (p q_x (p q_v1 q_x)) H0) q) (pst13); let pst15 : (p (p x H0) (p x H0)) = (p (p (p q_x (p q_v1 q_x)) H0) (p (p q_x (p q_v1 q_x)) H0)) := Eq.trans (pst12) (pst14); let pst16 : H0 = (p (p (p q_x (p q_v1 q_x)) H0) (p (p q_x (p q_v1 q_x)) H0)) := Eq.trans (pst9) (pst15); pst16)
      have hlt : sz H0 < sz (p (p (p q_x (p q_v1 q_x)) H0) (p (p q_x (p q_v1 q_x)) H0)) := Nat.lt_trans (sz_lt_p_right (p q_x (p q_v1 q_x)) H0) (sz_lt_p_left (p (p q_x (p q_v1 q_x)) H0) (p (p q_x (p q_v1 q_x)) H0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change (p x H0) = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change v0 = q_v0 at e1
      have e2 := congrArg (fun q => (R q)) hb
      change v0 = (p (p q_x q_H0) (p q_v0 q_v0)) at e2
      have cyc : H0 = (p (p (p q_x q_H0) H0) (p (p q_x q_H0) H0)) := (let peq0 : (p x H0) = q_v0 := e0; let peq1 : v0 = q_v0 := e1; let peq2 : v0 = (p (p q_x q_H0) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = (p x H0) := Eq.symm (peq0); let pst1 : v0 = (p x H0) := Eq.trans (peq1) (pst0); let pst2 : (p x H0) = v0 := Eq.symm (pst1); let pst3 : (p x H0) = (p (p q_x q_H0) (p q_v0 q_v0)) := Eq.trans (pst2) (peq2); let pst4 : (p q_v0 q_v0) = (p (p x H0) q_v0) := congrArg (fun q => p q q_v0) (pst0); let pst5 : (p (p x H0) q_v0) = (p (p x H0) (p x H0)) := congrArg (fun q => p (p x H0) q) (pst0); let pst6 : (p q_v0 q_v0) = (p (p x H0) (p x H0)) := Eq.trans (pst4) (pst5); let pst7 : (p (p q_x q_H0) (p q_v0 q_v0)) = (p (p q_x q_H0) (p (p x H0) (p x H0))) := congrArg (fun q => p (p q_x q_H0) q) (pst6); let pst8 : (p x H0) = (p (p q_x q_H0) (p (p x H0) (p x H0))) := Eq.trans (pst3) (pst7); let pst9 : H0 = (p (p x H0) (p x H0)) := congrArg (fun q => R q) (pst8); let pst10 : x = (p q_x q_H0) := congrArg (fun q => L q) (pst8); let pst11 : (p x H0) = (p (p q_x q_H0) H0) := congrArg (fun q => p q H0) (pst10); let pst12 : (p (p x H0) (p x H0)) = (p (p (p q_x q_H0) H0) (p x H0)) := congrArg (fun q => p q (p x H0)) (pst11); let pst13 : (p x H0) = (p (p q_x q_H0) H0) := congrArg (fun q => p q H0) (pst10); let pst14 : (p (p (p q_x q_H0) H0) (p x H0)) = (p (p (p q_x q_H0) H0) (p (p q_x q_H0) H0)) := congrArg (fun q => p (p (p q_x q_H0) H0) q) (pst13); let pst15 : (p (p x H0) (p x H0)) = (p (p (p q_x q_H0) H0) (p (p q_x q_H0) H0)) := Eq.trans (pst12) (pst14); let pst16 : H0 = (p (p (p q_x q_H0) H0) (p (p q_x q_H0) H0)) := Eq.trans (pst9) (pst15); pst16)
      have hlt : sz H0 < sz (p (p (p q_x q_H0) H0) (p (p q_x q_H0) H0)) := Nat.lt_trans (sz_lt_p_right (p q_x q_H0) H0) (sz_lt_p_left (p (p q_x q_H0) H0) (p (p q_x q_H0) H0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 H0 : CM)
    (s0 : Step v1 x H0) :
    ¬ ∃ o, Code v0 (p (p x H0) (p v0 v0)) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p x (p v1 x)) = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = (p q_x (p q_v1 q_x)) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v0 = (p q_v0 q_v0) at e3
      have cyc : q_x = (p q_x (p q_v1 q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x (p v1 x)) = q_v0 := e1; let peq2 : v0 = (p q_x (p q_v1 q_x)) := e2; let peq3 : v0 = (p q_v0 q_v0) := e3; let pst0 : q_v0 = (p x (p v1 x)) := Eq.symm (peq1); let pst1 : v0 = (p x (p v1 x)) := Eq.trans (peq0) (pst0); let pst2 : (p x (p v1 x)) = v0 := Eq.symm (pst1); let pst3 : (p x (p v1 x)) = (p q_x (p q_v1 q_x)) := Eq.trans (pst2) (peq2); let pst4 : x = q_x := congrArg (fun q => L q) (pst3); let pst5 : (p x (p v1 x)) = (p q_x (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst4); let pst6 : (p v1 x) = (p v1 q_x) := congrArg (fun q => p v1 q) (pst4); let pst7 : (p v1 q_x) = (p v1 x) := Eq.symm (pst6); let pst8 : (p v1 x) = (p q_v1 q_x) := congrArg (fun q => R q) (pst3); let pst9 : (p v1 q_x) = (p q_v1 q_x) := Eq.trans (pst7) (pst8); let pst10 : v1 = q_v1 := congrArg (fun q => L q) (pst9); let pst11 : (p v1 x) = (p q_v1 x) := congrArg (fun q => p q x) (pst10); let pst12 : (p q_v1 x) = (p q_v1 q_x) := congrArg (fun q => p q_v1 q) (pst4); let pst13 : (p v1 x) = (p q_v1 q_x) := Eq.trans (pst11) (pst12); let pst14 : (p q_x (p v1 x)) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst13); let pst15 : (p x (p v1 x)) = (p q_x (p q_v1 q_x)) := Eq.trans (pst5) (pst14); let pst16 : q_v0 = (p q_x (p q_v1 q_x)) := Eq.trans (pst0) (pst15); let pst17 : v0 = (p q_x (p q_v1 q_x)) := Eq.trans (peq0) (pst16); let pst18 : (p q_x (p q_v1 q_x)) = v0 := Eq.symm (pst17); let pst19 : (p q_x (p q_v1 q_x)) = (p q_v0 q_v0) := Eq.trans (pst18) (peq3); let pst20 : (p x (p v1 x)) = (p q_x (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst4); let pst21 : (p v1 x) = (p q_v1 x) := congrArg (fun q => p q x) (pst10); let pst22 : (p q_v1 x) = (p q_v1 q_x) := congrArg (fun q => p q_v1 q) (pst4); let pst23 : (p v1 x) = (p q_v1 q_x) := Eq.trans (pst21) (pst22); let pst24 : (p q_x (p v1 x)) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst23); let pst25 : (p x (p v1 x)) = (p q_x (p q_v1 q_x)) := Eq.trans (pst20) (pst24); let pst26 : q_v0 = (p q_x (p q_v1 q_x)) := Eq.trans (pst0) (pst25); let pst27 : (p q_v0 q_v0) = (p (p q_x (p q_v1 q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst26); let pst28 : (p x (p v1 x)) = (p q_x (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst4); let pst29 : (p v1 x) = (p q_v1 x) := congrArg (fun q => p q x) (pst10); let pst30 : (p q_v1 x) = (p q_v1 q_x) := congrArg (fun q => p q_v1 q) (pst4); let pst31 : (p v1 x) = (p q_v1 q_x) := Eq.trans (pst29) (pst30); let pst32 : (p q_x (p v1 x)) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst31); let pst33 : (p x (p v1 x)) = (p q_x (p q_v1 q_x)) := Eq.trans (pst28) (pst32); let pst34 : q_v0 = (p q_x (p q_v1 q_x)) := Eq.trans (pst0) (pst33); let pst35 : (p (p q_x (p q_v1 q_x)) q_v0) = (p (p q_x (p q_v1 q_x)) (p q_x (p q_v1 q_x))) := congrArg (fun q => p (p q_x (p q_v1 q_x)) q) (pst34); let pst36 : (p q_v0 q_v0) = (p (p q_x (p q_v1 q_x)) (p q_x (p q_v1 q_x))) := Eq.trans (pst27) (pst35); let pst37 : (p q_x (p q_v1 q_x)) = (p (p q_x (p q_v1 q_x)) (p q_x (p q_v1 q_x))) := Eq.trans (pst19) (pst36); let pst38 : q_x = (p q_x (p q_v1 q_x)) := congrArg (fun q => L q) (pst37); pst38)
      have hlt : sz q_x < sz (p q_x (p q_v1 q_x)) := sz_lt_p_left q_x (p q_v1 q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p x (p v1 x)) = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = (p q_x q_H0) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v0 = (p q_v0 q_v0) at e3
      have cyc : q_x = (p q_x (p v1 q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x (p v1 x)) = q_v0 := e1; let peq2 : v0 = (p q_x q_H0) := e2; let peq3 : v0 = (p q_v0 q_v0) := e3; let pst0 : q_v0 = (p x (p v1 x)) := Eq.symm (peq1); let pst1 : v0 = (p x (p v1 x)) := Eq.trans (peq0) (pst0); let pst2 : (p x (p v1 x)) = v0 := Eq.symm (pst1); let pst3 : (p x (p v1 x)) = (p q_x q_H0) := Eq.trans (pst2) (peq2); let pst4 : x = q_x := congrArg (fun q => L q) (pst3); let pst5 : (p x (p v1 x)) = (p q_x (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst4); let pst6 : (p v1 x) = (p v1 q_x) := congrArg (fun q => p v1 q) (pst4); let pst7 : (p q_x (p v1 x)) = (p q_x (p v1 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p x (p v1 x)) = (p q_x (p v1 q_x)) := Eq.trans (pst5) (pst7); let pst9 : q_v0 = (p q_x (p v1 q_x)) := Eq.trans (pst0) (pst8); let pst10 : v0 = (p q_x (p v1 q_x)) := Eq.trans (peq0) (pst9); let pst11 : (p q_x (p v1 q_x)) = v0 := Eq.symm (pst10); let pst12 : (p q_x (p v1 q_x)) = (p q_v0 q_v0) := Eq.trans (pst11) (peq3); let pst13 : (p x (p v1 x)) = (p q_x (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst4); let pst14 : (p v1 x) = (p v1 q_x) := congrArg (fun q => p v1 q) (pst4); let pst15 : (p q_x (p v1 x)) = (p q_x (p v1 q_x)) := congrArg (fun q => p q_x q) (pst14); let pst16 : (p x (p v1 x)) = (p q_x (p v1 q_x)) := Eq.trans (pst13) (pst15); let pst17 : q_v0 = (p q_x (p v1 q_x)) := Eq.trans (pst0) (pst16); let pst18 : (p q_v0 q_v0) = (p (p q_x (p v1 q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst17); let pst19 : (p x (p v1 x)) = (p q_x (p v1 x)) := congrArg (fun q => p q (p v1 x)) (pst4); let pst20 : (p v1 x) = (p v1 q_x) := congrArg (fun q => p v1 q) (pst4); let pst21 : (p q_x (p v1 x)) = (p q_x (p v1 q_x)) := congrArg (fun q => p q_x q) (pst20); let pst22 : (p x (p v1 x)) = (p q_x (p v1 q_x)) := Eq.trans (pst19) (pst21); let pst23 : q_v0 = (p q_x (p v1 q_x)) := Eq.trans (pst0) (pst22); let pst24 : (p (p q_x (p v1 q_x)) q_v0) = (p (p q_x (p v1 q_x)) (p q_x (p v1 q_x))) := congrArg (fun q => p (p q_x (p v1 q_x)) q) (pst23); let pst25 : (p q_v0 q_v0) = (p (p q_x (p v1 q_x)) (p q_x (p v1 q_x))) := Eq.trans (pst18) (pst24); let pst26 : (p q_x (p v1 q_x)) = (p (p q_x (p v1 q_x)) (p q_x (p v1 q_x))) := Eq.trans (pst12) (pst25); let pst27 : q_x = (p q_x (p v1 q_x)) := congrArg (fun q => L q) (pst26); pst27)
      have hlt : sz q_x < sz (p q_x (p v1 q_x)) := sz_lt_p_left q_x (p v1 q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p x H0) = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = (p q_x (p q_v1 q_x)) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v0 = (p q_v0 q_v0) at e3
      have cyc : q_x = (p q_x (p q_v1 q_x)) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x H0) = q_v0 := e1; let peq2 : v0 = (p q_x (p q_v1 q_x)) := e2; let peq3 : v0 = (p q_v0 q_v0) := e3; let pst0 : q_v0 = (p x H0) := Eq.symm (peq1); let pst1 : v0 = (p x H0) := Eq.trans (peq0) (pst0); let pst2 : (p x H0) = v0 := Eq.symm (pst1); let pst3 : (p x H0) = (p q_x (p q_v1 q_x)) := Eq.trans (pst2) (peq2); let pst4 : x = q_x := congrArg (fun q => L q) (pst3); let pst5 : (p x H0) = (p q_x H0) := congrArg (fun q => p q H0) (pst4); let pst6 : H0 = (p q_v1 q_x) := congrArg (fun q => R q) (pst3); let pst7 : (p q_x H0) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p x H0) = (p q_x (p q_v1 q_x)) := Eq.trans (pst5) (pst7); let pst9 : q_v0 = (p q_x (p q_v1 q_x)) := Eq.trans (pst0) (pst8); let pst10 : v0 = (p q_x (p q_v1 q_x)) := Eq.trans (peq0) (pst9); let pst11 : (p q_x (p q_v1 q_x)) = v0 := Eq.symm (pst10); let pst12 : (p q_x (p q_v1 q_x)) = (p q_v0 q_v0) := Eq.trans (pst11) (peq3); let pst13 : (p x H0) = (p q_x H0) := congrArg (fun q => p q H0) (pst4); let pst14 : (p q_x H0) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst15 : (p x H0) = (p q_x (p q_v1 q_x)) := Eq.trans (pst13) (pst14); let pst16 : q_v0 = (p q_x (p q_v1 q_x)) := Eq.trans (pst0) (pst15); let pst17 : (p q_v0 q_v0) = (p (p q_x (p q_v1 q_x)) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : (p x H0) = (p q_x H0) := congrArg (fun q => p q H0) (pst4); let pst19 : (p q_x H0) = (p q_x (p q_v1 q_x)) := congrArg (fun q => p q_x q) (pst6); let pst20 : (p x H0) = (p q_x (p q_v1 q_x)) := Eq.trans (pst18) (pst19); let pst21 : q_v0 = (p q_x (p q_v1 q_x)) := Eq.trans (pst0) (pst20); let pst22 : (p (p q_x (p q_v1 q_x)) q_v0) = (p (p q_x (p q_v1 q_x)) (p q_x (p q_v1 q_x))) := congrArg (fun q => p (p q_x (p q_v1 q_x)) q) (pst21); let pst23 : (p q_v0 q_v0) = (p (p q_x (p q_v1 q_x)) (p q_x (p q_v1 q_x))) := Eq.trans (pst17) (pst22); let pst24 : (p q_x (p q_v1 q_x)) = (p (p q_x (p q_v1 q_x)) (p q_x (p q_v1 q_x))) := Eq.trans (pst12) (pst23); let pst25 : q_x = (p q_x (p q_v1 q_x)) := congrArg (fun q => L q) (pst24); pst25)
      have hlt : sz q_x < sz (p q_x (p q_v1 q_x)) := sz_lt_p_left q_x (p q_v1 q_x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => q) ha
      change v0 = q_v0 at e0
      have e1 := congrArg (fun q => (L q)) hb
      change (p x H0) = q_v0 at e1
      have e2 := congrArg (fun q => (L (R q))) hb
      change v0 = (p q_x q_H0) at e2
      have e3 := congrArg (fun q => (R (R q))) hb
      change v0 = (p q_v0 q_v0) at e3
      have cyc : q_x = (p q_x q_H0) := (let peq0 : v0 = q_v0 := e0; let peq1 : (p x H0) = q_v0 := e1; let peq2 : v0 = (p q_x q_H0) := e2; let peq3 : v0 = (p q_v0 q_v0) := e3; let pst0 : q_v0 = (p x H0) := Eq.symm (peq1); let pst1 : v0 = (p x H0) := Eq.trans (peq0) (pst0); let pst2 : (p x H0) = v0 := Eq.symm (pst1); let pst3 : (p x H0) = (p q_x q_H0) := Eq.trans (pst2) (peq2); let pst4 : x = q_x := congrArg (fun q => L q) (pst3); let pst5 : (p x H0) = (p q_x H0) := congrArg (fun q => p q H0) (pst4); let pst6 : H0 = q_H0 := congrArg (fun q => R q) (pst3); let pst7 : (p q_x H0) = (p q_x q_H0) := congrArg (fun q => p q_x q) (pst6); let pst8 : (p x H0) = (p q_x q_H0) := Eq.trans (pst5) (pst7); let pst9 : q_v0 = (p q_x q_H0) := Eq.trans (pst0) (pst8); let pst10 : v0 = (p q_x q_H0) := Eq.trans (peq0) (pst9); let pst11 : (p q_x q_H0) = v0 := Eq.symm (pst10); let pst12 : (p q_x q_H0) = (p q_v0 q_v0) := Eq.trans (pst11) (peq3); let pst13 : (p x H0) = (p q_x H0) := congrArg (fun q => p q H0) (pst4); let pst14 : (p q_x H0) = (p q_x q_H0) := congrArg (fun q => p q_x q) (pst6); let pst15 : (p x H0) = (p q_x q_H0) := Eq.trans (pst13) (pst14); let pst16 : q_v0 = (p q_x q_H0) := Eq.trans (pst0) (pst15); let pst17 : (p q_v0 q_v0) = (p (p q_x q_H0) q_v0) := congrArg (fun q => p q q_v0) (pst16); let pst18 : (p x H0) = (p q_x H0) := congrArg (fun q => p q H0) (pst4); let pst19 : (p q_x H0) = (p q_x q_H0) := congrArg (fun q => p q_x q) (pst6); let pst20 : (p x H0) = (p q_x q_H0) := Eq.trans (pst18) (pst19); let pst21 : q_v0 = (p q_x q_H0) := Eq.trans (pst0) (pst20); let pst22 : (p (p q_x q_H0) q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := congrArg (fun q => p (p q_x q_H0) q) (pst21); let pst23 : (p q_v0 q_v0) = (p (p q_x q_H0) (p q_x q_H0)) := Eq.trans (pst17) (pst22); let pst24 : (p q_x q_H0) = (p (p q_x q_H0) (p q_x q_H0)) := Eq.trans (pst12) (pst23); let pst25 : q_x = (p q_x q_H0) := congrArg (fun q => L q) (pst24); pst25)
      have hlt : sz q_x < sz (p q_x q_H0) := sz_lt_p_left q_x q_H0
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval v0 (eval v0 (eval (eval x (eval v1 x)) (eval v0 v0)))) := by
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
  change x = (eval v0 (eval v0 (eval (eval x H0) (eval v0 v0))))
  have rawEq : (eval v0 (eval v0 (eval (eval x H0) (eval v0 v0)))) = (eval v0 (p v0 (p (p x H0) (p v0 v0)))) := by
    calc
      (eval v0 (eval v0 (eval (eval x H0) (eval v0 v0)))) = (eval v0 (eval v0 (eval (p x H0) (eval v0 v0)))) := congrArg (fun q => (eval v0 (eval v0 (eval q (eval v0 v0))))) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval v0 (eval v0 (eval (p x H0) (p v0 v0)))) := congrArg (fun q => (eval v0 (eval v0 (eval (p x H0) q)))) (eval_raw (nr1 x v0 v1))
      _ = (eval v0 (eval v0 (p (p x H0) (p v0 v0)))) := congrArg (fun q => (eval v0 (eval v0 q))) (eval_raw (nr2 x v0 v1 H0 s0))
      _ = (eval v0 (p v0 (p (p x H0) (p v0 v0)))) := congrArg (fun q => (eval v0 q)) (eval_raw (nr3 x v0 v1 H0 s0))
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
