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
      Code (p (p (p v0 v0) H0) (p (p v0 v0) x)) v0 x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 : CM, Step q_x q_v1 q_H0 ∧ a = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) ∧ b = q_v0 ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 s0 => ⟨x, v0, v1, H0, s0, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (R (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz b < sz a ∧ sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, s0, ha, hb, ho⟩
  subst a
  subst b
  subst o
  simp only [sz] <;> omega

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
    change v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code (p v0 v0) H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have he : q_H0 = q_x := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p (p q_v0 q_v0) q_x) := congrArg (fun q => (R q)) (ha); let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); pst2)
    exact step_ne_first (by simpa only [he] using qs0)
  | hit s0h =>
    have he : q_H0 = q_x := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p (p q_v0 q_v0) q_x) := congrArg (fun q => (R q)) (ha); let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); pst2)
    exact step_ne_first (by simpa only [he] using qs0)
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have qs0B := step_bound qs0
  cases qs0 with
  | raw =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_x q_v1))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_x q_v1)) (p (p q_v0 q_v0) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    have e0 := congrArg (fun q => q) ha
    change v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) at e0
    have e1 := congrArg (fun q => q) hb
    change v0 = q_v0 at e1
    have cyc : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := (let peq0 : v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := e0; let peq1 : v0 = q_v0 := e1; let pst0 : (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) = v0 := Eq.symm (peq0); let pst1 : (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) = q_v0 := Eq.trans (pst0) (peq1); let pst2 : q_v0 = (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := Eq.symm (pst1); pst2)
    have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) q_H0)) (sz_lt_p_left (p (p q_v0 q_v0) q_H0) (p (p q_v0 q_v0) q_x))
    exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr3 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code (p v0 v0) x o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have he : q_H0 = q_x := (let peq0 : v0 = (p (p q_v0 q_v0) q_H0) := congrArg (fun q => (L q)) (ha); let peq1 : v0 = (p (p q_v0 q_v0) q_x) := congrArg (fun q => (R q)) (ha); let pst0 : (p (p q_v0 q_v0) q_H0) = v0 := Eq.symm (peq0); let pst1 : (p (p q_v0 q_v0) q_H0) = (p (p q_v0 q_v0) q_x) := Eq.trans (pst0) (peq1); let pst2 : q_H0 = q_x := congrArg (fun q => R q) (pst1); pst2)
  exact step_ne_first (by simpa only [he] using qs0)
theorem nr4 (x v0 v1 H0 : CM)
    (s0 : Step x v1 H0) :
    ¬ ∃ o, Code (p (p v0 v0) H0) (p (p v0 v0) x) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, qs0, ha, hb, ho⟩
  have s0B := step_bound s0
  cases s0 with
  | raw =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = (p q_x q_v1) at e1
      have e2 := congrArg (fun q => (L (R q))) ha
      change x = (p q_v0 q_v0) at e2
      have e3 := congrArg (fun q => (R (R q))) ha
      change v1 = q_x at e3
      have e4 := congrArg (fun q => q) hb
      change (p (p v0 v0) x) = q_v0 at e4
      have cyc : q_v1 = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_x q_v1) := e1; let peq2 : x = (p q_v0 q_v0) := e2; let peq4 : (p (p v0 v0) x) = q_v0 := e4; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : q_x = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst7 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst9 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst8); let pst10 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst7) (pst9); let pst11 : v0 = (p q_v1 q_v1) := Eq.trans (peq0) (pst10); let pst12 : (p v0 v0) = (p (p q_v1 q_v1) v0) := congrArg (fun q => p q v0) (pst11); let pst13 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst14 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst15 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst16 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst15); let pst17 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst14) (pst16); let pst18 : v0 = (p q_v1 q_v1) := Eq.trans (peq0) (pst17); let pst19 : (p (p q_v1 q_v1) v0) = (p (p q_v1 q_v1) (p q_v1 q_v1)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst18); let pst20 : (p v0 v0) = (p (p q_v1 q_v1) (p q_v1 q_v1)) := Eq.trans (pst12) (pst19); let pst21 : (p (p v0 v0) x) = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) := congrArg (fun q => p q x) (pst20); let pst22 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst23 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst22); let pst24 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst25 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst24); let pst26 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst23) (pst25); let pst27 : x = (p q_v1 q_v1) := Eq.trans (peq2) (pst26); let pst28 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) := congrArg (fun q => p (p (p q_v1 q_v1) (p q_v1 q_v1)) q) (pst27); let pst29 : (p (p v0 v0) x) = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) := Eq.trans (pst21) (pst28); let pst30 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) = (p (p v0 v0) x) := Eq.symm (pst29); let pst31 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) = q_v0 := Eq.trans (pst30) (peq4); let pst32 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst33 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) = q_v1 := Eq.trans (pst31) (pst32); let pst34 : q_v1 = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) := Eq.symm (pst33); pst34)
      have hlt : sz q_v1 < sz (p (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_left (p q_v1 q_v1) (p q_v1 q_v1))) (sz_lt_p_left (p (p q_v1 q_v1) (p q_v1 q_v1)) (p q_v1 q_v1))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = q_H0 at e1
      have e2 := congrArg (fun q => (L (R q))) ha
      change x = (p q_v0 q_v0) at e2
      have e3 := congrArg (fun q => (R (R q))) ha
      change v1 = q_x at e3
      have e4 := congrArg (fun q => q) hb
      change (p (p v0 v0) x) = q_v0 at e4
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq2 : x = (p q_v0 q_v0) := e2; let peq4 : (p (p v0 v0) x) = q_v0 := e4; let pst0 : (p v0 v0) = (p (p q_v0 q_v0) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 q_v0) v0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) := congrArg (fun q => p (p (p q_v0 q_v0) (p q_v0 q_v0)) q) (peq2); let pst5 : (p (p v0 v0) x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) := Eq.trans (pst3) (pst4); let pst6 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) = (p (p v0 v0) x) := Eq.symm (pst5); let pst7 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) = q_v0 := Eq.trans (pst6) (peq4); let pst8 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) := Eq.symm (pst7); pst8)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0)) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v0)) (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0B := step_bound qs0
    cases qs0 with
    | raw =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = (p q_x q_v1) at e1
      have e2 := congrArg (fun q => (R q)) ha
      change H0 = (p (p q_v0 q_v0) q_x) at e2
      have e3 := congrArg (fun q => q) hb
      change (p (p v0 v0) x) = q_v0 at e3
      have cyc : q_v1 = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq1 : v0 = (p q_x q_v1) := e1; let peq3 : (p (p v0 v0) x) = q_v0 := e3; let pst0 : (p q_v0 q_v0) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 q_v0) = (p q_x q_v1) := Eq.trans (pst0) (peq1); let pst2 : q_v0 = q_x := congrArg (fun q => L q) (pst1); let pst3 : q_x = q_v0 := Eq.symm (pst2); let pst4 : q_v0 = q_v1 := congrArg (fun q => R q) (pst1); let pst5 : q_x = q_v1 := Eq.trans (pst3) (pst4); let pst6 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst7 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst6); let pst8 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst9 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst8); let pst10 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst7) (pst9); let pst11 : v0 = (p q_v1 q_v1) := Eq.trans (peq0) (pst10); let pst12 : (p v0 v0) = (p (p q_v1 q_v1) v0) := congrArg (fun q => p q v0) (pst11); let pst13 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst14 : (p q_v0 q_v0) = (p q_v1 q_v0) := congrArg (fun q => p q q_v0) (pst13); let pst15 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst16 : (p q_v1 q_v0) = (p q_v1 q_v1) := congrArg (fun q => p q_v1 q) (pst15); let pst17 : (p q_v0 q_v0) = (p q_v1 q_v1) := Eq.trans (pst14) (pst16); let pst18 : v0 = (p q_v1 q_v1) := Eq.trans (peq0) (pst17); let pst19 : (p (p q_v1 q_v1) v0) = (p (p q_v1 q_v1) (p q_v1 q_v1)) := congrArg (fun q => p (p q_v1 q_v1) q) (pst18); let pst20 : (p v0 v0) = (p (p q_v1 q_v1) (p q_v1 q_v1)) := Eq.trans (pst12) (pst19); let pst21 : (p (p v0 v0) x) = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) := congrArg (fun q => p q x) (pst20); let pst22 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) = (p (p v0 v0) x) := Eq.symm (pst21); let pst23 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) = q_v0 := Eq.trans (pst22) (peq3); let pst24 : q_v0 = q_v1 := Eq.trans (pst2) (pst5); let pst25 : (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) = q_v1 := Eq.trans (pst23) (pst24); let pst26 : q_v1 = (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) := Eq.symm (pst25); pst26)
      have hlt : sz q_v1 < sz (p (p (p q_v1 q_v1) (p q_v1 q_v1)) x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v1 q_v1) (sz_lt_p_left (p q_v1 q_v1) (p q_v1 q_v1))) (sz_lt_p_left (p (p q_v1 q_v1) (p q_v1 q_v1)) x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have e0 := congrArg (fun q => (L (L q))) ha
      change v0 = (p q_v0 q_v0) at e0
      have e1 := congrArg (fun q => (R (L q))) ha
      change v0 = q_H0 at e1
      have e2 := congrArg (fun q => (R q)) ha
      change H0 = (p (p q_v0 q_v0) q_x) at e2
      have e3 := congrArg (fun q => q) hb
      change (p (p v0 v0) x) = q_v0 at e3
      have cyc : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) := (let peq0 : v0 = (p q_v0 q_v0) := e0; let peq3 : (p (p v0 v0) x) = q_v0 := e3; let pst0 : (p v0 v0) = (p (p q_v0 q_v0) v0) := congrArg (fun q => p q v0) (peq0); let pst1 : (p (p q_v0 q_v0) v0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := congrArg (fun q => p (p q_v0 q_v0) q) (peq0); let pst2 : (p v0 v0) = (p (p q_v0 q_v0) (p q_v0 q_v0)) := Eq.trans (pst0) (pst1); let pst3 : (p (p v0 v0) x) = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) := congrArg (fun q => p q x) (pst2); let pst4 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) = (p (p v0 v0) x) := Eq.symm (pst3); let pst5 : (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) = q_v0 := Eq.trans (pst4) (peq3); let pst6 : q_v0 = (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) := Eq.symm (pst5); pst6)
      have hlt : sz q_v0 < sz (p (p (p q_v0 q_v0) (p q_v0 q_v0)) x) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_left (p q_v0 q_v0) (p q_v0 q_v0))) (sz_lt_p_left (p (p q_v0 q_v0) (p q_v0 q_v0)) x)
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval (eval (eval v0 v0) (eval x v1)) (eval (eval v0 v0) x)) v0) := by
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
  change x = (eval (eval (eval (eval v0 v0) H0) (eval (eval v0 v0) x)) v0)
  have rawEq : (eval (eval (eval (eval v0 v0) H0) (eval (eval v0 v0) x)) v0) = (eval (p (p (p v0 v0) H0) (p (p v0 v0) x)) v0) := by
    calc
      (eval (eval (eval (eval v0 v0) H0) (eval (eval v0 v0) x)) v0) = (eval (eval (eval (p v0 v0) H0) (eval (eval v0 v0) x)) v0) := congrArg (fun q => (eval (eval (eval q H0) (eval (eval v0 v0) x)) v0)) (eval_raw (nr0 x v0 v1))
      _ = (eval (eval (p (p v0 v0) H0) (eval (eval v0 v0) x)) v0) := congrArg (fun q => (eval (eval q (eval (eval v0 v0) x)) v0)) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (eval (p (p v0 v0) H0) (eval (p v0 v0) x)) v0) := congrArg (fun q => (eval (eval (p (p v0 v0) H0) (eval q x)) v0)) (eval_raw (nr2 x v0 v1))
      _ = (eval (eval (p (p v0 v0) H0) (p (p v0 v0) x)) v0) := congrArg (fun q => (eval (eval (p (p v0 v0) H0) q) v0)) (eval_raw (nr3 x v0 v1))
      _ = (eval (p (p (p v0 v0) H0) (p (p v0 v0) x)) v0) := congrArg (fun q => (eval q v0)) (eval_raw (nr4 x v0 v1 H0 s0))
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
