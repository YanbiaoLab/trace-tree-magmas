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
      (s0 : Step v0 x H0)
      (s1 : Step v0 v1 H1) :
      Code (p v0 (p x H0)) (p H1 (p v0 v0)) x
inductive Step : CM → CM → CM → Prop
  | raw (a b : CM) : Step a b (p a b)
  | hit {a b o : CM} (h : Code a b o) : Step a b o
end
theorem code_shape {a b o : CM} (h : Code a b o) :
    ∃ q_x q_v0 q_v1 q_H0 q_H1 : CM, Step q_v0 q_x q_H0 ∧ Step q_v0 q_v1 q_H1 ∧ a = (p q_v0 (p q_x q_H0)) ∧ b = (p q_H1 (p q_v0 q_v0)) ∧ o = q_x := by
  exact match h with
  | .law x v0 v1 H0 H1 s0 s1 => ⟨x, v0, v1, H0, H1, s0, s1, rfl, rfl, rfl⟩
def getOut (a b : CM) : CM := (L (R a))
theorem code_get {a b o : CM} (h : Code a b o) : getOut a b = o := by
  cases h <;> rfl
theorem code_unique {a b o q : CM} (h : Code a b o) (k : Code a b q) : o = q :=
  (code_get h).symm.trans (code_get k)
theorem code_bounds {a b o : CM} (h : Code a b o) : sz o < sz a := by
  rcases code_shape h with ⟨q_x, q_v0, q_v1, q_H0, q_H1, s0, s1, ha, hb, ho⟩
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
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  cases qs0 with
  | raw =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x (p q_v0 q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_v0 q_v1) (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p (p q_v0 q_v1) (p q_v0 q_v0)) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_v0 q_v1) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 q_v1) (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v1) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x (p q_v0 q_x)) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_H1 (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p q_H1 (p q_v0 q_v0)) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p q_H1 (p q_v0 q_v0)) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_H1 (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_H1 (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit qs0h =>
    cases qs1 with
    | raw =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_H0) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p (p q_v0 q_v1) (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p (p q_v0 q_v1) (p q_v0 q_v0)) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p (p q_v0 q_v1) (p q_v0 q_v0)) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p (p q_v0 q_v1) (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p (p q_v0 q_v1) (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v1) (sz_lt_p_left (p q_v0 q_v1) (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs1h =>
      have e0 := congrArg (fun q => (L q)) ha
      change v = q_v0 at e0
      have e1 := congrArg (fun q => (R q)) ha
      change k = (p q_x q_H0) at e1
      have e2 := congrArg (fun q => q) hb
      change v = (p q_H1 (p q_v0 q_v0)) at e2
      have cyc : q_v0 = (p q_H1 (p q_v0 q_v0)) := (let peq0 : v = q_v0 := e0; let peq2 : v = (p q_H1 (p q_v0 q_v0)) := e2; let pst0 : q_v0 = v := Eq.symm (peq0); let pst1 : q_v0 = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq2); pst1)
      have hlt : sz q_v0 < sz (p q_H1 (p q_v0 q_v0)) := Nat.lt_trans (sz_lt_p_left q_v0 q_v0) (sz_lt_p_right q_H1 (p q_v0 q_v0))
      exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem step_no_first {a b o : CM} (st : Step a b o) :
    ¬ ∃ u, Code o a u := by
  cases st with
  | raw =>
    rintro ⟨u, hc⟩
    exact code_no_pair_left a b ⟨u, hc⟩
  | hit sth =>
    rintro ⟨u, hc⟩
    rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
    cases qs0 with
    | raw =>
      cases qs1 with
      | raw =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p u0_x q_v1) u0_x) := (let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p u0_v0 u0_x) = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst4); let pst6 : (p u0_x (p u0_v0 u0_x)) = (p u0_x (p (p q_v0 q_v1) u0_x)) := congrArg (fun q => p u0_x q) (pst5); let pst7 : (p q_v0 q_v0) = (p u0_x (p (p q_v0 q_v1) u0_x)) := Eq.trans (pst2) (pst6); let pst8 : q_v0 = u0_x := congrArg (fun q => L q) (pst7); let pst9 : u0_x = q_v0 := Eq.symm (pst8); let pst10 : q_v0 = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0_x = (p (p q_v0 q_v1) u0_x) := Eq.trans (pst9) (pst10); let pst12 : (p q_v0 q_v1) = (p u0_x q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst13 : (p (p q_v0 q_v1) u0_x) = (p (p u0_x q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst12); let pst14 : u0_x = (p (p u0_x q_v1) u0_x) := Eq.trans (pst11) (pst13); pst14)
            have hlt : sz u0_x < sz (p (p u0_x q_v1) u0_x) := Nat.lt_trans (sz_lt_p_left u0_x q_v1) (sz_lt_p_left (p u0_x q_v1) u0_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p u0_x q_v1) u0_x) := (let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p u0_v0 u0_x) = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst4); let pst6 : (p u0_x (p u0_v0 u0_x)) = (p u0_x (p (p q_v0 q_v1) u0_x)) := congrArg (fun q => p u0_x q) (pst5); let pst7 : (p q_v0 q_v0) = (p u0_x (p (p q_v0 q_v1) u0_x)) := Eq.trans (pst2) (pst6); let pst8 : q_v0 = u0_x := congrArg (fun q => L q) (pst7); let pst9 : u0_x = q_v0 := Eq.symm (pst8); let pst10 : q_v0 = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0_x = (p (p q_v0 q_v1) u0_x) := Eq.trans (pst9) (pst10); let pst12 : (p q_v0 q_v1) = (p u0_x q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst13 : (p (p q_v0 q_v1) u0_x) = (p (p u0_x q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst12); let pst14 : u0_x = (p (p u0_x q_v1) u0_x) := Eq.trans (pst11) (pst13); pst14)
            have hlt : sz u0_x < sz (p (p u0_x q_v1) u0_x) := Nat.lt_trans (sz_lt_p_left u0_x q_v1) (sz_lt_p_left (p u0_x q_v1) u0_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := (let peq0 : o = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p q_v0 q_x))) := congrArg (fun q => p q (p q_x (p q_v0 q_x))) (pst7); let pst9 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst10 : (p q_v0 q_x) = (p u0s0out q_x) := congrArg (fun q => p q q_x) (pst9); let pst11 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s0out q_x)) := congrArg (fun q => p q_x q) (pst10); let pst12 : (p u0s0out (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := congrArg (fun q => p u0s0out q) (pst11); let pst13 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (pst8) (pst12); let pst14 : o = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (peq0) (pst13); let pst15 : (p u0s0out (p q_x (p u0s0out q_x))) = o := Eq.symm (pst14); let pst16 : (p u0s0out (p q_x (p u0s0out q_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : (p u0s0out (p q_x (p u0s0out q_x))) = u0s0out := Eq.trans (pst16) (pst6); let pst18 : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.symm (pst17); pst18)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x (p u0s0out q_x))) := sz_lt_p_left u0s0out (p q_x (p u0s0out q_x))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := (let peq0 : o = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p q_v0 q_x))) := congrArg (fun q => p q (p q_x (p q_v0 q_x))) (pst7); let pst9 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst10 : (p q_v0 q_x) = (p u0s0out q_x) := congrArg (fun q => p q q_x) (pst9); let pst11 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s0out q_x)) := congrArg (fun q => p q_x q) (pst10); let pst12 : (p u0s0out (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := congrArg (fun q => p u0s0out q) (pst11); let pst13 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (pst8) (pst12); let pst14 : o = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (peq0) (pst13); let pst15 : (p u0s0out (p q_x (p u0s0out q_x))) = o := Eq.symm (pst14); let pst16 : (p u0s0out (p q_x (p u0s0out q_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : (p u0s0out (p q_x (p u0s0out q_x))) = u0s0out := Eq.trans (pst16) (pst6); let pst18 : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.symm (pst17); pst18)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x (p u0s0out q_x))) := sz_lt_p_left u0s0out (p q_x (p u0s0out q_x))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p u0_v0 u0_x) := (let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst6 : u0_x = (p u0_v0 u0_x) := Eq.trans (pst4) (pst5); pst6)
            have hlt : sz u0_x < sz (p u0_v0 u0_x) := sz_lt_p_right u0_v0 u0_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p u0_v0 u0_x) := (let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst6 : u0_x = (p u0_v0 u0_x) := Eq.trans (pst4) (pst5); pst6)
            have hlt : sz u0_x < sz (p u0_v0 u0_x) := sz_lt_p_right u0_v0 u0_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := (let peq0 : o = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p q_v0 q_x))) := congrArg (fun q => p q (p q_x (p q_v0 q_x))) (pst7); let pst9 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst10 : (p q_v0 q_x) = (p u0s0out q_x) := congrArg (fun q => p q q_x) (pst9); let pst11 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s0out q_x)) := congrArg (fun q => p q_x q) (pst10); let pst12 : (p u0s0out (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := congrArg (fun q => p u0s0out q) (pst11); let pst13 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (pst8) (pst12); let pst14 : o = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (peq0) (pst13); let pst15 : (p u0s0out (p q_x (p u0s0out q_x))) = o := Eq.symm (pst14); let pst16 : (p u0s0out (p q_x (p u0s0out q_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : (p u0s0out (p q_x (p u0s0out q_x))) = u0s0out := Eq.trans (pst16) (pst6); let pst18 : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.symm (pst17); pst18)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x (p u0s0out q_x))) := sz_lt_p_left u0s0out (p q_x (p u0s0out q_x))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := (let peq0 : o = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p q_v0 q_x))) := congrArg (fun q => p q (p q_x (p q_v0 q_x))) (pst7); let pst9 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst10 : (p q_v0 q_x) = (p u0s0out q_x) := congrArg (fun q => p q q_x) (pst9); let pst11 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s0out q_x)) := congrArg (fun q => p q_x q) (pst10); let pst12 : (p u0s0out (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := congrArg (fun q => p u0s0out q) (pst11); let pst13 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (pst8) (pst12); let pst14 : o = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.trans (peq0) (pst13); let pst15 : (p u0s0out (p q_x (p u0s0out q_x))) = o := Eq.symm (pst14); let pst16 : (p u0s0out (p q_x (p u0s0out q_x))) = u0_x := Eq.trans (pst15) (peq5); let pst17 : (p u0s0out (p q_x (p u0s0out q_x))) = u0s0out := Eq.trans (pst16) (pst6); let pst18 : u0s0out = (p u0s0out (p q_x (p u0s0out q_x))) := Eq.symm (pst17); pst18)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x (p u0s0out q_x))) := sz_lt_p_left u0s0out (p q_x (p u0s0out q_x))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      cases qs1 with
      | raw =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p u0_x q_v1) u0_x) := (let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p u0_v0 u0_x) = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst4); let pst6 : (p u0_x (p u0_v0 u0_x)) = (p u0_x (p (p q_v0 q_v1) u0_x)) := congrArg (fun q => p u0_x q) (pst5); let pst7 : (p q_v0 q_v0) = (p u0_x (p (p q_v0 q_v1) u0_x)) := Eq.trans (pst2) (pst6); let pst8 : q_v0 = u0_x := congrArg (fun q => L q) (pst7); let pst9 : u0_x = q_v0 := Eq.symm (pst8); let pst10 : q_v0 = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0_x = (p (p q_v0 q_v1) u0_x) := Eq.trans (pst9) (pst10); let pst12 : (p q_v0 q_v1) = (p u0_x q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst13 : (p (p q_v0 q_v1) u0_x) = (p (p u0_x q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst12); let pst14 : u0_x = (p (p u0_x q_v1) u0_x) := Eq.trans (pst11) (pst13); pst14)
            have hlt : sz u0_x < sz (p (p u0_x q_v1) u0_x) := Nat.lt_trans (sz_lt_p_left u0_x q_v1) (sz_lt_p_left (p u0_x q_v1) u0_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p u0_x q_v1) u0_x) := (let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = u0_v0 := congrArg (fun q => L q) (pst1); let pst4 : u0_v0 = (p q_v0 q_v1) := Eq.symm (pst3); let pst5 : (p u0_v0 u0_x) = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst4); let pst6 : (p u0_x (p u0_v0 u0_x)) = (p u0_x (p (p q_v0 q_v1) u0_x)) := congrArg (fun q => p u0_x q) (pst5); let pst7 : (p q_v0 q_v0) = (p u0_x (p (p q_v0 q_v1) u0_x)) := Eq.trans (pst2) (pst6); let pst8 : q_v0 = u0_x := congrArg (fun q => L q) (pst7); let pst9 : u0_x = q_v0 := Eq.symm (pst8); let pst10 : q_v0 = (p (p q_v0 q_v1) u0_x) := congrArg (fun q => R q) (pst7); let pst11 : u0_x = (p (p q_v0 q_v1) u0_x) := Eq.trans (pst9) (pst10); let pst12 : (p q_v0 q_v1) = (p u0_x q_v1) := congrArg (fun q => p q q_v1) (pst8); let pst13 : (p (p q_v0 q_v1) u0_x) = (p (p u0_x q_v1) u0_x) := congrArg (fun q => p q u0_x) (pst12); let pst14 : u0_x = (p (p u0_x q_v1) u0_x) := Eq.trans (pst11) (pst13); pst14)
            have hlt : sz u0_x < sz (p (p u0_x q_v1) u0_x) := Nat.lt_trans (sz_lt_p_left u0_x q_v1) (sz_lt_p_left (p u0_x q_v1) u0_x)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0s0out = (p u0s0out (p q_x q_H0)) := (let peq0 : o = (p q_v0 (p q_x q_H0)) := ha; let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x q_H0)) = (p u0s0out (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst7); let pst9 : o = (p u0s0out (p q_x q_H0)) := Eq.trans (peq0) (pst8); let pst10 : (p u0s0out (p q_x q_H0)) = o := Eq.symm (pst9); let pst11 : (p u0s0out (p q_x q_H0)) = u0_x := Eq.trans (pst10) (peq5); let pst12 : (p u0s0out (p q_x q_H0)) = u0s0out := Eq.trans (pst11) (pst6); let pst13 : u0s0out = (p u0s0out (p q_x q_H0)) := Eq.symm (pst12); pst13)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x q_H0)) := sz_lt_p_left u0s0out (p q_x q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0s0out = (p u0s0out (p q_x q_H0)) := (let peq0 : o = (p q_v0 (p q_x q_H0)) := ha; let peq1 : a = (p (p q_v0 q_v1) (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p (p q_v0 q_v1) (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x q_H0)) = (p u0s0out (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst7); let pst9 : o = (p u0s0out (p q_x q_H0)) := Eq.trans (peq0) (pst8); let pst10 : (p u0s0out (p q_x q_H0)) = o := Eq.symm (pst9); let pst11 : (p u0s0out (p q_x q_H0)) = u0_x := Eq.trans (pst10) (peq5); let pst12 : (p u0s0out (p q_x q_H0)) = u0s0out := Eq.trans (pst11) (pst6); let pst13 : u0s0out = (p u0s0out (p q_x q_H0)) := Eq.symm (pst12); pst13)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x q_H0)) := sz_lt_p_left u0s0out (p q_x q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape sth with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p u0_v0 u0_x) := (let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst6 : u0_x = (p u0_v0 u0_x) := Eq.trans (pst4) (pst5); pst6)
            have hlt : sz u0_x < sz (p u0_v0 u0_x) := sz_lt_p_right u0_v0 u0_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p u0_v0 u0_x) := (let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst6 : u0_x = (p u0_v0 u0_x) := Eq.trans (pst4) (pst5); pst6)
            have hlt : sz u0_x < sz (p u0_v0 u0_x) := sz_lt_p_right u0_v0 u0_x
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0s0out = (p u0s0out (p q_x q_H0)) := (let peq0 : o = (p q_v0 (p q_x q_H0)) := ha; let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x q_H0)) = (p u0s0out (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst7); let pst9 : o = (p u0s0out (p q_x q_H0)) := Eq.trans (peq0) (pst8); let pst10 : (p u0s0out (p q_x q_H0)) = o := Eq.symm (pst9); let pst11 : (p u0s0out (p q_x q_H0)) = u0_x := Eq.trans (pst10) (peq5); let pst12 : (p u0s0out (p q_x q_H0)) = u0s0out := Eq.trans (pst11) (pst6); let pst13 : u0s0out = (p u0s0out (p q_x q_H0)) := Eq.symm (pst12); pst13)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x q_H0)) := sz_lt_p_left u0s0out (p q_x q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0s0out = (p u0s0out (p q_x q_H0)) := (let peq0 : o = (p q_v0 (p q_x q_H0)) := ha; let peq1 : a = (p q_H1 (p q_v0 q_v0)) := hb; let peq3 : a = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : o = u0_x := u0o; let pst0 : (p q_H1 (p q_v0 q_v0)) = a := Eq.symm (peq1); let pst1 : (p q_H1 (p q_v0 q_v0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq3); let pst2 : (p q_v0 q_v0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = u0_x := congrArg (fun q => L q) (pst2); let pst4 : u0_x = q_v0 := Eq.symm (pst3); let pst5 : q_v0 = u0s0out := congrArg (fun q => R q) (pst2); let pst6 : u0_x = u0s0out := Eq.trans (pst4) (pst5); let pst7 : q_v0 = u0s0out := Eq.trans (pst3) (pst6); let pst8 : (p q_v0 (p q_x q_H0)) = (p u0s0out (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst7); let pst9 : o = (p u0s0out (p q_x q_H0)) := Eq.trans (peq0) (pst8); let pst10 : (p u0s0out (p q_x q_H0)) = o := Eq.symm (pst9); let pst11 : (p u0s0out (p q_x q_H0)) = u0_x := Eq.trans (pst10) (peq5); let pst12 : (p u0s0out (p q_x q_H0)) = u0s0out := Eq.trans (pst11) (pst6); let pst13 : u0s0out = (p u0s0out (p q_x q_H0)) := Eq.symm (pst12); pst13)
            have hlt : sz u0s0out < sz (p u0s0out (p q_x q_H0)) := sz_lt_p_left u0s0out (p q_x q_H0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
theorem nr0 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code x H0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change x = (p q_v0 (p q_x (p q_v0 q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = (p q_v0 q_v1) at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 q_v0) at e2
        have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := e0; let peq2 : x = (p q_v0 q_v0) := e2; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : (p q_x (p q_v0 q_x)) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p q_x (p q_v0 q_x)) := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change x = (p q_v0 (p q_x (p q_v0 q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change v0 = q_H1 at e1
        have e2 := congrArg (fun q => (R q)) hb
        change x = (p q_v0 q_v0) at e2
        have cyc : q_v0 = (p q_x (p q_v0 q_x)) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := e0; let peq2 : x = (p q_v0 q_v0) := e2; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : (p q_x (p q_v0 q_x)) = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = (p q_x (p q_v0 q_x)) := Eq.symm (pst2); pst3)
        have hlt : sz q_v0 < sz (p q_x (p q_v0 q_x)) := Nat.lt_trans (sz_lt_p_left q_v0 q_x) (sz_lt_p_right q_x (p q_v0 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have epa : q_v0 = (p q_x q_H0) := Eq.symm (congrArg (fun q => R q) (Eq.trans (Eq.symm (ha)) (congrArg (fun q => (R q)) (hb))))
        have epb : q_x = q_x := rfl
        apply code_no_pair_left q_x q_H0
        exact ⟨_, by simpa only [epa, epb] using qs0h⟩
      | hit qs1h =>
        have epa : q_v0 = (p q_x q_H0) := Eq.symm (congrArg (fun q => R q) (Eq.trans (Eq.symm (ha)) (congrArg (fun q => (R q)) (hb))))
        have epb : q_x = q_x := rfl
        apply code_no_pair_left q_x q_H0
        exact ⟨_, by simpa only [epa, epb] using qs0h⟩
  | hit s0h =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p (p u0_v0 u0_v1) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p (p u0_v0 u0_v1) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p (p u0_v0 u0_v1) q_x) = (p (p u0_v0 u0_v1) u0_v0) := congrArg (fun q => p (p u0_v0 u0_v1) q) (pst8); let pst10 : (p (p u0_v0 u0_v1) u0_v0) = (p (p u0_v0 u0_v1) q_x) := Eq.symm (pst9); let pst11 : (p (p u0_v0 u0_v1) q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p (p u0_v0 u0_v1) u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v1) u0_v0) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v1) (sz_lt_p_left (p u0_v0 u0_v1) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p u0s1out u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p u0s1out q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s1out q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p u0s1out q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p u0s1out q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p u0s1out q_x) = (p u0s1out u0_v0) := congrArg (fun q => p u0s1out q) (pst8); let pst10 : (p u0s1out u0_v0) = (p u0s1out q_x) := Eq.symm (pst9); let pst11 : (p u0s1out q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p u0s1out u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p u0s1out u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p u0s1out u0_v0) := sz_lt_p_right u0s1out u0_v0
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p (p u0_v0 u0_v1) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p (p u0_v0 u0_v1) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p (p u0_v0 u0_v1) q_x) = (p (p u0_v0 u0_v1) u0_v0) := congrArg (fun q => p (p u0_v0 u0_v1) q) (pst8); let pst10 : (p (p u0_v0 u0_v1) u0_v0) = (p (p u0_v0 u0_v1) q_x) := Eq.symm (pst9); let pst11 : (p (p u0_v0 u0_v1) q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p (p u0_v0 u0_v1) u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v1) u0_v0) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v1) (sz_lt_p_left (p u0_v0 u0_v1) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p u0s1out u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p u0s1out q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s1out q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p u0s1out q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p u0s1out q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p u0s1out q_x) = (p u0s1out u0_v0) := congrArg (fun q => p u0s1out q) (pst8); let pst10 : (p u0s1out u0_v0) = (p u0s1out q_x) := Eq.symm (pst9); let pst11 : (p u0s1out q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p u0s1out u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p u0s1out u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p u0s1out u0_v0) := sz_lt_p_right u0s1out u0_v0
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p (p u0_v0 u0_v1) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p (p u0_v0 u0_v1) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p (p u0_v0 u0_v1) q_x) = (p (p u0_v0 u0_v1) u0_v0) := congrArg (fun q => p (p u0_v0 u0_v1) q) (pst8); let pst10 : (p (p u0_v0 u0_v1) u0_v0) = (p (p u0_v0 u0_v1) q_x) := Eq.symm (pst9); let pst11 : (p (p u0_v0 u0_v1) q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p (p u0_v0 u0_v1) u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v1) u0_v0) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v1) (sz_lt_p_left (p u0_v0 u0_v1) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p u0s1out u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p u0s1out q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s1out q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p u0s1out q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p u0s1out q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p u0s1out q_x) = (p u0s1out u0_v0) := congrArg (fun q => p u0s1out q) (pst8); let pst10 : (p u0s1out u0_v0) = (p u0s1out q_x) := Eq.symm (pst9); let pst11 : (p u0s1out q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p u0s1out u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p u0s1out u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p u0s1out u0_v0) := sz_lt_p_right u0s1out u0_v0
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p (p u0_v0 u0_v1) q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p (p u0_v0 u0_v1) q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p (p u0_v0 u0_v1) q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p (p u0_v0 u0_v1) q_x) = (p (p u0_v0 u0_v1) u0_v0) := congrArg (fun q => p (p u0_v0 u0_v1) q) (pst8); let pst10 : (p (p u0_v0 u0_v1) u0_v0) = (p (p u0_v0 u0_v1) q_x) := Eq.symm (pst9); let pst11 : (p (p u0_v0 u0_v1) q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p (p u0_v0 u0_v1) u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p (p u0_v0 u0_v1) u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p (p u0_v0 u0_v1) u0_v0) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_v1) (sz_lt_p_left (p u0_v0 u0_v1) u0_v0)
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p u0s1out u0_v0) := (let peq0 : x = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_x) = (p u0s1out q_x) := congrArg (fun q => p q q_x) (pst2); let pst4 : (p q_x (p q_v0 q_x)) = (p q_x (p u0s1out q_x)) := congrArg (fun q => p q_x q) (pst3); let pst5 : (p q_x (p u0s1out q_x)) = (p q_x (p q_v0 q_x)) := Eq.symm (pst4); let pst6 : (p q_x (p q_v0 q_x)) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst7 : (p q_x (p u0s1out q_x)) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : q_x = u0_v0 := congrArg (fun q => L q) (pst7); let pst9 : (p u0s1out q_x) = (p u0s1out u0_v0) := congrArg (fun q => p u0s1out q) (pst8); let pst10 : (p u0s1out u0_v0) = (p u0s1out q_x) := Eq.symm (pst9); let pst11 : (p u0s1out q_x) = u0_v0 := congrArg (fun q => R q) (pst7); let pst12 : (p u0s1out u0_v0) = u0_v0 := Eq.trans (pst10) (pst11); let pst13 : u0_v0 = (p u0s1out u0_v0) := Eq.symm (pst12); pst13)
            have hlt : sz u0_v0 < sz (p u0s1out u0_v0) := sz_lt_p_right u0s1out u0_v0
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have ena : q_v0 = (p u0_v0 u0_v1) := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
          | hit u0s1h =>
            have ena : q_v0 = u0s1out := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have ena : q_v0 = (p u0_v0 u0_v1) := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
          | hit u0s1h =>
            have ena : q_v0 = u0s1out := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
      | hit qs1h =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have ena : q_v0 = (p u0_v0 u0_v1) := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
          | hit u0s1h =>
            have ena : q_v0 = u0s1out := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have ena : q_v0 = (p u0_v0 u0_v1) := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = (p u0_v0 u0_v1) := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
          | hit u0s1h =>
            have ena : q_v0 = u0s1out := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0s1out := congrArg (fun q => L q) (pst1); pst2)
            have enb : q_x = u0_v0 := (let peq0 : x = (p q_v0 (p q_x q_H0)) := ha; let peq4 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = x := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_v0 u0_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_v0 := congrArg (fun q => L q) (pst2); pst3)
            apply u0s1N
            refine ⟨q_H0, ?_⟩
            simpa only [ena, enb] using qs0h
theorem nr1 (x v0 v1 H0 : CM)
    (s0 : Step v0 x H0) :
    ¬ ∃ o, Code v0 (p x H0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s0N := step_no_first s0
  cases s0 with
  | raw =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p q_x (p q_v0 q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = (p q_v0 q_v1) at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p q_v0 (p q_x (p q_v0 q_x))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_x (p q_v0 q_x))) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 (p q_x (p q_v0 q_x))) := sz_lt_p_left q_v0 (p q_x (p q_v0 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p q_x (p q_v0 q_x))) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_H1 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p q_v0 (p q_x (p q_v0 q_x))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_x (p q_v0 q_x))) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 (p q_x (p q_v0 q_x))) := sz_lt_p_left q_v0 (p q_x (p q_v0 q_x))
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p q_x q_H0)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = (p q_v0 q_v1) at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p q_v0 (p q_x q_H0)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_x q_H0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 (p q_x q_H0)) := sz_lt_p_left q_v0 (p q_x q_H0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => q) ha
        change v0 = (p q_v0 (p q_x q_H0)) at e0
        have e1 := congrArg (fun q => (L q)) hb
        change x = q_H1 at e1
        have e2 := congrArg (fun q => (L (R q))) hb
        change v0 = q_v0 at e2
        have e3 := congrArg (fun q => (R (R q))) hb
        change x = q_v0 at e3
        have cyc : q_v0 = (p q_v0 (p q_x q_H0)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := e0; let peq2 : v0 = q_v0 := e2; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = q_v0 := Eq.trans (pst0) (peq2); let pst2 : q_v0 = (p q_v0 (p q_x q_H0)) := Eq.symm (pst1); pst2)
        have hlt : sz q_v0 < sz (p q_v0 (p q_x q_H0)) := sz_lt_p_left q_v0 (p q_x q_H0)
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s0h =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have he : u0_H1 = u0_v0 := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = (p q_v0 q_v1) := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0_H0)) := u0a; let peq5 : x = (p u0_H1 (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0_H0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p u0_v0 q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : x = (p u0_v0 q_v1) := Eq.trans (peq1) (pst3); let pst5 : (p u0_v0 q_v1) = x := Eq.symm (pst4); let pst6 : (p u0_v0 q_v1) = (p u0_H1 (p u0_v0 u0_v0)) := Eq.trans (pst5) (peq5); let pst7 : u0_v0 = u0_H1 := congrArg (fun q => L q) (pst6); let pst8 : u0_H1 = u0_v0 := Eq.symm (pst7); pst8)
        exact step_ne_first (by simpa only [he] using u0s1)
      | hit qs1h =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x u1s0out)) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x u1s0out)) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v1) (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x u1s0out)) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v1) = (p (p u1_v0 (p u1_x u1s0out)) u0_v1) := congrArg (fun q => p q u0_v1) (pst6); let pst8 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) := congrArg (fun q => p q (p u0_v0 u0_v0)) (pst7); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst10 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst11 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst9) (pst10); let pst12 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) q) (pst11); let pst13 : (p (p u0_v0 u0_v1) (p u0_v0 u0_v0)) = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst8) (pst12); let pst14 : q_H1 = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst13); let pst15 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst14); let pst16 : (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst15) (peq9); let pst17 : u1_x = (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst16); pst17)
                have hlt : sz u1_x < sz (p (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) u0_v1)) (sz_lt_p_left (p (p u1_v0 (p u1_x u1s0out)) u0_v1) (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs1h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x (p u1_v0 u1_x)) (sz_lt_p_right u1_v0 (p u1_x (p u1_v0 u1_x)))) (sz_lt_p_left (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x))))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x (p q_v0 q_x))) := ha; let peq1 : x = q_H1 := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq5 : x = (p u0s1out (p u0_v0 u0_v0)) := u0b; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq9 : q_H1 = u1_x := u1o; let pst0 : q_H1 = x := Eq.symm (peq1); let pst1 : q_H1 = (p u0s1out (p u0_v0 u0_v0)) := Eq.trans (pst0) (peq5); let pst2 : (p q_v0 (p q_x (p q_v0 q_x))) = v0 := Eq.symm (peq0); let pst3 : (p q_v0 (p q_x (p q_v0 q_x))) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst2) (peq4); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst3); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst8 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst9 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst8); let pst10 : (p u0s1out (p u0_v0 u0_v0)) = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := congrArg (fun q => p u0s1out q) (pst9); let pst11 : q_H1 = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.trans (pst1) (pst10); let pst12 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = q_H1 := Eq.symm (pst11); let pst13 : (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) = u1_x := Eq.trans (pst12) (peq9); let pst14 : u1_x = (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Eq.symm (pst13); pst14)
                have hlt : sz u1_x < sz (p u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_right u1_v0 (p u1_x u1s0out))) (sz_lt_p_left (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out)))) (sz_lt_p_right u0s1out (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have he : u0_H1 = u0_v0 := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq1 : x = (p q_v0 q_v1) := congrArg (fun q => (L q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0_H0)) := u0a; let peq5 : x = (p u0_H1 (p u0_v0 u0_v0)) := u0b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x u0_H0)) := Eq.trans (pst0) (peq4); let pst2 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst3 : (p q_v0 q_v1) = (p u0_v0 q_v1) := congrArg (fun q => p q q_v1) (pst2); let pst4 : x = (p u0_v0 q_v1) := Eq.trans (peq1) (pst3); let pst5 : (p u0_v0 q_v1) = x := Eq.symm (pst4); let pst6 : (p u0_v0 q_v1) = (p u0_H1 (p u0_v0 u0_v0)) := Eq.trans (pst5) (peq5); let pst7 : u0_v0 = u0_H1 := congrArg (fun q => L q) (pst6); let pst8 : u0_H1 = u0_v0 := Eq.symm (pst7); pst8)
        exact step_ne_first (by simpa only [he] using u0s1)
      | hit qs1h =>
        rcases code_shape s0h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p u1s1out (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p u1s1out (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq8 : q_x = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := u1b; let peq9 : q_H0 = u1_x := u1o; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_H0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst8 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst9 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst10 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst8) (pst9); let pst11 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst10); let pst12 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst11); let pst13 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst12) (peq6); let pst14 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst13); let pst15 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst16 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst17 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst15) (pst16); let pst18 : u0_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst14) (pst17); let pst19 : q_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst18); let pst20 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = q_x := Eq.symm (pst19); let pst21 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := Eq.trans (pst20) (peq8); let pst22 : (p u1_v0 (p u1_x u1s0out)) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst21); let pst23 : (p u1_x u1s0out) = u1_v0 := congrArg (fun q => R q) (pst22); let pst24 : u1_v0 = (p u1_x u1s0out) := Eq.symm (pst23); let pst25 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst26 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst25); let pst27 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) := congrArg (fun q => p q u0_x) (pst26); let pst28 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst29 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst28); let pst30 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst29); let pst31 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst32 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst31); let pst33 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst32); let pst34 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst30) (pst33); let pst35 : u0_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst14) (pst34); let pst36 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst35); let pst37 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst27) (pst36); let pst38 : q_H0 = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst3) (pst37); let pst39 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = q_H0 := Eq.symm (pst38); let pst40 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = u1_x := Eq.trans (pst39) (peq9); let pst41 : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.symm (pst40); pst41)
                have hlt : sz u1_x < sz (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_left (p u1_x u1s0out) (p u1_x u1s0out))) (sz_lt_p_left (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq8 : q_x = (p u1s1out (p u1_v0 u1_v0)) := u1b; let peq9 : q_H0 = u1_x := u1o; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_H0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst8 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst9 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst10 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst8) (pst9); let pst11 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst10); let pst12 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst11); let pst13 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst12) (peq6); let pst14 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst13); let pst15 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst16 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst17 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst15) (pst16); let pst18 : u0_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst14) (pst17); let pst19 : q_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst18); let pst20 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = q_x := Eq.symm (pst19); let pst21 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = (p u1s1out (p u1_v0 u1_v0)) := Eq.trans (pst20) (peq8); let pst22 : (p u1_v0 (p u1_x u1s0out)) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst21); let pst23 : (p u1_x u1s0out) = u1_v0 := congrArg (fun q => R q) (pst22); let pst24 : u1_v0 = (p u1_x u1s0out) := Eq.symm (pst23); let pst25 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst26 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst25); let pst27 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) := congrArg (fun q => p q u0_x) (pst26); let pst28 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst29 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst28); let pst30 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst29); let pst31 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst32 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst31); let pst33 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst32); let pst34 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst30) (pst33); let pst35 : u0_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst14) (pst34); let pst36 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst35); let pst37 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst27) (pst36); let pst38 : q_H0 = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst3) (pst37); let pst39 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = q_H0 := Eq.symm (pst38); let pst40 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = u1_x := Eq.trans (pst39) (peq9); let pst41 : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.symm (pst40); pst41)
                have hlt : sz u1_x < sz (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_left (p u1_x u1s0out) (p u1_x u1s0out))) (sz_lt_p_left (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p u1s1out (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p u1s1out (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq8 : q_x = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := u1b; let peq9 : q_H0 = u1_x := u1o; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_H0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst8 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst9 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst10 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst8) (pst9); let pst11 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst10); let pst12 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst11); let pst13 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst12) (peq6); let pst14 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst13); let pst15 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst16 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst17 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst15) (pst16); let pst18 : u0_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst14) (pst17); let pst19 : q_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst18); let pst20 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = q_x := Eq.symm (pst19); let pst21 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := Eq.trans (pst20) (peq8); let pst22 : (p u1_v0 (p u1_x u1s0out)) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst21); let pst23 : (p u1_x u1s0out) = u1_v0 := congrArg (fun q => R q) (pst22); let pst24 : u1_v0 = (p u1_x u1s0out) := Eq.symm (pst23); let pst25 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst26 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst25); let pst27 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) := congrArg (fun q => p q u0_x) (pst26); let pst28 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst29 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst28); let pst30 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst29); let pst31 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst32 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst31); let pst33 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst32); let pst34 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst30) (pst33); let pst35 : u0_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst14) (pst34); let pst36 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst35); let pst37 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst27) (pst36); let pst38 : q_H0 = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst3) (pst37); let pst39 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = q_H0 := Eq.symm (pst38); let pst40 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = u1_x := Eq.trans (pst39) (peq9); let pst41 : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.symm (pst40); pst41)
                have hlt : sz u1_x < sz (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_left (p u1_x u1s0out) (p u1_x u1s0out))) (sz_lt_p_left (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x u1s0out)) := u1a; let peq8 : q_x = (p u1s1out (p u1_v0 u1_v0)) := u1b; let peq9 : q_H0 = u1_x := u1o; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst1); let pst3 : q_H0 = (p u0_v0 u0_x) := congrArg (fun q => R q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : u0_v0 = q_v0 := Eq.symm (pst4); let pst6 : u0_v0 = (p u1_v0 (p u1_x u1s0out)) := Eq.trans (pst5) (peq7); let pst7 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst8 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst9 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst10 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst8) (pst9); let pst11 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst10); let pst12 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst11); let pst13 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst12) (peq6); let pst14 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst13); let pst15 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst6); let pst16 : (p (p u1_v0 (p u1_x u1s0out)) u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (pst6); let pst17 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst15) (pst16); let pst18 : u0_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst14) (pst17); let pst19 : q_x = (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) := Eq.trans (pst7) (pst18); let pst20 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = q_x := Eq.symm (pst19); let pst21 : (p (p u1_v0 (p u1_x u1s0out)) (p u1_v0 (p u1_x u1s0out))) = (p u1s1out (p u1_v0 u1_v0)) := Eq.trans (pst20) (peq8); let pst22 : (p u1_v0 (p u1_x u1s0out)) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst21); let pst23 : (p u1_x u1s0out) = u1_v0 := congrArg (fun q => R q) (pst22); let pst24 : u1_v0 = (p u1_x u1s0out) := Eq.symm (pst23); let pst25 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst26 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst25); let pst27 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) := congrArg (fun q => p q u0_x) (pst26); let pst28 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst29 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst28); let pst30 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) := congrArg (fun q => p q u0_v0) (pst29); let pst31 : (p u1_v0 (p u1_x u1s0out)) = (p (p u1_x u1s0out) (p u1_x u1s0out)) := congrArg (fun q => p q (p u1_x u1s0out)) (pst24); let pst32 : u0_v0 = (p (p u1_x u1s0out) (p u1_x u1s0out)) := Eq.trans (pst6) (pst31); let pst33 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst32); let pst34 : (p u0_v0 u0_v0) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst30) (pst33); let pst35 : u0_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))) := Eq.trans (pst14) (pst34); let pst36 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := congrArg (fun q => p (p (p u1_x u1s0out) (p u1_x u1s0out)) q) (pst35); let pst37 : (p u0_v0 u0_x) = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst27) (pst36); let pst38 : q_H0 = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.trans (pst3) (pst37); let pst39 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = q_H0 := Eq.symm (pst38); let pst40 : (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) = u1_x := Eq.trans (pst39) (peq9); let pst41 : u1_x = (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Eq.symm (pst40); pst41)
                have hlt : sz u1_x < sz (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out)))) := Nat.lt_trans (Nat.lt_trans (sz_lt_p_left u1_x u1s0out) (sz_lt_p_left (p u1_x u1s0out) (p u1_x u1s0out))) (sz_lt_p_left (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p (p u1_x u1s0out) (p u1_x u1s0out)) (p (p u1_x u1s0out) (p u1_x u1s0out))))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p u1s1out (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p u1s1out (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have epa : u1_v0 = (p u1_x u1s0out) := Eq.symm (congrArg (fun q => R q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => L q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (ha)) (u0a)))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => (R q)) (hb)) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (congrArg (fun q => p u0_v0 q) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a))))))) (u0o))) (Eq.trans (congrArg (fun q => p q u0_v0) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))) (congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))))))) (u1b))))
                have epb : u1_x = u1_x := rfl
                apply code_no_pair_left u1_x u1s0out
                exact ⟨_, by simpa only [epa, epb] using u1s0h⟩
              | hit u1s1h =>
                have epa : u1_v0 = (p u1_x u1s0out) := Eq.symm (congrArg (fun q => R q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => L q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (ha)) (u0a)))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => (R q)) (hb)) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (congrArg (fun q => p u0_v0 q) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a))))))) (u0o))) (Eq.trans (congrArg (fun q => p q u0_v0) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))) (congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))))))) (u1b))))
                have epb : u1_x = u1_x := rfl
                apply code_no_pair_left u1_x u1s0out
                exact ⟨_, by simpa only [epa, epb] using u1s0h⟩
          | hit u0s1h =>
            rcases code_shape qs0h with ⟨u1_x, u1_v0, u1_v1, u1_H0, u1_H1, u1s0, u1s1, u1a, u1b, u1o⟩
            have u1s0N := step_no_first u1s0
            let u1s0out := u1_H0
            cases u1s0 with
            | raw =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p (p u1_v0 u1_v1) (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
              | hit u1s1h =>
                have cyc : u1_v0 = (p u1_x (p u1_v0 u1_x)) := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq2 : H0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq6 : H0 = u0_x := u0o; let peq7 : q_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := u1a; let peq8 : q_x = (p u1s1out (p u1_v0 u1_v0)) := u1b; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst0) (peq4); let pst2 : (p q_x q_H0) = (p u0_x u0s0out) := congrArg (fun q => R q) (pst1); let pst3 : q_x = u0_x := congrArg (fun q => L q) (pst2); let pst4 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst1); let pst5 : (p q_v0 q_v0) = (p u0_v0 q_v0) := congrArg (fun q => p q q_v0) (pst4); let pst6 : (p u0_v0 q_v0) = (p u0_v0 u0_v0) := congrArg (fun q => p u0_v0 q) (pst4); let pst7 : (p q_v0 q_v0) = (p u0_v0 u0_v0) := Eq.trans (pst5) (pst6); let pst8 : H0 = (p u0_v0 u0_v0) := Eq.trans (peq2) (pst7); let pst9 : (p u0_v0 u0_v0) = H0 := Eq.symm (pst8); let pst10 : (p u0_v0 u0_v0) = u0_x := Eq.trans (pst9) (peq6); let pst11 : u0_x = (p u0_v0 u0_v0) := Eq.symm (pst10); let pst12 : u0_v0 = q_v0 := Eq.symm (pst4); let pst13 : u0_v0 = (p u1_v0 (p u1_x (p u1_v0 u1_x))) := Eq.trans (pst12) (peq7); let pst14 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) := congrArg (fun q => p q u0_v0) (pst13); let pst15 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := congrArg (fun q => p (p u1_v0 (p u1_x (p u1_v0 u1_x))) q) (pst13); let pst16 : (p u0_v0 u0_v0) = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst14) (pst15); let pst17 : u0_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst11) (pst16); let pst18 : q_x = (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) := Eq.trans (pst3) (pst17); let pst19 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = q_x := Eq.symm (pst18); let pst20 : (p (p u1_v0 (p u1_x (p u1_v0 u1_x))) (p u1_v0 (p u1_x (p u1_v0 u1_x)))) = (p u1s1out (p u1_v0 u1_v0)) := Eq.trans (pst19) (peq8); let pst21 : (p u1_v0 (p u1_x (p u1_v0 u1_x))) = (p u1_v0 u1_v0) := congrArg (fun q => R q) (pst20); let pst22 : (p u1_x (p u1_v0 u1_x)) = u1_v0 := congrArg (fun q => R q) (pst21); let pst23 : u1_v0 = (p u1_x (p u1_v0 u1_x)) := Eq.symm (pst22); pst23)
                have hlt : sz u1_v0 < sz (p u1_x (p u1_v0 u1_x)) := Nat.lt_trans (sz_lt_p_left u1_v0 u1_x) (sz_lt_p_right u1_x (p u1_v0 u1_x))
                exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
            | hit u1s0h =>
              have u1s1N := step_no_first u1s1
              let u1s1out := u1_H1
              cases u1s1 with
              | raw =>
                have epa : u1_v0 = (p u1_x u1s0out) := Eq.symm (congrArg (fun q => R q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => L q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (ha)) (u0a)))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => (R q)) (hb)) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (congrArg (fun q => p u0_v0 q) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a))))))) (u0o))) (Eq.trans (congrArg (fun q => p q u0_v0) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))) (congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))))))) (u1b))))
                have epb : u1_x = u1_x := rfl
                apply code_no_pair_left u1_x u1s0out
                exact ⟨_, by simpa only [epa, epb] using u1s0h⟩
              | hit u1s1h =>
                have epa : u1_v0 = (p u1_x u1s0out) := Eq.symm (congrArg (fun q => R q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => L q) (congrArg (fun q => R q) (Eq.trans (Eq.symm (ha)) (u0a)))) (Eq.trans (Eq.symm (Eq.trans (Eq.symm (Eq.trans (congrArg (fun q => (R q)) (hb)) (Eq.trans (congrArg (fun q => p q q_v0) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (congrArg (fun q => p u0_v0 q) (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a))))))) (u0o))) (Eq.trans (congrArg (fun q => p q u0_v0) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))) (congrArg (fun q => p (p u1_v0 (p u1_x u1s0out)) q) (Eq.trans (Eq.symm (congrArg (fun q => L q) (Eq.trans (Eq.symm (ha)) (u0a)))) (u1a))))))) (u1b))))
                have epb : u1_x = u1_x := rfl
                apply code_no_pair_left u1_x u1s0out
                exact ⟨_, by simpa only [epa, epb] using u1s0h⟩
theorem nr2 (x v0 v1 : CM)
 :
    ¬ ∃ o, Code v0 v0 o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have he : q_H0 = q_v0 := (let peq0 : v0 = (p q_v0 (p q_x q_H0)) := ha; let peq1 : v0 = (p q_H1 (p q_v0 q_v0)) := hb; let pst0 : (p q_v0 (p q_x q_H0)) = v0 := Eq.symm (peq0); let pst1 : (p q_v0 (p q_x q_H0)) = (p q_H1 (p q_v0 q_v0)) := Eq.trans (pst0) (peq1); let pst2 : (p q_x q_H0) = (p q_v0 q_v0) := congrArg (fun q => R q) (pst1); let pst3 : q_v0 = q_H1 := congrArg (fun q => L q) (pst1); let pst4 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst3); let pst5 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst3); let pst6 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst4) (pst5); let pst7 : (p q_x q_H0) = (p q_H1 q_H1) := Eq.trans (pst2) (pst6); let pst8 : q_H0 = q_H1 := congrArg (fun q => R q) (pst7); let pst9 : q_H1 = q_v0 := Eq.symm (pst3); let pst10 : q_H0 = q_v0 := Eq.trans (pst8) (pst9); pst10)
  exact step_ne_first (by simpa only [he] using qs0)
theorem nr3 (x v0 v1 H1 : CM)
    (s1 : Step v0 v1 H1) :
    ¬ ∃ o, Code H1 (p v0 v0) o := by
  rintro ⟨o, hc⟩
  rcases code_shape hc with ⟨q_x, q_v0, q_v1, q_H0, q_H1, qs0, qs1, ha, hb, ho⟩
  have s1N := step_no_first s1
  cases s1 with
  | raw =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v0 = (p q_v0 q_v1) at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 q_v0) at e3
        have cyc : q_v0 = (p q_v0 q_v1) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v0 q_v1) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_v1) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 q_v1) := sz_lt_p_left q_v0 q_v1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x (p q_v0 q_x)) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v0 = q_H1 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 q_v0) at e3
        have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = q_H1 := e2; let peq3 : v0 = (p q_v0 q_v0) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
        have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x q_H0) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v0 = (p q_v0 q_v1) at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 q_v0) at e3
        have cyc : q_v0 = (p q_v0 q_v1) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = (p q_v0 q_v1) := e2; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = (p q_v0 q_v1) := Eq.trans (pst0) (peq2); pst1)
        have hlt : sz q_v0 < sz (p q_v0 q_v1) := sz_lt_p_left q_v0 q_v1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have e0 := congrArg (fun q => (L q)) ha
        change v0 = q_v0 at e0
        have e1 := congrArg (fun q => (R q)) ha
        change v1 = (p q_x q_H0) at e1
        have e2 := congrArg (fun q => (L q)) hb
        change v0 = q_H1 at e2
        have e3 := congrArg (fun q => (R q)) hb
        change v0 = (p q_v0 q_v0) at e3
        have cyc : q_H1 = (p q_H1 q_H1) := (let peq0 : v0 = q_v0 := e0; let peq2 : v0 = q_H1 := e2; let peq3 : v0 = (p q_v0 q_v0) := e3; let pst0 : q_v0 = v0 := Eq.symm (peq0); let pst1 : q_v0 = q_H1 := Eq.trans (pst0) (peq2); let pst2 : v0 = q_H1 := Eq.trans (peq0) (pst1); let pst3 : q_H1 = v0 := Eq.symm (pst2); let pst4 : q_H1 = (p q_v0 q_v0) := Eq.trans (pst3) (peq3); let pst5 : (p q_v0 q_v0) = (p q_H1 q_v0) := congrArg (fun q => p q q_v0) (pst1); let pst6 : (p q_H1 q_v0) = (p q_H1 q_H1) := congrArg (fun q => p q_H1 q) (pst1); let pst7 : (p q_v0 q_v0) = (p q_H1 q_H1) := Eq.trans (pst5) (pst6); let pst8 : q_H1 = (p q_H1 q_H1) := Eq.trans (pst4) (pst7); pst8)
        have hlt : sz q_H1 < sz (p q_H1 q_H1) := sz_lt_p_left q_H1 q_H1
        exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
  | hit s1h =>
    have qs0N := step_no_first qs0
    cases qs0 with
    | raw =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have p0 := ha
        change H1 = (p q_v0 (p q_x (p q_v0 q_x))) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = (p q_v0 q_v1) at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change v0 = (p q_v0 q_v0) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB z0 z1 z2 z3
        omega
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change H1 = (p q_v0 (p q_x (p q_v0 q_x))) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H1 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change v0 = (p q_v0 q_v0) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs1hB z0 z1 z2 z3
        omega
    | hit qs0h =>
      have qs1N := step_no_first qs1
      cases qs1 with
      | raw =>
        rcases code_shape s1h with ⟨u0_x, u0_v0, u0_v1, u0_H0, u0_H1, u0s0, u0s1, u0a, u0b, u0o⟩
        have u0s0N := step_no_first u0s0
        let u0s0out := u0_H0
        cases u0s0 with
        | raw =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_v0 = (p u0_x (p u0_v0 u0_x)) := (let peq1 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq1); let pst1 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (pst2); let pst4 : v0 = (p q_v0 q_v0) := Eq.trans (peq1) (pst3); let pst5 : (p q_v0 q_v0) = v0 := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst5) (peq4); let pst7 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst6); let pst8 : u0_v0 = q_v0 := Eq.symm (pst7); let pst9 : q_v0 = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst6); let pst10 : u0_v0 = (p u0_x (p u0_v0 u0_x)) := Eq.trans (pst8) (pst9); pst10)
            have hlt : sz u0_v0 < sz (p u0_x (p u0_v0 u0_x)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_right u0_x (p u0_v0 u0_x))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_v0 = (p u0_x (p u0_v0 u0_x)) := (let peq1 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := u0a; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq1); let pst1 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (pst2); let pst4 : v0 = (p q_v0 q_v0) := Eq.trans (peq1) (pst3); let pst5 : (p q_v0 q_v0) = v0 := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = (p u0_v0 (p u0_x (p u0_v0 u0_x))) := Eq.trans (pst5) (peq4); let pst7 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst6); let pst8 : u0_v0 = q_v0 := Eq.symm (pst7); let pst9 : q_v0 = (p u0_x (p u0_v0 u0_x)) := congrArg (fun q => R q) (pst6); let pst10 : u0_v0 = (p u0_x (p u0_v0 u0_x)) := Eq.trans (pst8) (pst9); pst10)
            have hlt : sz u0_v0 < sz (p u0_x (p u0_v0 u0_x)) := Nat.lt_trans (sz_lt_p_left u0_v0 u0_x) (sz_lt_p_right u0_x (p u0_v0 u0_x))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
        | hit u0s0h =>
          have u0s1N := step_no_first u0s1
          let u0s1out := u0_H1
          cases u0s1 with
          | raw =>
            have cyc : u0_x = (p (p u0_x u0s0out) (p q_x q_H0)) := (let peq0 : H1 = (p q_v0 (p q_x q_H0)) := ha; let peq1 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq1); let pst1 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (pst2); let pst4 : v0 = (p q_v0 q_v0) := Eq.trans (peq1) (pst3); let pst5 : (p q_v0 q_v0) = v0 := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst5) (peq4); let pst7 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst6); let pst8 : u0_v0 = q_v0 := Eq.symm (pst7); let pst9 : q_v0 = (p u0_x u0s0out) := congrArg (fun q => R q) (pst6); let pst10 : u0_v0 = (p u0_x u0s0out) := Eq.trans (pst8) (pst9); let pst11 : q_v0 = (p u0_x u0s0out) := Eq.trans (pst7) (pst10); let pst12 : (p q_v0 (p q_x q_H0)) = (p (p u0_x u0s0out) (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst11); let pst13 : H1 = (p (p u0_x u0s0out) (p q_x q_H0)) := Eq.trans (peq0) (pst12); let pst14 : (p (p u0_x u0s0out) (p q_x q_H0)) = H1 := Eq.symm (pst13); let pst15 : (p (p u0_x u0s0out) (p q_x q_H0)) = u0_x := Eq.trans (pst14) (peq6); let pst16 : u0_x = (p (p u0_x u0s0out) (p q_x q_H0)) := Eq.symm (pst15); pst16)
            have hlt : sz u0_x < sz (p (p u0_x u0s0out) (p q_x q_H0)) := Nat.lt_trans (sz_lt_p_left u0_x u0s0out) (sz_lt_p_left (p u0_x u0s0out) (p q_x q_H0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
          | hit u0s1h =>
            have cyc : u0_x = (p (p u0_x u0s0out) (p q_x q_H0)) := (let peq0 : H1 = (p q_v0 (p q_x q_H0)) := ha; let peq1 : v0 = (p q_v0 q_v1) := congrArg (fun q => (L q)) (hb); let peq2 : v0 = (p q_v0 q_v0) := congrArg (fun q => (R q)) (hb); let peq4 : v0 = (p u0_v0 (p u0_x u0s0out)) := u0a; let peq6 : H1 = u0_x := u0o; let pst0 : (p q_v0 q_v1) = v0 := Eq.symm (peq1); let pst1 : (p q_v0 q_v1) = (p q_v0 q_v0) := Eq.trans (pst0) (peq2); let pst2 : q_v1 = q_v0 := congrArg (fun q => R q) (pst1); let pst3 : (p q_v0 q_v1) = (p q_v0 q_v0) := congrArg (fun q => p q_v0 q) (pst2); let pst4 : v0 = (p q_v0 q_v0) := Eq.trans (peq1) (pst3); let pst5 : (p q_v0 q_v0) = v0 := Eq.symm (pst4); let pst6 : (p q_v0 q_v0) = (p u0_v0 (p u0_x u0s0out)) := Eq.trans (pst5) (peq4); let pst7 : q_v0 = u0_v0 := congrArg (fun q => L q) (pst6); let pst8 : u0_v0 = q_v0 := Eq.symm (pst7); let pst9 : q_v0 = (p u0_x u0s0out) := congrArg (fun q => R q) (pst6); let pst10 : u0_v0 = (p u0_x u0s0out) := Eq.trans (pst8) (pst9); let pst11 : q_v0 = (p u0_x u0s0out) := Eq.trans (pst7) (pst10); let pst12 : (p q_v0 (p q_x q_H0)) = (p (p u0_x u0s0out) (p q_x q_H0)) := congrArg (fun q => p q (p q_x q_H0)) (pst11); let pst13 : H1 = (p (p u0_x u0s0out) (p q_x q_H0)) := Eq.trans (peq0) (pst12); let pst14 : (p (p u0_x u0s0out) (p q_x q_H0)) = H1 := Eq.symm (pst13); let pst15 : (p (p u0_x u0s0out) (p q_x q_H0)) = u0_x := Eq.trans (pst14) (peq6); let pst16 : u0_x = (p (p u0_x u0s0out) (p q_x q_H0)) := Eq.symm (pst15); pst16)
            have hlt : sz u0_x < sz (p (p u0_x u0s0out) (p q_x q_H0)) := Nat.lt_trans (sz_lt_p_left u0_x u0s0out) (sz_lt_p_left (p u0_x u0s0out) (p q_x q_H0))
            exact (Nat.ne_of_lt hlt) (congrArg sz cyc)
      | hit qs1h =>
        have hcB := code_bounds hc
        have s1hB := code_bounds s1h
        have qs0hB := code_bounds qs0h
        have qs1hB := code_bounds qs1h
        have p0 := ha
        change H1 = (p q_v0 (p q_x q_H0)) at p0
        have z0 := congrArg sz p0
        have p1 := congrArg (fun q => (L q)) (hb)
        change v0 = q_H1 at p1
        have z1 := congrArg sz p1
        have p2 := congrArg (fun q => (R q)) (hb)
        change v0 = (p q_v0 q_v0) at p2
        have z2 := congrArg sz p2
        have p3 := ho
        change o = q_x at p3
        have z3 := congrArg sz p3
        simp only [getOut, L, R, U, sz] at hcB s1hB qs0hB qs1hB z0 z1 z2 z3
        omega
theorem source_holds (x v0 v1 : CM) :
    x = (eval (eval v0 (eval x (eval v0 x))) (eval (eval v0 v1) (eval v0 v0))) := by
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
  let H1 := eval v0 v1
  have e1a : v0 = v0 := by
    change v0 = v0
    rfl
  have e1b : v1 = v1 := by
    change v1 = v1
    rfl
  have s1 : Step v0 v1 H1 := by
    rw [← e1a, ← e1b]
    exact eval_step v0 v1
  change x = (eval (eval v0 (eval x H0)) (eval H1 (eval v0 v0)))
  have rawEq : (eval (eval v0 (eval x H0)) (eval H1 (eval v0 v0))) = (eval (p v0 (p x H0)) (p H1 (p v0 v0))) := by
    calc
      (eval (eval v0 (eval x H0)) (eval H1 (eval v0 v0))) = (eval (eval v0 (p x H0)) (eval H1 (eval v0 v0))) := congrArg (fun q => (eval (eval v0 q) (eval H1 (eval v0 v0)))) (eval_raw (nr0 x v0 v1 H0 s0))
      _ = (eval (p v0 (p x H0)) (eval H1 (eval v0 v0))) := congrArg (fun q => (eval q (eval H1 (eval v0 v0)))) (eval_raw (nr1 x v0 v1 H0 s0))
      _ = (eval (p v0 (p x H0)) (eval H1 (p v0 v0))) := congrArg (fun q => (eval (p v0 (p x H0)) (eval H1 q))) (eval_raw (nr2 x v0 v1))
      _ = (eval (p v0 (p x H0)) (p H1 (p v0 v0))) := congrArg (fun q => (eval (p v0 (p x H0)) q)) (eval_raw (nr3 x v0 v1 H1 s1))
  exact (eval_hit (Code.law x v0 v1 H0 H1 s0 s1)).symm.trans rawEq.symm
noncomputable instance instMagma2 : Magma CM where op a b := eval b a
end CM
end submission
open submission
open submission.CM
noncomputable def submission : Goal := by
  refine ⟨CM, CM.instMagma2, ?_, ?_⟩
  · intro q0 q1 q2
    exact CM.source_holds q0 q1 q2
  · intro target
    have bad := target (CM.k CM.e) CM.e
    have hl : (CM.k CM.e) = (CM.k CM.e) := rfl
    have hr : CM.e = CM.e := rfl
    have bad2 := hl.symm.trans (bad.trans hr)
    exact Bool.noConfusion (congrArg (fun q => match q with | e => true | k _ => false | p _ _ => false) bad2)
