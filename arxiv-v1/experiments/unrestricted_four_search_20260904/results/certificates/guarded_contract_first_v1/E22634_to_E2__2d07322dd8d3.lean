import JudgeProblem
import Mathlib

set_option maxRecDepth 10000

namespace submission

def condEq {α β : Type} [DecidableEq α] (a b : α) (yes no : β) : β :=
  match decEq a b with
  | isTrue _ => yes
  | isFalse _ => no

lemma condEq_pos {α β : Type} [DecidableEq α]
    {a b : α} {yes no : β} (h : a = b) : condEq a b yes no = yes := by
  subst b
  unfold condEq
  cases decEq a a with
  | isTrue _ => rfl
  | isFalse h => exact (h rfl).elim

lemma condEq_neg {α β : Type} [DecidableEq α]
    {a b : α} {yes no : β} (h : a ≠ b) : condEq a b yes no = no := by
  unfold condEq
  cases decEq a b with
  | isTrue hab => exact (h hab).elim
  | isFalse _ => rfl

inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM

namespace CM

def cmDecEq : (a b : CM) → Decidable (a = b)
  | .e, .e => isTrue rfl
  | .e, .k _ => isFalse (fun h => CM.noConfusion h)
  | .e, .p _ _ => isFalse (fun h => CM.noConfusion h)
  | .k _, .e => isFalse (fun h => CM.noConfusion h)
  | .p _ _, .e => isFalse (fun h => CM.noConfusion h)
  | .k a, .k b =>
      match cmDecEq a b with
      | isTrue h => isTrue (congrArg CM.k h)
      | isFalse h => isFalse (fun hab => h (CM.k.inj hab))
  | .k _, .p _ _ => isFalse (fun h => CM.noConfusion h)
  | .p _ _, .k _ => isFalse (fun h => CM.noConfusion h)
  | .p a b, .p c d =>
      match cmDecEq a c with
      | isFalse h => isFalse (fun hab => h (CM.p.inj hab).1)
      | isTrue hac =>
          match cmDecEq b d with
          | isFalse h => isFalse (fun hab => h (CM.p.inj hab).2)
          | isTrue hbd => isTrue (by cases hac; cases hbd; rfl)

instance instDecidableEq : DecidableEq CM := cmDecEq

def sz : CM → Nat
  | .e => 0
  | .k x => sz x + 1
  | .p x y => (sz x + 1) + (sz y + 1)

def dec : CM → CM
  | .e => .e
  | .k x => x
  | .p a b =>
      condEq b a (.k a)
        (match b with
        | .p c x => condEq c a x .e
        | _ => .e)

lemma dec_p_eq (a b : CM) :
    dec (.p a b) = condEq b a (.k a)
      (match b with
      | .p c x => condEq c a x .e
      | _ => .e) := rfl

lemma dec_p_p_eq (a c x : CM) :
    dec (CM.p a (CM.p c x)) =
      condEq (CM.p c x) a (CM.k a) (condEq c a x CM.e) := rfl

def op (a b : CM) : CM :=
  condEq b .e (dec a) (condEq a (.p b b) .e (.p a b))

instance instMagma : Magma CM where
  op a b := op b a

lemma sz_p_pos (a b : CM) : 0 < sz (.p a b) := by
  change 0 < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))

lemma sz_lt_p_left (a b : CM) : sz a < sz (.p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))

lemma sz_dec_le (a : CM) : sz (dec a) ≤ sz a := by
  cases a with
  | e => exact Nat.le_refl 0
  | k x =>
      change sz x ≤ sz x + 1
      exact Nat.le_add_right (sz x) 1
  | p a b =>
      by_cases hba : b = a
      · subst b
        rw [dec_p_eq]
        rw [condEq_pos rfl]
        change sz a + 1 ≤ (sz a + 1) + (sz a + 1)
        exact Nat.le_add_right (sz a + 1) (sz a + 1)
      · cases b with
        | e =>
            rw [dec_p_eq]
            rw [condEq_neg hba]
            exact Nat.zero_le _
        | k b =>
            rw [dec_p_eq]
            rw [condEq_neg hba]
            exact Nat.zero_le _
        | p c x =>
            by_cases hca : c = a
            · subst c
              rw [dec_p_p_eq]
              rw [condEq_neg hba, condEq_pos rfl]
              change sz x ≤ (sz a + 1) + (((sz a + 1) + (sz x + 1)) + 1)
              exact Nat.le_trans (Nat.le_add_right (sz x) 1)
                (Nat.le_trans (Nat.le_add_left (sz x + 1) (sz a + 1))
                  (Nat.le_trans
                    (Nat.le_add_right ((sz a + 1) + (sz x + 1)) 1)
                    (Nat.le_add_left (((sz a + 1) + (sz x + 1)) + 1) (sz a + 1))))
            · rw [dec_p_p_eq]
              rw [condEq_neg hba, condEq_neg hca]
              exact Nat.zero_le _

lemma sz_dec_lt_of_ne_e (a : CM) (ha : a ≠ .e) : sz (dec a) < sz a := by
  cases a with
  | e => exact (ha rfl).elim
  | k x =>
      change sz x < sz x + 1
      exact Nat.lt_succ_self (sz x)
  | p a b =>
      by_cases hba : b = a
      · subst b
        rw [dec_p_eq]
        rw [condEq_pos rfl]
        change sz a + 1 < (sz a + 1) + (sz a + 1)
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ (sz a))
      · cases b with
        | e =>
            rw [dec_p_eq]
            rw [condEq_neg hba]
            exact sz_p_pos _ _
        | k b =>
            rw [dec_p_eq]
            rw [condEq_neg hba]
            exact sz_p_pos _ _
        | p c x =>
            by_cases hca : c = a
            · subst c
              rw [dec_p_p_eq]
              rw [condEq_neg hba, condEq_pos rfl]
              change sz x < (sz a + 1) + (((sz a + 1) + (sz x + 1)) + 1)
              exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz x))
                (Nat.le_trans (Nat.le_add_left (sz x + 1) (sz a + 1))
                  (Nat.le_trans
                    (Nat.le_add_right ((sz a + 1) + (sz x + 1)) 1)
                    (Nat.le_add_left (((sz a + 1) + (sz x + 1)) + 1) (sz a + 1))))
            · rw [dec_p_p_eq]
              rw [condEq_neg hba, condEq_neg hca]
              exact sz_p_pos _ _

lemma ne_self_p (a b : CM) : a ≠ .p a b := by
  intro h
  have hs := congrArg sz h
  exact (Nat.ne_of_lt (sz_lt_p_left a b)) hs

lemma dec_ne_p_self (a b : CM) : dec a ≠ .p a b := by
  intro h
  have hle := sz_dec_le a
  have hs := congrArg sz h
  rw [hs] at hle
  exact (Nat.lt_irrefl (sz a))
    (Nat.lt_of_lt_of_le (sz_lt_p_left a b) hle)

lemma dec_ne_self_of_dec_ne_e (a : CM) (ha : dec a ≠ .e) : dec a ≠ a := by
  have hae : a ≠ .e := by
    intro h
    subst a
    exact ha rfl
  intro h
  have hlt := sz_dec_lt_of_ne_e a hae
  have hs := congrArg sz h
  rw [hs] at hlt
  exact (Nat.lt_irrefl (sz a)) hlt

lemma dec_p_default (a b : CM) (hba : b ≠ a)
    (hshape : ∀ x, b ≠ .p a x) : dec (.p a b) = .e := by
  cases b with
  | e =>
      rw [dec_p_eq]
      rw [condEq_neg hba]
  | k x =>
      rw [dec_p_eq]
      rw [condEq_neg hba]
  | p c x =>
      have hca : c ≠ a := by
        intro h
        subst c
        exact hshape x rfl
      rw [dec_p_p_eq]
      rw [condEq_neg hba, condEq_neg hca]

lemma dec_p_same (a : CM) : dec (.p a a) = .k a := by
  rw [dec_p_eq]
  rw [condEq_pos rfl]

lemma dec_p_nested (a x : CM) : dec (.p a (.p a x)) = x := by
  have hba : .p a x ≠ a := by
    intro h
    exact ne_self_p a x h.symm
  rw [dec_p_p_eq]
  rw [condEq_neg hba, condEq_pos rfl]

lemma op_right_e (a : CM) : op a .e = dec a := by
  unfold op
  rw [condEq_pos rfl]

lemma op_normal (a b : CM) (hb : b ≠ .e) (ha : a ≠ .p b b) :
    op a b = .p a b := by
  unfold op
  rw [condEq_neg hb, condEq_neg ha]

lemma op_special (a b : CM) (hb : b ≠ .e) (ha : a = .p b b) :
    op a b = .e := by
  unfold op
  rw [condEq_neg hb, condEq_pos ha]

lemma decode_twice (y x : CM) : dec (op y (op y x)) = x := by
  by_cases hx : x = .e
  · subst x
    by_cases hd : dec y = .e
    · calc
        dec (op y (op y .e)) = dec (op y (dec y)) := by rw [op_right_e]
        _ = dec (op y .e) := by rw [hd]
        _ = dec (dec y) := by rw [op_right_e]
        _ = dec .e := by rw [hd]
        _ = .e := rfl
    · by_cases hy : y = .p (dec y) (dec y)
      · have oy : op y (dec y) = .e := op_special y (dec y) hd hy
        calc
          dec (op y (op y .e)) = dec (op y (dec y)) := by rw [op_right_e]
          _ = dec .e := by rw [oy]
          _ = .e := rfl
      · have hdy : dec y ≠ y := dec_ne_self_of_dec_ne_e y hd
        have hshape : ∀ q, dec y ≠ .p y q := fun q => dec_ne_p_self y q
        have hdefault : dec (.p y (dec y)) = .e :=
          dec_p_default y (dec y) hdy hshape
        have oy : op y (dec y) = .p y (dec y) := op_normal y (dec y) hd hy
        calc
          dec (op y (op y .e)) = dec (op y (dec y)) := by rw [op_right_e]
          _ = dec (.p y (dec y)) := by rw [oy]
          _ = .e := hdefault
  · by_cases hy : y = .p x x
    · subst y
      have hinner : op (.p x x) x = .e := op_special (.p x x) x hx rfl
      calc
        dec (op (.p x x) (op (.p x x) x)) = dec (op (.p x x) .e) := by rw [hinner]
        _ = dec (dec (.p x x)) := by rw [op_right_e]
        _ = dec (.k x) := by rw [dec_p_same]
        _ = x := rfl
    · have hbig : y ≠ .p (.p y x) (.p y x) := by
        intro h
        have hs := congrArg sz h
        have hlt := Nat.lt_trans (sz_lt_p_left y x)
          (sz_lt_p_left (.p y x) (.p y x))
        exact (Nat.ne_of_lt hlt) hs
      have hpxe : CM.p y x ≠ CM.e := by
        intro h
        exact CM.noConfusion h
      have hinner : op y x = .p y x := op_normal y x hx hy
      have houter : op y (.p y x) = .p y (.p y x) :=
        op_normal y (.p y x) hpxe hbig
      calc
        dec (op y (op y x)) = dec (op y (.p y x)) := by rw [hinner]
        _ = dec (.p y (.p y x)) := by rw [houter]
        _ = x := dec_p_nested y x

lemma triple (z : CM) : op (op z z) z = .e := by
  by_cases hz : z = .e
  · subst z
    have hee : op CM.e CM.e = CM.e := by
      calc
        op CM.e CM.e = dec CM.e := op_right_e CM.e
        _ = CM.e := rfl
    exact (congrArg (fun q => op q CM.e) hee).trans hee
  · have hself : z ≠ .p z z := ne_self_p z z
    have hinner : op z z = .p z z := op_normal z z hz hself
    calc
      op (op z z) z = op (.p z z) z := by rw [hinner]
      _ = .e := op_special (.p z z) z hz rfl



theorem source_instance (q0 q1 q2 : CM) :
    q0 = (CM.op (CM.op q2 (CM.op q2 q0)) (CM.op (CM.op q1 q1) q1)) := by
  simp only [triple, op_right_e, decode_twice]

end CM
end submission
open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, CM.source_instance, ?_⟩
  intro target
  have bad := target CM.e (CM.k CM.e)
  change CM.e = (CM.k CM.e) at bad
  exact (show Not (CM.e = (CM.k CM.e)) from by decide) bad
