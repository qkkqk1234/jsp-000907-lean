/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Basic

/-!
# `G m` is `4`-colourable

An explicit proper `4`-colouring: the hub gets a colour of its own, and a block vertex
in slot `y` of a block sitting over spine index `i` gets `fpos y + i` (spine block) or
`fpos y + i + 1` (leaf block), computed in `ZMod 3`.  Along every edge the two shades
differ by exactly `1`.
-/

namespace JSP907

variable {m : ℕ}

/-- The base three-colouring of a single pentagon. -/
def fpos : Pos → ZMod 3 := ![0, 1, 0, 1, 2]

lemma fpos_ne_of_posAdj {y z : Pos} (h : PosAdj y z) : fpos y ≠ fpos z := by
  revert y z
  decide

lemma fpos_zero : fpos 0 = 0 := rfl
lemma fpos_two : fpos 2 = 0 := rfl

lemma zmod3_ne_succ (x : ZMod 3) : x ≠ x + 1 := by revert x; decide

/-- The `ZMod 3` shade of a block vertex. -/
def shade : Blk m × Pos → ZMod 3
  | (Sum.inl S, y) => fpos y + (S.1 : ZMod 3)
  | (Sum.inr L, y) => fpos y + (L.1.1 : ZMod 3) + 1

@[simp] lemma shade_inl (S : SIdx m) (y : Pos) :
    shade (Sum.inl S, y) = fpos y + (S.1 : ZMod 3) := rfl

@[simp] lemma shade_inr (L : LIdx m) (y : Pos) :
    shade (Sum.inr L, y) = fpos y + (L.1.1 : ZMod 3) + 1 := rfl

lemma pos_cases_of_not_odd {y : Pos} (h1 : ¬ y = 1) (h3 : ¬ y = 3) (h4 : ¬ y = 4) :
    y = 0 ∨ y = 2 := by
  revert y
  decide

/-- A spine slot carrying no leaf block is either slot `0` with positive spine index,
or slot `2` with spine index `< m`. -/
lemma not_leafOK_cases {i : ℕ} {y : Pos} (h : ¬ LeafOK m i y) :
    (y = 0 ∧ i ≠ 0) ∨ (y = 2 ∧ i ≠ m) := by
  simp only [LeafOK, not_or, not_and] at h
  obtain ⟨h1, h3, h4, h0, h2⟩ := h
  have hy : y = 0 ∨ y = 2 := pos_cases_of_not_odd h1 h3 h4
  rcases hy with rfl | rfl
  · exact Or.inl ⟨rfl, h0 rfl⟩
  · exact Or.inr ⟨rfl, h2 rfl⟩

/-- Along an inter-block edge the two shades differ by exactly one. -/
lemma shade_ext_succ {p q : Blk m × Pos} (h : ext p = some q) :
    shade p = shade q + 1 ∨ shade q = shade p + 1 := by
  obtain ⟨B, y⟩ := p
  cases B with
  | inr L =>
      rw [ext_inr, extL] at h
      split_ifs at h with hy
      · obtain rfl : q = (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), L.1.2) := (Option.some.inj h).symm
        left
        rw [shade_inr, shade_inl, hy]
  | inl S =>
      rw [ext_inl, extS] at h
      split_ifs at h with hL hy
      · obtain rfl : q = (Sum.inr (⟨(S.1, y), ⟨S.2, hL⟩⟩ : LIdx m), y) := (Option.some.inj h).symm
        right
        rw [shade_inl, shade_inr]
      · obtain rfl : q = (Sum.inl (⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩ : SIdx m), 2) :=
          (Option.some.inj h).symm
        obtain ⟨-, hne⟩ | ⟨hy2, -⟩ := not_leafOK_cases hL
        · left
          have hsub : S.1 - 1 + 1 = S.1 := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hne)
          have hc : ((S.1 : ℕ) : ZMod 3) = ((S.1 - 1 : ℕ) : ZMod 3) + 1 := by
            conv_lhs => rw [← hsub]
            push_cast
            ring
          rw [shade_inl, shade_inl, hy, fpos_zero, fpos_two, zero_add, zero_add, hc]
        · exact absurd hy2 (by rw [hy]; decide)
      · obtain rfl : q = (Sum.inl (⟨min (S.1 + 1) m, min_le_right _ _⟩ : SIdx m), 0) :=
          (Option.some.inj h).symm
        obtain ⟨hy0, -⟩ | ⟨rfl, hne⟩ := not_leafOK_cases hL
        · exact absurd hy0 hy
        · right
          have hlt : S.1 < m := lt_of_le_of_ne S.2 hne
          have hmin : min (S.1 + 1) m = S.1 + 1 := by omega
          simp only [shade_inl, fpos_zero, fpos_two, zero_add, hmin]
          push_cast
          ring

lemma shade_ne_of_ext {p q : Blk m × Pos} (h : ext p = some q) : shade p ≠ shade q := by
  rcases shade_ext_succ h with h' | h' <;> intro hc
  · rw [hc] at h'; exact zmod3_ne_succ _ h'
  · rw [← hc] at h'; exact zmod3_ne_succ _ h'

/-- The explicit `4`-colouring. -/
def col4 : Vtx m → Fin 4
  | none => 3
  | some p => ⟨(shade p).val, by
      have := ZMod.val_lt (shade p)
      omega⟩

@[simp] lemma col4_val (p : Blk m × Pos) : (col4 (some p)).val = (shade p).val := rfl

lemma col4_some_ne_three (p : Blk m × Pos) : col4 (some p) ≠ (3 : Fin 4) := by
  intro h
  have h1 : (col4 (some p)).val = ((3 : Fin 4) : ℕ) := congrArg Fin.val h
  rw [col4_val] at h1
  have h2 := ZMod.val_lt (shade p)
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  omega

lemma shade_eq_of_col4_eq {p q : Blk m × Pos} (h : col4 (some p) = col4 (some q)) :
    shade p = shade q := by
  have h1 : (col4 (some p)).val = (col4 (some q)).val := congrArg Fin.val h
  rw [col4_val, col4_val] at h1
  exact ZMod.val_injective 3 h1

/-- `col4` is a proper colouring. -/
lemma col4_proper {u v : Vtx m} (h : (G m).Adj u v) : col4 u ≠ col4 v := by
  match u, v with
  | none, none => exact h.elim
  | none, some q => exact fun hc => col4_some_ne_three q hc.symm
  | some p, none => exact fun hc => col4_some_ne_three p hc
  | some p, some q =>
      intro hc
      have hs : shade p = shade q := shade_eq_of_col4_eq hc
      rcases h with ⟨hb, hpa⟩ | he | he
      · obtain ⟨Bp, yp⟩ := p
        obtain ⟨Bq, yq⟩ := q
        simp only at hb hpa
        subst hb
        refine fpos_ne_of_posAdj hpa ?_
        cases Bp with
        | inl S => exact add_right_cancel hs
        | inr L => exact add_right_cancel (add_right_cancel hs)
      · exact shade_ne_of_ext he hs
      · exact shade_ne_of_ext he hs.symm

/-- **`G m` is `4`-colourable.** -/
theorem colorable_four (m : ℕ) : (G m).Colorable 4 :=
  ⟨⟨col4, fun h => col4_proper h⟩⟩

end JSP907
