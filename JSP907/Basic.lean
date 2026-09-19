/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Defs

/-!
# Basic adjacency lemmas for `JSP907.G`
-/

namespace JSP907

variable {m : ℕ}

/-- Pentagon edges. -/
lemma adj_block (B : Blk m) {y z : Pos} (h : PosAdj y z) :
    (G m).Adj (some (B, y)) (some (B, z)) := Or.inl ⟨rfl, h⟩

/-- The hub is adjacent to every non-attachment vertex of every leaf block. -/
lemma adj_hub (L : LIdx m) {y : Pos} (h : y ≠ L.1.2) :
    (G m).Adj none (some (Sum.inr L, y)) := by
  change ext (Sum.inr L, y) = none
  rw [ext_inr, extL, ite_eq_right h]

/-- The attachment edge between a spine block and the leaf block hanging from it. -/
lemma adj_attach (S : SIdx m) {x : Pos} (h : LeafOK m S.1 x) :
    (G m).Adj (some (Sum.inl S, x)) (some (Sum.inr ⟨(S.1, x), ⟨S.2, h⟩⟩, x)) := by
  refine Or.inr (Or.inl ?_)
  rw [ext_inl, extS, dite_eq_left h]

/-- The spine edge `(i, 2) — (i+1, 0)`, available whenever `i < m`. -/
lemma adj_spine {i : ℕ} (hi : i < m) :
    (G m).Adj (some (Sum.inl ⟨i, hi.le⟩, 2)) (some (Sum.inl ⟨i + 1, hi⟩, 0)) := by
  refine Or.inr (Or.inl ?_)
  have hL : ¬ LeafOK m i 2 := by
    simp only [LeafOK, not_or]
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · rintro ⟨h, -⟩; exact absurd h (by decide)
    · rintro ⟨-, h⟩; omega
  rw [ext_inl, extS, dite_eq_right hL, ite_eq_right (by decide : ¬ (2 : Pos) = 0)]
  have : min (i + 1) m = i + 1 := by omega
  simp [this]

lemma leafOK_of_mem {i : ℕ} {y : Pos} (h : y = 1 ∨ y = 3 ∨ y = 4) : LeafOK m i y := by
  rcases h with h | h | h <;> simp [LeafOK, h]

lemma leafOK_zero {i : ℕ} (h : i = 0) : LeafOK m i 0 := by
  simp [LeafOK, h]

lemma leafOK_last {i : ℕ} (h : i = m) : LeafOK m i 2 := by
  simp [LeafOK, h]

lemma pos_ne_two {y : Pos} (h : y ≠ 2) : y = 0 ∨ y = 1 ∨ y = 3 ∨ y = 4 := by
  revert y; decide

lemma pos_ne_zero {y : Pos} (h : y ≠ 0) : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by
  revert y; decide

set_option maxRecDepth 8000 in
/-- Forcing inside a pentagon: in a proper `3`-colouring of the pentagon, if four of the
five slots avoid the colour `α`, the fifth slot has colour `α`. -/
lemma pentagon_forcing (C : Pos → Fin 3) (α : Fin 3) (z : Pos)
    (hC : ∀ y y', PosAdj y y' → C y ≠ C y') (h : ∀ y, y ≠ z → C y ≠ α) :
    C z = α := by
  revert C α z
  decide +kernel

end JSP907
