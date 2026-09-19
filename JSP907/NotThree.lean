/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Colour

/-!
# `G m` is not `3`-colourable (for `m ≥ 1`)

The hub forces the attachment vertex of every leaf block to take the hub's colour
(`leaf_attach_colour`).  Hence every spine slot carrying a leaf block avoids that
colour, and the pentagon forcing lemma propagates the hub's colour down the spine.
The two ends of the spine are asymmetric, and that asymmetry produces a contradiction.
-/

namespace JSP907

variable {m : ℕ}

/-- **`G m` is not `3`-colourable** whenever `1 ≤ m`. -/
theorem not_colorable_three (m : ℕ) (hm : 1 ≤ m) : ¬ (G m).Colorable 3 := by
  rintro ⟨C⟩
  set α := C none with hα
  -- Step 1: the attachment vertex of every leaf block carries the hub's colour.
  have leaf : ∀ L : LIdx m, C (some (Sum.inr L, L.1.2)) = α := by
    intro L
    refine pentagon_forcing (fun y => C (some (Sum.inr L, y))) α L.1.2 ?_ ?_
    · intro y y' h
      exact C.valid (adj_block (Sum.inr L) h)
    · intro y hy hc
      exact C.valid (adj_hub L hy) hc.symm
  -- Step 2: a spine slot carrying a leaf block avoids the hub's colour.
  have spine_avoid : ∀ (S : SIdx m) (x : Pos), LeafOK m S.1 x →
      C (some (Sum.inl S, x)) ≠ α := by
    intro S x hx hc
    exact C.valid (adj_attach S hx) (hc.trans (leaf ⟨(S.1, x), ⟨S.2, hx⟩⟩).symm)
  -- Step 3: the hub's colour propagates along the spine.
  have key : ∀ i : ℕ, ∀ S : SIdx m, S.1 = i → i < m → C (some (Sum.inl S, 2)) = α := by
    intro i
    induction i with
    | zero =>
        intro S hS _
        refine pentagon_forcing (fun y => C (some (Sum.inl S, y))) α 2 ?_ ?_
        · intro y y' h
          exact C.valid (adj_block (Sum.inl S) h)
        · intro y hy
          refine spine_avoid S y ?_
          rcases pos_ne_two hy with rfl | h | h | h
          · exact leafOK_zero hS
          · exact leafOK_of_mem (Or.inl h)
          · exact leafOK_of_mem (Or.inr (Or.inl h))
          · exact leafOK_of_mem (Or.inr (Or.inr h))
    | succ j ih =>
        intro S hS hlt
        have hj : j < m := by omega
        refine pentagon_forcing (fun y => C (some (Sum.inl S, y))) α 2 ?_ ?_
        · intro y y' h
          exact C.valid (adj_block (Sum.inl S) h)
        · intro y hy
          rcases pos_ne_two hy with rfl | h | h | h
          · -- slot `0` is joined to slot `2` of the previous spine block
            have hprev : C (some (Sum.inl (⟨j, hj.le⟩ : SIdx m), 2)) = α :=
              ih ⟨j, hj.le⟩ rfl hj
            have hSeq : S = (⟨j + 1, hj⟩ : SIdx m) := Subtype.ext hS
            subst hSeq
            intro hc
            exact C.valid (adj_spine hj) (hprev.trans hc.symm)
          · exact spine_avoid S _ (leafOK_of_mem (Or.inl h))
          · exact spine_avoid S _ (leafOK_of_mem (Or.inr (Or.inl h)))
          · exact spine_avoid S _ (leafOK_of_mem (Or.inr (Or.inr h)))
  -- Step 4: the terminal spine block gives the contradiction.
  have hm1 : m - 1 < m := by omega
  have hprev : C (some (Sum.inl (⟨m - 1, hm1.le⟩ : SIdx m), 2)) = α :=
    key (m - 1) ⟨m - 1, hm1.le⟩ rfl hm1
  have hlast : C (some (Sum.inl (⟨m, le_refl m⟩ : SIdx m), 0)) = α := by
    refine pentagon_forcing (fun y => C (some (Sum.inl (⟨m, le_refl m⟩ : SIdx m), y))) α 0 ?_ ?_
    · intro y y' h
      exact C.valid (adj_block (Sum.inl _) h)
    · intro y hy
      rcases pos_ne_zero hy with h | h | h | h
      · exact spine_avoid _ _ (leafOK_of_mem (Or.inl h))
      · subst h
        exact spine_avoid _ _ (leafOK_last rfl)
      · exact spine_avoid _ _ (leafOK_of_mem (Or.inr (Or.inl h)))
      · exact spine_avoid _ _ (leafOK_of_mem (Or.inr (Or.inr h)))
  have hstep : (⟨m - 1 + 1, hm1⟩ : SIdx m) = (⟨m, le_refl m⟩ : SIdx m) := by
    apply Subtype.ext
    simp only
    omega
  have := C.valid (adj_spine hm1)
  rw [hstep] at this
  exact this (hprev.trans hlast.symm)

end JSP907
