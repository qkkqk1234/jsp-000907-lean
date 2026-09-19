/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib

/-!
# JSP-000907 (Erdős problem 1091): the pentagon caterpillar `G m`

This file sets up the graph family used to answer Erdős' question negatively.

For each `m` we build a graph out of pentagons ("blocks").  The *spine* blocks are
indexed by `i ≤ m`.  A *leaf* block is attached to the spine vertex in slot `x` of
spine block `i` exactly when `LeafOK m i x` holds, which is the case for
`x ∈ {1, 3, 4}` always, for `x = 0` only at `i = 0`, and for `x = 2` only at `i = m`.
The remaining spine slots carry the spine edges `(i, 2) — (i+1, 0)`.

Finally a single *hub* vertex is joined to every leaf-block vertex other than the
attachment vertex.  Every vertex except the hub then has degree exactly `3`.
-/

namespace JSP907

/-- Slots inside a pentagon block; the pentagon is the cycle `0-1-2-3-4-0`. -/
abbrev Pos := Fin 5

/-- Two slots are neighbours on the pentagon. -/
def PosAdj (y z : Pos) : Prop := z = y + 1 ∨ y = z + 1

instance : DecidableRel PosAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma posAdj_symm {y z : Pos} (h : PosAdj y z) : PosAdj z y := h.symm

lemma posAdj_irrefl (y : Pos) : ¬ PosAdj y y := by
  revert y; decide

/-- Spine block `i` carries a leaf block in slot `x`. -/
def LeafOK (m i : ℕ) (x : Pos) : Prop :=
  x = 1 ∨ x = 3 ∨ x = 4 ∨ (x = 0 ∧ i = 0) ∨ (x = 2 ∧ i = m)

instance (m i : ℕ) (x : Pos) : Decidable (LeafOK m i x) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

/-- Index of a spine block. -/
abbrev SIdx (m : ℕ) : Type := {i : ℕ // i ≤ m}

/-- Index of a leaf block: the spine block and the slot it hangs from. -/
abbrev LIdx (m : ℕ) : Type := {p : ℕ × Pos // p.1 ≤ m ∧ LeafOK m p.1 p.2}

instance (m : ℕ) : DecidableEq (SIdx m) := Subtype.instDecidableEq
instance (m : ℕ) : DecidableEq (LIdx m) := Subtype.instDecidableEq

/-- A block is either a spine block or a leaf block. -/
abbrev Blk (m : ℕ) : Type := SIdx m ⊕ LIdx m

instance (m : ℕ) : DecidableEq (Blk m) := inferInstanceAs (DecidableEq (_ ⊕ _))

instance (m : ℕ) : Finite (LIdx m) :=
  Finite.of_injective
    (fun L => ((⟨L.1.1, Nat.lt_succ_of_le L.2.1⟩ : Fin (m + 1)), L.1.2))
    (by
      intro a b h
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2))

/-- Vertices: `none` is the hub, `some (B, y)` is slot `y` of block `B`. -/
abbrev Vtx (m : ℕ) : Type := Option (Blk m × Pos)

example (m : ℕ) : Finite (Vtx m) := inferInstance

instance (m : ℕ) : DecidableEq (Vtx m) := inferInstanceAs (DecidableEq (Option _))

end JSP907

namespace JSP907

variable {m : ℕ}

/-- The outside neighbour of slot `y` of the spine block `S`. -/
def extS (S : SIdx m) (y : Pos) : Vtx m :=
  if h : LeafOK m S.1 y then some (Sum.inr ⟨(S.1, y), ⟨S.2, h⟩⟩, y)
  else if y = 0 then some (Sum.inl ⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩, 2)
  else some (Sum.inl ⟨min (S.1 + 1) m, min_le_right _ _⟩, 0)

/-- The outside neighbour of slot `y` of the leaf block `L`; `none` is the hub. -/
def extL (L : LIdx m) (y : Pos) : Vtx m :=
  if y = L.1.2 then some (Sum.inl ⟨L.1.1, L.2.1⟩, L.1.2) else none

/-- The unique neighbour of a block vertex lying outside its own block;
`none` denotes the hub. -/
def ext : Blk m × Pos → Vtx m
  | (Sum.inl S, y) => extS S y
  | (Sum.inr L, y) => extL L y

@[simp] lemma ext_inl (S : SIdx m) (y : Pos) : ext (Sum.inl S, y) = extS S y := rfl
@[simp] lemma ext_inr (L : LIdx m) (y : Pos) : ext (Sum.inr L, y) = extL L y := rfl

/-- Adjacency of the pentagon caterpillar. -/
def AdjRel (u v : Vtx m) : Prop :=
  match u, v with
  | none, none => False
  | none, some q => ext q = none
  | some p, none => ext p = none
  | some p, some q => (p.1 = q.1 ∧ PosAdj p.2 q.2) ∨ ext p = some q ∨ ext q = some p

instance : DecidableRel (AdjRel (m := m)) := by
  intro u v
  match u, v with
  | none, none => exact inferInstanceAs (Decidable False)
  | none, some q => exact inferInstanceAs (Decidable (ext q = none))
  | some p, none => exact inferInstanceAs (Decidable (ext p = none))
  | some p, some q =>
      exact inferInstanceAs
        (Decidable ((p.1 = q.1 ∧ PosAdj p.2 q.2) ∨ ext p = some q ∨ ext q = some p))

lemma ext_ne_self (p : Blk m × Pos) : ext p ≠ some p := by
  obtain ⟨B, y⟩ := p
  cases B with
  | inr L =>
      rw [ext_inr, extL]
      split_ifs with hy
      · intro h
        have h1 : (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m) : Blk m) = Sum.inr L :=
          congrArg Prod.fst (Option.some.inj h)
        exact Sum.inl_ne_inr h1
      · simp
  | inl S =>
      rw [ext_inl, extS]
      split_ifs with hL hy
      · intro h
        have h1 : (Sum.inr (⟨(S.1, y), ⟨S.2, hL⟩⟩ : LIdx m) : Blk m) = Sum.inl S :=
          congrArg Prod.fst (Option.some.inj h)
        exact Sum.inr_ne_inl h1
      · intro h
        have h2 : (2 : Pos) = y := congrArg Prod.snd (Option.some.inj h)
        rw [hy] at h2
        exact absurd h2 (by decide)
      · intro h
        have h2 : (0 : Pos) = y := congrArg Prod.snd (Option.some.inj h)
        exact hy h2.symm

/-- The pentagon caterpillar graph `G m`. -/
def G (m : ℕ) : SimpleGraph (Vtx m) where
  Adj := AdjRel
  symm := ⟨by
    intro u v h
    match u, v with
    | none, none => exact h
    | none, some q => exact h
    | some p, none => exact h
    | some p, some q =>
        rcases h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨h1.symm, posAdj_symm h2⟩
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro u h
    match u with
    | none => exact h
    | some p =>
        rcases h with ⟨_, h2⟩ | h | h
        · exact posAdj_irrefl _ h2
        · exact ext_ne_self p h
        · exact ext_ne_self p h⟩

instance (m : ℕ) : DecidableRel (G m).Adj := inferInstanceAs (DecidableRel (AdjRel (m := m)))

@[simp] lemma G_adj (u v : Vtx m) : (G m).Adj u v ↔ AdjRel u v := Iff.rfl

end JSP907
