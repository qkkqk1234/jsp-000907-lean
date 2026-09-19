/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Cut

/-!
# The cuts used in the chord analysis
-/

namespace JSP907

open SimpleGraph

variable {m : ℕ}

/-- The spine index of a block. -/
def blkIdx : Blk m → ℕ
  | Sum.inl S => S.1
  | Sum.inr L => L.1.1

@[simp] lemma blkIdx_inl (S : SIdx m) : blkIdx (Sum.inl S) = S.1 := rfl
@[simp] lemma blkIdx_inr (L : LIdx m) : blkIdx (Sum.inr L) = L.1.1 := rfl

/-- Indicator of the vertex set of the leaf block `L`. -/
def inLeaf (L : LIdx m) : Vtx m → Bool
  | none => false
  | some (Sum.inl _, _) => false
  | some (Sum.inr L', _) => decide (L' = L)

/-- Indicator of the vertex set of `L` together with the hub. -/
def inLeafHub (L : LIdx m) : Vtx m → Bool
  | none => true
  | some (Sum.inl _, _) => false
  | some (Sum.inr L', _) => decide (L' = L)

/-- Indicator of the blocks of spine index at least `k`. -/
def inHigh (k : ℕ) : Vtx m → Bool
  | none => false
  | some (B, _) => decide (k ≤ blkIdx B)

/-- Indicator of the blocks of spine index at least `k`, together with the hub. -/
def inHighHub (k : ℕ) : Vtx m → Bool
  | none => true
  | some (B, _) => decide (k ≤ blkIdx B)

/-- The attachment edge of a leaf block. -/
def attachEdge (L : LIdx m) : Sym2 (Vtx m) :=
  s(some (Sum.inr L, L.1.2), some (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), L.1.2))

/-- The spine edge between spine blocks `i` and `i+1`. -/
def spineEdge {i : ℕ} (hi : i < m) : Sym2 (Vtx m) :=
  s(some (Sum.inl (⟨i, hi.le⟩ : SIdx m), 2), some (Sum.inl (⟨i + 1, hi⟩ : SIdx m), 0))

lemma inLeaf_some_inr {L L' : LIdx m} {y : Pos} :
    inLeaf L (some (Sum.inr L', y)) = true ↔ L' = L := by
  simp [inLeaf]

/-- Crossing an edge out of a leaf block. -/
lemma cross_leaf_aux {L : LIdx m} {a b : Vtx m} (hab : (G m).Adj a b)
    (ha : inLeaf L a = true) (hb : inLeaf L b = false) :
    s(a, b) = attachEdge L ∨ b = none := by
  cases a with
  | none => exact absurd ha (by simp [inLeaf])
  | some p =>
      obtain ⟨B, y⟩ := p
      cases B with
      | inl S => exact absurd ha (by simp [inLeaf])
      | inr L' =>
          have hL : L' = L := inLeaf_some_inr.1 ha
          rw [hL] at hab ⊢
          rcases (adj_some_iff (Sum.inr L, y) b).1 hab with h | h | h
          · exact absurd hb (by rw [h]; simp [inLeaf])
          · exact absurd hb (by rw [h]; simp [inLeaf])
          · rw [ext_inr, extL] at h
            split_ifs at h with hy
            · left
              rw [h, hy, attachEdge]
            · right
              exact h

/-- Crossing an edge out of a leaf block together with the hub. -/
lemma cross_leafHub_aux {L : LIdx m} {a b : Vtx m} (hab : (G m).Adj a b)
    (ha : inLeafHub L a = true) (hb : inLeafHub L b = false) :
    s(a, b) = attachEdge L ∨ a = none := by
  cases a with
  | none => exact Or.inr rfl
  | some p =>
      obtain ⟨B, y⟩ := p
      cases B with
      | inl S => exact absurd ha (by simp [inLeafHub])
      | inr L' =>
          have hL : L' = L := by simpa [inLeafHub] using ha
          rw [hL] at hab ⊢
          rcases (adj_some_iff (Sum.inr L, y) b).1 hab with h | h | h
          · exact absurd hb (by rw [h]; simp [inLeafHub])
          · exact absurd hb (by rw [h]; simp [inLeafHub])
          · rw [ext_inr, extL] at h
            split_ifs at h with hy
            · left
              rw [h, hy, attachEdge]
            · exact absurd hb (by rw [h]; simp [inLeafHub])

/-- Every neighbour of a block vertex outside its own block is its `ext` neighbour. -/
lemma ext_eq_of_adj_other_block {p q : Blk m × Pos} (hab : (G m).Adj (some p) (some q))
    (hne : q.1 ≠ p.1) : ext p = some q := by
  rcases (adj_some_iff p (some q)).1 hab with h | h | h
  · exact absurd (congrArg Prod.fst (Option.some.inj h)) hne
  · exact absurd (congrArg Prod.fst (Option.some.inj h)) hne
  · exact h.symm

/-- Crossing an edge out of the high part of the spine. -/
lemma cross_high_aux {i : ℕ} (hi : i < m) {a b : Vtx m} (hab : (G m).Adj a b)
    (ha : inHigh (i + 1) a = true) (hb : inHigh (i + 1) b = false) :
    s(a, b) = spineEdge hi ∨ b = none := by
  cases a with
  | none => exact absurd ha (by simp [inHigh])
  | some p =>
      cases b with
      | none => exact Or.inr rfl
      | some q =>
          left
          obtain ⟨B, y⟩ := p
          have hka : i + 1 ≤ blkIdx B := by simpa [inHigh] using ha
          have hkb : ¬ (i + 1 ≤ blkIdx q.1) := by simpa [inHigh] using hb
          have hne : q.1 ≠ B := by
            intro hc
            exact hkb (by rw [hc]; exact hka)
          have hext : ext (B, y) = some q := ext_eq_of_adj_other_block hab hne
          cases B with
          | inr L =>
              exfalso
              rw [ext_inr, extL] at hext
              split_ifs at hext with hy
              have hq : q = (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), L.1.2) :=
                (Option.some.inj hext).symm
              exact hkb (by rw [hq]; simpa using hka)
          | inl S =>
              rw [ext_inl, extS] at hext
              split_ifs at hext with hL hy
              · exfalso
                have hq : q = (Sum.inr (⟨(S.1, y), ⟨S.2, hL⟩⟩ : LIdx m), y) :=
                  (Option.some.inj hext).symm
                exact hkb (by rw [hq]; simpa using hka)
              · obtain ⟨-, hnz⟩ | ⟨hy2, -⟩ := not_leafOK_cases hL
                · have hq : q = (Sum.inl (⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩ : SIdx m), 2) :=
                    (Option.some.inj hext).symm
                  have h1 : i + 1 ≤ S.1 := hka
                  have h2 : ¬ (i + 1 ≤ S.1 - 1) := by rw [hq] at hkb; simpa using hkb
                  have hieq : i = S.1 - 1 := by omega
                  have hS : (⟨i + 1, hi⟩ : SIdx m) = S := Subtype.ext (by simp only; omega)
                  have hS' : (⟨i, hi.le⟩ : SIdx m) = (⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩) :=
                    Subtype.ext (by simp only; omega)
                  rw [hq, hy, spineEdge, hS, hS', Sym2.eq_swap]
                · exact absurd hy2 (by rw [hy]; decide)
              · exfalso
                obtain ⟨hy0, -⟩ | ⟨rfl, hnm⟩ := not_leafOK_cases hL
                · exact hy hy0
                · have hlt : S.1 < m := lt_of_le_of_ne S.2 hnm
                  have hq : q = (Sum.inl (⟨min (S.1 + 1) m, min_le_right _ _⟩ : SIdx m), 0) :=
                    (Option.some.inj hext).symm
                  have h1 : i + 1 ≤ S.1 := hka
                  have h2 : ¬ (i + 1 ≤ min (S.1 + 1) m) := by rw [hq] at hkb; simpa using hkb
                  omega

/-- Crossing an edge out of the high part of the spine, hub included. -/
lemma cross_highHub_aux {i : ℕ} (hi : i < m) {a b : Vtx m} (hab : (G m).Adj a b)
    (ha : inHighHub (i + 1) a = true) (hb : inHighHub (i + 1) b = false) :
    s(a, b) = spineEdge hi ∨ a = none := by
  cases a with
  | none => exact Or.inr rfl
  | some p =>
      cases b with
      | none => exact absurd hb (by simp [inHighHub])
      | some q =>
          have ha' : inHigh (i + 1) (some p) = true := by
            simpa [inHigh, inHighHub] using ha
          have hb' : inHigh (i + 1) (some q) = false := by
            simpa [inHigh, inHighHub] using hb
          rcases cross_high_aux hi hab ha' hb' with h | h
          · exact Or.inl h
          · exact absurd h (by simp)

end JSP907
