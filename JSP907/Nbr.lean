/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Colour
import JSP907.Connected

/-!
# The three neighbours of a block vertex

Every vertex other than the hub has exactly three neighbours: its two pentagon
neighbours and its single inter-block neighbour `ext`.
-/

namespace JSP907

variable {m : ℕ}

lemma posAdj_iff (y z : Pos) : PosAdj y z ↔ (z = y + 1 ∨ z = y + 1 + 1 + 1 + 1) := by
  revert y z
  decide

/-- `ext` is an involution on block vertices. -/
lemma ext_involutive {p q : Blk m × Pos} (h : ext p = some q) : ext q = some p := by
  obtain ⟨B, y⟩ := p
  cases B with
  | inr L =>
      rw [ext_inr, extL] at h
      split_ifs at h with hy
      · obtain rfl : q = (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), L.1.2) := (Option.some.inj h).symm
        rw [ext_inl, extS, dite_eq_left (by exact L.2.2)]
        have hL : (⟨(L.1.1, L.1.2), ⟨L.2.1, L.2.2⟩⟩ : LIdx m) = L := Subtype.ext (by ext <;> rfl)
        rw [hy, hL]
  | inl S =>
      rw [ext_inl, extS] at h
      split_ifs at h with hL hy
      · obtain rfl : q = (Sum.inr (⟨(S.1, y), ⟨S.2, hL⟩⟩ : LIdx m), y) := (Option.some.inj h).symm
        rw [ext_inr, extL, ite_eq_left rfl]
      · obtain rfl : q = (Sum.inl (⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩ : SIdx m), 2) :=
          (Option.some.inj h).symm
        obtain ⟨-, hne⟩ | ⟨hy2, -⟩ := not_leafOK_cases hL
        · have hpos : 0 < S.1 := Nat.pos_of_ne_zero hne
          have hm : 0 < m := lt_of_lt_of_le hpos S.2
          have hnl : ¬ LeafOK m (S.1 - 1) 2 := by
            rintro (hc | hc | hc | ⟨hc, -⟩ | ⟨-, hc⟩)
            · exact absurd hc (by decide)
            · exact absurd hc (by decide)
            · exact absurd hc (by decide)
            · exact absurd hc (by decide)
            · omega
          rw [ext_inl, extS, dite_eq_right hnl, ite_eq_right (by decide : ¬ (2 : Pos) = 0)]
          have hmin : min (S.1 - 1 + 1) m = S.1 := by omega
          have : (⟨min (S.1 - 1 + 1) m, min_le_right _ _⟩ : SIdx m) = S :=
            Subtype.ext (by simpa using hmin)
          rw [this, hy]
        · exact absurd hy2 (by rw [hy]; decide)
      · obtain rfl : q = (Sum.inl (⟨min (S.1 + 1) m, min_le_right _ _⟩ : SIdx m), 0) :=
          (Option.some.inj h).symm
        obtain ⟨hy0, -⟩ | ⟨rfl, hne⟩ := not_leafOK_cases hL
        · exact absurd hy0 hy
        · have hlt : S.1 < m := lt_of_le_of_ne S.2 hne
          have hmin : min (S.1 + 1) m = S.1 + 1 := by omega
          have hnl : ¬ LeafOK m (min (S.1 + 1) m) 0 := by
            rintro (hc | hc | hc | ⟨-, hc⟩ | ⟨hc, -⟩)
            · exact absurd hc (by decide)
            · exact absurd hc (by decide)
            · exact absurd hc (by decide)
            · omega
            · exact absurd hc (by decide)
          rw [ext_inl, extS, dite_eq_right hnl, ite_eq_left rfl]
          have : (⟨min (S.1 + 1) m - 1, (Nat.sub_le _ _).trans (min_le_right _ _)⟩ : SIdx m) = S :=
            Subtype.ext (by simp only; omega)
          rw [this]

lemma adj_none_iff (p : Blk m × Pos) : (G m).Adj (some p) none ↔ ext p = none := Iff.rfl

/-- The neighbours of a block vertex. -/
lemma adj_some_iff (p : Blk m × Pos) (v : Vtx m) :
    (G m).Adj (some p) v ↔
      (v = some (p.1, p.2 + 1) ∨ v = some (p.1, p.2 + 1 + 1 + 1 + 1) ∨ v = ext p) := by
  cases v with
  | none =>
      rw [adj_none_iff]
      constructor
      · intro h; exact Or.inr (Or.inr h.symm)
      · rintro (h | h | h)
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · exact h.symm
  | some q =>
      constructor
      · rintro (⟨hb, hpa⟩ | he | he)
        · rcases (posAdj_iff _ _).1 hpa with h1 | h1
          · exact Or.inl (congrArg some (Prod.ext hb.symm h1))
          · exact Or.inr (Or.inl (congrArg some (Prod.ext hb.symm h1)))
        · exact Or.inr (Or.inr he.symm)
        · exact Or.inr (Or.inr (ext_involutive he).symm)
      · rintro (h | h | h)
        · obtain rfl : q = (p.1, p.2 + 1) := Option.some.inj h
          exact Or.inl ⟨rfl, (posAdj_iff _ _).2 (Or.inl rfl)⟩
        · obtain rfl : q = (p.1, p.2 + 1 + 1 + 1 + 1) := Option.some.inj h
          exact Or.inl ⟨rfl, (posAdj_iff _ _).2 (Or.inr rfl)⟩
        · exact Or.inr (Or.inl h.symm)

end JSP907
