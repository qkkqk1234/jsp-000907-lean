/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Blocks

/-!
# Chords of a cycle in `G m`
-/

namespace JSP907

open SimpleGraph

variable {m : ℕ} {v : Vtx m} {c : (G m).Walk v v}

lemma dart_edge_mem (d : (G m).Dart) (hd : d ∈ c.darts) : d.edge ∈ c.edges :=
  mem_edges_of_mem_darts hd

lemma hub_nbr_of_dart {d : (G m).Dart} (hd : d ∈ c.darts) (h : d.toProd.1 = none) :
    d.toProd.2 ∈ c.toSubgraph.neighborSet none := by
  have he : d.edge ∈ c.edges := dart_edge_mem d hd
  rw [SimpleGraph.Dart.edge, h] at he
  exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.2 he

lemma hub_nbr_of_dart' {d : (G m).Dart} (hd : d ∈ c.darts) (h : d.toProd.2 = none) :
    d.toProd.1 ∈ c.toSubgraph.neighborSet none := by
  have he : d.edge ∈ c.edges := dart_edge_mem d hd
  rw [SimpleGraph.Dart.edge, h, Sym2.eq_swap] at he
  exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.2 he

lemma cross_cases {f : Vtx m → Bool} {d : (G m).Dart} (hcr : Crosses f d = true) :
    (f d.toProd.1 = true ∧ f d.toProd.2 = false) ∨
      (f d.toProd.1 = false ∧ f d.toProd.2 = true) := by
  simp only [Crosses, bne_iff_ne, ne_eq] at hcr
  cases h1 : f d.toProd.1 <;> cases h2 : f d.toProd.2 <;> simp_all

lemma dart_edge_eq (d : (G m).Dart) : d.edge = s(d.toProd.1, d.toProd.2) := rfl

/-- If the only non-hub crossing edge is unused, every crossing dart meets the hub. -/
lemma cross_hub_of_not_mem (f : Vtx m → Bool) (e : Sym2 (Vtx m))
    (hstep : ∀ {a b : Vtx m}, (G m).Adj a b → f a = true → f b = false →
        s(a, b) = e ∨ b = none ∨ a = none)
    (hne : e ∉ c.edges) :
    ∀ d ∈ c.darts, Crosses f d = true → (d.toProd.1 = none ∨ d.toProd.2 = none) := by
  intro d hd hcr
  rcases cross_cases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hstep d.adj h1 h2 with h | h | h
    · refine absurd ?_ hne
      have hde : d.edge = e := by rw [dart_edge_eq]; exact h
      exact hde ▸ dart_edge_mem d hd
    · exact Or.inr h
    · exact Or.inl h
  · rcases hstep d.adj.symm h2 h1 with h | h | h
    · refine absurd ?_ hne
      have : d.edge = e := by rw [dart_edge_eq, Sym2.eq_swap]; exact h
      exact this ▸ dart_edge_mem d hd
    · exact Or.inl h
    · exact Or.inr h

/-- The attachment edge of a leaf block is never a chord. -/
lemma attach_not_chord (hc : c.IsCycle) (L : LIdx m) : ¬ c.IsChord (attachEdge L) := by
  intro hch
  rw [attachEdge, SimpleGraph.Walk.isChord_sym2Mk] at hch
  obtain ⟨-, hne, hx, hy⟩ := hch
  refine cut_absurd hc (inLeaf L) ?_ hx hy (by simp) (by simp) (by simp [inLeaf])
  refine cross_hub_of_not_mem (inLeaf L) (attachEdge L) ?_ (by rw [attachEdge]; exact hne)
  intro a b hab ha hb
  rcases cross_leaf_aux hab ha hb with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Spine edges are never chords. -/
lemma spine_not_chord (hc : c.IsCycle) {i : ℕ} (hi : i < m) : ¬ c.IsChord (spineEdge hi) := by
  intro hch
  rw [spineEdge, SimpleGraph.Walk.isChord_sym2Mk] at hch
  obtain ⟨-, hne, hx, hy⟩ := hch
  refine cut_absurd hc (inHigh (i + 1)) ?_ hx hy (by simp) (by simp) ?_
  · refine cross_hub_of_not_mem (inHigh (i + 1)) (spineEdge hi) ?_ (by rw [spineEdge]; exact hne)
    intro a b hab ha hb
    rcases cross_high_aux hi hab ha hb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · simp [inHigh]

lemma eq_of_inLeaf {L : LIdx m} {a : Vtx m} (h : inLeaf L a = true) :
    ∃ y : Pos, a = some (Sum.inr L, y) := by
  cases a with
  | none => simp [inLeaf] at h
  | some p =>
      obtain ⟨B, y⟩ := p
      cases B with
      | inl S => simp [inLeaf] at h
      | inr L' => exact ⟨y, by rw [inLeaf_some_inr.1 h]⟩

/-- Every leaf block met by the cycle contains a cycle-neighbour of the hub. -/
lemma leaf_has_hub_nbr (hc : c.IsCycle) (L : LIdx m) {y0 : Pos}
    (hmem : some (Sum.inr L, y0) ∈ c.support) (hhub : (none : Vtx m) ∈ c.support) :
    ∃ y : Pos, some (Sum.inr L, y) ∈ c.toSubgraph.neighborSet none := by
  by_contra hcon
  push Not at hcon
  refine cut_absurd' hc (inLeaf L) (attachEdge L) ?_ hmem hhub (by simp [inLeaf])
  intro d hd hcr
  rcases cross_cases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases cross_leaf_aux d.adj h1 h2 with h | h
    · rw [beq_iff_eq, dart_edge_eq]; exact h
    · exfalso
      obtain ⟨y, hy⟩ := eq_of_inLeaf h1
      exact hcon y (hy ▸ hub_nbr_of_dart' hd h)
  · rcases cross_leaf_aux d.adj.symm h2 h1 with h | h
    · rw [beq_iff_eq, dart_edge_eq, Sym2.eq_swap]; exact h
    · exfalso
      obtain ⟨y, hy⟩ := eq_of_inLeaf h2
      exact hcon y (hy ▸ hub_nbr_of_dart hd h)

lemma Nc_subset_nbr (u : Vtx m) :
    c.toSubgraph.neighborSet u ⊆ (G m).neighborSet u := fun _ hx => c.toSubgraph.adj_sub hx

/-- If a pentagon edge at `some p` is a chord, the inter-block edge at `some p` is used. -/
lemma ext_mem_edges_of_pent_chord (hc : c.IsCycle) {p q : Blk m × Pos} (hbq : q.1 = p.1)
    (hch : c.IsChord s(some p, some q)) : s(some p, ext p) ∈ c.edges := by
  rw [SimpleGraph.Walk.isChord_sym2Mk] at hch
  obtain ⟨hadj, hne, hx, hy⟩ := hch
  have hN : (c.toSubgraph.neighborSet (some p)).ncard = 2 :=
    hc.ncard_neighborSet_toSubgraph_eq_two hx
  by_contra hcon
  have hqnot : (some q : Vtx m) ∉ c.toSubgraph.neighborSet (some p) := by
    intro hmem
    exact hne (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hmem)
  have hextnot : (ext p : Vtx m) ∉ c.toSubgraph.neighborSet (some p) := by
    intro hmem
    exact hcon (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hmem)
  have hq3 : (some q : Vtx m) = some (p.1, p.2 + 1) ∨
      (some q : Vtx m) = some (p.1, p.2 + 1 + 1 + 1 + 1) := by
    rcases (adj_some_iff p (some q)).1 hadj with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hbq (ext_block_ne h.symm)
  have hsub : c.toSubgraph.neighborSet (some p) ⊆
      ({if (some q : Vtx m) = some (p.1, p.2 + 1) then some (p.1, p.2 + 1 + 1 + 1 + 1)
        else some (p.1, p.2 + 1)} : Set (Vtx m)) := by
    intro z hz
    have hz' : z ∈ (G m).neighborSet (some p) := Nc_subset_nbr _ hz
    rw [neighborSet_some] at hz'
    have hzq : z ≠ some q := fun h => hqnot (h ▸ hz)
    have hze : z ≠ ext p := fun h => hextnot (h ▸ hz)
    rcases hz' with h | h | h
    · rcases hq3 with hq | hq
      · exact absurd (h.trans hq.symm) hzq
      · rw [Set.mem_singleton_iff]
        split_ifs with hif
        · exact absurd (hq.symm.trans hif) (by
            simpa using (pentNbr_ne p).symm)
        · exact h
    · rcases hq3 with hq | hq
      · rw [Set.mem_singleton_iff, ite_eq_left hq]
        exact h
      · exact absurd (h.trans hq.symm) hzq
    · exact absurd h hze
  have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [hN, Set.ncard_singleton] at this
  omega

/-- Every inter-block edge is an attachment edge or a spine edge. -/
lemma ext_edge_cases {p q : Blk m × Pos} (h : ext p = some q) :
    (∃ L : LIdx m, s((some p : Vtx m), some q) = attachEdge L) ∨
      (∃ (i : ℕ) (hi : i < m), s((some p : Vtx m), some q) = spineEdge hi) := by
  obtain ⟨B, y⟩ := p
  cases B with
  | inr L =>
      rw [ext_inr, extL] at h
      split_ifs at h with hy
      refine Or.inl ⟨L, ?_⟩
      obtain rfl : q = (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m), L.1.2) := (Option.some.inj h).symm
      rw [attachEdge, hy]
  | inl S =>
      rw [ext_inl, extS] at h
      split_ifs at h with hL hy
      · obtain rfl : q = (Sum.inr (⟨(S.1, y), ⟨S.2, hL⟩⟩ : LIdx m), y) := (Option.some.inj h).symm
        refine Or.inl ⟨⟨(S.1, y), ⟨S.2, hL⟩⟩, ?_⟩
        rw [attachEdge, Sym2.eq_swap]
      · obtain rfl : q = (Sum.inl (⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩ : SIdx m), 2) :=
          (Option.some.inj h).symm
        obtain ⟨-, hnz⟩ | ⟨hy2, -⟩ := not_leafOK_cases hL
        · have hi : S.1 - 1 < m := by omega
          refine Or.inr ⟨S.1 - 1, hi, ?_⟩
          rw [spineEdge, Sym2.eq_swap, hy]
          have h1 : (⟨S.1 - 1 + 1, hi⟩ : SIdx m) = S := Subtype.ext (by simp only; omega)
          have h2 : (⟨S.1 - 1, hi.le⟩ : SIdx m) = ⟨S.1 - 1, (Nat.sub_le _ _).trans S.2⟩ :=
            Subtype.ext rfl
          rw [h1, h2]
        · exact absurd hy2 (by rw [hy]; decide)
      · obtain rfl : q = (Sum.inl (⟨min (S.1 + 1) m, min_le_right _ _⟩ : SIdx m), 0) :=
          (Option.some.inj h).symm
        obtain ⟨hy0, -⟩ | ⟨rfl, hnm⟩ := not_leafOK_cases hL
        · exact absurd hy0 hy
        · have hlt : S.1 < m := lt_of_le_of_ne S.2 hnm
          refine Or.inr ⟨S.1, hlt, ?_⟩
          rw [spineEdge]
          have h1 : (⟨S.1, hlt.le⟩ : SIdx m) = S := Subtype.ext rfl
          have h2 : (⟨S.1 + 1, hlt⟩ : SIdx m) = ⟨min (S.1 + 1) m, min_le_right _ _⟩ :=
            Subtype.ext (by simp only; omega)
          rw [h1, h2]

/-- No inter-block edge is a chord. -/
lemma interblock_not_chord (hc : c.IsCycle) {p q : Blk m × Pos} (h : ext p = some q) :
    ¬ c.IsChord s((some p : Vtx m), some q) := by
  rcases ext_edge_cases h with ⟨L, hL⟩ | ⟨i, hi, hi'⟩
  · rw [hL]; exact attach_not_chord hc L
  · rw [hi']; exact spine_not_chord hc hi

/-- If the cycle meets a leaf block and also something outside it, the hub is on it. -/
lemma hub_mem_of_leaf_and_outside (hc : c.IsCycle) (L : LIdx m) {a b : Vtx m}
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hia : inLeaf L a = true) (hib : inLeaf L b = false) : (none : Vtx m) ∈ c.support := by
  by_contra hcon
  refine cut_absurd' hc (inLeaf L) (attachEdge L) ?_ ha hb (by rw [hia, hib]; simp)
  intro d hd hcr
  rcases cross_cases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases cross_leaf_aux d.adj h1 h2 with h | h
    · rw [beq_iff_eq, dart_edge_eq]; exact h
    · exact absurd (h ▸ c.dart_snd_mem_support_of_mem_darts hd) hcon
  · rcases cross_leaf_aux d.adj.symm h2 h1 with h | h
    · rw [beq_iff_eq, dart_edge_eq, Sym2.eq_swap]; exact h
    · exact absurd (h ▸ c.dart_fst_mem_support_of_mem_darts hd) hcon

/-- Half of the block analysis for a pentagon chord: the vertex `some (B, x)` is assumed
to have a leaf block hanging from it, or to be a non-attachment leaf vertex. -/
lemma pent_chord_aux (hc : c.IsCycle) {B : Blk m} {x y : Pos}
    (he : c.IsChord s((some (B, x) : Vtx m), some (B, y))) :
    ((∃ L : LIdx m, B = Sum.inr L ∧ x ≠ L.1.2) ∨ (∃ S : SIdx m, B = Sum.inl S ∧ LeafOK m S.1 x)) →
    ∃ L : LIdx m, (∃ z : Pos, some (Sum.inr L, z) ∈ c.toSubgraph.neighborSet none) ∧
      (B = Sum.inr L ∨ B = Sum.inl ⟨L.1.1, L.2.1⟩) := by
  rintro (⟨L, rfl, hxa⟩ | ⟨S, rfl, hL⟩)
  · have hext : s((some (Sum.inr L, x) : Vtx m), ext (Sum.inr L, x)) ∈ c.edges :=
      ext_mem_edges_of_pent_chord hc (p := (Sum.inr L, x)) (q := (Sum.inr L, y)) rfl he
    rw [ext_inr, extL, ite_eq_right hxa] at hext
    have hhub : (none : Vtx m) ∈ c.support := c.snd_mem_support_of_mem_edges hext
    have hmem : (some (Sum.inr L, x) : Vtx m) ∈ c.support :=
      c.fst_mem_support_of_mem_edges hext
    exact ⟨L, leaf_has_hub_nbr hc L hmem hhub, Or.inl rfl⟩
  · have hext : s((some (Sum.inl S, x) : Vtx m), ext (Sum.inl S, x)) ∈ c.edges :=
      ext_mem_edges_of_pent_chord hc (p := (Sum.inl S, x)) (q := (Sum.inl S, y)) rfl he
    rw [ext_inl, extS, dite_eq_left hL] at hext
    set L : LIdx m := ⟨(S.1, x), ⟨S.2, hL⟩⟩ with hLdef
    have hleaf : (some (Sum.inr L, x) : Vtx m) ∈ c.support :=
      c.snd_mem_support_of_mem_edges hext
    have hspine : (some (Sum.inl S, x) : Vtx m) ∈ c.support :=
      c.fst_mem_support_of_mem_edges hext
    have hhub : (none : Vtx m) ∈ c.support :=
      hub_mem_of_leaf_and_outside hc L hleaf hspine (by simp [inLeaf]) (by simp [inLeaf])
    refine ⟨L, leaf_has_hub_nbr hc L hleaf hhub, Or.inr ?_⟩
    congr 1

end JSP907
