/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Chord
import JSP907.NotThree

/-!
# Main theorem for JSP-000907 (Erdős problem 1091)
-/

namespace JSP907

open SimpleGraph

variable {m : ℕ} {v : Vtx m} {c : (G m).Walk v v}

/-- The five pentagon edges of a block. -/
def pentEdges (B : Blk m) : Finset (Sym2 (Vtx m)) :=
  (Finset.univ : Finset Pos).image (fun x => s((some (B, x) : Vtx m), some (B, x + 1)))

/-- The five hub edges at a leaf block. -/
def hubEdges (L : LIdx m) : Finset (Sym2 (Vtx m)) :=
  (Finset.univ : Finset Pos).image (fun z => s((none : Vtx m), some (Sum.inr L, z)))

/-- The edges that can be chords "because of" the leaf block `L`. -/
def locEdges (L : LIdx m) : Finset (Sym2 (Vtx m)) :=
  pentEdges (Sum.inr L) ∪ pentEdges (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m)) ∪ hubEdges L

lemma card_pentEdges (B : Blk m) : (pentEdges B).card ≤ 5 := by
  refine le_trans (Finset.card_image_le) ?_
  simp

lemma card_hubEdges (L : LIdx m) : (hubEdges L).card ≤ 5 := by
  refine le_trans (Finset.card_image_le) ?_
  simp

lemma card_locEdges (L : LIdx m) : (locEdges L).card ≤ 15 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := card_pentEdges (Sum.inr L)
  have h2 := card_pentEdges (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m))
  have h3 := card_hubEdges L
  have h4 := Finset.card_union_le (pentEdges (Sum.inr L))
    (pentEdges (Sum.inl (⟨L.1.1, L.2.1⟩ : SIdx m)))
  omega

lemma pos_five (x : Pos) : x + 1 + 1 + 1 + 1 + 1 = x := by
  revert x
  decide

lemma mem_pentEdges (B : Blk m) {x y : Pos} (h : PosAdj x y) :
    s((some (B, x) : Vtx m), some (B, y)) ∈ pentEdges B := by
  rcases (posAdj_iff x y).1 h with rfl | rfl
  · exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, rfl⟩
  · refine Finset.mem_image.2 ⟨x + 1 + 1 + 1 + 1, Finset.mem_univ _, ?_⟩
    rw [pos_five]
    exact Sym2.eq_swap

lemma posAdj_ne {x y : Pos} (h : PosAdj x y) : x ≠ y := by
  revert x y
  decide

lemma posAdj_leafSlot {x y : Pos} (h : PosAdj x y) :
    (x = 1 ∨ x = 3 ∨ x = 4) ∨ (y = 1 ∨ y = 3 ∨ y = 4) := by
  revert x y
  decide

lemma hub_adj_leaf {b : Vtx m} (h : (G m).Adj none b) :
    ∃ (L : LIdx m) (z : Pos), b = some (Sum.inr L, z) := by
  cases b with
  | none => exact absurd h (fun hh => hh.elim)
  | some p =>
      obtain ⟨B, y⟩ := p
      cases B with
      | inr L => exact ⟨L, y, rfl⟩
      | inl S =>
          exfalso
          have hx : ext (Sum.inl S, y) = none := h
          rw [ext_inl, extS] at hx
          split_ifs at hx

/-- Every chord of a cycle lies in `locEdges L` for a leaf block `L` containing a
cycle-neighbour of the hub. -/
theorem chord_mem_locEdges (hc : c.IsCycle) {a b : Vtx m} (he : c.IsChord s(a, b)) :
    ∃ L : LIdx m, (∃ z : Pos, some (Sum.inr L, z) ∈ c.toSubgraph.neighborSet none) ∧
      s(a, b) ∈ locEdges L := by
  have he' := he
  rw [SimpleGraph.Walk.isChord_sym2Mk] at he'
  obtain ⟨hadj, hne, ha, hb⟩ := he'
  match a, b with
  | none, b =>
      obtain ⟨L, z, rfl⟩ := hub_adj_leaf hadj
      refine ⟨L, leaf_has_hub_nbr hc L hb ha, ?_⟩
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨z, Finset.mem_univ _, rfl⟩)
  | some p, none =>
      obtain ⟨L, z, hz⟩ := hub_adj_leaf hadj.symm
      refine ⟨L, leaf_has_hub_nbr hc L (hz ▸ ha) hb, ?_⟩
      rw [Sym2.eq_swap, hz]
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨z, Finset.mem_univ _, rfl⟩)
  | some p, some q =>
      have hsame : q.1 = p.1 := by
        by_contra hc2
        exact interblock_not_chord hc (ext_eq_of_adj_other_block hadj hc2) he
      obtain ⟨B0, x⟩ := p
      obtain ⟨B, y⟩ := q
      simp only at hsame
      subst hsame
      have hpa : PosAdj x y := by
        rcases (adj_some_iff (B, x) (some (B, y))).1 hadj with h | h | h
        · have hy : y = x + 1 := congrArg Prod.snd (Option.some.inj h)
          rw [hy]
          exact (posAdj_iff _ _).2 (Or.inl rfl)
        · have hy : y = x + 1 + 1 + 1 + 1 := congrArg Prod.snd (Option.some.inj h)
          rw [hy]
          exact (posAdj_iff _ _).2 (Or.inr rfl)
        · exact absurd rfl (ext_block_ne (p := (B, x)) (q := (B, y)) h.symm)
      have hswap : c.IsChord s((some (B, y) : Vtx m), some (B, x)) := by
        rw [Sym2.eq_swap]; exact he
      have key : ∃ L : LIdx m,
          (∃ z : Pos, some (Sum.inr L, z) ∈ c.toSubgraph.neighborSet none) ∧
          (B = Sum.inr L ∨ B = Sum.inl ⟨L.1.1, L.2.1⟩) := by
        cases B with
        | inr L =>
            by_cases hx : x = L.1.2
            · refine pent_chord_aux hc hswap (Or.inl ⟨L, rfl, ?_⟩)
              rw [← hx]
              exact (posAdj_ne hpa).symm
            · exact pent_chord_aux hc he (Or.inl ⟨L, rfl, hx⟩)
        | inl S =>
            rcases posAdj_leafSlot hpa with h | h
            · exact pent_chord_aux hc he (Or.inr ⟨S, rfl, leafOK_of_mem h⟩)
            · exact pent_chord_aux hc hswap (Or.inr ⟨S, rfl, leafOK_of_mem h⟩)
      obtain ⟨L, hL, hB⟩ := key
      refine ⟨L, hL, ?_⟩
      rcases hB with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_pentEdges _ hpa))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_pentEdges _ hpa))

/-- **Every cycle of `G m` carries at most `30` chords.** -/
theorem chord_card_le (hc : c.IsCycle) (t : Finset (Sym2 (Vtx m)))
    (ht : ∀ e ∈ t, c.IsChord e) : t.card ≤ 30 := by
  by_cases hhub : (none : Vtx m) ∈ c.support
  · have hN : (c.toSubgraph.neighborSet none).ncard = 2 :=
      hc.ncard_neighborSet_toSubgraph_eq_two hhub
    obtain ⟨u1, u2, -, hNeq⟩ := Set.ncard_eq_two.1 hN
    have hmem1 : u1 ∈ c.toSubgraph.neighborSet none := by rw [hNeq]; exact Or.inl rfl
    have hmem2 : u2 ∈ c.toSubgraph.neighborSet none := by rw [hNeq]; exact Or.inr rfl
    obtain ⟨L1, z1, hu1⟩ := hub_adj_leaf (c.toSubgraph.adj_sub hmem1)
    obtain ⟨L2, z2, hu2⟩ := hub_adj_leaf (c.toSubgraph.adj_sub hmem2)
    have key : ∀ (a b : Vtx m), c.IsChord s(a, b) → s(a, b) ∈ locEdges L1 ∪ locEdges L2 := by
      intro a b hab
      obtain ⟨L, ⟨z, hz⟩, hmem⟩ := chord_mem_locEdges hc hab
      rw [hNeq] at hz
      rcases hz with h | h
      · have : L = L1 := by
          rw [hu1] at h
          have h1 : (Sum.inr L : Blk m) = Sum.inr L1 := congrArg Prod.fst (Option.some.inj h)
          exact Sum.inr.inj h1
        rw [this] at hmem
        exact Finset.mem_union_left _ hmem
      · have : L = L2 := by
          rw [hu2] at h
          have h1 : (Sum.inr L : Blk m) = Sum.inr L2 := congrArg Prod.fst (Option.some.inj h)
          exact Sum.inr.inj h1
        rw [this] at hmem
        exact Finset.mem_union_right _ hmem
    have hsub : t ⊆ locEdges L1 ∪ locEdges L2 := by
      intro e het
      revert het
      induction e using Sym2.ind with
      | _ a b => exact fun het => key a b (ht _ het)
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := card_locEdges L1
    have h2 := card_locEdges L2
    omega
  · have : t = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun e het => ?_)
      revert het
      induction e using Sym2.ind with
      | _ a b =>
          intro het
          obtain ⟨L, ⟨z, hz⟩, -⟩ := chord_mem_locEdges hc (ht _ het)
          exact hhub (c.fst_mem_support_of_mem_edges
            (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.1 hz))
    rw [this]
    simp

/-- A vertex set of size at most `r ≤ m` cannot be everything. -/
lemma exists_outside {r : ℕ} (hr : r ≤ m) (s : Finset (Vtx m)) (hs : s.card ≤ r) :
    ∃ w : Vtx m, w ∉ s := by
  by_contra hcon
  push Not at hcon
  set f : Fin (m + 1) → Vtx m :=
    fun i => some (Sum.inl (⟨i.1, Nat.lt_succ_iff.1 i.2⟩ : SIdx m), 0) with hf
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : (⟨i.1, Nat.lt_succ_iff.1 i.2⟩ : SIdx m) = ⟨j.1, Nat.lt_succ_iff.1 j.2⟩ :=
      Sum.inl.inj (congrArg Prod.fst (Option.some.inj hij))
    exact Fin.ext (congrArg Subtype.val h1)
  have hsub : (Finset.univ : Finset (Fin (m + 1))).image f ⊆ s := fun x _ => hcon x
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- The induced subgraph on a small vertex set is `3`-colourable. -/
lemma induce_colorable_three {r : ℕ} (hr : r ≤ m) (s : Finset (Vtx m)) (hs : s.card ≤ r) :
    ((G m).induce (↑s : Set (Vtx m))).Colorable 3 := by
  obtain ⟨w, hw⟩ := exists_outside hr s hs
  obtain ⟨col, hcol⟩ := partial_colourable w s.card s le_rfl hw
  exact ⟨SimpleGraph.Coloring.mk (fun x => col x.1)
    (fun {x y} hxy => hcol x.1 x.2 y.1 y.2 hxy)⟩

/-- **Erdős problem 1091, second question: the answer is negative.**

Erdős asks two things in #1091.  The first — must every `K₄`-free graph of chromatic
number `4` contain an odd cycle with at least two chords? — was answered affirmatively by
Voss; it is *not* treated here.  The second asks whether there is `f(r) → ∞` such that
every `4`-chromatic graph all of whose subgraphs on at most `r` vertices are
`3`-colourable contains an odd cycle with at least `f(r)` chords.

This theorem refutes the second question: for every `r` there is a *finite* graph `H` with
`χ(H) = 4`, all of whose subgraphs on at most `r` vertices are `3`-colourable, in which
every cycle — in particular every odd cycle — carries at most `30` chords. -/
theorem erdos_1091 (r : ℕ) :
    ∃ (V : Type) (H : SimpleGraph V), Finite V ∧
      ¬ H.Colorable 3 ∧ H.Colorable 4 ∧ H.chromaticNumber = 4 ∧
      (∀ s : Finset V, s.card ≤ r → (H.induce (↑s : Set V)).Colorable 3) ∧
      (∀ (x : V) (cyc : H.Walk x x), cyc.IsCycle →
          ∀ t : Finset (Sym2 V), (∀ e ∈ t, cyc.IsChord e) → t.card ≤ 30) := by
  have h3 : ¬ (G (max r 1)).Colorable 3 := not_colorable_three _ (le_max_right _ _)
  have h4 : (G (max r 1)).Colorable 4 := colorable_four _
  have hchi : (G (max r 1)).chromaticNumber = 4 := by
    have h : (G (max r 1)).chromaticNumber = ((3 : ℕ) : ℕ∞) + 1 :=
      SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.2 ⟨h4, h3⟩
    rw [h]
    rfl
  exact ⟨Vtx (max r 1), G (max r 1), inferInstance, h3, h4, hchi,
    fun s hs => induce_colorable_three (le_max_left _ _) s hs,
    fun x cyc hcyc t ht => chord_card_le hcyc t ht⟩

/-- The same statement in refutation form: for every `r` and every threshold `K > 30`
there is a finite `4`-chromatic graph whose `r`-vertex subgraphs are `3`-colourable and
which has **no** cycle at all carrying `K` chords. -/
theorem erdos_1091_no_bound (r K : ℕ) (hK : 30 < K) :
    ∃ (V : Type) (H : SimpleGraph V), Finite V ∧
      ¬ H.Colorable 3 ∧ H.Colorable 4 ∧ H.chromaticNumber = 4 ∧
      (∀ s : Finset V, s.card ≤ r → (H.induce (↑s : Set V)).Colorable 3) ∧
      (∀ (x : V) (cyc : H.Walk x x), cyc.IsCycle →
          ¬ ∃ t : Finset (Sym2 V), (∀ e ∈ t, cyc.IsChord e) ∧ K ≤ t.card) := by
  obtain ⟨V, H, hfin, h3, h4, hchi, hsmall, hchord⟩ := erdos_1091 r
  refine ⟨V, H, hfin, h3, h4, hchi, hsmall, ?_⟩
  rintro x cyc hcyc ⟨t, ht, hcard⟩
  have := hchord x cyc hcyc t ht
  omega

/-- **No function tending to infinity can serve as `f`.**  For every `f` with
`f r → ∞` there is an `r` and a finite `4`-chromatic graph whose `r`-vertex subgraphs are
`3`-colourable and which has no cycle — in particular no odd cycle — with `f r` chords. -/
theorem erdos_1091_negation (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ (r : ℕ) (V : Type) (H : SimpleGraph V), Finite V ∧
      ¬ H.Colorable 3 ∧ H.Colorable 4 ∧ H.chromaticNumber = 4 ∧
      (∀ s : Finset V, s.card ≤ r → (H.induce (↑s : Set V)).Colorable 3) ∧
      (∀ (x : V) (cyc : H.Walk x x), cyc.IsCycle →
          ¬ ∃ t : Finset (Sym2 V), (∀ e ∈ t, cyc.IsChord e) ∧ f r ≤ t.card) := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.1 hf 31
  obtain ⟨V, H, hfin, h3, h4, hchi, hsmall, hchord⟩ := erdos_1091 N
  refine ⟨N, V, H, hfin, h3, h4, hchi, hsmall, ?_⟩
  rintro x cyc hcyc ⟨t, ht, hcard⟩
  have h1 := hchord x cyc hcyc t ht
  have h2 := hN N le_rfl
  omega

end JSP907
