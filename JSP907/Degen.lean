/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Nbr

/-!
# Proper subgraphs of `G m` are `2`-degenerate, hence `3`-colourable
-/

namespace JSP907

variable {m : ℕ}

/-- There is at least one leaf block. -/
lemma leafIdx_nonempty (m : ℕ) : Nonempty (LIdx m) :=
  ⟨⟨(0, 1), ⟨Nat.zero_le m, leafOK_of_mem (Or.inl rfl)⟩⟩⟩

lemma pos_succ_ne (y : Pos) : y + 1 ≠ y := by revert y; decide

/-- A nonempty set of vertices which is not everything contains a vertex with at most
two neighbours inside the set. -/
lemma exists_low_degree (s : Finset (Vtx m)) (hs : s.Nonempty) {w : Vtx m} (hw : w ∉ s) :
    ∃ u ∈ s, (s.filter fun v => (G m).Adj u v).card ≤ 2 := by
  by_cases hex : ∃ p : Blk m × Pos, some p ∈ s ∧ ∃ v, (G m).Adj (some p) v ∧ v ∉ s
  · obtain ⟨p, hp, v, hadj, hv⟩ := hex
    refine ⟨some p, hp, ?_⟩
    set F : Finset (Vtx m) :=
      {some (p.1, p.2 + 1), some (p.1, p.2 + 1 + 1 + 1 + 1), ext p} with hF
    have hmemF : ∀ x, (G m).Adj (some p) x → x ∈ F := by
      intro x hx
      rcases (adj_some_iff p x).1 hx with h | h | h <;> simp [hF, h]
    have hsub : (s.filter fun x => (G m).Adj (some p) x) ⊆ F.erase v := by
      intro x hx
      rw [Finset.mem_filter] at hx
      refine Finset.mem_erase.2 ⟨?_, hmemF x hx.2⟩
      rintro rfl
      exact hv hx.1
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_erase_of_mem (hmemF v hadj)]
    have hc3 : F.card ≤ 3 := by
      have h1 := Finset.card_insert_le (some (p.1, p.2 + 1))
        ({some (p.1, p.2 + 1 + 1 + 1 + 1), ext p} : Finset (Vtx m))
      have h2 := Finset.card_insert_le (some (p.1, p.2 + 1 + 1 + 1 + 1))
        ({ext p} : Finset (Vtx m))
      have h3 : ({ext p} : Finset (Vtx m)).card = 1 := Finset.card_singleton _
      rw [hF]
      omega
    omega
  · push Not at hex
    by_cases hp : ∃ p : Blk m × Pos, some p ∈ s
    · exfalso
      obtain ⟨p₀, hp₀⟩ := hp
      have hclosed : ∀ p : Blk m × Pos, some p ∈ (↑s : Set (Vtx m)) →
          ∀ v, (G m).Adj (some p) v → v ∈ (↑s : Set (Vtx m)) := by
        intro p hp v hv
        exact hex p hp v hv
      have hall : ∀ p : Blk m × Pos, some p ∈ (↑s : Set (Vtx m)) :=
        closure_all (↑s : Set (Vtx m)) hclosed (p₀ := p₀) hp₀
      obtain ⟨L⟩ := leafIdx_nonempty m
      have hleaf : some (Sum.inr L, L.1.2 + 1) ∈ s := hall _
      have hnone : (none : Vtx m) ∈ s :=
        hex _ hleaf none (adj_hub L (pos_succ_ne L.1.2)).symm
      refine hw ?_
      cases w with
      | none => exact hnone
      | some q => exact hall q
    · push Not at hp
      obtain ⟨u, hu⟩ := hs
      have hun : u = none := by
        cases u with
        | none => rfl
        | some q => exact absurd hu (hp q)
      subst hun
      refine ⟨none, hu, ?_⟩
      have : (s.filter fun v => (G m).Adj none v) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro x hx
        rw [Finset.mem_filter] at hx
        cases x with
        | none => exact ((G m).loopless.irrefl none) hx.2
        | some q => exact hp q hx.1
      rw [this]
      simp

/-- Any vertex set missing at least one vertex carries a proper `3`-colouring. -/
theorem partial_colourable (w : Vtx m) :
    ∀ (n : ℕ) (s : Finset (Vtx m)), s.card ≤ n → w ∉ s →
      ∃ c : Vtx m → Fin 3, ∀ u ∈ s, ∀ v ∈ s, (G m).Adj u v → c u ≠ c v := by
  intro n
  induction n with
  | zero =>
      intro s hs _
      have : s = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
      subst this
      exact ⟨fun _ => 0, by simp⟩
  | succ n ih =>
      intro s hs hw
      rcases s.eq_empty_or_nonempty with rfl | hne
      · exact ⟨fun _ => 0, by simp⟩
      obtain ⟨u, hu, hdeg⟩ := exists_low_degree s hne hw
      have hcard : (s.erase u).card ≤ n := by
        have := Finset.card_erase_of_mem hu
        omega
      obtain ⟨c', hc'⟩ := ih (s.erase u) hcard (fun h => hw (Finset.mem_of_mem_erase h))
      set N : Finset (Vtx m) := (s.erase u).filter fun v => (G m).Adj u v with hN
      have hNsub : N ⊆ s.filter fun v => (G m).Adj u v := by
        intro x hx
        rw [hN, Finset.mem_filter] at hx
        exact Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hx.1, hx.2⟩
      have hNcard : (N.image c').card ≤ 2 :=
        le_trans Finset.card_image_le (le_trans (Finset.card_le_card hNsub) hdeg)
      have hexa : ∃ a : Fin 3, a ∉ N.image c' := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset (Fin 3)) ⊆ N.image c' := fun a _ => hcon a
        have := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨a, ha⟩ := hexa
      refine ⟨Function.update c' u a, ?_⟩
      intro x hx y hy hadj
      by_cases hxu : x = u
      · subst hxu
        have hyu : y ≠ x := fun h => (G m).loopless.irrefl x (h ▸ hadj)
        have hyN : y ∈ N := by
          rw [hN]
          exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hyu, hy⟩, hadj⟩
        rw [Function.update_self, Function.update_of_ne hyu]
        intro hc
        exact ha (Finset.mem_image.2 ⟨y, hyN, hc.symm⟩)
      · by_cases hyu : y = u
        · subst hyu
          have hxy : x ≠ y := fun h => (G m).loopless.irrefl y (h ▸ hadj)
          have hxN : x ∈ N := by
            rw [hN]
            exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hxy, hx⟩, hadj.symm⟩
          rw [Function.update_self, Function.update_of_ne hxy]
          intro hc
          exact ha (Finset.mem_image.2 ⟨x, hxN, hc⟩)
        · rw [Function.update_of_ne hxu, Function.update_of_ne hyu]
          exact hc' x (Finset.mem_erase.2 ⟨hxu, hx⟩) y (Finset.mem_erase.2 ⟨hyu, hy⟩) hadj

end JSP907
