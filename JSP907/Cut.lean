/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import JSP907.Cycle

/-!
# Cut arguments for cycles in `G m`
-/

namespace JSP907

open SimpleGraph

variable {m : ℕ} {v : Vtx m} {c : (G m).Walk v v}

/-- A two-valued function that does not change along `c` is constant on its support. -/
lemma const_on_support (f : Vtx m → Bool) (h : c.darts.countP (Crosses f) = 0)
    {x : Vtx m} (hx : x ∈ c.support) : f v = f x := by
  refine const_of_no_cross (c.takeUntil x hx) f ?_
  rw [List.countP_eq_zero]
  intro d hd
  have hd' : d ∈ c.darts := (c.darts_takeUntil_subset_darts hx) hd
  rw [List.countP_eq_zero] at h
  exact h d hd'

/-- If every crossing dart of `f` uses one fixed edge, `f` is constant on the cycle. -/
lemma cut_absurd' (hc : c.IsCycle) (f : Vtx m → Bool) (e : Sym2 (Vtx m))
    (hcross : ∀ d ∈ c.darts, Crosses f d = true → (d.edge == e) = true)
    {x y : Vtx m} (hx : x ∈ c.support) (hy : y ∈ c.support) (hxy : f x ≠ f y) : False := by
  have h1 : c.darts.countP (Crosses f) ≤ c.darts.countP (fun d => d.edge == e) :=
    List.countP_mono_left hcross
  have h2 := trail_countP_edge_le_one hc.isTrail e
  have h3 := cycle_countP_crosses_even c f
  have h4 : c.darts.countP (Crosses f) = 0 := by omega
  exact hxy ((const_on_support f h4 hx).symm.trans (const_on_support f h4 hy))

/-- If every crossing dart of `f` is incident to the hub, then `f` cannot separate two
non-hub vertices of the cycle. -/
lemma cut_absurd (hc : c.IsCycle) (f : Vtx m → Bool)
    (hcross : ∀ d ∈ c.darts, Crosses f d = true → (d.toProd.1 = none ∨ d.toProd.2 = none))
    {x y : Vtx m} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxne : x ≠ none) (hyne : y ≠ none) (hxy : f x ≠ f y) : False := by
  have hc' : (c.rotate x hx).IsCycle := (SimpleGraph.Walk.isCycle_rotate hx).2 hc
  have hy' : y ∈ (c.rotate x hx).support := (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  set c' := c.rotate x hx with hc'def
  set p := c'.takeUntil y hy' with hpdef
  set q := c'.dropUntil y hy' with hqdef
  have hsplit : p.append q = c' := c'.take_spec hy'
  have hdarts : p.darts ++ q.darts = c'.darts := by
    rw [← SimpleGraph.Walk.darts_append, hsplit]
  have hmemc : ∀ d ∈ c'.darts, d ∈ c.darts := fun d hd =>
    ((c.rotate_darts x hx).mem_iff).1 hd
  have hp : p.darts.countP (Crosses f) % 2 = 1 := by
    rw [countP_crosses_parity f p, ite_eq_right hxy]
  have hq : q.darts.countP (Crosses f) % 2 = 1 := by
    rw [countP_crosses_parity f q, ite_eq_right (fun h => hxy h.symm)]
  have hhub : ∀ (a b : Vtx m) (w : (G m).Walk a b),
      w.darts.countP (Crosses f) % 2 = 1 → (∀ d ∈ w.darts, d ∈ c.darts) →
      (none : Vtx m) ∈ w.support := by
    intro a b w hw hsub
    by_contra hcon
    have : w.darts.countP (Crosses f) = 0 := by
      rw [List.countP_eq_zero]
      intro d hd hcr
      rcases hcross d (hsub d hd) hcr with h | h
      · exact hcon (h ▸ w.dart_fst_mem_support_of_mem_darts hd)
      · exact hcon (h ▸ w.dart_snd_mem_support_of_mem_darts hd)
    omega
  have hnp : (none : Vtx m) ∈ p.support :=
    hhub _ _ p hp (fun d hd => hmemc d (hdarts ▸ List.mem_append_left _ hd))
  have hnq : (none : Vtx m) ∈ q.support :=
    hhub _ _ q hq (fun d hd => hmemc d (hdarts ▸ List.mem_append_right _ hd))
  have hnqt : (none : Vtx m) ∈ q.support.tail := by
    have hqs : (y : Vtx m) :: q.support.tail = q.support := SimpleGraph.Walk.cons_tail_support q
    rw [← hqs] at hnq
    rcases List.mem_cons.1 hnq with h | h
    · exact absurd h.symm hyne
    · exact h
  have hnpt : (none : Vtx m) ∈ p.support.tail := by
    have hps : (x : Vtx m) :: p.support.tail = p.support := SimpleGraph.Walk.cons_tail_support p
    rw [← hps] at hnp
    rcases List.mem_cons.1 hnp with h | h
    · exact absurd h.symm hxne
    · exact h
  have hsupp : c'.support = p.support ++ q.support.tail := by
    rw [← hsplit, SimpleGraph.Walk.support_append]
  have hps : (x : Vtx m) :: p.support.tail = p.support := SimpleGraph.Walk.cons_tail_support p
  have htail : c'.support.tail = p.support.tail ++ q.support.tail := by
    rw [hsupp, ← hps]
    rfl
  have hnodup : c'.support.tail.Nodup := hc'.support_nodup
  rw [htail] at hnodup
  exact (List.nodup_append.1 hnodup).2.2 none hnpt none hnqt rfl

end JSP907
