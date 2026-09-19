/-
Copyright (c) 2026 qkkqk1234. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: qkkqk1234
-/
import Mathlib

/-!
# A cut-parity lemma for walks

For a two-valued function `f` on the vertices, a walk from `x` to `y` uses an odd number
of "crossing" darts exactly when `f x ≠ f y`.  In particular a closed walk uses an even
number of crossing darts, and a walk using none is constant on `f`.
-/

namespace JSP907

variable {V : Type*} {H : SimpleGraph V}

/-- The crossing predicate on darts. -/
def Crosses (f : V → Bool) (d : H.Dart) : Bool := f d.fst != f d.snd

lemma countP_crosses_parity (f : V → Bool) :
    ∀ {x y : V} (w : H.Walk x y),
      (w.darts.countP (Crosses f)) % 2 = (if f x = f y then 0 else 1) := by
  intro x y w
  induction w with
  | nil => simp
  | @cons u v w' h p ih =>
      rw [SimpleGraph.Walk.darts_cons, List.countP_cons]
      have hc : (Crosses f ⟨(u, v), h⟩) = (f u != f v) := rfl
      rw [hc]
      cases hu : f u <;> cases hv : f v <;> cases hw : f w' <;>
        simp_all <;> omega

lemma cycle_countP_crosses_even {x : V} (w : H.Walk x x) (f : V → Bool) :
    (w.darts.countP (Crosses f)) % 2 = 0 := by
  rw [countP_crosses_parity f w]
  simp

lemma const_of_no_cross {x y : V} (w : H.Walk x y) (f : V → Bool)
    (h : w.darts.countP (Crosses f) = 0) : f x = f y := by
  have := countP_crosses_parity f w
  rw [h] at this
  by_cases hf : f x = f y
  · exact hf
  · rw [ite_eq_right hf] at this
    omega

end JSP907

namespace JSP907

variable {V : Type*} [DecidableEq V] {H : SimpleGraph V}

/-- In a trail each edge is used by at most one dart. -/
lemma trail_countP_edge_le_one {x y : V} {w : H.Walk x y} (hw : w.IsTrail) (e : Sym2 V) :
    w.darts.countP (fun d => d.edge == e) ≤ 1 := by
  have h1 : w.edges.count e = w.darts.countP (fun d => d.edge == e) := by
    have : w.edges = w.darts.map SimpleGraph.Dart.edge := rfl
    rw [this, List.count_eq_countP, List.countP_map]
    rfl
  rw [← h1]
  exact List.nodup_iff_count_le_one.1 hw.edges_nodup e

omit [DecidableEq V] in
lemma mem_edges_of_mem_darts {x y : V} {w : H.Walk x y} {d : H.Dart} (h : d ∈ w.darts) :
    d.edge ∈ w.edges := by
  have : w.edges = w.darts.map SimpleGraph.Dart.edge := rfl
  rw [this]
  exact List.mem_map_of_mem h

end JSP907
