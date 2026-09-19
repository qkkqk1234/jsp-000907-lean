# Statement fidelity — JSP-000907

## The problem as recorded

The awards catalogue records JSP-000907 as

> Must every four-chromatic graph contain an odd cycle with the prescribed number of
> chords?

with references `[La79]` (Larson), `[Vo82]` (Voss) and `[APSSV26b]`, status **Solved**,
`Lean proof: No`, `Eligible to claim: No`.

On erdosproblems.com this is problem **1091**, and it is stated there as **two**
questions, verbatim:

> Let `G` be a `K₄`-free graph with chromatic number `4`. Must `G` contain an odd cycle
> with at least two diagonals?
>
> More generally, is there some `f(r) → ∞` such that every graph with chromatic number
> `4`, in which every subgraph on `≤ r` vertices has chromatic number `≤ 3`, contains an
> odd cycle with at least `f(r)` diagonals?

| Question | Answer | Source |
|---|---|---|
| first (qualitative) | **yes** | H.-J. Voss, *Graphs having circuits with at least two chords*, J. Combin. Theory Ser. B **32** (1982), 264–285, after Larson (1979) |
| second (quantitative) | **no** | Alexeev–Putterman–Sawhney–Sellke–Valiant, [arXiv:2604.06609](https://arxiv.org/abs/2604.06609) §4 (2026); the paper records the proof as due to an internal model at OpenAI |

## What this submission proves

**Only the second question, in the negative.**

`JSP907.erdos_1091 (r : ℕ)` produces a graph `H` with

| Clause | Formal statement |
|---|---|
| finiteness | `Finite V` |
| `χ(H) = 4` | `¬ H.Colorable 3 ∧ H.Colorable 4 ∧ H.chromaticNumber = 4` |
| local `3`-colourability | `∀ s : Finset V, s.card ≤ r → (H.induce ↑s).Colorable 3` |
| bounded chords | every finite set of chords of every cycle has at most `30` elements |

`JSP907.erdos_1091_negation (f) (hf : Tendsto f atTop atTop)` turns this into the
refutation: for every such `f` there is an `r` and such a graph in which **no** cycle
carries `f r` chords. `JSP907.erdos_1091_no_bound (r K) (hK : 30 < K)` is the
intermediate form.

The graph is `JSP907.G (max r 1)`; it is the construction of arXiv:2604.06609 §4.2.

**Subgraph versus induced subgraph.** The question says "every subgraph on `≤ r`
vertices"; the formal clause says "every *induced* subgraph on `≤ r` vertices". These
agree: a subgraph on a vertex set `s` is contained in the induced subgraph on `s`, and
`3`-colourability passes to subgraphs (`SimpleGraph.Colorable.mono_left`). The induced
form is the stronger one.

## What is *not* proved here

1. **Voss's affirmative theorem** — the first question of #1091. Not formalized, and not
   needed for the refutation of the second.
2. **The sharp constant.** The source paper proves `≤ 10` chords per cycle; this
   development proves `≤ 30`. The looser constant comes from bounding the chords in each
   of the (at most four) relevant pentagon blocks by all five of its edges, and the hub
   chords at each of the (at most two) relevant leaf blocks by all five hub edges there,
   rather than running the paper's finer arc analysis. **The bound `10` is not claimed.**
3. **`K₄`-freeness.** The source construction is `K₄`-free; that is not formalized. The
   question quoted above does not require it.
4. **Full `4`-criticality.** What is formalized is that every subgraph on at most `r`
   vertices is `3`-colourable — exactly the hypothesis of the question — not that *every
   proper* subgraph is `3`-colourable. (The underlying degeneracy lemma,
   `JSP907.exists_low_degree`, does give the latter for proper *vertex* subsets; the
   packaging simply was not done.)
5. **The vertex count `20m+31`.** Not formalized; the vertex type carries the
   construction directly rather than through a bijection with `Fin (20m+31)`.

## Conventions

* Cycles are mathlib closed walks satisfying `SimpleGraph.Walk.IsCycle`.
* Chords use mathlib's `SimpleGraph.Walk.IsChord`: an edge of the ambient graph, not an
  edge of the walk, with both endpoints on the walk. For a cycle this is exactly "joins
  two non-consecutive vertices of the cycle".
* The chord bound is phrased as "every `Finset` of chords has at most `30` elements", so
  that no finiteness instance on `Sym2 V` is needed; it is equivalent to a cardinality
  bound on the set of chords.
