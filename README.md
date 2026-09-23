# JSP-000907 — Lean 4 formalization

**Problem.** JSP-000907 = Erdős problem [#1091](https://www.erdosproblems.com/1091),
recorded there as **two** questions:

> Let `G` be a `K₄`-free graph with chromatic number `4`. Must `G` contain an odd cycle
> with at least two diagonals?
>
> More generally, is there some `f(r) → ∞` such that every graph with chromatic number
> `4`, in which every subgraph on `≤ r` vertices has chromatic number `≤ 3`, contains an
> odd cycle with at least `f(r)` diagonals?

The **first** question was answered *affirmatively* by Voss (1982), building on Larson
(1979). The **second** was answered *negatively* in April 2026 by an explicit
construction, published as Alexeev, Putterman, Sawhney, Sellke and Valiant, *Short proofs
in combinatorics, probability and number theory II*,
[arXiv:2604.06609](https://arxiv.org/abs/2604.06609), §4 (the paper records the proof as
due to an internal model at OpenAI).

**What is formalized here: the second question only, in the negative.** Voss's theorem is
not formalized. See `STATEMENT.md`.

## Headline theorems (`JSP907/Main.lean`)

```lean
theorem erdos_1091 (r : ℕ) :
    ∃ (V : Type) (H : SimpleGraph V), Finite V ∧
      ¬ H.Colorable 3 ∧ H.Colorable 4 ∧ H.chromaticNumber = 4 ∧
      (∀ s : Finset V, s.card ≤ r → (H.induce (↑s : Set V)).Colorable 3) ∧
      (∀ (x : V) (cyc : H.Walk x x), cyc.IsCycle →
          ∀ t : Finset (Sym2 V), (∀ e ∈ t, cyc.IsChord e) → t.card ≤ 30)

theorem erdos_1091_negation (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ (r : ℕ) (V : Type) (H : SimpleGraph V), Finite V ∧
      ¬ H.Colorable 3 ∧ H.Colorable 4 ∧ H.chromaticNumber = 4 ∧
      (∀ s : Finset V, s.card ≤ r → (H.induce (↑s : Set V)).Colorable 3) ∧
      (∀ (x : V) (cyc : H.Walk x x), cyc.IsCycle →
          ¬ ∃ t : Finset (Sym2 V), (∀ e ∈ t, cyc.IsChord e) ∧ f r ≤ t.card)
```

`erdos_1091_negation` is the refutation proper: **no** `f` with `f r → ∞` satisfies the
second question. `erdos_1091_no_bound (r K) (hK : 30 < K)` is the intermediate form.

Cycles are mathlib's `Walk.IsCycle`; chords are mathlib's `Walk.IsChord` — an edge of the
ambient graph, not an edge of the walk, with both endpoints on the walk, which for a cycle
is exactly "joins two non-consecutive vertices". The chord bound is phrased as "every
finite set of chords has at most `30` elements", equivalent to a count and needing no
finiteness instance.

## The construction

`JSP907.G m` is the pentagon caterpillar of arXiv:2604.06609 §4.2:

| Piece | Description |
|---|---|
| spine blocks | `S_0, …, S_m`, each a `5`-cycle with slots `0,1,2,3,4` (the paper's `a,b,c,d,e`) |
| spine edges | `S_i[2] — S_{i+1}[0]` for `i < m` |
| leaf blocks | a `5`-cycle hung on spine slot `x` of `S_i` exactly when `LeafOK m i x`: always for `x ∈ {1,3,4}`, for `x = 0` only at `i = 0`, for `x = 2` only at `i = m` |
| attachment | `S_i[x] — L_{i,x}[x]` |
| hub | one extra vertex joined to every leaf-block vertex other than the attachment vertex |

Every vertex except the hub then has degree exactly `3`, and the two ends of the spine are
asymmetric — that asymmetry is what forces the fourth colour.

## Proof map

| File | Content |
|---|---|
| `Defs.lean` | vertex type, `ext` (the unique inter-block neighbour), the graph `G m`, finiteness |
| `Basic.lean` | the four edge types; the pentagon forcing lemma |
| `Colour.lean` | explicit proper `4`-colouring (`colorable_four`) |
| `NotThree.lean` | `not_colorable_three`: the hub forces every leaf attachment vertex to its own colour, which then propagates down the spine |
| `Connected.lean` | the hub-free part is connected, phrased as a closure principle |
| `Nbr.lean` | `ext` is an involution; the three neighbours of a non-hub vertex |
| `Degen.lean` | every proper vertex subset is `2`-degenerate, hence `3`-colourable |
| `Parity.lean` | a walk crosses a cut an odd number of times iff its two ends differ |
| `Cycle.lean` | local analysis at a vertex of a cycle: the three neighbours are distinct |
| `Cut.lean` | the two cut-contradiction lemmas `cut_absurd`, `cut_absurd'` |
| `Blocks.lean` | the cuts `inLeaf`, `inLeafHub`, `inHigh`, `inHighHub` and their crossing edges |
| `Chord.lean` | no inter-block edge is a chord; a pentagon chord pins down its block |
| `Main.lean` | every chord lies in `locEdges L` for a leaf block `L` **containing one of** the hub's two cycle-neighbours; the `30` bound; the headline theorems |

The constant `30` is `2 × (5 + 5 + 5)`: at most two such leaf blocks `L`, and for each,
the five pentagon edges of `L`, the five pentagon edges of the spine block carrying `L`,
and the five hub edges at `L`.

## Scope — what is *not* claimed

See `STATEMENT.md`. In short: the chord bound proved is **`30`**, not the sharper **`10`**
of the source paper; `K₄`-freeness of the construction is **not** formalized; and Voss's
affirmative answer to the first question of #1091 is **not** formalized. None of these
affects the refutation of the second question, which needs only a uniform constant.

## Other Lean work

See `PRIOR_ART.md`.

## Verification

```
bash scripts/verify.sh
```

Lean `v4.34.0`, mathlib `v4.34.0`. Every audited declaration depends on at most
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`, no custom
axiom. `scripts/verify.sh` fails if any audited declaration depends on anything outside
that list.
