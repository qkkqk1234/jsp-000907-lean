# Prior art — JSP-000907 / Erdős 1091

**This is not the first Lean formalization of this problem, and the earlier one is more
complete.**

A sorry-free Lean 4.33.0 development of Erdős problem 1091 exists at

* `plby/lean-proofs`, `src/latest/ErdosProblems/Erdos1091.lean` together with roughly
  twenty-five auxiliary modules under `src/latest/ErdosProblems/Erdos1091/` (Brooks, the
  Voss case analysis, …) and the shared modules
  `ErdosProblems/Erdos58/Critical.lean`, `ErdosProblems/Erdos127/CriticalClique.lean`
  and `ErdosProblems/Erdos744.lean`, at commit
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` (pushed 2026-09-15T20:59Z), formal author
  recorded as "OpenAI Codex".

That development is **strictly stronger** than this one. It proves

* **Voss's affirmative theorem** — the first question of #1091, which is not attempted
  here;
* the APSSV counterexample family on `Fin (20*m+31)` with `K₄`-freeness, the **sharp**
  chord bound `≤ 10`, and — for a `4`-critical spanning subgraph of that graph —
  `∀ H : G.Subgraph, H < ⊤ → H.coe.Colorable 3`;
* the refutation in the quantified form `¬ ∃ f, Tendsto f atTop atTop ∧ …`.

This submission proves the bound `≤ 30`, omits `K₄`-freeness, and omits Voss's theorem.

The development in this directory was written independently of it: the Lean sources and
the `tex` reconstruction in `plby/lean-proofs` were not read, and the mathematics was
taken from the published source, arXiv:2604.06609 §4. It differs in the vertex encoding
(a hub plus an indexed family of pentagon blocks rather than `Fin (20m+31)`), in the proof
of the chord bound (a cut-parity argument rather than an arc analysis), and in being
weaker as listed above.

**No priority is claimed.** Whether an independent, weaker second formalization has any
standing under this prize is for the maintainers to decide; the record should be accurate
rather than favourable.

## Status in the community databases

At the time of writing, `teorth/erdosproblems` (`data/problems.yaml`, snapshot
2026-09-09) records problem 1091 as `informal_status: solved`, `formal_status:
unformalized` — i.e. the `plby` development had not been ingested there. The awards
catalogue entry for JSP-000907 likewise records `Lean proof: No` and, consequently,
`Eligible to claim: No`. Neither of those should be read as a claim of priority for this
submission, and the `Eligible to claim` flag is a screening marker maintained by the
repository, not something this submission asserts anything about.
