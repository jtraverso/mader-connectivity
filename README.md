# Mader's theorem on highly connected subgraphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

`MaderTheorem.mader`, **Mader (1972)**, in the form of Diestel, *Graph Theory*, Theorem 1.4.3:
let `k ≥ 1`; every nonempty finite simple graph `G` of average degree `d(G) = 2e(G)/|G| ≥ 4k` has a
`(k + 1)`-connected induced subgraph `H = G[S]` with `e(H)/|H| > e(G)/|G| − k`.

A graph is `k`-connected (`MaderTheorem.IsKConnected`) if it has more than `k` vertices and stays
connected after the deletion of any set of fewer than `k` vertices; this is the same definition as
in the Menger–Hamiltonicity entry (PALOMAR-2026-10-15-000020). Adding edges preserves
`k`-connectivity and can only increase `e(H)`, so stating the result for induced subgraphs is
equivalent to stating it for arbitrary subgraphs. The definition is stated in `Challenge.lean`;
`comparator.json` selects only the theorem. Mathlib has connectivity but neither vertex
connectivity nor this theorem.

## Files

- [`Challenge.lean`](Challenge.lean): the definition and the audited statement. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean) and [`MaderLib/`](MaderLib): the proof.
- [`comparator.json`](comparator.json): the theorem that is compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proof goes

Let `γ = e(G)/|G| ≥ 2k` and choose `S` of minimum size with `|S| ≥ 2k` and `e(G[S]) > γ(|S| − k)`
(`S = V` qualifies). No set of size exactly `2k` qualifies, so deleting a vertex of degree `≤ γ`
from `S` would contradict minimality: `G[S]` has minimum degree `> γ`, hence more than `2k + 1`
vertices, and `e(G[S]) > (γ − k)|S|`. If at most `k` vertices separated `G[S]` into `U₁` and `U₂`,
the two smaller sets `U₁ ∪ X`, `U₂ ∪ X` would both satisfy `e ≤ γ(|·| − k)` by minimality, and
adding gives `e(G[S]) ≤ γ(|S| − k)`, a contradiction. The library keeps all inequalities as integer
statements (`MaderAux.lean`, `MaderSteps.lean`).

## Sources

* W. Mader, *Existenz n-fach zusammenhängender Teilgraphen in Graphen genügend großer
  Kantendichte*, Abh. Math. Sem. Univ. Hamburg 37 (1972) 86–97, doi:10.1007/BF02993903.
* R. Diestel, *Graph Theory*, Graduate Texts in Mathematics 173, Springer, Theorem 1.4.3.

## Authorship and use of AI

The author chose the result. The statement and proof plan were written with Claude in Claude Code;
the statement was checked on degenerate cases (it needs `V` nonempty). The proof was produced by
Harmonic's Aristotle in one run, then audited and rebuilt locally. Lean checks everything
mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
