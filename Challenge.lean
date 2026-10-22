/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Mader's theorem on highly connected subgraphs

* `MaderTheorem.mader`: **Mader (1972).** Let `k ≥ 1`. Every nonempty finite simple graph `G` of
  average
  degree `d(G) = 2 e(G) / |G|` at least `4k` has a `(k + 1)`-connected (induced) subgraph `H` with
  `e(H) / |H| > e(G) / |G| − k`.

This is the form of Diestel, *Graph Theory*, Theorem 1.4.3. A graph is `k`-connected if it has more
than `k` vertices and stays connected after the deletion of any set of fewer than `k` vertices
(`MaderTheorem.IsKConnected`, the same definition as in the Menger–Hamiltonicity entry). Since
adding edges
preserves `k`-connectivity and can only increase `e(H)`, stating the result for induced subgraphs
`G.induce S` is equivalent to stating it for arbitrary subgraphs.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph

namespace MaderTheorem

variable {V : Type*}

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after the deletion of
any set of fewer than `k` vertices. -/
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected

/-- **Mader (1972)**, in the form of Diestel's Theorem 1.4.3. -/
theorem mader [Fintype V] [Nonempty V] (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hd : 4 * k * Fintype.card V ≤ 2 * G.edgeSet.ncard) :
    ∃ S : Finset V, IsKConnected (G.induce (S : Set V)) (k + 1) ∧
      (G.edgeSet.ncard : ℝ) / Fintype.card V - k <
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) / S.card := by
  sorry

end MaderTheorem
