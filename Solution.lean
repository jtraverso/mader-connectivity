/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MaderLib.Mader

/-!
# Proofs of the statements in `Challenge.lean`

The theorem is proved in `MaderLib/` (namespace `Mader`), with the definition stated identically
there, following Diestel's proof with all inequalities kept as integer statements. A set `S` of
minimum size with `|S| ≥ 2k` and `e(G[S]) > ε(G) (|S| − k)` is chosen; minimality gives minimum
degree `> ε(G)` in `G[S]` (`MaderSteps.stepA`), the density bound, and `(k + 1)`-connectivity,
since a separator of size at most `k` would split `S` into two smaller sets one of which violates
minimality (`MaderSteps.no_split`, `MaderSteps.induce_connected`).
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
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) / S.card :=
  Mader.mader G hk hd

end MaderTheorem
