/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Auxiliary edge counting for Mader's theorem

`Mader.dbl G S` is the number of ordered pairs of adjacent vertices of `S`, i.e. twice the number
of edges of `G[S]`, and `Mader.ndeg G S v` is the number of neighbours of `v` inside `S`.
-/

@[expose] public section

open SimpleGraph Finset

namespace Mader

variable {V : Type*}

open Classical in
/-- Twice the number of edges of `G[S]`: the number of ordered adjacent pairs in `S`. -/
noncomputable def dbl (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card

open Classical in
/-- The number of neighbours of `v` inside `S`. -/
noncomputable def ndeg (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

variable (G : SimpleGraph V)

theorem dbl_eq_sum (S : Finset V) : dbl G S = ∑ v ∈ S, ndeg G S v := by
  classical
  unfold dbl ndeg
  rw [Finset.card_filter, Finset.sum_product]
  refine sum_congr rfl fun v _ => ?_
  rw [Finset.card_filter]

theorem ndeg_le {S : Finset V} {v : V} (hv : v ∈ S) : ndeg G S v ≤ S.card - 1 := by
  classical
  unfold ndeg
  rw [← Finset.card_erase_of_mem hv]
  apply card_le_card
  intro w
  simp only [mem_filter, mem_erase]
  intro ⟨hw, hadj⟩
  exact ⟨(G.ne_of_adj hadj).symm, hw⟩

theorem ndeg_le_card {S T : Finset V} {v : V} (h : ∀ w ∈ S, G.Adj v w → w ∈ T) :
    ndeg G S v ≤ T.card := by
  classical
  unfold ndeg
  apply card_le_card
  intro w hw
  rw [mem_filter] at hw
  exact h w hw.1 hw.2

theorem dbl_le (S : Finset V) : dbl G S ≤ S.card * (S.card - 1) := by
  classical
  rw [dbl_eq_sum]
  calc _ ≤ ∑ _v ∈ S, (S.card - 1) := sum_le_sum (fun v hv => ndeg_le G hv)
    _ = _ := by simp

open Classical in
theorem dbl_erase {S : Finset V} {v : V} (hv : v ∈ S) :
    dbl G S ≤ dbl G (S.erase v) + 2 * ndeg G S v := by
  classical
  have hsub : (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) ⊆
      ((S.erase v ×ˢ S.erase v).filter (fun p => G.Adj p.1 p.2) ∪
        (S.filter (G.Adj v)).image (fun w => (v, w))) ∪
        (S.filter (G.Adj v)).image (fun w => (w, v)) := by
    rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_product] at h
    simp only [mem_union, mem_filter, mem_product, mem_erase, mem_image, Prod.mk.injEq]
    by_cases ha : a = v
    · subst ha; left; right; exact ⟨b, ⟨h.1.2, h.2⟩, rfl, rfl⟩
    by_cases hb : b = v
    · subst hb; right; exact ⟨a, ⟨h.1.1, h.2.symm⟩, rfl, rfl⟩
    left; left; exact ⟨⟨⟨ha, h.1.1⟩, hb, h.1.2⟩, h.2⟩
  unfold dbl ndeg
  have h0 := card_le_card hsub
  have h1 := card_union_le (((S.erase v ×ˢ S.erase v).filter (fun p => G.Adj p.1 p.2) ∪
        (S.filter (G.Adj v)).image (fun w => (v, w))))
        ((S.filter (G.Adj v)).image (fun w => (w, v)))
  have h2 := card_union_le ((S.erase v ×ˢ S.erase v).filter (fun p => G.Adj p.1 p.2))
        ((S.filter (G.Adj v)).image (fun w => (v, w)))
  have h3 := card_image_le (s := S.filter (G.Adj v)) (f := fun w => (v, w))
  have h4 := card_image_le (s := S.filter (G.Adj v)) (f := fun w => (w, v))
  omega

theorem dbl_union_le {S H₁ H₂ : Finset V}
    (hcov : ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → (a ∈ H₁ ∧ b ∈ H₁) ∨ (a ∈ H₂ ∧ b ∈ H₂)) :
    dbl G S ≤ dbl G H₁ + dbl G H₂ := by
  classical
  unfold dbl
  refine (card_le_card ?_).trans (card_union_le _ _)
  rintro ⟨a, b⟩ h
  simp only [mem_filter, mem_product] at h
  simp only [mem_union, mem_filter, mem_product]
  rcases hcov a h.1.1 b h.1.2 h.2 with h' | h'
  · exact Or.inl ⟨h', h.2⟩
  · exact Or.inr ⟨h', h.2⟩

open Classical in
theorem two_mul_ncard_edgeSet {W : Type*} [Fintype W] (G' : SimpleGraph W) :
    2 * G'.edgeSet.ncard = ∑ v, G'.degree v := by
  classical
  rw [sum_degrees_eq_twice_card_edges, Set.ncard_eq_toFinset_card']
  rfl

open Classical in
theorem dbl_univ [Fintype V] : dbl G univ = 2 * G.edgeSet.ncard := by
  classical
  rw [two_mul_ncard_edgeSet, dbl_eq_sum]
  refine sum_congr rfl (fun v _ => ?_)
  unfold ndeg
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]

open Classical in
theorem dbl_induce (S : Finset V) :
    dbl G S = 2 * (G.induce (S : Set V)).edgeSet.ncard := by
  classical
  rw [two_mul_ncard_edgeSet, dbl_eq_sum, ← Finset.sum_finset_coe]
  refine sum_congr rfl (fun ⟨v, hv⟩ _ => ?_)
  unfold ndeg
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  refine Finset.card_bij (fun w hw => ⟨w, (mem_filter.1 hw).1⟩) ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, comap_adj, Function.Embedding.coe_subtype]
    exact (mem_filter.1 hw).2
  · intro a _ b _ h
    simpa using h
  · rintro ⟨w, hw⟩ h
    simp only [mem_filter, mem_univ, true_and, comap_adj, Function.Embedding.coe_subtype] at h
    exact ⟨w, mem_filter.2 ⟨hw, h⟩, rfl⟩

end Mader
