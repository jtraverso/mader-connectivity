/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import MaderLib.MaderAux

/-!
# The main steps of the proof of Mader's theorem

We fix the doubled edge count `m = 2 e(G)` and `n = |G|`, and a vertex set `S` which is minimal
among the sets with `|S| ≥ 2k` and `m (|S| - k) < 2 e(G[S]) n` (i.e. `e(G[S]) > γ (|S| - k)` with
`γ = e(G)/|G|`).

* `Mader.stepA`: every vertex of `G[S]` has degree `> γ`.
* `Mader.no_split`: `S` cannot be split by a set `X` of at most `k` vertices.
* `Mader.induce_connected`: hence `G[S]` stays connected after deleting fewer than `k + 1`
  vertices.
-/

@[expose] public section

open SimpleGraph Finset

namespace Mader

variable {V : Type*} (G : SimpleGraph V)

theorem side_card [DecidableEq V] {S U X : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n) {x : V} (hxS : x ∈ S)
    (hnb : ∀ w ∈ S, G.Adj x w → w ∈ U ∪ X) : 2 * k < (U ∪ X).card := by
  have h1 := hdeg x hxS
  have h2 := ndeg_le_card G hnb
  have h3 : 2 * k * (2 * n) < ndeg G S x * (2 * n) := by
    calc 2 * k * (2 * n) = 4 * k * n := by ring
      _ ≤ m := hm
      _ < 2 * ndeg G S x * n := h1
      _ = ndeg G S x * (2 * n) := by ring
  have := Nat.lt_of_mul_lt_mul_right h3
  omega

theorem no_split [DecidableEq V] {S X U₁ U₂ : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n)
    (hX : X.card ≤ k) (hS : S = U₁ ∪ U₂ ∪ X) (h12 : Disjoint U₁ U₂) (h1X : Disjoint U₁ X)
    (h2X : Disjoint U₂ X) (hne1 : U₁.Nonempty) (hne2 : U₂.Nonempty)
    (hno : ∀ a ∈ U₁, ∀ b ∈ U₂, ¬ G.Adj a b) : False := by
  classical
  have hcS : S.card = U₁.card + U₂.card + X.card := by
    rw [hS, card_union_of_disjoint (disjoint_union_left.2 ⟨h1X, h2X⟩),
      card_union_of_disjoint h12]
  have hc1 : (U₁ ∪ X).card = U₁.card + X.card := card_union_of_disjoint h1X
  have hc2 : (U₂ ∪ X).card = U₂.card + X.card := card_union_of_disjoint h2X
  have hp1 : 0 < U₂.card := hne2.card_pos
  have hp2 : 0 < U₁.card := hne1.card_pos
  obtain ⟨x, hx⟩ := hne1
  obtain ⟨y, hy⟩ := hne2
  have hxS : x ∈ S := by rw [hS]; simp [hx]
  have hyS : y ∈ S := by rw [hS]; simp [hy]
  have hb1 : 2 * k < (U₁ ∪ X).card := side_card G hm hdeg hxS (by
    intro w hw hadj
    rw [hS] at hw
    simp only [mem_union] at hw ⊢
    rcases hw with (hw | hw) | hw
    · exact Or.inl hw
    · exact absurd hadj (hno x hx w hw)
    · exact Or.inr hw)
  have hb2 : 2 * k < (U₂ ∪ X).card := side_card G hm hdeg hyS (by
    intro w hw hadj
    rw [hS] at hw
    simp only [mem_union] at hw ⊢
    rcases hw with (hw | hw) | hw
    · exact absurd hadj.symm (hno w hw y hy)
    · exact Or.inl hw
    · exact Or.inr hw)
  have e1 := hmin (U₁ ∪ X) (by omega) (by omega)
  have e2 := hmin (U₂ ∪ X) (by omega) (by omega)
  have hcov := dbl_union_le G (S := S) (H₁ := U₁ ∪ X) (H₂ := U₂ ∪ X) (by
    intro a ha b hb hadj
    rw [hS] at ha hb
    simp only [mem_union] at ha hb ⊢
    rcases ha with (ha | ha) | ha <;> rcases hb with (hb | hb) | hb
    all_goals first
      | exact absurd hadj (hno a ha b hb)
      | exact absurd hadj.symm (hno b hb a ha)
      | tauto)
  rw [hc1] at e1
  rw [hc2] at e2
  have hcz : (S.card : ℤ) = U₁.card + U₂.card + X.card := by exact_mod_cast hcS
  have hXz : (X.card : ℤ) ≤ k := by exact_mod_cast hX
  have hcovz : (dbl G S : ℤ) * n ≤ ((dbl G (U₁ ∪ X) : ℤ) + dbl G (U₂ ∪ X)) * n := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcov) (by positivity)
  push_cast at e1 e2
  nlinarith [mul_le_mul_of_nonneg_left hXz (show (0 : ℤ) ≤ m by positivity)]

theorem stepA {S : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (h2k : 2 * k ≤ S.card)
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n) :
    ∀ v ∈ S, m < 2 * ndeg G S v * n := by
  classical
  intro v hv
  by_contra hcon
  push Not at hcon
  have hne : S.card ≠ 2 * k := by
    intro heq
    have hD := dbl_le G S
    rw [heq] at hD hP
    have hDz : (dbl G S : ℤ) ≤ 2 * k * (2 * k - 1) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp at hD; simp [hD]
      have : ((2 * k * (2 * k - 1) : ℕ) : ℤ) = 2 * k * (2 * k - 1) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; ring
      rw [← this]; exact_mod_cast hD
    have hmz : (4 * k * n : ℤ) ≤ m := by exact_mod_cast hm
    push_cast at hP
    have h1 := mul_le_mul_of_nonneg_right hDz (show (0 : ℤ) ≤ n by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmz (show (0 : ℤ) ≤ k by positivity)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k by positivity) (show (0 : ℤ) ≤ n by positivity)]
  have hpos := card_pos.2 ⟨v, hv⟩
  have hcard : (S.erase v).card = S.card - 1 := card_erase_of_mem hv
  have hle := hmin (S.erase v) (by rw [hcard]; omega) (by rw [hcard]; omega)
  rw [hcard] at hle
  have hE := dbl_erase G hv
  have hEz : (dbl G S : ℤ) * n ≤ (dbl G (S.erase v) : ℤ) * n + 2 * ndeg G S v * n := by
    have : (dbl G S : ℤ) ≤ dbl G (S.erase v) + 2 * ndeg G S v := by exact_mod_cast hE
    nlinarith
  have hcz : (2 * ndeg G S v * n : ℤ) ≤ m := by exact_mod_cast hcon
  push_cast [Nat.cast_sub (show 1 ≤ S.card by omega)] at hle
  linarith

theorem induce_connected {S : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hmin : ∀ S' : Finset V, S'.card < S.card → 2 * k ≤ S'.card →
       (dbl G S' : ℤ) * n ≤ (m : ℤ) * ((S'.card : ℤ) - k))
    (hP : (m : ℤ) * ((S.card : ℤ) - k) < (dbl G S : ℤ) * n)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n)
    (hbig : k + 1 < S.card) (T : Set (S : Set V)) (hT : T.ncard < k + 1) :
    ((G.induce (S : Set V)).induce Tᶜ).Connected := by
  classical
  set H := G.induce (S : Set V) with hH
  have hnonempty : Nonempty (Tᶜ : Set (S : Set V)) := by
    by_contra hcon
    rw [not_nonempty_iff, Set.isEmpty_coe_sort, Set.compl_empty_iff] at hcon
    rw [hcon, Set.ncard_univ, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hT
    omega
  rw [connected_iff]
  refine ⟨?_, hnonempty⟩
  by_contra hpre
  simp only [Preconnected, not_forall] at hpre
  obtain ⟨u, w, huw⟩ := hpre
  let X : Finset V := S.filter (fun v => ∃ h : v ∈ S, (⟨v, h⟩ : (S : Set V)) ∈ T)
  let U₁ : Finset V := S.filter (fun v => ∃ h : v ∈ S, ∃ h' : (⟨v, h⟩ : (S : Set V)) ∈ Tᶜ,
      (H.induce Tᶜ).Reachable u ⟨⟨v, h⟩, h'⟩)
  let U₂ : Finset V := (S \ X) \ U₁
  apply no_split G hm hmin hP hdeg (X := X) (U₁ := U₁) (U₂ := U₂)
  · have hXT : (X : Set V) = Subtype.val '' T := by
      ext v
      simp only [X, coe_filter, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨_, h, hT⟩
        exact ⟨⟨v, h⟩, hT, rfl⟩
      · rintro ⟨⟨v', hv'⟩, hT, rfl⟩
        exact ⟨hv', hv', hT⟩
    have h := Set.ncard_coe_finset X
    rw [hXT, Set.ncard_image_of_injective _ Subtype.val_injective] at h
    omega
  · ext v
    simp only [mem_union, U₂, mem_sdiff]
    constructor
    · intro hv
      by_cases h1 : v ∈ U₁
      · exact Or.inl (Or.inl h1)
      by_cases h2 : v ∈ X
      · exact Or.inr h2
      exact Or.inl (Or.inr ⟨⟨hv, h2⟩, h1⟩)
    · rintro ((h | h) | h)
      · exact (mem_filter.1 h).1
      · exact h.1.1
      · exact (mem_filter.1 h).1
  · exact disjoint_left.2 fun a h1 h2 => (mem_sdiff.1 h2).2 h1
  · refine disjoint_left.2 fun a h1 h2 => ?_
    obtain ⟨_, h, h', _⟩ := mem_filter.1 h1
    obtain ⟨_, h2', hT'⟩ := mem_filter.1 h2
    exact h' hT'
  · exact disjoint_left.2 fun a h1 h2 => (mem_sdiff.1 (mem_sdiff.1 h1).1).2 h2
  · exact ⟨u.1.1, mem_filter.2 ⟨u.1.2, u.1.2, u.2, Reachable.refl _⟩⟩
  · refine ⟨w.1.1, mem_sdiff.2 ⟨mem_sdiff.2 ⟨w.1.2, fun h => ?_⟩, fun h => ?_⟩⟩
    · obtain ⟨_, h2, hT'⟩ := mem_filter.1 h
      exact w.2 hT'
    · obtain ⟨_, h2, h', hr⟩ := mem_filter.1 h
      exact huw hr
  · intro a ha b hb hadj
    obtain ⟨_, haS, haT, hr⟩ := mem_filter.1 ha
    obtain ⟨hbSX, hbU⟩ := mem_sdiff.1 hb
    obtain ⟨hbS, hbX⟩ := mem_sdiff.1 hbSX
    have hbT : (⟨b, hbS⟩ : (S : Set V)) ∈ Tᶜ := fun h => hbX (mem_filter.2 ⟨hbS, hbS, h⟩)
    apply hbU
    refine mem_filter.2 ⟨hbS, hbS, hbT, hr.trans (Adj.reachable ?_)⟩
    simpa [hH] using hadj

end Mader
