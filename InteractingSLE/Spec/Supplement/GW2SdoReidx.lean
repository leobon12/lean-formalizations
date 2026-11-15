/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Re-indexing countably many increasing families so that they are eventually good all at once

Packet PROVE-GW2-SDE (round 14; the near words (N1)–(N2)). The near word of the history `l` is read at the selected
candidate `a_m` (which changes with `m`), so the near slot of candidate `a` at index `m` must be alive at its stage
start for ALL candidates at once, eventually in `m`. Each candidate's own versions are alive eventually (they exhaust),
but not uniformly in the candidate. A deterministic re-indexing fixes this (Borel–Cantelli):

* **`exists_reindex_eventually_all`**: for countably many increasing families of measurable sets `E a k` (`k ↑`) under
  a finite measure there are monotone re-indexings `ψ a` with `ψ a m ≥ m` such that almost surely, eventually in `m`,
  every `a` whose family eventually contains the sample has `ω ∈ E a (ψ a m)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace InteractingSLE.Theorem14.GW2Sdo

/-- **Re-indexing countably many increasing families so that they are eventually good all at once.** -/
theorem exists_reindex_eventually_all {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (E : ℕ → ℕ → Set Ω) (hE : ∀ a k, MeasurableSet (E a k)) (hmono : ∀ a, Monotone (E a)) :
    ∃ ψ : ℕ → ℕ → ℕ, (∀ a, Monotone (ψ a)) ∧ (∀ a m, m ≤ ψ a m) ∧
      ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, ∀ a, (∃ k, ω ∈ E a k) → ω ∈ E a (ψ a m) := by
  classical
  set r : ℝ≥0∞ := 2⁻¹ with hr
  have hr0 : r ≠ 0 := by simp [hr]
  have hr1 : r < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  -- the bad parts: not yet good, but good later
  set F : ℕ → ℕ → Set Ω := fun a k => (E a k)ᶜ ∩ ⋃ k', E a k' with hF
  have hFm : ∀ a k, MeasurableSet (F a k) := fun a k =>
    (hE a k).compl.inter (MeasurableSet.iUnion fun k' => hE a k')
  have hFanti : ∀ a, Antitone (F a) := fun a k k' hkk' =>
    inter_subset_inter_left _ (compl_subset_compl.2 (hmono a hkk'))
  have hFinter : ∀ a, ⋂ k, F a k = ∅ := fun a => by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases h : ∃ k', ω ∈ E a k'
    · obtain ⟨k', hk'⟩ := h
      exact ⟨k', fun hF' => hF'.1 hk'⟩
    · exact ⟨0, fun hF' => h (mem_iUnion.1 hF'.2)⟩
  have htend : ∀ a, Tendsto (fun k => μ (F a k)) atTop (𝓝 0) := fun a => by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hFm a k).nullMeasurableSet) (hFanti a)
      ⟨0, measure_ne_top μ _⟩
    rwa [hFinter a, measure_empty] at this
  -- the chosen indices
  have hκ : ∀ a m, ∃ k, μ (F a k) ≤ r ^ m * r ^ a := fun a m => by
    have hpos : 0 < r ^ m * r ^ a := ENNReal.mul_pos (pow_ne_zero _ hr0) (pow_ne_zero _ hr0)
    obtain ⟨k, hk⟩ := ((tendsto_order.1 (htend a)).2 _ hpos).exists
    exact ⟨k, hk.le⟩
  choose κ hκ using hκ
  set ψ : ℕ → ℕ → ℕ := fun a m => m + ∑ j ∈ Finset.range (m + 1), κ a j with hψ
  have hψmono : ∀ a, Monotone (ψ a) := fun a m m' hmm' => by
    simp only [hψ]
    exact Nat.add_le_add hmm' (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hmm')))
  have hψκ : ∀ a m, κ a m ≤ ψ a m := fun a m =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (κ a j)) (Finset.mem_range.2 (Nat.lt_succ_self m))).trans
      (Nat.le_add_left _ _)
  refine ⟨ψ, hψmono, fun a m => Nat.le_add_right _ _, ?_⟩
  set G : ℕ → Set Ω := fun m => ⋃ a, F a (ψ a m) with hG
  have hGle : ∀ m, μ (G m) ≤ ∑' a, r ^ m * r ^ a := fun m =>
    (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun a =>
      (measure_mono (hFanti a (hψκ a m))).trans (hκ a m))
  have hsum : ∑' m, μ (G m) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' m, ∑' a, r ^ m * r ^ a) ?_ (ENNReal.tsum_le_tsum hGle)
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    have h1 : (1 - r)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne'
    exact ENNReal.mul_ne_top h1 h1
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with m hm a hgood
  by_contra hnot
  exact hm (mem_iUnion.2 ⟨a, hnot, mem_iUnion.2 hgood⟩)

end InteractingSLE.Theorem14.GW2Sdo
