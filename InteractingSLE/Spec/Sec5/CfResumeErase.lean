/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeZeroStrip

/-!
# Ordered erasure of passive marks

Packet PROVE-CFCHART2, continuation. Every finite weight list has an ordered sublist
retaining its seed and exactly its nonzero nonseed weights. The all-extension chart
clause survives this erasure, by the already proved canonical-clause adapter.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfResume

open CfGiven CfChart CfConv

/-- Keep the seed and all nonzero weights in their original order. No retained nonseed
weight vanishes, and every omitted weight vanishes. -/
theorem exists_ordered_zero_erasure {n : ℕ} (ρ : Fin (n + 1) → ℝ) :
    ∃ (k : ℕ) (e : Fin (k + 1) ↪o Fin (n + 1)), e 0 = 0 ∧
      (∀ i, i ≠ 0 → ρ (e i) ≠ 0) ∧ ∀ j, j ∉ range e → ρ j = 0 := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun j => j = 0 ∨ ρ j ≠ 0
  have h0 : (0 : Fin (n + 1)) ∈ S :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Finset.card_pos.2 ⟨0, h0⟩))
  let e : Fin (k + 1) ↪o Fin (n + 1) := S.orderEmbOfFin hk
  have hr : range e = (S : Set (Fin (n + 1))) := Finset.range_orderEmbOfFin S hk
  have he0 : e 0 = 0 := by
    obtain ⟨i, hi⟩ : (0 : Fin (n + 1)) ∈ range e := by rw [hr]; exact h0
    apply le_antisymm
    · calc
        e 0 ≤ e i := e.monotone (Fin.zero_le i)
        _ = 0 := hi
    · exact Fin.zero_le _
  refine ⟨k, e, he0, ?_, ?_⟩
  · intro i hi
    have hm : e i ∈ S := Finset.orderEmbOfFin_mem S hk i
    rcases (Finset.mem_filter.1 hm).2 with he | hn
    · exact False.elim (hi (e.injective (he.trans he0.symm)))
    · exact hn
  · intro j hj
    by_contra hn
    apply hj
    rw [hr]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr hn⟩

/-- Zero-weight erasure preserves the chart clause quantified over all harmonic
extensions, with exactly the same field, filtration, chart, driver and lifetime. -/
theorem chartConst_reindex_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {nL nR kL kR : ℕ} {κ a k : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {h : Ω → DistOn upperHalfPlaneOpens}
    (eL : Fin kL ↪ Fin nL) (eR : Fin kR ↪ Fin nR)
    (hL : ∀ j, j ∉ range eL → ρL j = 0) (hR : ∀ j, j ∉ range eR → ρR j = 0)
    (hc : ∀ ω, (c ω).IsConformal) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR ζ c a k h) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst κ (ρL ∘ eL) (ρR ∘ eR) P 𝓐 W
      (fun i => VL (eL i)) (fun j => VR (eR j)) ζ c a k h := by
  have hWr := fun ω => (hWc ω).comp continuous_real_toNNReal
  apply (isChartCouplingCharFunConst_iff_canon hc hWr).2
  exact CfConv.IsChartCanon.reindex_zero eL eR hL hR hc hWr
    ((isChartCouplingCharFunConst_iff_canon hc hWr).1 hchart)

end InteractingSLE.Sec5.CfResume
