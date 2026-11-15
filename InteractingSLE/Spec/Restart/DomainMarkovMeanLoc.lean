/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovMean
import InteractingSLE.Spec.Restart.DomainMarkovLocP

/-!
# K2's input (L) in a chart: the later-line marked locality read through the retained chart

Packet PROVE-DOMAINMARKOV6. Input (L) of K2 is `K2.HasSafeMembers`: at every deterministic capacity time `s` of the
continuation, on every event of the continuation filtration on which `s` is before the lifetime and the continuation
hull `K̃_s` avoids a finite union of rational closed balls, the Dirichlet directions of those balls enter the
characteristic functional of the field with the Gaussian factor of the projection (`projFactor`).

For the field `X = chartTransport c 1 a k h` read through a retained chart `c`, this follows from the **history-marked
local-set property** of the physical later-line union `B_s` (Aux. lemma 77; S2's `isHistoryAvoidanceLocal_ruleKHist`)
with marks `ℋ_s ⊇ 𝓗_s`, as soon as `ℍ ∖ B_s = inv(ℍ ∖ K̃_s)` on the live event: LocalExtO's conditional decomposition
through a random chart (`LocalExt.exists_condDecomp_chart`) and Lemma 7.2's member identity from a kernel
(`Lemma72D.setIntegral_lapTest_of_kernel`), as in PROVE-DOMAINMARKOV3's restart instance
(`setIntegral_lapTest_restart_piece`), with the restart chart replaced by any measurable conformal chart with harmonic
lifts.

* `relHull`: the continuation hull `K̃_s` where the driver is regular and `s` is before the lifetime, `∅` otherwise
  (relatively closed for every `ω`);
* **`hasSafeMembers_chartTransport`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.Mean

open Coupling K2 LocalSets WholeField

section Loc

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open Classical in
/-- The continuation hull `K̃_s` where the driver is regular and `s` is before the lifetime; `∅` otherwise. -/
def relHull (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω) : Set ℂ :=
  if IsDrvReg W ζ ω ∧ (s : ℝ≥0∞) < ζ ω then fwdHull (fun r : ℝ => W r.toNNReal ω) s else ∅

omit mΩ in
theorem relHull_relClosed (s : ℝ≥0) (ω : Ω) : relHull W ζ s ω ⊆ H ∧ IsOpen (H \ relHull W ζ s ω) := by
  unfold relHull
  split_ifs with hω
  · exact LocalExt.fwdHull_relClosed_of_continuousOn hω.1.1 hω.2
  · refine ⟨empty_subset _, ?_⟩
    rw [sdiff_empty]
    exact QuantumZipper.isOpen_H

omit mΩ in
theorem relHull_eq {s : ℝ≥0} {ω : Ω} (hreg : IsDrvReg W ζ ω) (hs : (s : ℝ≥0∞) < ζ ω) :
    relHull W ζ s ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s := by
  unfold relHull
  simp only [hreg, hs, and_self, ↓reduceIte]

/-- **K2's input (L) for a field read through a retained chart.** Let `h` be a measurable field whose centring
`h − u₀` is a zero-boundary GFF, `c` a conformal chart measurable for `𝒢 ≤ 𝓗_0` with continuous harmonic lifts, and
`X = chartTransport c 1 a k h`. Suppose that at every capacity time `s` of the continuation there are marks
`ℋ_s ⊇ 𝓗_s` and a hitting-measurable relatively closed random set `B_s` (the physical later-line union) which is a
history-marked local set of `h − u₀` for the marks `ℋ_s` (Aux. lemma 77), with `ℍ ∖ B_s = inv(ℍ ∖ K̃_s)` almost
surely on `F ∩ {s < ζ}`, and that the driver is regular on `F`. Then `HasSafeMembers P 𝓗 F ζ W X`. -/
theorem hasSafeMembers_chartTransport {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω} (h𝒢𝓗 : 𝒢 ≤ 𝓗 0)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓗ℋ : ∀ s, 𝓗 s ≤ ℋ s) (hℋ : ∀ s, ℋ s ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ s, Measurable[mΩ, hittingSigma] (B s))
    (hBc : ∀ s ω, B s ω ⊆ H ∧ IsOpen (H \ B s ω))
    (hloc : ∀ s, IsHistoryAvoidanceLocal (ℋ s) (B s) (centredField h u₀) P)
    (hBK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (s : ℝ≥0∞) < ζ ω →
      H \ B s ω = (c ω).2.1 '' (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) s))
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsDrvReg W ζ ω) :
    HasSafeMembers P 𝓗 F ζ W fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  intro s Fb hFH D hD hDs f Ξ
  have h𝒢ℋ : 𝒢 ≤ ℋ s := h𝒢𝓗.trans ((𝓗.mono (zero_le (a := s))).trans (h𝓗ℋ s))
  have hDℋ : MeasurableSet[ℋ s] D := h𝓗ℋ s _ hD
  have hDm : MeasurableSet D := hℋ s _ hDℋ
  by_cases hPD : P D = 0
  · rw [setIntegral_measure_zero _ hPD, setIntegral_measure_zero _ hPD, mul_zero]
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hDac : P[|D] ≪ P := cond_absolutelyContinuous
  have hDae : ∀ᵐ ω ∂(P[|D]), ω ∈ D := ae_cond_mem hDm
  -- the chart relation under `P[· | D]`
  have hBK' : ∀ᵐ ω ∂(P[|D]), H \ B s ω = (c ω).2.1 '' (H \ relHull W ζ s ω) := by
    filter_upwards [hDae, hDac.ae_le hDs, hDac.ae_le (hBK s), hDac.ae_le hreg] with ω hωD h1 h2 h3
    obtain ⟨hωF, hsζ, -⟩ := h1 hωD
    rw [relHull_eq (h3 hωF) hsζ]
    exact h2 hωF hsζ
  obtain ⟨M, hMm, hMharm, hMcond⟩ := LocalExt.exists_condDecomp_chart (P := P) hhm hu₀ hh0 hc
    (fun z => h𝒢ℋ _ (hdom z)) (fun z => (hfwd z).mono h𝒢ℋ le_rfl) (fun z => (hliftm z).mono h𝒢ℋ le_rfl)
    hliftc hlift (hℋ s) (hBm s) (hBc s) (hloc s) (relHull_relClosed (W := W) (ζ := ζ) s) hDℋ hPD hBK' a k
  have h𝒦 : germSigma (B s) (centredField h u₀) ⊔ ℋ s ≤ mΩ :=
    sup_le (germSigma_le (hBm s) (measurable_centredField hhm u₀)) (hℋ s)
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢ℋ.trans (hℋ s)
  have hXm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => h𝒢m _ (hdom z))
      (fun z => (hfwd z).mono h𝒢m le_rfl) (fun z => (hliftm z).mono h𝒢m le_rfl) hliftc hhm 1 a k
  have hker := fun χ => condExp_cexp_eq_rangeKerCF (Q := P[|D]) h𝒦 hXm hMm hMcond χ
  have hUH : ballsOpen Fb ≤ upperHalfPlaneOpens := fun z hz => hFH (ballsU_subset_ballsK Fb hz)
  have hD𝒦 : MeasurableSet[germSigma (B s) (centredField h u₀) ⊔ ℋ s] D :=
    (le_sup_right : ℋ s ≤ _) _ hDℋ
  have hDV : ∀ᵐ ω ∂(P[|D]), ω ∈ D → IsOpen (H \ relHull W ζ s ω) ∧ H \ relHull W ζ s ω ⊆ H ∧
      ((ballsOpen Fb : Set ℂ) ⊆ H \ relHull W ζ s ω) ∧ IsHarmonicDistOn (M ω) (H \ relHull W ζ s ω) := by
    filter_upwards [hMharm, hDac.ae_le hDs, hDac.ae_le hreg] with ω hM h1 h3 hωD
    obtain ⟨hωF, hsζ, hdisj⟩ := h1 hωD
    refine ⟨(relHull_relClosed s ω).2, sdiff_subset, fun z hz => ⟨hFH (ballsU_subset_ballsK Fb hz), fun hzK => ?_⟩,
      hM⟩
    rw [relHull_eq (h3 hωF) hsζ] at hzK
    exact Set.disjoint_left.1 hdisj (ballsU_subset_ballsK Fb hz) hzK
  have key := Sec7.Lemma72D.setIntegral_lapTest_of_kernel (P := P[|D]) h𝒦 hXm hker hUH hD𝒦 hDV f Ξ
  rw [setIntegral_cond_of_subset' hDm subset_rfl, setIntegral_cond_of_subset' hDm subset_rfl,
    mul_smul_comm] at key
  have hne : (P D)⁻¹.toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top _ _), ENNReal.inv_ne_top.2 hPD⟩
  exact smul_right_injective ℂ hne key

end Loc

end InteractingSLE.Restart.DomainMarkov.Mean
