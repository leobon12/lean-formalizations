/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1GlueReduce

/-!
# Lemma 7.8's mean formula on `D` gives the chart identity

Packet PROVE-RESTART-CPL7, (R1) (c). Lemma 7.8 (p. 290) states the mean identification on the joint unbounded
component `D` as `𝒞_K = 𝔤 ∘ φ − χ arg φ′`, with `𝔤` the bounded harmonic extension of the chart datum. The glued (R1)
(`ae_condExp_cexp_chartField_eq_gaussCF_meetSet`) uses it in the chart: the chart transport of the conditional mean is
the word mean (`IsBoxMeanIdentification`). Here the first form gives the second:

* `chartTransport_eq_integral_of_eq_integral`: for a conformal chart with a continuous lift, a distribution equal on the
  chart domain to `G ∘ φ − k · lift` (`G` continuous on `ℍ`) is transported (`σ = 1`, `a = 0`, coefficient `k`) to `G`
  (the derivative-lift term cancels; the model is `Chart.chartTransport_loewner_couplingMean`);
* `IsBoxPointwiseMean`: Lemma 7.8's formula on every box, tested against the test functions supported in `D`;
* **`isBoxMeanIdentification_of_pointwise`**: a provider of `FirstContactWordKernelStatement` may establish the mean
  identification in Lemma 7.8's own (distributional) form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets

/-- **The chart transport of `G ∘ φ − k · lift` is `G`.** -/
theorem chartTransport_eq_integral_of_eq_integral {c : Chart} (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom)
    (k : ℝ) {T : DistOn upperHalfPlaneOpens} {G : ℂ → ℝ} (hG : ContinuousOn G H)
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.dom → T φ = ∫ z, (G (c.1 z) - k * c.2.2 z) * φ z)
    (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport hc 1 0 k T φ = ∫ w, G w * φ w := by
  have hℓc := hc.continuousOn_lift_inv hℓ
  rw [Chart.chartTransport_apply', ← Chart.pullField_apply, Chart.pullField_apply_of_eq_integral hc hT,
    Chart.liftDist_apply (Chart.locallyIntegrableOn_of_continuousOn hℓc)]
  have he : ∀ w, (G (c.1 (c.2.1 w)) - k * c.2.2 (c.2.1 w)) * φ w = G w * φ w - k * (c.2.2 (c.2.1 w) * φ w) :=
    fun w => by
      by_cases hw : w ∈ H
      · rw [hc.2.2 w hw]
        ring
      · have h0 : φ w = 0 := φ.zero_on_compl hw
        rw [h0]
        ring
  simp_rw [he]
  have hi₁ : Integrable fun w => G w * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (B := upperHalfPlaneOpens) hG φ
    simpa only [mul_comm] using this
  have hi₂ : Integrable fun w => c.2.2 (c.2.1 w) * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (B := upperHalfPlaneOpens) hℓc φ
    simpa only [mul_comm] using this
  rw [integral_sub hi₁ (hi₂.const_mul _), integral_const_mul]
  ring

section Pair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : PairData Ω}

/-- **Lemma 7.8's formula in the first-contact chart**: on the contact event, a distribution equal on `D` to
`𝔤 ∘ φ − χ arg φ′` (`𝔤` the word mean, `φ = d.fwd`, `arg φ′ = d.lift`) is transported to the word mean. -/
theorem chartTransport_chart_eq_integral_mean (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (κ : ℝ)
    {T : DistOn upperHalfPlaneOpens} {c : BoundaryWord}
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ d.D ω →
      T φ = ∫ z, (c.mean (d.fwd ω z) - QuantumZipper.chiC κ * d.lift ω z) * φ z)
    (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ) T φ = ∫ z, c.mean z * φ z := by
  refine chartTransport_eq_integral_of_eq_integral (hd.isConformal_chart ω) (hd.continuousOn_lift_chart ω) _
    (BoundaryWord.continuousOn_mean c) (fun ψ hψ => ?_) φ
  rw [hd.coe_dom_chart ω] at hψ
  rw [hT ψ hψ, PairData.chart_of_mem hE]

variable {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.8's mean formula on every box, in its own form** (`𝒞_K = 𝔤 ∘ φ − χ arg φ′` on `D`, p. 290): for every
cap `m`, every pair of capped versions and every version `g` of the conditional mean of the centred field given the
germs of their first-contact union, almost surely on the box `m`, for every test function supported in `D`, the
conditional mean `g + 𝔥₀` of the field paired with it is the pairing of `𝔤_β ∘ φ − χ arg φ′`. -/
def IsBoxPointwiseMean (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (d : PairData Ω) (β : Ω → BoundaryWord) : Prop :=
  ∀ (m : ℕ) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) →
    IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ d.D ω →
      (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, ((β ω).mean (d.fwd ω z) - QuantumZipper.chiC κ * d.lift ω z) * φ z

/-- **The pointwise form gives the chart form** of the mean identification. -/
theorem isBoxMeanIdentification_of_pointwise (hd : d.IsMeasGood) {κ : ℝ} {u₀ : ℂ → ℝ} {β : Ω → BoundaryWord}
    (hpt : IsBoxPointwiseMean κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β) : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β := by
  intro m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  filter_upwards [hpt m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg] with ω hω hbox φ
  exact chartTransport_chart_eq_integral_mean hd (mem_meetBox_iff.1 hbox).1 κ (hω hbox) φ

end Pair

end Restart

end InteractingSLE
