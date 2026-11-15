/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetZoneProp38

/-!
# Proposition 3.8 in a chart for nested history-marked local sets

Packet PROVE-T15-RET6 (Aux. lemma 82, supplement pp. 296–297: "Retain the marked Gaussian kernels of `A` and `A ∪ B`,
with the earlier marked information included in the later one"). The conditional Gaussian laws of the chart form of
Proposition 3.8 (`RetZone.IsChartData`) come from two nested history-marked local sets `A₂ ⊆ A` with marks
`ℋ₁ ≤ ℋ`, through the cover σ-algebras (`Sec7.FlatClockProof.isCondGaussian_of_cover`, the nested Proposition 3.9 of
PROVE-FLATCLOCK): given `𝒢 = 𝒜₂ ∨ σ(A₂) ∨ ℋ₁` the field is Gaussian with the mean of any version of `𝒞_{A₂}`, and given
`𝒥 = 𝒜 ∨ σ(A) ∨ ℋ ∨ 𝒢` with the mean of any version of `𝒞_A` (the germ of the smaller set lies in every cover
σ-algebra of the larger one, `Sec7.FlatClockProof.germSigma_le_aeSigma_of_ae_subset`). The chart may then be any
`ℋ₁`-measurable chart of a union of components of `ℍ ∖ A₂`.

* **`isChartData_of_history`** and, with Proposition 3.8 in a chart,
* **`ae_tendsto_zero_of_history`**.

No Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.LocalSets (germSigma aeSigma le_aeSigma coverSigmaM IsLocalSetMean)

namespace InteractingSLE

namespace RLC

namespace RetZone

variable {Ω : Type*} {ℋ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A A₂ D : Ω → Set ℂ} {G : Ω → ℂ → ℂ}
  {g g₂ : Ω → DistOn upperHalfPlaneOpens}

/-- The small conditioning σ-algebra `𝒢 = 𝒜₂ ∨ σ(A₂) ∨ ℋ₁`. -/
abbrev histSigma₂ (A₂ : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (ℋ₁ : MeasurableSpace Ω) :
    MeasurableSpace Ω :=
  germSigma A₂ h ⊔ (MeasurableSpace.comap A₂ hittingSigma ⊔ ℋ₁)

/-- The large conditioning σ-algebra `𝒥 = 𝒜 ∨ σ(A) ∨ ℋ ∨ 𝒢`. -/
abbrev histSigma₁ (A A₂ : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (ℋ ℋ₁ : MeasurableSpace Ω) :
    MeasurableSpace Ω :=
  germSigma A h ⊔ (MeasurableSpace.comap A hittingSigma ⊔ ℋ) ⊔ histSigma₂ A₂ h ℋ₁

/-- **Nested history-marked local sets give the standing hypotheses of Proposition 3.8 in a chart.** -/
theorem isChartData_of_history (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hℋ : ℋ ≤ mΩ) (hℋ₁ : ℋ₁ ≤ ℋ)
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A h P) (hloc₁ : WholeField.IsHistoryAvoidanceLocal ℋ₁ A₂ h P)
    (hA₂ℋ : MeasurableSpace.comap A₂ hittingSigma ≤ aeSigma (MeasurableSpace.comap A hittingSigma ⊔ ℋ) P)
    (hclosed : ∀ᵐ ω ∂P, (A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧ (A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧ A₂ ω ⊆ A ω)
    (hg : IsLocalSetMean A h P g) (hg₂ : IsLocalSetMean A₂ h P g₂)
    (hchart : ∀ᵐ ω ∂P, IsChartSetting (D ω) (H \ A₂ ω) (G ω) ∧ ∃ M : ℝ, ∀ z ∈ D ω, ‖G ω z - z‖ ≤ M)
    (hDm : ∀ q, MeasurableSet[ℋ₁] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[ℋ₁] fun ω => chartInd D G ω q) :
    IsChartData (histSigma₂ A₂ h ℋ₁) (histSigma₁ A A₂ h ℋ ℋ₁) P h g g₂ A A₂ D G := by
  have hhm := hh.measurable
  have hmk := WholeField.isCoverMarking_history hh hAm hℋ hloc
  have hmk₁ := WholeField.isCoverMarking_history hh hA₂m (hℋ₁.trans hℋ) hloc₁
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hclosed.mono fun _ h => h.1
  have hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω) := hclosed.mono fun _ h => h.2.1
  have hsub : ∀ᵐ ω ∂P, A₂ ω ⊆ A ω := hclosed.mono fun _ h => h.2.2
  have h𝒢le : histSigma₂ A₂ h ℋ₁ ≤ mΩ :=
    sup_le (LocalSets.germSigma_le hA₂m hhm) (sup_le hA₂m.comap_le (hℋ₁.trans hℋ))
  have h𝒥le : histSigma₁ A A₂ h ℋ ℋ₁ ≤ mΩ :=
    sup_le (sup_le (LocalSets.germSigma_le hAm hhm) (sup_le hAm.comap_le hℋ)) h𝒢le
  -- the trace conditions
  have htr₂ : ∀ j, histSigma₂ A₂ h ℋ₁ ≤
      aeSigma (coverSigmaM (MeasurableSpace.comap A₂ hittingSigma ⊔ ℋ₁) j A₂ h) P := fun j =>
    sup_le (fun G hG => LocalSets.germSigmaAt_le_aeSigmaM hh hmk₁.comap_le j G
      (LocalSets.measurableSet_germSigmaAt_coverRad hG j))
      ((le_sup_left : MeasurableSpace.comap A₂ hittingSigma ⊔ ℋ₁ ≤ coverSigmaM _ j A₂ h).trans (le_aeSigma _ P))
  have htr₁ : ∀ j, histSigma₁ A A₂ h ℋ ℋ₁ ≤
      aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ ℋ) j A h) P := by
    intro j
    have hM : MeasurableSpace.comap A hittingSigma ⊔ ℋ ≤
        aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ ℋ) j A h) P :=
      (le_sup_left : MeasurableSpace.comap A hittingSigma ⊔ ℋ ≤ coverSigmaM _ j A h).trans (le_aeSigma _ P)
    refine sup_le (sup_le (fun G hG => LocalSets.germSigmaAt_le_aeSigmaM hh hmk.comap_le j G
      (LocalSets.measurableSet_germSigmaAt_coverRad hG j)) hM) (sup_le ?_ (sup_le ?_ ?_))
    · exact Sec7.FlatClockProof.germSigma_le_aeSigma_of_ae_subset hh hmk.comap_le hA₂ℋ hsub j
    · exact hA₂ℋ.trans (Sec7.FlatClockProof.aeSigma_mono (le_sup_left : MeasurableSpace.comap A hittingSigma ⊔ ℋ ≤
        coverSigmaM _ j A h))
    · exact (hℋ₁.trans (le_sup_right : ℋ ≤ MeasurableSpace.comap A hittingSigma ⊔ ℋ)).trans hM
  have hℋ₁𝒢 : ℋ₁ ≤ histSigma₂ A₂ h ℋ₁ := le_sup_right.trans le_sup_right
  exact
    { le := le_sup_right
      law₁ := fun ψ => Sec7.FlatClockProof.isCondGaussian_of_cover hh hAm hmk hAc
        (le_sup_left.trans le_sup_left) h𝒥le htr₁ hg ψ
      law₂ := fun ψ => Sec7.FlatClockProof.isCondGaussian_of_cover hh hA₂m hmk₁ hA₂c le_sup_left h𝒢le htr₂ hg₂ ψ
      meas_A := (le_sup_left.trans le_sup_right).trans le_sup_left
      meas_A₂ := le_sup_left.trans le_sup_right
      meas_g := hg.1.mono (LocalSets.germSigma_le hAm hhm) le_rfl
      meas_g₂ := hg₂.1.mono (LocalSets.germSigma_le hA₂m hhm) le_rfl
      closed := hclosed
      harm := by filter_upwards [hg.2.1, hg₂.2.1] with ω h1 h2 using ⟨h1, h2⟩
      chart := hchart
      meas_D := fun q => hℋ₁𝒢 _ (hDm q)
      meas_G := fun q => (hGm q).mono hℋ₁𝒢 le_rfl }

/-- **Proposition 3.8 in a chart for nested history-marked local sets.** -/
theorem ae_tendsto_zero_of_history (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAm : Measurable[mΩ, hittingSigma] A) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hℋ : ℋ ≤ mΩ) (hℋ₁ : ℋ₁ ≤ ℋ)
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A h P) (hloc₁ : WholeField.IsHistoryAvoidanceLocal ℋ₁ A₂ h P)
    (hA₂ℋ : MeasurableSpace.comap A₂ hittingSigma ≤ aeSigma (MeasurableSpace.comap A hittingSigma ⊔ ℋ) P)
    (hclosed : ∀ᵐ ω ∂P, (A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧ (A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧ A₂ ω ⊆ A ω)
    (hg : IsLocalSetMean A h P g) (hg₂ : IsLocalSetMean A₂ h P g₂)
    (hchart : ∀ᵐ ω ∂P, IsChartSetting (D ω) (H \ A₂ ω) (G ω) ∧ ∃ M : ℝ, ∀ z ∈ D ω, ‖G ω z - z‖ ≤ M)
    (hDm : ∀ q, MeasurableSet[ℋ₁] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[ℋ₁] fun ω => chartInd D G ω q) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ A ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ y ρ : ℝ, 0 < ρ → (∀ z ∈ D ω, G ω z ∈ ball (y : ℂ) ρ → z ∉ A ω) →
        ∀ F : Filter ℂ, F ≤ 𝓟 (D ω) → Tendsto (G ω) F (𝓝 (y : ℂ)) → Tendsto u F (𝓝 0) :=
  ae_tendsto_zero_of_chart (isChartData_of_history hh hAm hA₂m hℋ hℋ₁ hloc hloc₁ hA₂ℋ hclosed hg hg₂ hchart
    hDm hGm)

end RetZone

end RLC

end InteractingSLE
