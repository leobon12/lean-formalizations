import HigherDimLQGMetric.Thm16.LfppInput
import HigherDimLQGMetric.Limits.ScalePrelimit

/-! Uniform lower pair distance in normalized affine LFPP fields. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_affineLfpp_pairLower {d : ℕ} (hd : 3 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (r : ℝ) (_hr : 0 < r) (δ : ℝ) (_hδ : δ ∈ Ioo (0 : ℝ) 1),
      (normLGFLaw d) {H | ¬ ∀ p ∈
          Metric.closedBall (e₁ d) (1 / 4) ×ˢ Metric.closedBall (-e₁ d) (1 / 4),
          η < (toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ
            (addConst (affineComp r 0 H)
              (-sphereAvg (affineComp r 0 H) 1 0)))) p} < θ := by
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  let X : ℝ → DistRd d → C(Rd d × Rd d, ℝ) :=
    fun δ H => toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ H)
  have hT : TightFamily (normLGFLaw d) X (Ioo (0 : ℝ) 1) :=
    l9c_normLfpp_tight hd hκ hξ hsub hB2 hL6a
  obtain ⟨η, hη, hbad⟩ := l9c_tightFamily_pairLower (by omega : 0 < d) hT hθ
  refine ⟨η, hη, ?_⟩
  let A : Set (Rd d × Rd d) :=
    Metric.closedBall (e₁ d) (1 / 4) ×ˢ Metric.closedBall (-e₁ d) (1 / 4)
  let E : Set C(Rd d × Rd d, ℝ) := {M | ¬ MapsTo M A (Ioi η)}
  have hE : MeasurableSet E :=
    (LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
      isOpen_Ioi).measurableSet
  intro r hr δ hδ
  let g : DistRd d → DistRd d := fun H =>
    addConst (affineComp r 0 H) (-sphereAvg (affineComp r 0 H) 1 0)
  have hgm : Measurable g :=
    measurable_addConst.comp
      (((measurable_affineComp r 0).comp hn.1.measurable).prodMk
        ((measurable_sphereAvg_left 1 0).comp
          ((measurable_affineComp r 0).comp hn.1.measurable)).neg)
  have hmapg : (normLGFLaw d).map g = normLGFLaw d := by
    simpa [g, Function.id_def] using l6c_map_normalizedAffine_eq hd2 (normLGFLaw d) id hn hr
  have hXm : AEMeasurable (X δ) (normLGFLaw d) := hT.1 δ hδ
  have hYm : AEMeasurable (X δ ∘ g) (normLGFLaw d) := by
    apply AEMeasurable.comp_aemeasurable _ hgm.aemeasurable
    rw [hmapg]
    exact hXm
  have hmap : (normLGFLaw d).map (X δ ∘ g) = (normLGFLaw d).map (X δ) := by
    simpa [X, g, Function.comp_def, Function.id_def] using
      l6c_map_lfppMetric_normalizedAffine hd2 κ hκ ξ
        (normLGFLaw d) id hn hδ.1 hr
  calc
    (normLGFLaw d) {H | ¬ ∀ p ∈ A, η < X δ (g H) p} =
        ((normLGFLaw d).map (X δ ∘ g)) E := by
      rw [Measure.map_apply₀ hYm hE.nullMeasurableSet]
      rfl
    _ = ((normLGFLaw d).map (X δ)) E := by rw [hmap]
    _ = (normLGFLaw d) {H | ¬ ∀ p ∈ A, η < X δ H p} := by
      rw [Measure.map_apply₀ hXm hE.nullMeasurableSet]
      rfl
    _ < θ := hbad δ hδ

/-- The same tail bound expressed with the raw real LFPP distance. -/
theorem l9c_affineLfpp_pairLower_raw {d : ℕ} (hd : 3 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (r : ℝ) (_hr : 0 < r) (δ : ℝ) (_hδ : δ ∈ Ioo (0 : ℝ) 1),
      (normLGFLaw d) {H | ¬ ∀ p ∈
          Metric.closedBall (e₁ d) (1 / 4) ×ˢ Metric.closedBall (-e₁ d) (1 / 4),
          η < (aEps κ ξ δ)⁻¹ * lfppDist κ ξ δ
            (addConst (affineComp r 0 H)
              (-sphereAvg (affineComp r 0 H) 1 0)) p} < θ := by
  obtain ⟨η, hη, hbad⟩ :=
    l9c_affineLfpp_pairLower hd hκ hξ hsub hB2 hL6a hθ
  refine ⟨η, hη, ?_⟩
  intro r hr δ hδ
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  let k : DistRd d → DistRd d := fun H => affineComp r 0 H
  have hk : IsWholeSpaceLGF k (normLGFLaw d) := hn.1.affineComp hr 0
  have hconv : ∀ᵐ H ∂(normLGFLaw d), k H ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hd2 one_pos 0
  let g : DistRd d → DistRd d := fun H =>
    addConst (k H) (-sphereAvg (k H) 1 0)
  have hg : IsNormalizedLGF g (normLGFLaw d) :=
    hk.isNormalizedLGF_normalize (by omega) hconv
  have hcont := l10a_ae_continuous_convMollify hd2 κ hκ
    (normLGFLaw d) g hg hδ.1
  have hle : (normLGFLaw d) {H | ¬ ∀ p ∈
        Metric.closedBall (e₁ d) (1 / 4) ×ˢ Metric.closedBall (-e₁ d) (1 / 4),
        η < (aEps κ ξ δ)⁻¹ * lfppDist κ ξ δ (g H) p} ≤
      (normLGFLaw d) {H | ¬ ∀ p ∈
        Metric.closedBall (e₁ d) (1 / 4) ×ˢ Metric.closedBall (-e₁ d) (1 / 4),
        η < (toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ (g H))) p} := by
    refine measure_mono_ae ?_
    filter_upwards [hcont] with H hH hbadRaw hgood
    apply hbadRaw
    intro p hp
    have hlfpp : Continuous (lfppDist κ ξ δ (g H)) := by
      have heq : lfppDist κ ξ δ (g H) =
          fieldLfpp ξ (convMollify κ δ (g H)) := by
        funext p
        exact (fieldLfpp_eq_lfppDistOn hH p).symm
      rw [heq]
      exact continuous_fieldLfpp hH
    have hcontScaled : Continuous ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ (g H)) :=
      hlfpp.const_smul _
    have hh := hgood p hp
    rw [toCMapRd_apply_of_continuous hcontScaled] at hh
    exact hh
  exact hle.trans_lt (hbad r hr δ hδ)

end HigherDimLQGMetric
