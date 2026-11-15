/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Root
import InteractingSLE.Spec.Supplement.GB6LMeanFinal

/-! # The exact counterflow record is known to its own retained filtration -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR7

open LQGMetric WholeField Exist.StagedLaw Supp8.GB6 Supp8.RelSafeS
open GW2TipSystem GW2JointKernel GW2JDetR4

/-- The regularized record, including its time and flag, is measurable in the
actual driving filtration. No measurability of the raw driver after death is used. -/
theorem measurable_cfRec_driving
    {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling k xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    (hm : Measurable (cfRec s W ζ)) :
    Measurable[drivingFiltration P hC.2.2.2.1 s] (cfRec s W ζ) := by
  let hX := hC.2.2.2.1
  have hKW : ∀ r, Measurable (cfKW W ζ r) := fun r =>
    Restart.measurable_ite_of_adaptedBefore hC.1.2.1 r
  have heW : ∀ᵐ ω ∂P, ∀ r, cfKW W ζ r ω = W r ω := by
    filter_upwards [hζ] with ω hω r
    simp only [cfKW, hω, ENNReal.coe_lt_top, ↓reduceIte]
  let R : Ω → RecData := fun ω =>
    (fun q : ℚ => cfKW W ζ (min (q : ℝ).toNNReal s) ω, (s : ℝ≥0∞), false)
  have hR : Measurable[drivingFiltration P hX s] R := by
    let : MeasurableSpace Ω := drivingFiltration P hX s
    refine (measurable_pi_iff.mpr fun q : ℚ => ?_).prodMk
      (measurable_const.prodMk measurable_const)
    exact measurable_version_drivingFiltration (mΩ := mΩ) hX hζ hKW heW (min_le_right _ _)
  have he : cfRec s W ζ =ᵐ[P] R := by
    filter_upwards [hC.1.2.2.2.2, hζ, heW] with ω hp hζω hKWω
    have hc : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
    have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
    have hr := cfRec_eq_live_samples s hc hp.1 hs
    change (fun q : ℚ => W (min (q : ℝ).toNNReal s) ω, (s : ℝ≥0∞), false) =
      cfRec s W ζ ω at hr
    rw [← hr]
    exact Prod.ext (funext fun q => (hKWω _).symm) rfl
  exact Supp8.GB6LineL.measurable_of_ae_eq_nullSets
    ((drivingFiltration P hX).le s) (nullSets_le_drivingFiltration' hX s) hm hR he

end InteractingSLE.Theorem14.GW2JDetR7
