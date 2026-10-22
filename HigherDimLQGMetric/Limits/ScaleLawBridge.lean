import HigherDimLQGMetric.Limits.ScaleRatio
import HigherDimLQGMetric.Limits.ScaleStable

/-!
# Law version of the exact LFPP scale identity

The normalized affine field has the same law as the original normalized LGF.
The pathwise scaling identity then identifies its LFPP law with a deterministic
multiple of the randomly rescaled original LFPP law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The exact prelimit scaling relation expressed as equality of metric laws. -/
theorem l6c_law_scaled_prelimit {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    P.map (fun ω => toCMapRd ((aEps κ ξ (ε / r))⁻¹ •
      lfppDist κ ξ (ε / r) (h ω))) =
    (P.map (fun ω => Real.exp (-ξ * sphereAvg (h ω) r 0) •
      (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))).comp
        ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩)).map
      (fun D => (aEps κ ξ ε / (r * aEps κ ξ (ε / r))) • D) := by
  let g : Ω → DistRd d := fun ω =>
    addConst (affineComp r 0 (h ω))
      (-sphereAvg (affineComp r 0 (h ω)) 1 0)
  let W : Ω → C(Rd d × Rd d, ℝ) := fun ω =>
    Real.exp (-ξ * sphereAvg (h ω) r 0) •
      (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))).comp
        ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩
  let b : ℝ := aEps κ ξ ε / (r * aEps κ ξ (ε / r))
  have hX : AEMeasurable
      (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ hε P h
      hh.1.isLGFPlusBddCont
  have hW : AEMeasurable W P := by
    have hs : Measurable (fun ω => Real.exp (-ξ * sphereAvg (h ω) r 0)) :=
      Real.measurable_exp.comp
        (measurable_const.mul ((measurable_sphereAvg_left r 0).comp hh.1.measurable))
    exact hs.aemeasurable.smul
      ((ContinuousMap.continuous_precomp _).measurable.comp_aemeasurable hX)
  have hmapg := l6c_map_lfppMetric_normalizedAffine hd κ hκ ξ P h hh
    (div_pos hε hr) hr
  have hpath := l6c_ae_scaled_lfppMetric hd κ hκ ξ P h hh hε hr
  calc
    P.map (fun ω => toCMapRd ((aEps κ ξ (ε / r))⁻¹ •
        lfppDist κ ξ (ε / r) (h ω))) =
      P.map (fun ω => toCMapRd ((aEps κ ξ (ε / r))⁻¹ •
        lfppDist κ ξ (ε / r) (g ω))) := hmapg.symm
    _ = P.map (fun ω => b • W ω) := by
      apply Measure.map_congr
      filter_upwards [hpath] with ω hω
      simpa only [g, W, b, smul_smul] using hω
    _ = (P.map W).map (fun D => b • D) := by
      exact (AEMeasurable.map_map_of_aemeasurable
        ((show Continuous (fun D : C(Rd d × Rd d, ℝ) => b • D) from
          by fun_prop).measurable.aemeasurable) hW).symm

end HigherDimLQGMetric
