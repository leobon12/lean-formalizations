import HigherDimLQGMetric.Limits.ScaleIdentity
import HigherDimLQGMetric.Limits.ScaleMedianBounds
import HigherDimLQGMetric.LfppTight.LawInput

/-!
# Scaled prelimit metrics

The raw LFPP identity is converted to the normalized continuous-map metric
used in the stable limit.  All random field identities are on one a.s. event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The normalized affine field gives the same LFPP metric law at any fixed
positive cutoff. -/
theorem l6c_map_lfppMetric_normalizedAffine {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    P.map (fun ω => toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ
      (addConst (affineComp r 0 (h ω))
        (-sphereAvg (affineComp r 0 (h ω)) 1 0)))) =
    P.map (fun ω => toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ (h ω))) := by
  let g : Ω → DistRd d := fun ω =>
    addConst (affineComp r 0 (h ω))
      (-sphereAvg (affineComp r 0 (h ω)) 1 0)
  let F : DistRd d → C(Rd d × Rd d, ℝ) := fun x =>
    toCMapRd ((aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ x)
  have hmap : P.map g = P.map h := l6c_map_normalizedAffine_eq hd P h hh hr
  have hgm : Measurable g :=
    measurable_addConst.comp
      (((measurable_affineComp r 0).comp hh.1.measurable).prodMk
        ((measurable_sphereAvg_left 1 0).comp
          ((measurable_affineComp r 0).comp hh.1.measurable)).neg)
  have hnorm : IsNormalizedLGF id (P.map h) := hh.map_id
  have hFm : AEMeasurable F (P.map h) :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ hδ (P.map h) id
      hnorm.1.isLGFPlusBddCont
  have hFg : AEMeasurable F (P.map g) := by rw [hmap]; exact hFm
  change P.map (F ∘ g) = P.map (F ∘ h)
  calc
    P.map (F ∘ g) = (P.map g).map F :=
      (AEMeasurable.map_map_of_aemeasurable hFg hgm.aemeasurable).symm
    _ = (P.map h).map F := by rw [hmap]
    _ = P.map (F ∘ h) :=
      AEMeasurable.map_map_of_aemeasurable hFm hh.1.measurable.aemeasurable

/-- Normalized affine LFPP equals the randomly rescaled original LFPP times
the deterministic normalization ratio. -/
theorem l6c_ae_scaled_lfppMetric {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∀ᵐ ω ∂P,
      let g := addConst (affineComp r 0 (h ω))
        (-sphereAvg (affineComp r 0 (h ω)) 1 0)
      toCMapRd ((aEps κ ξ (ε / r))⁻¹ • lfppDist κ ξ (ε / r) g) =
        ((aEps κ ξ ε) / (r * aEps κ ξ (ε / r)) *
          Real.exp (-ξ * sphereAvg (h ω) r 0)) •
          (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))).comp
            ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩ := by
  let k : Ω → DistRd d := fun ω => affineComp r 0 (h ω)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp hr 0
  have hconv : ∀ᵐ ω ∂P, k ω ∈ convSet d :=
    hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  let g : Ω → DistRd d := fun ω => addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hg : IsNormalizedLGF g P := hk.isNormalizedLGF_normalize (by omega) hconv
  have hεr : 0 < ε / r := div_pos hε hr
  have ha : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε
  have har : 0 < aEps κ ξ (ε / r) := l6a_aEps_pos hd κ hκ ξ hεr
  filter_upwards [l6c_ae_lfppDist_scale hd κ hκ ξ P h hh hr,
    l10a_ae_continuous_convMollify hd κ hκ P h hh hε,
    l10a_ae_continuous_convMollify hd κ hκ P g hg hεr]
    with ω hscale hc hc'
  dsimp
  apply ContinuousMap.ext
  rintro ⟨u, v⟩
  have hlfpp : Continuous (lfppDist κ ξ ε (h ω)) := by
    have heq : lfppDist κ ξ ε (h ω) = fieldLfpp ξ (convMollify κ ε (h ω)) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn hc p).symm
    rw [heq]
    exact continuous_fieldLfpp hc
  have hlfpp' : Continuous (lfppDist κ ξ (ε / r) (g ω)) := by
    have heq : lfppDist κ ξ (ε / r) (g ω) =
        fieldLfpp ξ (convMollify κ (ε / r) (g ω)) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn hc' p).symm
    rw [heq]
    exact continuous_fieldLfpp hc'
  rw [toCMapRd_apply_of_continuous (hlfpp'.const_smul _)]
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply,
    toCMapRd_apply_of_continuous (hlfpp.const_smul _), Pi.smul_apply, smul_eq_mul]
  have hs := hscale ε hε u v
  change lfppDist κ ξ ε (h ω) (r • u, r • v) =
    r * Real.exp (ξ * sphereAvg (h ω) r 0) *
      lfppDist κ ξ (ε / r) (g ω) (u, v) at hs
  have : aEps κ ξ ε ≠ 0 := ha.ne'
  have : aEps κ ξ (ε / r) ≠ 0 := har.ne'
  have : r ≠ 0 := hr.ne'
  change (aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (g ω) (u, v) =
    aEps κ ξ ε / (r * aEps κ ξ (ε / r)) *
      Real.exp (-ξ * sphereAvg (h ω) r 0) *
      ((aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε (h ω) (r • u, r • v))
  rw [hs]
  rw [show -ξ * sphereAvg (h ω) r 0 = -(ξ * sphereAvg (h ω) r 0) by ring,
    Real.exp_neg]
  field_simp

end HigherDimLQGMetric
