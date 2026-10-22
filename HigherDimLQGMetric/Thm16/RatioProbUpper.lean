import HigherDimLQGMetric.Thm16.RatioDomain
import HigherDimLQGMetric.Thm16.ProbIntersect
import HigherDimLQGMetric.Sec4.LfppScaleProb
import HigherDimLQGMetric.Thm16.LfppLowerLaw

/-! The first Prop 4.2 inequality bounds the fixed-scale normalizer ratio above. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_fixed_ratio_upper {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c)
    (hprop42 : Prop42Shape)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      l9c_ratio (aEps κ ξ) ε r ≤ K * c r := by
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  obtain ⟨C, hC, hprop⟩ := hprop42 d hd hξ hsub hκ hD
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨η, hη, hlfpp⟩ := l9c_affineLfpp_pairLower_raw hd hκ hξ hsub
    hB2 hL6a (by norm_num : (0 : ℝ≥0∞) < 8⁻¹)
  obtain ⟨M, hM, hdiam⟩ := hD.scaledSphereDiamUpper hd2
    (by norm_num : (0 : ℝ≥0∞) < 8⁻¹)
  refine ⟨C * M / η, div_pos (mul_pos hC hM) hη, ?_⟩
  intro r hr
  let U : Set (Rd d) := ball 0 (3 * r)
  have hUr : 0 < 3 * r := by positivity
  have hUopen : IsOpen U := isOpen_ball
  have hUbounded : Bornology.IsBounded U := isBounded_ball
  have hUconn : IsConnected U := Metric.isConnected_ball hUr
  have hAnn : ann (0 : Rd d) (r / 2) (2 * r) ⊆ U := l9c_ann_subset_ball_three hr
  obtain ⟨hz, hw⟩ := l9c_sphere_point_mem_ball_three (by omega : 0 < d) hr
  have hp42 := hprop U hUopen hUbounded hUconn (normLGFLaw d) id hn
  have hp42small : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (normLGFLaw d) {H | ¬ ∀ z ∈ U, ∀ w ∈ U,
        ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppSetDistIn κ ξ ε H
          (thickening (ε ^ (1 - (1 / 2 : ℝ))) U)
          (ball z (ε ^ (1 - (1 / 2 : ℝ))))
          (ball w (ε ^ (1 - (1 / 2 : ℝ)))) ≤
          ENNReal.ofReal C * (D H).internal U z w ∧
        setDistIn (D H) (thickening (ε ^ (1 - (1 / 2 : ℝ))) U)
          (ball z (ε ^ (1 - (1 / 2 : ℝ))))
          (ball w (ε ^ (1 - (1 / 2 : ℝ)))) ≤
          ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
            lfppDistIn κ ξ ε H U z w)} < (8⁻¹ : ℝ≥0∞) :=
    hp42.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 8⁻¹))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < r ∧ ε < (r / 4) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hr),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (pow_pos (by positivity : (0 : ℝ) < r / 4) 2))]
      with ε hε hεr hεq
    exact ⟨hε, hεr, hεq⟩
  filter_upwards [hp42small, hsmall] with ε hp hεsmall
  obtain ⟨hε, hεr, hεq⟩ := hεsmall
  let q : ℝ := ε ^ (1 / 2 : ℝ)
  have hq : q ≤ r / 4 := by
    change ε ^ (1 / 2 : ℝ) ≤ r / 4
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨by positivity, hεq.le⟩
  have hδ : ε / r ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hε hr, (div_lt_one hr).2 hεr⟩
  have haε : 0 < aEps κ ξ ε := l6a_aEps_pos hd2 κ hκ ξ hε
  have haδ : 0 < aEps κ ξ (ε / r) := l6a_aEps_pos hd2 κ hκ ξ hδ.1
  let g : DistRd d → DistRd d := fun H =>
    addConst (affineComp r 0 H) (-sphereAvg (affineComp r 0 H) 1 0)
  let A : Set (DistRd d) := {H | ¬ ∀ z ∈ U, ∀ w ∈ U,
        ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppSetDistIn κ ξ ε H
          (thickening (ε ^ (1 - (1 / 2 : ℝ))) U)
          (ball z (ε ^ (1 - (1 / 2 : ℝ))))
          (ball w (ε ^ (1 - (1 / 2 : ℝ)))) ≤
          ENNReal.ofReal C * (D H).internal U z w ∧
        setDistIn (D H) (thickening (ε ^ (1 - (1 / 2 : ℝ))) U)
          (ball z (ε ^ (1 - (1 / 2 : ℝ))))
          (ball w (ε ^ (1 - (1 / 2 : ℝ)))) ≤
          ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
            lfppDistIn κ ξ ε H U z w)}
  let B : Set (DistRd d) := {H | ¬ ∀ p ∈
      closedBall (e₁ d) (1 / 4) ×ˢ closedBall (-e₁ d) (1 / 4),
      η < (aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (g H) p}
  let F : Set (DistRd d) := {H | ENNReal.ofReal M <
      sphereDiam (weakScaledMetric ξ D c H hr 0 (hD.c_pos r hr)) 0 1}
  let N : Set (DistRd d) := {H | ¬ Continuous (convMollify κ ε H) ∨
    ¬ ∀ u v : Rd d,
      lfppDist κ ξ ε H (r • u, r • v) =
        r * Real.exp (ξ * sphereAvg H r 0) * lfppDist κ ξ (ε / r) (g H) (u, v)}
  have hN : (normLGFLaw d) N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [l10a_ae_continuous_convMollify hd2 κ hκ
      (normLGFLaw d) id hn hε,
      l6c_ae_lfppDist_scale hd2 κ hκ ξ (normLGFLaw d) id hn hr]
      with H hcont hscale
    change ¬ (¬ Continuous (convMollify κ ε H) ∨ ¬ ∀ u v : Rd d,
      lfppDist κ ξ ε H (r • u, r • v) =
        r * Real.exp (ξ * sphereAvg H r 0) * lfppDist κ ξ (ε / r) (g H) (u, v))
    exact not_or.mpr ⟨not_not.mpr hcont, not_not.mpr (hscale ε hε)⟩
  have hB : (normLGFLaw d) B < (8⁻¹ : ℝ≥0∞) := hlfpp r hr (ε / r) hδ
  have hF : (normLGFLaw d) F < (8⁻¹ : ℝ≥0∞) :=
    hdiam (normLGFLaw d) id hn.1 r hr 0
  obtain ⟨H, hA, hB', hF', hN'⟩ :=
    l9c_exists_good_four (normLGFLaw d) hp hB hF hN
  have hpropGood : ∀ z ∈ U, ∀ w ∈ U,
        ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppSetDistIn κ ξ ε H
          (thickening (ε ^ (1 - (1 / 2 : ℝ))) U)
          (ball z (ε ^ (1 - (1 / 2 : ℝ))))
          (ball w (ε ^ (1 - (1 / 2 : ℝ)))) ≤
          ENNReal.ofReal C * (D H).internal U z w ∧
        setDistIn (D H) (thickening (ε ^ (1 - (1 / 2 : ℝ))) U)
          (ball z (ε ^ (1 - (1 / 2 : ℝ))))
          (ball w (ε ^ (1 - (1 / 2 : ℝ)))) ≤
          ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
            lfppDistIn κ ξ ε H U z w) := not_not.mp hA
  have hLo : ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
      closedBall (-e₁ d) (1 / 4),
      η < (aEps κ ξ (ε / r))⁻¹ * lfppDist κ ξ (ε / r) (g H) p :=
    not_not.mp hB'
  have hDiam : sphereDiam (weakScaledMetric ξ D c H hr 0 (hD.c_pos r hr)) 0 1 ≤
      ENNReal.ofReal M := not_lt.mp hF'
  have hAe : Continuous (convMollify κ ε H) ∧
      ∀ u v : Rd d,
        lfppDist κ ξ ε H (r • u, r • v) =
          r * Real.exp (ξ * sphereAvg H r 0) * lfppDist κ ξ (ε / r) (g H) (u, v) :=
    (not_or.mp hN').imp_left not_not.mp |>.imp_right not_not.mp
  have hpSample := (hpropGood (r • e₁ d) hz (-(r • e₁ d)) hw).1
  have hpSample' : ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
        lfppSetDistIn κ ξ ε H (thickening q U)
          (ball (r • e₁ d) q) (ball (-(r • e₁ d)) q) ≤
        ENNReal.ofReal C * (D H).internal U (r • e₁ d) (-(r • e₁ d)) := by
    simpa only [q, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hpSample
  exact l9c_ratio_upper_sample (by omega : 0 < d) κ ξ ε H (g H)
    D c (aEps κ ξ) hr hq hC hM.le hη (hD.c_pos r hr)
    haε haδ hAe.1 hAe.2 hLo hAnn hDiam hpSample'

end HigherDimLQGMetric
