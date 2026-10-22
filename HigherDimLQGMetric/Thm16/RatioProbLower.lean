import HigherDimLQGMetric.Thm16.RatioProbUpper

/-! The second Prop 4.2 inequality bounds the fixed-scale ratio below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_fixed_ratio_lower {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c)
    (hprop42 : Prop42Shape)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c r ≤ K * l9c_ratio (aEps κ ξ) ε r := by
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  obtain ⟨C, hC, hprop⟩ := hprop42 d hd hξ hsub hκ hD
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨η, hη, hDlower⟩ := hD.scaledLowerOffDiag hd2
    ((isCompact_closedBall (e₁ d) (1 / 4)).prod
      (isCompact_closedBall (-e₁ d) (1 / 4)))
    (fun p hp => l9c_pairBalls_offDiag (by omega : 0 < d) hp)
    (by norm_num : (0 : ℝ≥0∞) < 8⁻¹)
  obtain ⟨M, hM, hLfpp⟩ := l9b_lfpp_diam_prob hL6a hB2 hd2 hκ hξ hsub
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
      η < scaledField ξ D c r 0 H p}
  let F : Set (DistRd d) := {H | M * (r * aEps κ ξ (ε / r)) *
      Real.exp (ξ * sphereAvg H r 0) <
      DGZ.lfppDiam ξ (convMollify κ ε H)
        (sphere (0 : Rd d) r) (ann 0 (r / 2) (2 * r))}
  let N : Set (DistRd d) := {H | ¬ Continuous (convMollify κ ε H)}
  have hN : (normLGFLaw d) N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [l10a_ae_continuous_convMollify hd2 κ hκ
      (normLGFLaw d) id hn hε] with H hcont
    exact not_not.mpr hcont
  have hB : (normLGFLaw d) B < (8⁻¹ : ℝ≥0∞) :=
    hDlower (normLGFLaw d) id hn.1 r hr 0
  have hF : (normLGFLaw d) F < (8⁻¹ : ℝ≥0∞) :=
    hLfpp (normLGFLaw d) id hn ε r hε hεr 0
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
  have hDlo : ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
      closedBall (-e₁ d) (1 / 4),
      η ≤ scaledField ξ D c r 0 H p := by
    intro p hp
    exact (not_not.mp hB') p hp |>.le
  have hLfppGood : DGZ.lfppDiam ξ (convMollify κ ε H)
      (sphere (0 : Rd d) r) (ann 0 (r / 2) (2 * r)) ≤
      M * (r * aEps κ ξ (ε / r)) * Real.exp (ξ * sphereAvg H r 0) :=
    not_lt.mp hF'
  have hcont : Continuous (convMollify κ ε H) := not_not.mp hN'
  have hpSample := (hpropGood (r • e₁ d) hz (-(r • e₁ d)) hw).2
  have hpSample' : setDistIn (D H) (thickening q U)
        (ball (r • e₁ d) q) (ball (-(r • e₁ d)) q) ≤
      ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
        lfppDistIn κ ξ ε H U (r • e₁ d) (-(r • e₁ d))) := by
    simpa only [q, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hpSample
  exact l9c_ratio_lower_sample hd2 κ ξ ε H D c (aEps κ ξ)
    hr hq hC hM.le hη (hD.c_pos r hr) haε haδ hcont
    hDlo hAnn hLfppGood hpSample'

end HigherDimLQGMetric
