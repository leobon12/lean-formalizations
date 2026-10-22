import HigherDimLQGMetric.LfppTight.FarMedianUpper
import HigherDimLQGMetric.LfppTight.PureShellSmall
import HigherDimLQGMetric.DGZ.FunctionalsBounds

/-! Uniform normalized shell lower tails on cutoff intervals away from zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6a_sphere_nonempty {d : ℕ} (hd : 0 < d)
    (c : Rd d) {r : ℝ} (hr : 0 ≤ r) : (sphere c r).Nonempty := by
  refine ⟨c + r • e₁ d, ?_⟩
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
    HigherDimLFPP.norm_e₁ hd, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]

theorem l6a_pure_shell_tail_far {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (c : Rd d) {r₁ r₂ a θ : ℝ}
    (hr₂ : 0 < r₂) (hr : r₂ < r₁) (ha : 0 < a) (hθ : 0 < θ) :
    ∃ m : ℝ, 0 < m ∧ ∀ ε ∈ Ico a 1,
      P {ω | DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m} ≤
          ENNReal.ofReal θ := by
  let δ : ℝ := (r₁ - r₂) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let R : ℝ := ‖c‖ + r₁ + 2
  obtain ⟨L, hL, hbad⟩ := l6a_far_field_sup_tail hd κ hκ P h hh
    (a := a) (R := R) (θ := θ) ha hθ
  obtain ⟨T, hT, hmed⟩ := l6a_aEps_upper_far hd κ hκ ξ P h hh ha
  let w : ℝ := Real.exp (-|ξ| * L) * δ
  have hw : 0 < w := mul_pos (Real.exp_pos _) hδ
  let m : ℝ := (w / T) / 2
  have hm : 0 < m := by dsimp [m]; positivity
  refine ⟨m, hm, ?_⟩
  intro ε hε
  have hε0 : 0 < ε := ha.trans_le hε.1
  have hae : 0 < aEps κ ξ ε := l6a_aEps_pos hd κ hκ ξ hε0
  have hcont := l10a_ae_continuous_convMollify hd κ hκ P h hh hε0
  have hsub : ∀ᵐ ω ∂P,
      DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) ≤ m →
      ∃ η ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) R,
        L < |convMollify κ η (h ω) z| := by
    filter_upwards [hcont] with ω hc hω
    by_contra hn
    let φ : Rd d → ℝ := convMollify κ ε (h ω)
    have hfield : ∀ z ∈ closedBall (0 : Rd d) R, |φ z| ≤ L := by
      intro z hz
      exact le_of_not_gt (fun hlt => hn ⟨ε, ⟨hε.1, hε.2.le⟩, z, hz, hlt⟩)
    have hA : (sphere c r₂).Nonempty :=
      l6a_sphere_nonempty (by omega : 0 < d) c hr₂.le
    have hB : (sphere c r₁).Nonempty :=
      l6a_sphere_nonempty (by omega : 0 < d) c (hr₂.trans hr).le
    have hsep : ∀ x ∈ sphere c r₂, ∀ y ∈ sphere c r₁,
        δ ≤ ‖y - x‖ := by
      intro x hx y hy
      have htri := dist_triangle y x c
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
      have hxc : ‖x - c‖ = r₂ := by simpa only [mem_sphere, dist_eq_norm] using hx
      have hyc : ‖y - c‖ = r₁ := by simpa only [mem_sphere, dist_eq_norm] using hy
      rw [hxc, hyc] at htri
      dsimp [δ]
      linarith
    have hweight : ∀ x ∈ sphere c r₂, ∀ z ∈ closedBall x δ,
        -|ξ| * L ≤ ξ * φ z := by
      intro x hx z hz
      have hxc : ‖x - c‖ = r₂ := by simpa only [mem_sphere, dist_eq_norm] using hx
      have hzx : ‖z - x‖ ≤ δ := by simpa only [mem_closedBall, dist_eq_norm] using hz
      have hnorm : ‖z‖ ≤ ‖c‖ + r₂ + δ := by
        have h1 := norm_le_insert' z x
        have h2 := norm_le_insert' x c
        linarith
      have hzR : z ∈ closedBall (0 : Rd d) R := by
        rw [mem_closedBall, dist_zero_right]
        dsimp [R, δ] at *
        linarith
      have hf := hfield z hzR
      have habs : |ξ * φ z| ≤ |ξ| * L := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hf (abs_nonneg ξ)
      linarith [neg_abs_le (ξ * φ z)]
    have hlower : w ≤ DGZ.lfppSetDist ξ φ univ (sphere c r₂) (sphere c r₁) := by
      change Real.exp (-|ξ| * L) * δ ≤ _
      exact DGZ.exp_mul_le_lfppSetDist hc hA hB hsep hweight
        (fun x _ y _ => HigherDimLFPP.PcwJoined.of_convex convex_univ
          (mem_univ x) (mem_univ y))
    have heq : DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))) =
          (aEps κ ξ ε)⁻¹ * DGZ.lfppSetDist ξ φ univ
            (sphere c r₂) (sphere c r₁) := by
      change DGZ.nd_setInf (sphere c r₂) (sphere c r₁)
        (DGZ.normMetricC ξ φ (aEps κ ξ ε)) = _
      exact DGZ.nd_setInf_normMetricC hc hae ξ _ _
    rw [heq] at hω
    have hTinv : T⁻¹ ≤ (aEps κ ξ ε)⁻¹ :=
      (inv_le_inv₀ hT hae).2 (hmed ε hε)
    have hnorm : w / T ≤ (aEps κ ξ ε)⁻¹ *
        DGZ.lfppSetDist ξ φ univ (sphere c r₂) (sphere c r₁) := by
      calc
        w / T = T⁻¹ * w := by ring
        _ ≤ (aEps κ ξ ε)⁻¹ * w :=
          mul_le_mul_of_nonneg_right hTinv hw.le
        _ ≤ _ := mul_le_mul_of_nonneg_left hlower (inv_pos.mpr hae).le
    dsimp [m] at hω
    have hposwT : 0 < w / T := div_pos hw hT
    linarith
  exact (measure_mono_ae hsub).trans hbad

end HigherDimLQGMetric
