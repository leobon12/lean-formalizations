import SupercriticalConformalCovariance.TV.MarkovVariance
import QuantumZipper.Proofs.GFF.K3.MixedM7D7
import LQGMetric.Papers.GM.S2.SpatialIndepRad

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open QuantumZipper QuantumZipper.K3 Metric InnerProductSpace MeasureTheory
open LQGMetric.GM
open scoped ComplexConjugate

namespace SupercriticalConformalCovariance.TV

/-- The smooth part of the difference between the whole-plane and disk Green kernels. -/
def diskHarmonicKernel (L : ℝ) (x y : ℂ) : ℝ :=
  Real.log L - Real.log ‖(L : ℂ) ^ 2 - x * conj y‖

theorem diskHarmonicKernel_increment {L : ℝ} (hL : 0 < L) {y : ℂ}
    (hy : ‖y‖ < L) :
    diskHarmonicKernel L y y + diskHarmonicKernel L 0 0 -
      2 * diskHarmonicKernel L y 0 =
        -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) := by
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hy2 : ‖y‖ ^ 2 < L ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hy)
      (add_pos_of_nonneg_of_pos (norm_nonneg y) hL)]
  have hnorm : ‖(L : ℂ) ^ 2 - y * conj y‖ = L ^ 2 - ‖y‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hy2)]
  have hnorm0 : ‖(L : ℂ) ^ 2 - y * conj 0‖ = L ^ 2 := by
    simp [Complex.norm_real]
  have hnorm00 : ‖(L : ℂ) ^ 2 - (0 : ℂ) * conj 0‖ = L ^ 2 := by
    simp [Complex.norm_real]
  simp only [diskHarmonicKernel, hnorm, hnorm0, hnorm00]
  have hlog : Real.log (L ^ 2 - ‖y‖ ^ 2) - Real.log (L ^ 2) =
      Real.log (1 - ‖y‖ ^ 2 / L ^ 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  linarith

theorem diskHarmonicKernel_comm (L : ℝ) (x y : ℂ) :
    diskHarmonicKernel L x y = diskHarmonicKernel L y x := by
  unfold diskHarmonicKernel
  have h : (L : ℂ) ^ 2 - y * conj x =
      conj ((L : ℂ) ^ 2 - x * conj y) := by
    simp [map_sub, map_mul, Complex.conj_ofReal, mul_comm]
  rw [h, Complex.norm_conj]

theorem harmonicOnNhd_diskHarmonicKernel_left
    {L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    {y : ℂ} (hy : ‖y‖ < L) :
    InnerProductSpace.HarmonicOnNhd (fun x => diskHarmonicKernel L x y)
      (closedBall (0 : ℂ) r) := by
  intro x hx
  have hxnorm : ‖x‖ ≤ r := by simpa [mem_closedBall] using hx
  have hprod : ‖x - (0 : ℂ)‖ * ‖y - (0 : ℂ)‖ < L ^ 2 := by
    simp only [sub_zero]
    calc ‖x‖ * ‖y‖ ≤ r * ‖y‖ :=
        mul_le_mul_of_nonneg_right hxnorm (norm_nonneg y)
      _ < L * L := by
        have hy0 := norm_nonneg y
        nlinarith [mul_nonneg (sub_nonneg.mpr hr) hy0]
      _ = L ^ 2 := by ring
  have hneq : (L : ℂ) ^ 2 - (x - 0) * (conj y - 0) ≠ 0 :=
    numer_ne_zero_m7d hprod
  have han : AnalyticAt ℂ
      (fun z : ℂ => (L : ℂ) ^ 2 - (z - 0) * (conj y - 0)) x :=
    analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul analyticAt_const)
  have hh := han.harmonicAt_log_norm hneq
  convert (harmonicAt_const (Real.log L)).sub hh using 1
  funext z
  simp [diskHarmonicKernel]

theorem harmonicOnNhd_diskHarmonicKernel_right
    {L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    {x : ℂ} (hx : ‖x‖ < L) :
    InnerProductSpace.HarmonicOnNhd (fun y => diskHarmonicKernel L x y)
      (closedBall (0 : ℂ) r) := by
  simpa only [diskHarmonicKernel_comm] using
    harmonicOnNhd_diskHarmonicKernel_left hL hr hrL hx

theorem integral_diskHarmonicKernel_radBump_left
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {u y : ℂ} (hu : ‖u‖ + δ < r) (hy : ‖y‖ < L) :
    ∫ x, diskHarmonicKernel L x y * radBump δ hδ.le u x =
      diskHarmonicKernel L u y * ∫ x, radProf δ x := by
  have hB : closedBall u δ ⊆ ball (0 : ℂ) r := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_ball, dist_zero_right]
    have ht := norm_add_le (x - u) u
    rw [sub_add_cancel] at ht
    linarith
  have hh : HarmonicOnNhd (fun x => diskHarmonicKernel L x y)
      (ball (0 : ℂ) r) :=
    (harmonicOnNhd_diskHarmonicKernel_left hL hr hrL hy).mono
      ball_subset_closedBall
  have hmv := integral_mul_radial_of_harmonic isOpen_ball hh hB
    (contDiff_radProf δ).continuous
    (fun x hx => radProf_eq_zero hδ.le hx.le) (radProf_rot δ)
  have hshift :
      (∫ x, diskHarmonicKernel L x y * radBump δ hδ.le u x) =
      ∫ x, diskHarmonicKernel L (u + x) y * radProf δ x := by
    rw [← integral_add_left_eq_self
      (fun x => diskHarmonicKernel L x y * radBump δ hδ.le u x) u]
    congr 1
    funext x
    simp [radBump_apply]
  rw [hshift]
  exact hmv

theorem integral_diskHarmonicKernel_radBump_right
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {u y : ℂ} (hu : ‖u‖ + δ < r) (hy : ‖y‖ < L) :
    ∫ x, diskHarmonicKernel L y x * radBump δ hδ.le u x =
      diskHarmonicKernel L y u * ∫ x, radProf δ x := by
  simpa only [diskHarmonicKernel_comm] using
    integral_diskHarmonicKernel_radBump_left hL hr hrL hδ hu hy

end SupercriticalConformalCovariance.TV
