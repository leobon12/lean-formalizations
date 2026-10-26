import SupercriticalConformalCovariance.TV.DiskCovariance
import LQGMetric.Papers.GM.S2.SpatialIndepMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric LQGMetric.GM QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- A radial mollifier contained in a disk, regarded as a domain test. -/
def radBumpOnDisk {L δ : ℝ} (hδ : 0 < δ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ + δ < L) : TestOn ⟨ball (0 : ℂ) L, isOpen_ball⟩ :=
  ⟨radBump δ hδ.le u, (radBump δ hδ.le u).contDiff,
   (radBump δ hδ.le u).hasCompactSupport, by
    refine (closure_minimal (t := closedBall u δ) (fun x hx => ?_)
      isClosed_closedBall).trans ?_
    · by_contra hn
      rw [mem_closedBall, dist_eq_norm, not_le] at hn
      exact hx (radProf_eq_zero hδ.le hn.le)
    · intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      change x ∈ ball (0 : ℂ) L
      rw [mem_ball, dist_zero_right]
      have ht := norm_add_le (x - u) u
      rw [sub_add_cancel] at ht
      linarith⟩

theorem radBumpOnDisk_apply {L δ : ℝ} (hδ : 0 < δ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ + δ < L) (x : ℂ) :
    radBumpOnDisk hδ hL u hu x = radBump δ hδ.le u x := rfl

/-- The smooth harmonic kernel evaluated on two radial mollifiers. -/
theorem integral_diskHarmonicKernel_radBump_prod
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {u v : ℂ}
    (hu : ‖u‖ + δ < r) (hv : ‖v‖ + δ < r) :
    (∫ p : ℂ × ℂ,
       radBump δ hδ.le u p.1 * radBump δ hδ.le v p.2 *
         diskHarmonicKernel L p.1 p.2
       ∂((volume : Measure ℂ).prod volume)) =
      diskHarmonicKernel L u v * (∫ x, radProf δ x) ^ 2 := by
  have huL : ‖u‖ + δ < L := hu.trans hrL
  have hvL : ‖v‖ + δ < L := hv.trans hrL
  have hu' : ‖u‖ < L := by linarith
  have hv' : ‖v‖ < L := by linarith
  let φ := radBumpOnDisk hδ hL u huL
  let ψ := radBumpOnDisk hδ hL v hvL
  have hi := integrable_diskHarmonicKernel_test_mul hL φ ψ
  have he : (fun p : ℂ × ℂ =>
      φ p.1 * ψ p.2 * diskHarmonicKernel L p.1 p.2) =
      fun p => radBump δ hδ.le u p.1 * radBump δ hδ.le v p.2 *
        diskHarmonicKernel L p.1 p.2 := by
    funext p
    rfl
  rw [he] at hi
  rw [integral_prod _ hi]
  calc
    (∫ x : ℂ, ∫ y : ℂ,
        radBump δ hδ.le u x * radBump δ hδ.le v y *
          diskHarmonicKernel L x y) =
      ∫ x : ℂ, radBump δ hδ.le u x *
        (diskHarmonicKernel L x v * ∫ y, radProf δ y) := by
          congr 1
          funext x
          by_cases hx : ‖x‖ < L
          · have hk := integral_diskHarmonicKernel_radBump_right hL hr hrL hδ hv hx
            calc
              _ = radBump δ hδ.le u x *
                  ∫ y, diskHarmonicKernel L x y * radBump δ hδ.le v y := by
                    rw [← integral_const_mul]
                    congr 1
                    funext y
                    ring
              _ = _ := by rw [hk]
          · have hzero : radBump δ hδ.le u x = 0 := by
              have hnot : x ∉ ball (0 : ℂ) L := by simpa [mem_ball, dist_zero_right] using hx
              exact φ.zero_on_compl hnot
            simp [hzero]
    _ = (diskHarmonicKernel L u v * ∫ y, radProf δ y) *
        ∫ y, radProf δ y := by
          have hk := integral_diskHarmonicKernel_radBump_left hL hr hrL hδ hu hv'
          calc
            _ = (∫ x, diskHarmonicKernel L x v * radBump δ hδ.le u x) *
                ∫ y, radProf δ y := by
                  rw [← integral_mul_const]
                  congr 1
                  funext x
                  ring
            _ = _ := by rw [hk]
    _ = _ := by ring

/-- The disk harmonic covariance on a difference of two radial mollifiers. -/
theorem integral_diskHarmonicKernel_radDiff
    {L r δ : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) {y : ℂ} (hy : ‖y‖ + δ < r) (h0 : δ < r) :
    let φy := radBumpOnDisk hδ hL y (hy.trans hrL)
    let φ0 := radBumpOnDisk hδ hL 0 (by simpa using h0.trans hrL)
    (∫ p : ℂ × ℂ, (φy p.1 - φ0 p.1) * (φy p.2 - φ0 p.2) *
      diskHarmonicKernel L p.1 p.2
      ∂((volume : Measure ℂ).prod volume)) =
      -Real.log (1 - ‖y‖ ^ 2 / L ^ 2) * (∫ x, radProf δ x) ^ 2 := by
  dsimp
  have h0r : ‖(0 : ℂ)‖ + δ < r := by simpa using h0
  have hyL : ‖y‖ + δ < L := hy.trans hrL
  have h0L : ‖(0 : ℂ)‖ + δ < L := h0r.trans hrL
  let a := radBumpOnDisk hδ hL y hyL
  let b := radBumpOnDisk hδ hL 0 h0L
  have hy' : ‖y‖ < L := by linarith
  have hyy := integral_diskHarmonicKernel_radBump_prod hL hr hrL hδ hy hy
  have hy0 := integral_diskHarmonicKernel_radBump_prod hL hr hrL hδ hy h0r
  have h0y := integral_diskHarmonicKernel_radBump_prod hL hr hrL hδ h0r hy
  have h00 := integral_diskHarmonicKernel_radBump_prod hL hr hrL hδ h0r h0r
  have iyy := integrable_diskHarmonicKernel_test_mul hL a a
  have iy0 := integrable_diskHarmonicKernel_test_mul hL a b
  have i0y := integrable_diskHarmonicKernel_test_mul hL b a
  have i00 := integrable_diskHarmonicKernel_test_mul hL b b
  have he : (fun p : ℂ × ℂ =>
      (a p.1 - b p.1) * (a p.2 - b p.2) * diskHarmonicKernel L p.1 p.2) =
    fun p => (a p.1 * a p.2 * diskHarmonicKernel L p.1 p.2 -
      a p.1 * b p.2 * diskHarmonicKernel L p.1 p.2) -
      b p.1 * a p.2 * diskHarmonicKernel L p.1 p.2 +
      b p.1 * b p.2 * diskHarmonicKernel L p.1 p.2 := by
    funext p
    ring
  change (∫ p : ℂ × ℂ,
    (a p.1 - b p.1) * (a p.2 - b p.2) * diskHarmonicKernel L p.1 p.2
    ∂((volume : Measure ℂ).prod volume)) = _
  rw [he]
  have hlin := integral_add ((iyy.sub iy0).sub i0y) i00
  simp only [Pi.sub_apply] at hlin
  rw [hlin]
  have hlin2 := integral_sub (iyy.sub iy0) i0y
  simp only [Pi.sub_apply] at hlin2
  rw [hlin2]
  have hlin3 := integral_sub iyy iy0
  rw [hlin3]
  change (∫ p, radBump δ hδ.le y p.1 * radBump δ hδ.le y p.2 *
      diskHarmonicKernel L p.1 p.2 ∂((volume : Measure ℂ).prod volume)) -
    (∫ p, radBump δ hδ.le y p.1 * radBump δ hδ.le 0 p.2 *
      diskHarmonicKernel L p.1 p.2 ∂((volume : Measure ℂ).prod volume)) -
    (∫ p, radBump δ hδ.le 0 p.1 * radBump δ hδ.le y p.2 *
      diskHarmonicKernel L p.1 p.2 ∂((volume : Measure ℂ).prod volume)) +
    (∫ p, radBump δ hδ.le 0 p.1 * radBump δ hδ.le 0 p.2 *
      diskHarmonicKernel L p.1 p.2 ∂((volume : Measure ℂ).prod volume)) = _
  rw [hyy, hy0, h0y, h00,
    diskHarmonicKernel_comm L 0 y]
  rw [← diskHarmonicKernel_increment hL hy']
  ring

end SupercriticalConformalCovariance.TV
