import SupercriticalConformalCovariance.Small.ZoomData
import SupercriticalConformalCovariance.Univalent.KoebeCore

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric TopologicalSpace
namespace SupercriticalConformalCovariance.Small

/-- Global source zoom domains exhaust the plane when centres converge to an
interior point and radii tend to zero. -/
theorem eventually_compact_subset_affinePreimage
    (U : Opens ℂ) {z : ℂ} (hz : z ∈ (U : Set ℂ))
    (zn : ℕ → ℂ) (r : ℕ → ℝ)
    (hzn : Tendsto zn atTop (𝓝 z)) (hr : Tendsto r atTop (𝓝 0))
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ n in atTop, K ⊆ (affinePreimage U (zn n) (r n) : Set ℂ) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp U.isOpen z hz
  obtain ⟨M₀, hM₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let M := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : K ⊆ closedBall (0 : ℂ) M :=
    hM₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hρ : 0 < M + 1 := by linarith
  have hδ2 : 0 < δ / 2 := by positivity
  have hδρ : 0 < δ / (2 * (M + 1)) := by positivity
  have hzsmall : ∀ᶠ n in atTop, dist (zn n) z < δ / 2 :=
    hzn.eventually (Metric.ball_mem_nhds z hδ2)
  have hrsmall : ∀ᶠ n in atTop, |r n| < δ / (2 * (M + 1)) := by
    have ht := hr.eventually (Metric.ball_mem_nhds 0 hδρ)
    filter_upwards [ht] with n hn
    simpa only [Real.dist_eq, sub_zero] using hn
  filter_upwards [hzsmall, hrsmall] with n hn hrn w hw
  have hwM : ‖w‖ ≤ M := by
    simpa only [mem_closedBall, dist_zero_right] using hM hw
  have hscale : ‖(r n : ℂ) * w‖ < δ / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |r n| * ‖w‖ ≤ |r n| * M := mul_le_mul_of_nonneg_left hwM (abs_nonneg _)
      _ ≤ |r n| * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < δ / 2 := by
        have h := mul_lt_mul_of_pos_right hrn hρ
        have heq : δ / (2 * (M + 1)) * (M + 1) = δ / 2 := by
          field_simp
          <;> ring
        simpa only [heq] using h
  have hdist : dist (LQGMetric.affinePt (r n) (zn n) w) z < δ := by
    rw [LQGMetric.affinePt_apply, dist_eq_norm]
    calc
      ‖(r n : ℂ) * w + zn n - z‖ ≤ ‖(r n : ℂ) * w‖ + ‖zn n - z‖ := by
        simpa only [add_sub_assoc] using
          norm_add_le ((r n : ℂ) * w) (zn n - z)
      _ < δ := by
        rw [dist_eq_norm] at hn
        linarith
  exact hδU (mem_ball.2 hdist)

/-- The centred zoom fixes the origin. -/
theorem zoomMap_zero (φ : ℂ → ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    SmallGammaGeodesics.CC.zoomMap φ z r 0 = 0 := by
  simp [SmallGammaGeodesics.CC.zoomMap, hr.ne']

/-- The derivative at the origin of a centred zoom is the original derivative
at its centre. -/
theorem deriv_zoomMap_zero {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : SupercriticalConformalCovariance.IsConformalBijection φ U V)
    {z : ℂ} (hz : z ∈ (U : Set ℂ)) {r : ℝ} (hr : 0 < r) :
    deriv (SmallGammaGeodesics.CC.zoomMap φ z r) 0 = deriv φ z := by
  have hd := hφ.1.differentiableAt (U.isOpen.mem_nhds hz)
  convert SmallGammaGeodesics.CC.deriv_zoomMap hr.ne' (w := 0) (by simpa using hd) using 1
  simp

/-- A failing sequence in a compact subset of the source domain supplies
exactly the expanding disks and derivative limit required by Lemma 3.3. -/
theorem zoom_sequence_tangent_geometry {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : SupercriticalConformalCovariance.IsConformalBijection φ U V)
    {z : ℂ} (hz : z ∈ (U : Set ℂ))
    (zn : ℕ → ℂ) (r : ℕ → ℝ)
    (hznU : ∀ n, zn n ∈ (U : Set ℂ)) (hrpos : ∀ n, 0 < r n)
    (hzn : Tendsto zn atTop (𝓝 z)) (hr : Tendsto r atTop (𝓝 0)) :
    ∃ R : ℕ → ℝ,
      Tendsto R atTop atTop ∧
      (∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ affinePreimage U (zn n) (r n)) ∧
      (∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop,
        K ⊆ (affinePreimage U (zn n) (r n) : Set ℂ)) ∧
      (∀ n, SmallGammaGeodesics.CC.zoomMap φ (zn n) (r n) 0 = 0) ∧
      deriv φ z ≠ 0 ∧
      Tendsto (fun n => deriv (SmallGammaGeodesics.CC.zoomMap φ (zn n) (r n)) 0)
        atTop (𝓝 (deriv φ z)) := by
  have hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop,
      K ⊆ (affinePreimage U (zn n) (r n) : Set ℂ) :=
    eventually_compact_subset_affinePreimage U hz zn r hzn hr
  obtain ⟨S, hSpos, hSlarge, hSsub⟩ := SupercriticalConformalCovariance.Univalent.exhaustion_radii
    (U := fun n => (affinePreimage U (zn n) (r n) : Set ℂ))
    (fun n => (affinePreimage U (zn n) (r n)).isOpen)
    (fun n => by change LQGMetric.affinePt (r n) (zn n) 0 ∈ U
                 simpa [LQGMetric.affinePt_apply] using hznU n)
    hexhaust
  let R : ℕ → ℝ := fun n => S n / 3
  have hRlarge : Tendsto R atTop atTop := by
    have ht := hSlarge.const_mul_atTop (show (0 : ℝ) < 1 / 3 by norm_num)
    simpa only [R, one_div, div_eq_mul_inv, one_mul, mul_comm] using ht
  have hRsub : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ affinePreimage U (zn n) (r n) := by
    intro n
    refine ⟨by dsimp [R]; exact div_pos (hSpos n) (by norm_num), ?_⟩
    intro w hw
    apply hSsub n
    have hlt : 2 * R n < S n := by dsimp [R]; linarith [hSpos n]
    exact mem_ball.2 ((mem_ball.1 hw).trans hlt)
  have hderiv : ContinuousAt (deriv φ) z :=
    ((hφ.1.deriv U.isOpen).continuousOn).continuousAt (U.isOpen.mem_nhds hz)
  have hderivlim : Tendsto (fun n => deriv φ (zn n)) atTop (𝓝 (deriv φ z)) :=
    hderiv.tendsto.comp hzn
  refine ⟨R, hRlarge, hRsub, hexhaust,
    (fun n => zoomMap_zero φ (zn n) (hrpos n)),
    QuantumZipper.CA.deriv_ne_zero_of_injOn U.isOpen hφ.1 hφ.2.injOn hz, ?_⟩
  have heq : (fun n => deriv (SmallGammaGeodesics.CC.zoomMap φ (zn n) (r n)) 0) =
      (fun n => deriv φ (zn n)) := by
    funext n
    exact deriv_zoomMap_zero hφ (hznU n) (hrpos n)
  rw [heq]
  exact hderivlim

end SupercriticalConformalCovariance.Small
