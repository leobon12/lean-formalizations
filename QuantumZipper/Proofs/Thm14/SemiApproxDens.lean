import QuantumZipper.Proofs.Thm14.FcRPairSemi
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# SEMI-APPROX, part 1: the polar-product smoothings of a semicircle

For a real centre `c`, a radius `s > 0` and `j : ℕ` we define (own elementary construction,
see `handoff/FCR-PAIR.md`)

  `ψ_j(z) = a((‖z−c‖−s)/ε_j)/ε_j · φ_j(Im(z−c)/‖z−c‖) / (‖z−c‖ Z_j)`,

with `a` a fixed smooth bump on `ℝ` of mass one supported in `(-1,1)`, `ε_j = s/(4(j+1))`,
`φ_j(x) = smoothTransition((j+2)x − 1)` and `Z_j = ∫_{(0,π)} φ_j(sin θ) dθ`. In polar
coordinates around `c`, `r ψ_j(c + r e^{iθ}) = a((r−s)/ε_j)/ε_j · φ_j(sin θ)/Z_j`.

This file: the scalar ingredients (`saA`, `saAng`, `saZ`) and the test function `saTF`
(smooth, compactly supported in `ℍ`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

/-- The fixed bump on `ℝ` (radii `1/2`, `1`). -/
def saBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The radial profile `a`: smooth, `≥ 0`, mass one, support `(-1,1)`. -/
def saA (t : ℝ) : ℝ := saBump.normed volume t

/-- The angular profile `φ_j(sin θ)`. -/
def saAng (j : ℕ) (θ : ℝ) : ℝ := Real.smoothTransition (((j : ℝ) + 2) * Real.sin θ - 1)

/-- The angular normalization `Z_j`. -/
def saZ (j : ℕ) : ℝ := ∫ θ in Ioo 0 π, saAng j θ

/-- The radial width `ε_j = s/(4(j+1))`. -/
def saEps (s : ℝ) (j : ℕ) : ℝ := s / (4 * ((j : ℝ) + 1))

/-- The density `ψ_j`. -/
def saPsi (c s : ℝ) (j : ℕ) (z : ℂ) : ℝ :=
  saA ((‖z - c‖ - s) / saEps s j) / saEps s j *
    Real.smoothTransition (((j : ℝ) + 2) * (z - c).im / ‖z - c‖ - 1) / (‖z - c‖ * saZ j)

/-! ## The radial bump -/

theorem saA_nonneg (t : ℝ) : 0 ≤ saA t := saBump.nonneg_normed t

theorem saA_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) saA := saBump.contDiff_normed

theorem saA_continuous : Continuous saA := saBump.continuous_normed

theorem saA_integral : ∫ t, saA t = 1 := saBump.integral_normed

theorem saA_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : saA t = 0 := by
  by_contra h
  have : t ∈ Function.support (saBump.normed volume) := h
  rw [saBump.support_normed_eq] at this
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
  exact absurd ht (not_le.2 (by simpa [saBump] using this))

theorem exists_saA_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, saA t ≤ M := by
  obtain ⟨M, hM⟩ := saA_continuous.bounded_above_of_compact_support saBump.hasCompactSupport_normed
  exact ⟨max M 0, le_max_right _ _, fun t =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM t).trans (le_max_left _ _))⟩

/-! ## The angular profile and its normalization -/

theorem saAng_nonneg (j : ℕ) (θ : ℝ) : 0 ≤ saAng j θ := Real.smoothTransition.nonneg _

theorem saAng_le_one (j : ℕ) (θ : ℝ) : saAng j θ ≤ 1 := Real.smoothTransition.le_one _

theorem saAng_continuous (j : ℕ) : Continuous (saAng j) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

theorem saAng_eq_zero (j : ℕ) {θ : ℝ} (h : Real.sin θ ≤ 0) : saAng j θ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [(j.cast_nonneg : (0:ℝ) ≤ j)])

theorem saAng_mono {j k : ℕ} (hjk : j ≤ k) {θ : ℝ} (h : 0 ≤ Real.sin θ) :
    saAng j θ ≤ saAng k θ := by
  refine Real.smoothTransition.monotone ?_
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  nlinarith

theorem saAng_eventually_one {θ : ℝ} (h : 0 < Real.sin θ) :
    ∀ᶠ j : ℕ in atTop, saAng j θ = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / Real.sin θ)
  refine eventually_atTop.2 ⟨N, fun j hj => Real.smoothTransition.one_of_one_le ?_⟩
  have hj : (N : ℝ) ≤ j := by exact_mod_cast hj
  have : 2 < (j : ℝ) * Real.sin θ := by
    rw [div_lt_iff₀ h] at hN; nlinarith
  nlinarith

theorem saAng_integrableOn (j : ℕ) : IntegrableOn (saAng j) (Ioo 0 π) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (saAng_continuous j).aestronglyMeasurable
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (saAng_nonneg j θ)]
  exact saAng_le_one j θ

theorem saZ_pos (j : ℕ) : 0 < saZ j := by
  unfold saZ
  rw [integral_pos_iff_support_of_nonneg (fun θ => saAng_nonneg j θ) (saAng_integrableOn j)]
  set S : Set ℝ := Ioo 0 π ∩ {θ | 1 < ((j : ℝ) + 2) * Real.sin θ}
  have hSo : IsOpen S := isOpen_Ioo.inter (isOpen_lt continuous_const (by fun_prop))
  have hSn : S.Nonempty := ⟨π / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, by
    show 1 < ((j : ℝ) + 2) * Real.sin (π / 2)
    rw [Real.sin_pi_div_two]; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]⟩
  have hS : S ⊆ Function.support (saAng j) ∩ Ioo 0 π := fun θ hθ =>
    ⟨(Real.smoothTransition.pos_of_pos (sub_pos.2 hθ.2)).ne', hθ.1⟩
  rw [Measure.restrict_apply' measurableSet_Ioo]
  exact (hSo.measure_pos volume hSn).trans_le (measure_mono hS)

theorem saZ_mono {j k : ℕ} (hjk : j ≤ k) : saZ j ≤ saZ k :=
  setIntegral_mono_on (saAng_integrableOn j) (saAng_integrableOn k) measurableSet_Ioo
    fun θ hθ => saAng_mono hjk (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le

theorem saZ_tendsto : Tendsto saZ atTop (𝓝 π) := by
  have hπ : (∫ θ in Ioo 0 π, (1 : ℝ)) = π := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [← hπ]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun j => (saAng_continuous j).aestronglyMeasurable) (integrable_const _)
    (fun j => ae_of_all _ fun θ => ?_) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (saAng_nonneg j θ)]; exact saAng_le_one j θ
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact tendsto_const_nhds.congr' ((saAng_eventually_one
      (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)).mono fun j h => h.symm)

/-! ## The density is a test function on `ℍ` -/

theorem saEps_pos {s : ℝ} (hs : 0 < s) (j : ℕ) : 0 < saEps s j := by
  unfold saEps; positivity

theorem saEps_le {s : ℝ} (hs : 0 < s) (j : ℕ) : saEps s j ≤ s / 4 := by
  unfold saEps
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [(j.cast_nonneg : (0:ℝ) ≤ j)]

theorem saPsi_nonneg (c s : ℝ) (hs : 0 < s) (j : ℕ) (z : ℂ) : 0 ≤ saPsi c s j z := by
  unfold saPsi
  have := saEps_pos hs j
  have := saZ_pos j
  have := saA_nonneg ((‖z - c‖ - s) / saEps s j)
  have := Real.smoothTransition.nonneg (((j : ℝ) + 2) * (z - c).im / ‖z - c‖ - 1)
  positivity

/-- Where `ψ_j ≠ 0`: `|‖z−c‖ − s| < ε_j` and `(j+2) Im(z−c) > ‖z−c‖`. -/
theorem saPsi_ne_zero {c s : ℝ} (hs : 0 < s) {j : ℕ} {z : ℂ} (h : saPsi c s j z ≠ 0) :
    |‖z - c‖ - s| < saEps s j ∧ ‖z - c‖ < ((j : ℝ) + 2) * (z - c).im := by
  have he := saEps_pos hs j
  unfold saPsi at h
  have h1 : saA ((‖z - c‖ - s) / saEps s j) ≠ 0 := fun h0 => h (by simp [h0])
  have h2 : Real.smoothTransition (((j : ℝ) + 2) * (z - c).im / ‖z - c‖ - 1) ≠ 0 :=
    fun h0 => h (by rw [h0]; simp)
  have ha : |‖z - c‖ - s| < saEps s j := by
    by_contra hc
    refine h1 (saA_eq_zero ?_)
    rw [abs_div, abs_of_pos he, le_div_iff₀ he, one_mul]
    exact not_lt.1 hc
  refine ⟨ha, ?_⟩
  have hn : 0 < ‖z - c‖ := by
    have := saEps_le hs j; rw [abs_lt] at ha; linarith
  by_contra hc
  refine h2 (Real.smoothTransition.zero_of_nonpos ?_)
  rw [sub_nonpos, div_le_one hn]
  exact not_lt.1 hc

/-- The closed set containing the support of `ψ_j`. -/
theorem saPsi_support_subset {c s : ℝ} (hs : 0 < s) (j : ℕ) :
    Function.support (saPsi c s j) ⊆
      {z : ℂ | s / 2 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ 2 * s ∧ ‖z - c‖ ≤ ((j : ℝ) + 2) * (z - c).im} := by
  intro z hz
  obtain ⟨h1, h2⟩ := saPsi_ne_zero hs hz
  have := saEps_le hs j
  rw [abs_lt] at h1
  exact ⟨by linarith, by linarith, h2.le⟩

theorem saPsi_eventually_zero_near_center {c s : ℝ} (hs : 0 < s) (j : ℕ) :
    saPsi c s j =ᶠ[𝓝 (c : ℂ)] fun _ => 0 := by
  have hb : Metric.ball (c : ℂ) (s / 2) ∈ 𝓝 (c : ℂ) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hb] with z hz
  by_contra h
  have := (saPsi_support_subset hs j h).1
  rw [Metric.mem_ball, dist_eq_norm] at hz
  linarith

theorem saPsi_contDiff (c s : ℝ) (hs : 0 < s) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (saPsi c s j) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z = c
  · subst hz
    exact contDiffAt_const.congr_of_eventuallyEq (saPsi_eventually_zero_near_center hs j)
  · have hz' : z - c ≠ 0 := sub_ne_zero.2 hz
    have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => ‖w - c‖) z :=
      (contDiffAt_norm ℝ hz').comp z (contDiffAt_id.sub contDiffAt_const)
    have hn0 : ‖z - c‖ ≠ 0 := norm_ne_zero_iff.2 hz'
    have him : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => (w - c).im) z :=
      (Complex.imCLM.contDiff.contDiffAt).comp z (contDiffAt_id.sub contDiffAt_const)
    have hZ := (saZ_pos j).ne'
    have he := (saEps_pos hs j).ne'
    unfold saPsi
    refine ContDiffAt.div (ContDiffAt.mul (ContDiffAt.div_const ?_ _) ?_)
      (hn.mul contDiffAt_const) (mul_ne_zero hn0 hZ)
    · exact saA_contDiff.contDiffAt.comp z ((hn.sub contDiffAt_const).div_const _)
    · exact Real.smoothTransition.contDiff.contDiffAt.comp z
        ((((contDiffAt_const.mul him).div hn hn0)).sub contDiffAt_const)

theorem saPsi_tsupport_subset (c s : ℝ) (hs : 0 < s) (j : ℕ) :
    tsupport (saPsi c s j) ⊆
      {z : ℂ | s / 2 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ 2 * s ∧ ‖z - c‖ ≤ ((j : ℝ) + 2) * (z - c).im} := by
  refine closure_minimal (saPsi_support_subset hs j) ?_
  have e : {z : ℂ | s / 2 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ 2 * s ∧ ‖z - c‖ ≤ ((j : ℝ) + 2) * (z - c).im} =
      {z : ℂ | s / 2 ≤ ‖z - c‖} ∩ ({z : ℂ | ‖z - c‖ ≤ 2 * s} ∩
        {z : ℂ | ‖z - c‖ ≤ ((j : ℝ) + 2) * (z - c).im}) := rfl
  rw [e]
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter ((isClosed_le (by fun_prop)
    (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop)))

/-- **The semicircle smoothing `ψ_j` as a test function on `ℍ`.** -/
def saTF (c s : ℝ) (hs : 0 < s) (j : ℕ) : TestFun H :=
  ⟨saPsi c s j, saPsi_contDiff c s hs j, by
    refine HasCompactSupport.intro (isCompact_closedBall (c : ℂ) (2 * s)) fun z hz => ?_
    by_contra h
    refine hz ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (saPsi_support_subset hs j h).2.1, by
    intro z hz
    obtain ⟨h1, -, h3⟩ := saPsi_tsupport_subset c s hs j hz
    show 0 < z.im
    have : (z - c).im = z.im := by simp
    rw [this] at h3
    have : 0 < ((j : ℝ) + 2) * z.im := by linarith
    exact pos_of_mul_pos_right this (by positivity)⟩

end Thm14WDG
end QuantumZipper
