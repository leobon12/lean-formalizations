import GaussianLQG.Metric.Rotation
import LQGMetric.Papers.DFGPS.L2_6

/-!
# Rotation covariance of LFPP (blueprint `prop:metric-facts` (F3), rotation case, first step)

Blueprint Proposition `prop:metric-facts` (F3) for rotations "follows directly from the exact
rotation covariance of LFPP and the convergence of `a_ε⁻¹ D^ε_h`". Here: for `‖a‖ = 1`,

  `D^ε_{h(a·)}(z, w) = D^ε_h(a z, a w)`,

where `D^ε_h = LQGMetric.lfppDistE ξ ε h` (GM (1.4)) and `h(a·) = rotDist a h`
(`⟨h(a·), φ⟩ = ⟨h, φ(a⁻¹·)⟩`).

**The definition of `h*_ε` and the statement for every distribution.** `LQGMetric.heatMollify`
defines `h*_ε(z)` as the limit (junk `0` if it does not exist) of the truncated pairings
`⟨h, p_{ε²/2}(z,·) χ_n⟩`, where the cutoff `χ_n = LQGMetric.cutoff n` is a mathlib `ContDiffBump`.
Its profile `someContDiffBumpBase ℂ` is chosen by `Nonempty.some`: it is only known to be
symmetric under `x ↦ -x`, not radial. The truncations of the rotated field are
`⟨h, p_{ε²/2}(az,·) χ_n(a⁻¹·)⟩`, which differ from those of `h` at `az` by
`⟨h, rotTruncDiff ε²/2 a z n⟩`, a pairing with a test function supported in the annulus
`n + 1 ≤ |x| ≤ n + 2` and of size `O(e^{-n²/ε²})`. For a general distribution these pairings
need not tend to `0` (even when both truncation limits exist), so the identity is not available
for every `h : DistC`. We prove:

* the deterministic reduction `lfppDistE_rotDist_of_heatMollify`: if `(h(a·))*_ε = h*_ε(a ·)`
  then `D^ε_{h(a·)}(z, w) = D^ε_h(az, aw)` for all `z, w` (the change of variables `P ↦ aP` of
  piecewise `C¹` paths, `LQGMetric.DFGPS.lfppInfFn_const_mul`, with `|a| = 1`);
* the deterministic heat-kernel identity `heatMollify_rotDist_of_tendsto` under the hypotheses
  that the defining limit of `h*_ε(a x)` exists and the rotation differences tend to `0`, and the
  resulting `lfppDistE_rotDist_of_tendsto`;
* the identity for **every** distribution when the cutoffs are invariant under the rotation
  (`lfppDistE_rotDist_of_cutoff`), in particular for `a = -1` (`lfppDistE_rotDist_neg_one`);
* the almost sure identity for every whole-plane GFF `h` (any additive constant), at all
  `z, w` simultaneously (`ae_lfppDistE_rotDist`), which is the form used for (F3): the rotation
  differences are a.s. summable by the Gaussian tail bound
  `LQGMetric.IsWholePlaneGFF.ae_summable_abs_of_decay`, and both mollified fields are a.s.
  continuous (`h(a·)` is again a whole-plane GFF, `GaussianLQG.isWholePlaneGFF_rotDist`).

This follows the proof of the scaling and translation identities in `LQGMetric`
(`LQGMetric.DFGPS.ae_heatMollify_affineComp`, `LQGMetric.DFGPS.ae_heatMollify_translate`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.DFGPS

/-! ## The heat kernel and its truncations under a rotation -/

lemma norm_mul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) (x : ℂ) : ‖a * x‖ = ‖x‖ := by
  rw [norm_mul, ha, one_mul]

lemma norm_inv_mul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) (x : ℂ) : ‖a⁻¹ * x‖ = ‖x‖ :=
  norm_mul_of_norm_eq_one (norm_inv_of_norm_eq_one ha) x

/-- The heat kernel is rotation invariant: `p_s(z, a⁻¹ x) = p_s(a z, x)` for `|a| = 1`. -/
lemma heatKernel_rot {a : ℂ} (ha : ‖a‖ = 1) (s : ℝ) (z x : ℂ) :
    heatKernel s z (a⁻¹ * x) = heatKernel s (a * z) x := by
  have e : a * z - x = a * (z - a⁻¹ * x) := by
    rw [mul_sub, mul_inv_cancel_left₀ (ne_zero_of_norm_eq_one ha)]
  unfold heatKernel
  rw [e, norm_mul_of_norm_eq_one ha]

/-- the difference of the two truncations under a rotation: `p_s(a z, ·)(χ_n(a⁻¹ ·) − χ_n)` -/
def rotTruncDiff (s : ℝ) (a z : ℂ) (n : ℕ) : TestC :=
  testRot a (heatTrunc s z n) - heatTrunc s (a * z) n

lemma rotTruncDiff_apply {a : ℂ} (ha : ‖a‖ = 1) (s : ℝ) (z : ℂ) (n : ℕ) (x : ℂ) :
    rotTruncDiff s a z n x = heatKernel s (a * z) x *
      ((cutoff n : ℂ → ℝ) (a⁻¹ * x) - (cutoff n : ℂ → ℝ) x) := by
  show testRot a (heatTrunc s z n) x - heatTrunc s (a * z) n x = _
  rw [testRot_apply (ne_zero_of_norm_eq_one ha), heatTrunc_apply, heatTrunc_apply,
    heatKernel_rot ha]
  ring

lemma abs_rotTruncDiff_le {s : ℝ} (hs : 0 < s) {a : ℂ} (ha : ‖a‖ = 1) (z : ℂ) (n : ℕ) (x : ℂ) :
    |rotTruncDiff s a z n x| ≤
      (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + ‖z‖) * Real.exp (-(n : ℝ)) := by
  rw [rotTruncDiff_apply ha]
  have hnx := norm_inv_mul_of_norm_eq_one ha x
  by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
  · rw [cutoff_eq_one (hnx ▸ hx), cutoff_eq_one hx, sub_self, mul_zero, abs_zero]
    positivity
  push Not at hx
  have hp := heatKernel_nonneg s hs.le (a * z) x
  have hc : |(cutoff n : ℂ → ℝ) (a⁻¹ * x) - (cutoff n : ℂ → ℝ) x| ≤ 1 := by
    have := (cutoff n).nonneg (x := a⁻¹ * x); have := (cutoff n).le_one (x := a⁻¹ * x)
    have := (cutoff n).nonneg (x := x); have := (cutoff n).le_one (x := x)
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hp]
  refine (mul_le_of_le_one_right hp hc).trans ?_
  unfold heatKernel
  rw [mul_assoc _ (Real.exp _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (2 * Real.pi * s)⁻¹)
  refine (exp_neg_sq_div_le' s _ 1 hs one_pos).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have ht : ‖x‖ - ‖z‖ ≤ ‖a * z - x‖ := by
    have := norm_sub_norm_le x (a * z)
    rw [norm_sub_rev, norm_mul_of_norm_eq_one ha] at this
    linarith
  simp only [one_pow, mul_one, div_one]
  linarith

lemma rotTruncDiff_eq_zero {a : ℂ} (ha : ‖a‖ = 1) (s : ℝ) (z : ℂ) (n : ℕ) (x : ℂ)
    (hx : (n : ℝ) + 3 ≤ ‖x‖) : rotTruncDiff s a z n x = 0 := by
  have hnx := norm_inv_mul_of_norm_eq_one ha x
  rw [rotTruncDiff_apply ha, cutoff_eq_zero (by rw [hnx]; linarith),
    cutoff_eq_zero (by linarith), sub_self, mul_zero]

/-- The truncations of the rotated field:
`⟨h(a·), p_s(z,·) χ_n⟩ = ⟨h, p_s(az,·) χ_n⟩ + ⟨h, rotTruncDiff s a z n⟩`. -/
lemma rotDist_heatTrunc (a : ℂ) (h : DistC) (s : ℝ) (z : ℂ) (n : ℕ) :
    rotDist a h (heatTrunc s z n) = h (heatTrunc s (a * z) n) + h (rotTruncDiff s a z n) := by
  rw [rotDist_apply, rotTruncDiff, map_sub]
  ring

/-! ## Deterministic statements -/

/-- **The heat-kernel rotation identity, deterministic form**: if the defining limit of
`h*_ε(a x)` exists and the rotation differences `⟨h, rotTruncDiff⟩` tend to `0`, then
`(h(a·))*_ε(x) = h*_ε(a x)`. -/
theorem heatMollify_rotDist_of_tendsto (a : ℂ) (ε : ℝ) (h : DistC) (x : ℂ)
    (h1 : Tendsto (fun n : ℕ => h (heatTrunc (ε ^ 2 / 2) (a * x) n)) atTop
      (𝓝 (heatMollify ε h (a * x))))
    (h2 : Tendsto (fun n : ℕ => h (rotTruncDiff (ε ^ 2 / 2) a x n)) atTop (𝓝 0)) :
    heatMollify ε (rotDist a h) x = heatMollify ε h (a * x) := by
  have h3 := h1.add h2
  rw [add_zero] at h3
  simp_rw [← rotDist_heatTrunc] at h3
  exact h3.limUnder_eq

/-- **Exact rotation covariance of LFPP, deterministic reduction**: if `|a| = 1` and
`(h(a·))*_ε = h*_ε(a ·)`, then `D^ε_{h(a·)}(z, w) = D^ε_h(a z, a w)` for all `z, w`. -/
theorem lfppDistE_rotDist_of_heatMollify {a : ℂ} (ha : ‖a‖ = 1) (ξ ε : ℝ) (h : DistC)
    (hrot : ∀ x, heatMollify ε (rotDist a h) x = heatMollify ε h (a * x)) (z w : ℂ) :
    lfppDistE ξ ε (rotDist a h) z w = lfppDistE ξ ε h (a * z) (a * w) := by
  rw [lfppDistE_eq_lfppInfFn, lfppDistE_eq_lfppInfFn,
    lfppInfFn_const_mul ξ _ (ne_zero_of_norm_eq_one ha), ha, ENNReal.ofReal_one, one_mul]
  congr 1
  funext x
  exact hrot x

/-- **Exact rotation covariance of LFPP under the convergence hypotheses** of
`heatMollify_rotDist_of_tendsto` at every point. -/
theorem lfppDistE_rotDist_of_tendsto {a : ℂ} (ha : ‖a‖ = 1) (ξ ε : ℝ) (h : DistC)
    (h1 : ∀ x, Tendsto (fun n : ℕ => h (heatTrunc (ε ^ 2 / 2) (a * x) n)) atTop
      (𝓝 (heatMollify ε h (a * x))))
    (h2 : ∀ x, Tendsto (fun n : ℕ => h (rotTruncDiff (ε ^ 2 / 2) a x n)) atTop (𝓝 0))
    (z w : ℂ) :
    lfppDistE ξ ε (rotDist a h) z w = lfppDistE ξ ε h (a * z) (a * w) :=
  lfppDistE_rotDist_of_heatMollify ha ξ ε h
    (fun x => heatMollify_rotDist_of_tendsto a ε h x (h1 x) (h2 x)) z w

/-- If the cutoffs `χ_n` are invariant under the rotation, the truncations of `h(a·)` at `x` are
exactly those of `h` at `a x`, so `(h(a·))*_ε = h*_ε(a ·)` for **every** distribution. -/
theorem heatMollify_rotDist_of_cutoff {a : ℂ} (ha : ‖a‖ = 1)
    (hχ : ∀ (n : ℕ) (x : ℂ), (cutoff n : ℂ → ℝ) (a⁻¹ * x) = (cutoff n : ℂ → ℝ) x) (ε : ℝ)
    (h : DistC) (x : ℂ) : heatMollify ε (rotDist a h) x = heatMollify ε h (a * x) := by
  have e : ∀ n : ℕ, rotDist a h (heatTrunc (ε ^ 2 / 2) x n) =
      h (heatTrunc (ε ^ 2 / 2) (a * x) n) := by
    intro n
    have h0 : rotTruncDiff (ε ^ 2 / 2) a x n = 0 := TestFunction.ext fun y => by
      rw [rotTruncDiff_apply ha, hχ, sub_self, mul_zero]
      rfl
    rw [rotDist_heatTrunc, h0, map_zero, add_zero]
  unfold heatMollify
  simp_rw [e]

/-- **Exact rotation covariance of LFPP for every distribution**, when the cutoffs are invariant
under the rotation. -/
theorem lfppDistE_rotDist_of_cutoff {a : ℂ} (ha : ‖a‖ = 1)
    (hχ : ∀ (n : ℕ) (x : ℂ), (cutoff n : ℂ → ℝ) (a⁻¹ * x) = (cutoff n : ℂ → ℝ) x) (ξ ε : ℝ)
    (h : DistC) (z w : ℂ) :
    lfppDistE ξ ε (rotDist a h) z w = lfppDistE ξ ε h (a * z) (a * w) :=
  lfppDistE_rotDist_of_heatMollify ha ξ ε h (heatMollify_rotDist_of_cutoff ha hχ ε h) z w

/-- **Exact covariance of LFPP under `x ↦ -x`, for every distribution** (the cutoffs are
symmetric). -/
theorem lfppDistE_rotDist_neg_one (ξ ε : ℝ) (h : DistC) (z w : ℂ) :
    lfppDistE ξ ε (rotDist (-1) h) z w = lfppDistE ξ ε h (-1 * z) (-1 * w) := by
  have ha : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
  refine lfppDistE_rotDist_of_cutoff ha (fun n x => ?_) ξ ε h z w
  rw [inv_neg, inv_one, neg_one_mul]
  exact (cutoff n).neg x

/-! ## The whole-plane GFF -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **The heat-kernel rotation identity**, a.s. at a fixed point, for a whole-plane GFF:
`(h(a·))*_ε(z) = h*_ε(a z)`. -/
theorem ae_heatMollify_rotDist_at (hh : IsWholePlaneGFF h P) {ε : ℝ} (hε : ε ≠ 0) {a : ℂ}
    (ha : ‖a‖ = 1) (z : ℂ) :
    ∀ᵐ ω ∂P, heatMollify ε (rotDist a (h ω)) z = heatMollify ε (h ω) (a * z) := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have h1 := hh.ae_tendsto_heatMollify ε hε (a * z)
  have h3 := hh.ae_summable_abs_of_decay (fun n => rotTruncDiff (ε ^ 2 / 2) a z n)
    (by positivity) (fun n w => abs_rotTruncDiff_le hs ha z n w)
    (fun n w hw => rotTruncDiff_eq_zero ha _ z n w hw)
  filter_upwards [h1, h3] with ω hω1 hω3
  exact heatMollify_rotDist_of_tendsto a ε (h ω) z hω1 hω3.of_abs.tendsto_atTop_zero

/-- **The heat-kernel rotation identity**, a.s. at all points simultaneously (both sides are a.s.
continuous). -/
theorem ae_heatMollify_rotDist (hh : IsWholePlaneGFF h P) {ε : ℝ} (hε : ε ≠ 0) {a : ℂ}
    (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ z, heatMollify ε (rotDist a (h ω)) z = heatMollify ε (h ω) (a * z) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hall := (ae_ball_iff hSc).2 fun z _ => ae_heatMollify_rotDist_at hh hε ha z
  have hc1 := (isWholePlaneGFF_rotDist hh ha).ae_tendstoLocallyUniformly_heatMollify ε hε
  have hc2 := hh.ae_tendstoLocallyUniformly_heatMollify ε hε
  filter_upwards [hall, hc1, hc2] with ω hω h1 h2
  have := Continuous.ext_on hSd h1.2 (h2.2.comp (continuous_const.mul continuous_id))
    fun z hz => hω z hz
  exact fun z => congrFun this z

/-- **Exact rotation covariance of LFPP for the whole-plane GFF** (first step of blueprint
`prop:metric-facts` (F3), rotation case): for `|a| = 1`, a.s. for all `z, w`,
`D^ε_{h(a·)}(z, w) = D^ε_h(a z, a w)`. -/
theorem ae_lfppDistE_rotDist (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε : ℝ} (hε : ε ≠ 0) {a : ℂ}
    (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ,
      lfppDistE ξ ε (rotDist a (h ω)) z w = lfppDistE ξ ε (h ω) (a * z) (a * w) := by
  filter_upwards [ae_heatMollify_rotDist hh hε ha] with ω hω z w
  exact lfppDistE_rotDist_of_heatMollify ha ξ ε (h ω) hω z w

end GaussianLQG
