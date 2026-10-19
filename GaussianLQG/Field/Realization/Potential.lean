import GaussianLQG.Core.Defs
import GaussianLQG.Energy.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Hölder continuity of the potential of a measure with a ball-mass bound

For a finite measure `ν` on `ℂ` with `ν(B_r(u)) ≤ C r^α` (`0 < r ≤ 1`) and compact support, the
potential `G_ν(z) = ∫ G(z, w) ν(dw)` of the kernel `kernelG` is `s`-Hölder for every
`0 < s ≤ 1` with `s < α` (`abs_potG_sub_le`). This is the estimate behind the `L²` convergence rate of
mollified pairings (blueprint Lemma 1.10 and Lemma 2.4, "coupling").

* `lintegral_rpow_neg_le`: `∫ |z - w|^{-s} ν(dw) ≤ ν(ℂ) + C s / (α - s)` (layer-cake formula);
* `abs_log_sub_log_le`: `|log a - log b| ≤ |a - b|^s (a^{-s} + b^{-s}) / s`;
* `abs_potG_sub_le`: `|G_ν(z) - G_ν(z')| ≤ K |z - z'|^s` for `|z - z'| ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace GaussianLQG
namespace Realization

/-- The ball-mass bound `ν(B_r(u)) ≤ C r^α` for `0 < r ≤ 1`. -/
def BallBound (ν : Measure ℂ) (C α : ℝ) : Prop :=
  ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (ν (ball u r)).toReal ≤ C * r ^ α

variable {ν : Measure ℂ} {C α : ℝ}

lemma BallBound.measure_ball_le [IsFiniteMeasure ν] (hb : BallBound ν C α) (u : ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) : ν (ball u r) ≤ ENNReal.ofReal (C * r ^ α) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν (ball u r))]
  exact ENNReal.ofReal_le_ofReal (hb u r hr hr1)

lemma BallBound.nonneg (hb : BallBound ν C α) : 0 ≤ C := by
  have := hb 0 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at this
  exact ENNReal.toReal_nonneg.trans this

lemma BallBound.measure_singleton [IsFiniteMeasure ν] (hb : BallBound ν C α) (hα : 0 < α)
    (z : ℂ) : ν {z} = 0 := by
  have hle : ∀ r : ℝ, 0 < r → r ≤ 1 → ν {z} ≤ ENNReal.ofReal (C * r ^ α) := fun r hr hr1 =>
    (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb.measure_ball_le z hr hr1)
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ α)) (𝓝[>] 0) (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h : Tendsto (fun r : ℝ => r ^ α) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
      rw [Real.zero_rpow hα.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    simpa using h.const_mul C
  refine le_antisymm (ge_of_tendsto hlim ?_) (zero_le)
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  exact hle r hr.1 hr.2

/-! ### Negative moments -/

lemma setOf_lt_rpow_neg_subset {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : ℂ) :
    {w : ℂ | t < ‖z - w‖ ^ (-s)} ⊆ ball z (t ^ (-s⁻¹)) := by
  intro w hw
  simp only [mem_ofPred_eq] at hw
  rw [mem_ball, dist_eq_norm, norm_sub_rev]
  set x := ‖z - w‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  rcases hx0.lt_or_eq with hxpos | hxzero
  · have h1 : (x ^ (-s)) ^ (-s⁻¹) < t ^ (-s⁻¹) :=
      Real.rpow_lt_rpow_of_neg ht hw (by simpa using hs)
    rwa [← Real.rpow_mul hx0, show -s * -s⁻¹ = 1 by field_simp, Real.rpow_one] at h1
  · rw [← hxzero, Real.zero_rpow (by simpa using hs.ne')] at hw
    exact absurd hw (not_lt.mpr ht.le)

/-- **Negative moments by the layer-cake formula.** -/
theorem lintegral_rpow_neg_le [IsFiniteMeasure ν] (hb : BallBound ν C α) {s : ℝ} (hs : 0 < s)
    (hsα : s < α) (z : ℂ) :
    ∫⁻ w, ENNReal.ofReal (‖z - w‖ ^ (-s)) ∂ν ≤
      ENNReal.ofReal (ν.real univ + C * (s / (α - s))) := by
  have hC := hb.nonneg
  have hmeas : Measurable fun w : ℂ => ‖z - w‖ ^ (-s) :=
    (measurable_const.sub measurable_id).norm.pow_const _
  rw [lintegral_eq_lintegral_meas_lt ν
    (Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg _) _) hmeas.aemeasurable]
  have hsplit : ∫⁻ t in Ioi (0 : ℝ), ν {w | t < ‖z - w‖ ^ (-s)} ≤
      (∫⁻ t in Ioc (0 : ℝ) 1, ν univ) +
        ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (C * t ^ (-(α / s))) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), lintegral_union measurableSet_Ioi
      (Ioc_disjoint_Ioi le_rfl)]
    have h1 : ∫⁻ t in Ioc (0 : ℝ) 1, ν {w | t < ‖z - w‖ ^ (-s)} ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ν univ :=
      setLIntegral_mono' (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) fun t _ =>
        measure_mono (μ := ν) (subset_univ _)
    refine add_le_add h1 (setLIntegral_mono' (measurableSet_Ioi (a := (1 : ℝ))) fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hr0 : 0 < t ^ (-s⁻¹) := Real.rpow_pos_of_pos ht0 _
    have hr1 : t ^ (-s⁻¹) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt ht) (by simpa using (inv_pos.mpr hs).le)
    refine (measure_mono (setOf_lt_rpow_neg_subset hs ht0 z)).trans
      ((hb.measure_ball_le z hr0 hr1).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
    rw [← Real.rpow_mul ht0.le]
    congr 2
    field_simp
  refine hsplit.trans (le_of_eq ?_)
  have hαs1 : -(α / s) < -1 := by
    have : 1 < α / s := (one_lt_div hs).mpr hsα
    linarith
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-(α / s))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hαs1 one_pos).const_mul C
  have hval : ∫ t in Ioi (1 : ℝ), C * t ^ (-(α / s)) = C * (s / (α - s)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hαs1 one_pos, Real.one_rpow]
    have hαs : α - s ≠ 0 := by linarith
    have hs0 : s ≠ 0 := hs.ne'
    have h1 : -(α / s) + 1 ≠ 0 := by linarith
    congr 1
    rw [div_eq_div_iff h1 hαs]
    field_simp
    ring
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
    ← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => mul_nonneg hC (Real.rpow_nonneg (lt_trans one_pos ht).le _))),
    hval, ← ENNReal.ofReal_toReal (measure_ne_top ν univ),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hC (div_nonneg hs.le (by linarith)))]
  rfl

/-- The negative-moment bound `ν(ℂ) + C s / (α - s)`. -/
def negMoment (ν : Measure ℂ) (C α s : ℝ) : ℝ := ν.real univ + C * (s / (α - s))

lemma negMoment_nonneg (hb : BallBound ν C α) {s : ℝ} (hs : 0 < s) (hsα : s < α) :
    0 ≤ negMoment ν C α s :=
  add_nonneg measureReal_nonneg (mul_nonneg hb.nonneg (div_nonneg hs.le (by linarith)))

lemma measurable_rpow_neg_norm (s : ℝ) (z : ℂ) : Measurable fun w : ℂ => ‖z - w‖ ^ (-s) :=
  (measurable_const.sub measurable_id).norm.pow_const _

theorem integrable_rpow_neg [IsFiniteMeasure ν] (hb : BallBound ν C α) {s : ℝ} (hs : 0 < s)
    (hsα : s < α) (z : ℂ) : Integrable (fun w => ‖z - w‖ ^ (-s)) ν := by
  refine ⟨(measurable_rpow_neg_norm s z).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg _) _)]
  exact (lintegral_rpow_neg_le hb hs hsα z).trans_lt ENNReal.ofReal_lt_top

theorem integral_rpow_neg_le [IsFiniteMeasure ν] (hb : BallBound ν C α) {s : ℝ} (hs : 0 < s)
    (hsα : s < α) (z : ℂ) : ∫ w, ‖z - w‖ ^ (-s) ∂ν ≤ negMoment ν C α s := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg _) _)
    (measurable_rpow_neg_norm s z).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (negMoment_nonneg hb hs hsα)
    (lintegral_rpow_neg_le hb hs hsα z)

/-! ### An elementary inequality for the logarithm -/

lemma log_one_add_le_rpow_div {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.log (1 + x) ≤ x ^ s / s := by
  have h1 : (1 + x) ^ s ≤ 1 + x ^ s := by
    have := Real.rpow_add_le_add_rpow zero_le_one hx hs.le hs1
    rwa [Real.one_rpow] at this
  have h2 : Real.log ((1 + x) ^ s) ≤ x ^ s := by
    refine (Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) h1).trans ?_
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x ^ s by
      have := Real.rpow_nonneg hx s; linarith)
    linarith
  rw [Real.log_rpow (by linarith)] at h2
  rw [le_div_iff₀ hs]
  linarith

/-- `|log a - log b| ≤ |a - b|^s (a^{-s} + b^{-s}) / s` for `a, b > 0`, `0 < s ≤ 1`. -/
lemma abs_log_sub_log_le {a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hs1 : s ≤ 1) :
    |Real.log a - Real.log b| ≤ |a - b| ^ s * (a ^ (-s) + b ^ (-s)) / s := by
  wlog hab : a ≤ b generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    rwa [abs_sub_comm (Real.log b), abs_sub_comm b, add_comm (b ^ (-s))] at this
  have hx : 0 ≤ (b - a) / a := div_nonneg (by linarith) ha.le
  have hlog : Real.log b - Real.log a = Real.log (1 + (b - a) / a) := by
    rw [← Real.log_div hb.ne' ha.ne']
    congr 1
    field_simp
    ring
  rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.log_le_log ha hab]), hlog,
    abs_sub_comm, abs_of_nonneg (by linarith)]
  refine (log_one_add_le_rpow_div hx hs hs1).trans ?_
  rw [Real.div_rpow (by linarith) ha.le, div_eq_mul_inv ((b - a) ^ s),
    ← Real.rpow_neg ha.le]
  have hbs : 0 ≤ b ^ (-s) := Real.rpow_nonneg hb.le _
  have hba : 0 ≤ (b - a) ^ s := Real.rpow_nonneg (by linarith) _
  refine div_le_div_of_nonneg_right ?_ hs.le
  nlinarith

/-! ### The logarithmic potential is Hölder -/

lemma measurable_log_norm_sub (z : ℂ) : Measurable fun w : ℂ => Real.log ‖z - w‖ :=
  Real.measurable_log.comp (measurable_const.sub measurable_id).norm

/-- **Hölder bound for the logarithmic potential.** -/
theorem integral_abs_log_sub_le [IsFiniteMeasure ν] (hb : BallBound ν C α) (hα : 0 < α)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hsα : s < α) (z z' : ℂ) :
    Integrable (fun w => |Real.log ‖z - w‖ - Real.log ‖z' - w‖|) ν ∧
      ∫ w, |Real.log ‖z - w‖ - Real.log ‖z' - w‖| ∂ν ≤
        ‖z - z'‖ ^ s * (2 * negMoment ν C α s) / s := by
  set g : ℂ → ℝ := fun w => ‖z - z'‖ ^ s * (‖z - w‖ ^ (-s) + ‖z' - w‖ ^ (-s)) / s with hg
  have hgi : Integrable g ν :=
    (((integrable_rpow_neg hb hs hsα z).add (integrable_rpow_neg hb hs hsα z')).const_mul
      _).div_const _
  have hae : ∀ᵐ w ∂ν, |Real.log ‖z - w‖ - Real.log ‖z' - w‖| ≤ g w := by
    have h1 : ∀ᵐ w ∂ν, w ≠ z := by
      rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
      exact hb.measure_singleton hα z
    have h2 : ∀ᵐ w ∂ν, w ≠ z' := by
      rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
      exact hb.measure_singleton hα z'
    filter_upwards [h1, h2] with w hw hw'
    have ha : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw))
    have ha' : 0 < ‖z' - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw'))
    refine (abs_log_sub_log_le ha ha' hs hs1).trans ?_
    simp only [hg]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hs.le
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hs.le
    have := abs_norm_sub_norm_le (z - w) (z' - w)
    rwa [sub_sub_sub_cancel_right] at this
  have hmeas : AEStronglyMeasurable (fun w => |Real.log ‖z - w‖ - Real.log ‖z' - w‖|) ν :=
    (continuous_abs.measurable.comp ((measurable_log_norm_sub z).sub
      (measurable_log_norm_sub z'))).aestronglyMeasurable
  have hint : Integrable (fun w => |Real.log ‖z - w‖ - Real.log ‖z' - w‖|) ν :=
    hgi.mono' hmeas (by
      filter_upwards [hae] with w hw
      rwa [Real.norm_eq_abs, abs_abs])
  refine ⟨hint, ?_⟩
  calc ∫ w, |Real.log ‖z - w‖ - Real.log ‖z' - w‖| ∂ν ≤ ∫ w, g w ∂ν :=
        integral_mono_ae hint hgi hae
    _ = ‖z - z'‖ ^ s * ((∫ w, ‖z - w‖ ^ (-s) ∂ν) + ∫ w, ‖z' - w‖ ^ (-s) ∂ν) / s := by
        simp only [hg]
        rw [integral_div, integral_const_mul,
          integral_add (integrable_rpow_neg hb hs hsα z) (integrable_rpow_neg hb hs hsα z')]
    _ ≤ ‖z - z'‖ ^ s * (2 * negMoment ν C α s) / s := by
        have h1 := integral_rpow_neg_le hb hs hsα z
        have h2 := integral_rpow_neg_le hb hs hsα z'
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hs.le
        linarith

/-! ### The potential of the kernel `G` -/

/-- The potential `G_ν(z) = ∫ G(z, w) ν(dw)` of the kernel `kernelG`. -/
def potG (ν : Measure ℂ) (z : ℂ) : ℝ := ∫ w, kernelG z w ∂ν

lemma abs_log_le_rpow_neg_add {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    |Real.log x| ≤ x ^ (-s) / s + x := by
  rcases hx.lt_or_eq with hx0 | hx0
  · rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : Real.log x ≤ 0 := Real.log_nonpos hx hx1
      rw [abs_of_nonpos h1]
      have h2 := Real.log_le_rpow_div (inv_nonneg.mpr hx) hs
      rw [Real.log_inv, Real.inv_rpow hx, ← Real.rpow_neg hx] at h2
      linarith
    · have h1 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      rw [abs_of_nonneg h1]
      have h2 := Real.log_le_sub_one_of_pos hx0
      have h3 : 0 ≤ x ^ (-s) / s := div_nonneg (Real.rpow_nonneg hx _) hs.le
      linarith
  · rw [← hx0, Real.log_zero, abs_zero, Real.zero_rpow (by simpa using hs.ne'), zero_div,
      add_zero]

lemma abs_log_max_one_sub_le (a b : ℝ) :
    |Real.log (max 1 a) - Real.log (max 1 b)| ≤ |a - b| := by
  wlog hab : max 1 b ≤ max 1 a generalizing a b
  · have := this b a (le_of_not_ge hab)
    rwa [abs_sub_comm, abs_sub_comm b] at this
  have h1 : (0 : ℝ) < max 1 b := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [abs_of_nonneg (by linarith [Real.log_le_log h1 hab])]
  have h2 : Real.log (max 1 a) - Real.log (max 1 b) ≤ max 1 a / max 1 b - 1 := by
    rw [← Real.log_div (by linarith) h1.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) h1)
  have h3 : max 1 a / max 1 b - 1 ≤ max 1 a - max 1 b := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]
    have : 1 ≤ max 1 b := le_max_left _ _
    nlinarith
  have h4 : max 1 a - max 1 b ≤ |a - b| := by
    have := abs_max_sub_max_le_abs a b 1
    rw [max_comm a, max_comm b] at this
    exact (le_abs_self _).trans this
  linarith

variable {R : ℝ}

theorem integrable_log_norm_sub [IsFiniteMeasure ν] (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) (z : ℂ) :
    Integrable (fun w => Real.log ‖z - w‖) ν := by
  set s := min α 1 / 2 with hsdef
  have hs : 0 < s := by positivity
  have hsα : s < α := by
    have : min α 1 ≤ α := min_le_left _ _
    have : 0 < min α 1 := lt_min hα one_pos
    linarith
  refine ((integrable_rpow_neg hb hs hsα z).div_const s |>.add
    (integrable_const (‖z‖ + R))).mono' (measurable_log_norm_sub z).aestronglyMeasurable ?_
  filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hR] with w hw
  rw [Real.norm_eq_abs]
  refine (abs_log_le_rpow_neg_add (norm_nonneg _) hs).trans ?_
  have : ‖z - w‖ ≤ ‖z‖ + R := (norm_sub_le _ _).trans (by linarith)
  simp only [Pi.add_apply]
  linarith

theorem integrable_kernelG [IsFiniteMeasure ν] (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) (z : ℂ) : Integrable (kernelG z) ν := by
  have h := ((integrable_log_norm_sub hb hα hR z).neg.add
    (integrable_const (Real.log (max 1 ‖z‖)))).add (integrable_log_max_one_norm hR)
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [kernelG, Pi.add_apply, Pi.neg_apply]

/-- The Hölder constant of the potential. -/
def holderK (ν : Measure ℂ) (C α s : ℝ) : ℝ := 2 * negMoment ν C α s / s + ν.real univ

lemma holderK_nonneg (hb : BallBound ν C α) {s : ℝ} (hs : 0 < s) (hsα : s < α) :
    0 ≤ holderK ν C α s :=
  add_nonneg (div_nonneg (mul_nonneg zero_le_two (negMoment_nonneg hb hs hsα)) hs.le)
    measureReal_nonneg

/-- **The potential `G_ν` is `s`-Hölder.** -/
theorem abs_potG_sub_le [IsFiniteMeasure ν] (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hsα : s < α)
    {z z' : ℂ} (hzz : ‖z - z'‖ ≤ 1) :
    |potG ν z - potG ν z'| ≤ holderK ν C α s * ‖z - z'‖ ^ s := by
  obtain ⟨hint, hbound⟩ := integral_abs_log_sub_le hb hα hs hs1 hsα z z'
  set D : ℝ := Real.log (max 1 ‖z‖) - Real.log (max 1 ‖z'‖) with hD
  have hdiff : ∀ w, kernelG z w - kernelG z' w = -(Real.log ‖z - w‖ - Real.log ‖z' - w‖) + D :=
    fun w => by simp only [kernelG, hD]; ring
  have hsub : potG ν z - potG ν z' =
      ∫ w, (-(Real.log ‖z - w‖ - Real.log ‖z' - w‖) + D) ∂ν := by
    simp only [potG]
    rw [← integral_sub (integrable_kernelG hb hα hR z) (integrable_kernelG hb hα hR z')]
    exact integral_congr_ae (Eventually.of_forall hdiff)
  have hlogint : Integrable (fun w => Real.log ‖z - w‖ - Real.log ‖z' - w‖) ν :=
    (integrable_log_norm_sub hb hα hR z).sub (integrable_log_norm_sub hb hα hR z')
  have hD1 : |D| ≤ ‖z - z'‖ :=
    (abs_log_max_one_sub_le _ _).trans (abs_norm_sub_norm_le z z')
  have hpow : ‖z - z'‖ ≤ ‖z - z'‖ ^ s := by
    rcases (norm_nonneg (z - z')).lt_or_eq with h0 | h0
    · have := Real.rpow_le_rpow_of_exponent_ge h0 hzz hs1
      rwa [Real.rpow_one] at this
    · rw [← h0, Real.zero_rpow hs.ne']
  rw [hsub]
  calc |∫ w, (-(Real.log ‖z - w‖ - Real.log ‖z' - w‖) + D) ∂ν|
      ≤ ∫ w, |-(Real.log ‖z - w‖ - Real.log ‖z' - w‖) + D| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, (|Real.log ‖z - w‖ - Real.log ‖z' - w‖| + |D|) ∂ν := by
        refine integral_mono (hlogint.neg.add (integrable_const D)).abs
          (hint.add (integrable_const _)) fun w => ?_
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ = (∫ w, |Real.log ‖z - w‖ - Real.log ‖z' - w‖| ∂ν) + ν.real univ * |D| := by
        rw [integral_add hint (integrable_const _), integral_const, smul_eq_mul]
    _ ≤ ‖z - z'‖ ^ s * (2 * negMoment ν C α s) / s + ν.real univ * ‖z - z'‖ ^ s := by
        refine add_le_add hbound (mul_le_mul_of_nonneg_left (hD1.trans hpow) measureReal_nonneg)
    _ = holderK ν C α s * ‖z - z'‖ ^ s := by
        simp only [holderK]; ring

theorem continuous_potG [IsFiniteMeasure ν] (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) : Continuous (potG ν) := by
  set s := min α 1 / 2 with hsdef
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    have : min α 1 ≤ 1 := min_le_right _ _
    linarith
  have hsα : s < α := by
    have : min α 1 ≤ α := min_le_left _ _
    have : 0 < min α 1 := lt_min hα one_pos
    linarith
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hK := holderK_nonneg hb hs hsα
  have hlim : Tendsto (fun z : ℂ => holderK ν C α s * ‖z - z₀‖ ^ s) (𝓝 z₀) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_id (x := 𝓝 z₀))
    have h2 := (h1.rpow_const (Or.inr hs.le)).const_mul (holderK ν C α s)
    rwa [Real.zero_rpow hs.ne', mul_zero] at h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
  rw [mem_ball, dist_eq_norm] at hz
  rw [Real.norm_eq_abs]
  exact abs_potG_sub_le hb hα hR hs hs1 hsα hz.le

/-! ## Compatibility names (cleanup W15) -/

alias ae_norm_le := ae_norm_le_of_compl_closedBall_eq_zero

theorem integrable_log_max_norm [IsFiniteMeasure ν] (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) :
    Integrable (fun w => Real.log (max 1 ‖w‖)) ν :=
  integrable_log_max_one_norm hR

end Realization
end GaussianLQG
