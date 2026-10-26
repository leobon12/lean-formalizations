import SupercriticalLQGUniqueness.B2.Median.HeatShift

/-!
# The collar function of Lemma 3.2 (packet P32)

Planning audit `planning/audits/SB1-sections-1-3.md` A12, step 1: `f = B·g(|z|)` with `g`
continuous, `g = 1` on `[0, 3/8] ∪ [5, ∞)`, `g = 0` on `[9/20, 7/2]`, linear in between. Then
`f ≥ 0` is bounded continuous, `f = 0` on a neighbourhood `W = {9/20 < |z| < 7/2}` of
`V = {1/2 ≤ |z| ≤ 3}`, and `f = B` on the closed collars `{1/4 ≤ |z| ≤ 1/3}`, `{6 ≤ |z| ≤ 7}`
and on their neighbourhoods `{|z| < 3/8}`, `{5 < |z| < 8}`.

Its heat mollifications `f*_δ` are nonnegative, at least `B − 1` on the two neighbourhoods of
the collars and at most `β` in absolute value on `W`, for all small `δ` (`collar_heat_eventually`:
uniform convergence `f*_δ → f` on compacts, `B2.Median.tendstoUniformlyOn_heatMollify_fixed`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set Metric
open LQGMetric (heatMollify ofCont)

namespace SupercriticalLFPPAS.Local

/-- The radial profile of the collar function. -/
def collarProfile (r : ℝ) : ℝ :=
  max 0 (min 1 ((9 / 20 - r) * (40 / 3))) + max 0 (min 1 ((r - 7 / 2) * (2 / 3)))

theorem continuous_collarProfile : Continuous collarProfile := by
  unfold collarProfile
  fun_prop

theorem collarProfile_nonneg (r : ℝ) : 0 ≤ collarProfile r :=
  add_nonneg (le_max_left _ _) (le_max_left _ _)

theorem collarProfile_le_two (r : ℝ) : collarProfile r ≤ 2 := by
  unfold collarProfile
  have h1 : max 0 (min 1 ((9 / 20 - r) * (40 / 3))) ≤ 1 :=
    max_le zero_le_one (min_le_left _ _)
  have h2 : max 0 (min 1 ((r - 7 / 2) * (2 / 3))) ≤ 1 :=
    max_le zero_le_one (min_le_left _ _)
  linarith

theorem collarProfile_eq_one_of_le {r : ℝ} (hr : r ≤ 3 / 8) : collarProfile r = 1 := by
  unfold collarProfile
  rw [min_eq_left (by linarith), max_eq_right zero_le_one,
    min_eq_right (by linarith), max_eq_left (by linarith)]
  norm_num

theorem collarProfile_eq_one_of_ge {r : ℝ} (hr : 5 ≤ r) : collarProfile r = 1 := by
  unfold collarProfile
  rw [min_eq_right (by linarith : (9 / 20 - r) * (40 / 3) ≤ 1), max_eq_left (by linarith),
    min_eq_left (by linarith), max_eq_right zero_le_one]
  norm_num

theorem collarProfile_eq_zero {r : ℝ} (hr1 : 9 / 20 ≤ r) (hr2 : r ≤ 7 / 2) :
    collarProfile r = 0 := by
  unfold collarProfile
  rw [min_eq_right (by linarith : (9 / 20 - r) * (40 / 3) ≤ 1), max_eq_left (by linarith),
    min_eq_right (by linarith : (r - 7 / 2) * (2 / 3) ≤ 1), max_eq_left (by linarith)]
  norm_num

/-- The collar function `f(z) = B·g(|z|)`. -/
def collarFn (B : ℝ) : C(ℂ, ℝ) :=
  ⟨fun z => B * collarProfile ‖z‖, continuous_const.mul (continuous_collarProfile.comp continuous_norm)⟩

theorem collarFn_apply (B : ℝ) (z : ℂ) : collarFn B z = B * collarProfile ‖z‖ := rfl

theorem collarFn_nonneg {B : ℝ} (hB : 0 ≤ B) (z : ℂ) : 0 ≤ collarFn B z :=
  mul_nonneg hB (collarProfile_nonneg _)

theorem collarFn_abs_le {B : ℝ} (hB : 0 ≤ B) (z : ℂ) : |collarFn B z| ≤ 2 * B := by
  rw [abs_of_nonneg (collarFn_nonneg hB z), collarFn_apply, mul_comm 2 B]
  exact mul_le_mul_of_nonneg_left (collarProfile_le_two _) hB

theorem collarFn_eq_of_le (B : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3 / 8) : collarFn B z = B := by
  rw [collarFn_apply, collarProfile_eq_one_of_le hz, mul_one]

theorem collarFn_eq_of_ge (B : ℝ) {z : ℂ} (hz : 5 ≤ ‖z‖) : collarFn B z = B := by
  rw [collarFn_apply, collarProfile_eq_one_of_ge hz, mul_one]

theorem collarFn_eq_zero (B : ℝ) {z : ℂ} (hz1 : 9 / 20 ≤ ‖z‖) (hz2 : ‖z‖ ≤ 7 / 2) :
    collarFn B z = 0 := by
  rw [collarFn_apply, collarProfile_eq_zero hz1 hz2, mul_zero]

/-- The heat mollification of the collar function is nonnegative. -/
theorem collar_heat_nonneg {B : ℝ} (hB : 0 ≤ B) (δ : Set.Ioi (0 : ℝ)) (z : ℂ) :
    0 ≤ heatMollify (δ : ℝ) (ofCont (collarFn B)) z :=
  SupercriticalLQGUniqueness.B2.Median.heatMollify_nonneg_of_nonneg (collarFn B) (2 * B)
    (collarFn_abs_le hB) (collarFn_nonneg hB) δ z

/-- **Heat facts for the collar function**: for all small `δ`, `f*_δ ≥ B − 1` on
`{|z| < 3/8} ∪ {5 < |z| < 8}` and `|f*_δ| ≤ β` on `{9/20 < |z| < 7/2}`. -/
theorem collar_heat_eventually {B β : ℝ} (hB : 0 ≤ B) (hβ : 0 < β) :
    ∀ᶠ δ in comap Subtype.val (𝓝 (0 : ℝ)),
      (∀ z : ℂ, ‖z‖ < 3 / 8 ∨ (5 < ‖z‖ ∧ ‖z‖ < 8) →
        B - 1 ≤ heatMollify ((δ : Set.Ioi (0 : ℝ)) : ℝ) (ofCont (collarFn B)) z) ∧
      (∀ z : ℂ, 9 / 20 < ‖z‖ → ‖z‖ < 7 / 2 →
        |heatMollify ((δ : Set.Ioi (0 : ℝ)) : ℝ) (ofCont (collarFn B)) z| ≤ β) := by
  rw [Filter.eventually_iff_seq_eventually]
  intro x hx
  have hx' : Tendsto (fun n => (x n : ℝ)) atTop (𝓝 0) := tendsto_comap_iff.1 hx
  have hU := SupercriticalLQGUniqueness.B2.Median.tendstoUniformlyOn_heatMollify_fixed x hx'
    (collarFn B) (2 * B) (collarFn_abs_le hB) 8 (by norm_num)
  have hev := (Metric.tendstoUniformlyOn_iff.1 hU) (min 1 β) (lt_min one_pos hβ)
  filter_upwards [hev] with n hn
  refine ⟨fun z hz => ?_, fun z hz1 hz2 => ?_⟩
  · have hzb : z ∈ closedBall (0 : ℂ) 8 := by
      rw [mem_closedBall, dist_zero_right]
      rcases hz with hz | hz <;> linarith [hz]
    have hfz : collarFn B z = B := by
      rcases hz with hz | hz
      · exact collarFn_eq_of_le B hz.le
      · exact collarFn_eq_of_ge B hz.1.le
    have hd := hn z hzb
    rw [Real.dist_eq, hfz] at hd
    have h1 := neg_abs_le (B - heatMollify (x n : ℝ) (ofCont (collarFn B)) z)
    have h2 : |B - heatMollify (x n : ℝ) (ofCont (collarFn B)) z| < 1 :=
      lt_of_lt_of_le hd (min_le_left _ _)
    linarith [le_abs_self (B - heatMollify (x n : ℝ) (ofCont (collarFn B)) z)]
  · have hzb : z ∈ closedBall (0 : ℂ) 8 := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hfz : collarFn B z = 0 := collarFn_eq_zero B hz1.le hz2.le
    have hd := hn z hzb
    rw [Real.dist_eq, hfz, zero_sub, abs_neg] at hd
    exact (lt_of_lt_of_le hd (min_le_right _ _)).le

end SupercriticalLFPPAS.Local
