import QuantumZipper.Field.Sample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-BEURLING, part 1: the uniform circle measure of a thin horizontal strip

`circleUnif d r {u | |Im u| ≤ ε} ≤ (3/2) √(ε / r)` for `r > 0`, `ε ≥ 0`.

This is the last (elementary) step of the Beurling mass bound: the pulled-back circle points near
the curve are sent by `f_s` into a thin strip around `ℝ`, and a circle of radius `r` spends angle
`O(√(ε/r))` in a strip of width `ε` (the worst case is tangency). Own elementary proof: on each
half-period `[cπ - π/2, cπ + π/2]` Jordan's inequality gives
`|sin x - sin y| ≥ 2 (x - y)² / π²`, so the angles in the strip there form a set of diameter
`≤ π √(ε/r)`, and `[0, 2π)` is covered by three such half-periods.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace QuantumZipper
namespace RTBeur

/-- Jordan-type lower bound for the increment of `sin` on `[-π/2, π/2]`. -/
theorem sq_le_abs_sin_sub {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2))
    (hy : y ∈ Icc (-(π / 2)) (π / 2)) : 2 * (x - y) ^ 2 / π ^ 2 ≤ |sin x - sin y| := by
  have hπ := pi_pos
  set a : ℝ := (x - y) / 2 with ha
  set m : ℝ := (x + y) / 2 with hm
  have hsum : |a| + |m| ≤ π / 2 := by
    rw [ha, hm, abs_div, abs_div, abs_two]
    rcases abs_cases (x - y) with h1 | h1 <;> rcases abs_cases (x + y) with h2 | h2 <;>
      · rw [h1.1, h2.1]; linarith [hx.1, hx.2, hy.1, hy.2]
  have ha2 : |a| ≤ π / 2 := by linarith [abs_nonneg m]
  have hsa : 2 / π * |a| ≤ |sin a| := mul_abs_le_abs_sin ha2
  have hcm : 2 / π * |a| ≤ cos m := by
    have h1 : cos (π / 2 - |a|) ≤ cos |m| :=
      cos_le_cos_of_nonneg_of_le_pi (abs_nonneg m) (by linarith [abs_nonneg a]) (by linarith)
    rw [cos_pi_div_two_sub, cos_abs] at h1
    exact (mul_le_sin (abs_nonneg a) ha2).trans h1
  have hpa : 0 ≤ 2 / π * |a| := by positivity
  rw [sin_sub_sin, abs_mul, abs_mul, abs_two, abs_of_nonneg (hpa.trans hcm)]
  have hprod : (2 / π * |a|) * (2 / π * |a|) ≤ |sin a| * cos m :=
    mul_le_mul hsa hcm hpa (abs_nonneg _)
  have e : 2 * (x - y) ^ 2 / π ^ 2 = 2 * ((2 / π * |a|) * (2 / π * |a|)) := by
    rw [ha]; field_simp; rw [abs_div, abs_two]; ring_nf; rw [sq_abs]; ring
  rw [e]
  linarith

/-- On a half-period, the angles where `|b + r sin θ| ≤ ε` form a set of small diameter. -/
theorem volume_strip_piece_le {b r ε c : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hc : ∀ θ₁ θ₂ : ℝ, |sin θ₁ - sin θ₂| = |sin (θ₁ - c) - sin (θ₂ - c)|) :
    volume {θ : ℝ | θ ∈ Icc (c - π / 2) (c + π / 2) ∧ |b + r * sin θ| ≤ ε} ≤
      ENNReal.ofReal (π * Real.sqrt (ε / r)) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun x hx y hy => ?_)
  rw [edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hπ := pi_pos
  have hmem : ∀ θ ∈ Icc (c - π / 2) (c + π / 2), θ - c ∈ Icc (-(π / 2)) (π / 2) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 := sq_le_abs_sin_sub (hmem x hx.1) (hmem y hy.1)
  rw [← hc] at h1
  have e : x - c - (y - c) = x - y := by ring
  rw [e] at h1
  have h2 : r * |sin x - sin y| ≤ 2 * ε := by
    have e2 : r * |sin x - sin y| = |(b + r * sin x) - (b + r * sin y)| := by
      rw [show (b + r * sin x) - (b + r * sin y) = r * (sin x - sin y) by ring, abs_mul,
        abs_of_pos hr]
    rw [e2]
    exact (abs_sub _ _).trans (by linarith [hx.2, hy.2])
  have h3 : (x - y) ^ 2 ≤ (π * Real.sqrt (ε / r)) ^ 2 := by
    rw [mul_pow, sq_sqrt (div_nonneg hε hr.le)]
    have h4 : 2 * (x - y) ^ 2 / π ^ 2 * r ≤ 2 * ε := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h4
    rw [mul_div_assoc', le_div_iff₀ hr]
    nlinarith
  exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2 |> fun h => by
    rw [abs_le]; exact ⟨(abs_le_of_sq_le_sq' h3 (by positivity)).1, h⟩

/-- The angles in `[0, 2π)` where `|b + r sin θ| ≤ ε` have measure at most `3 π √(ε/r)`. -/
theorem volume_strip_le {b r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) :
    volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |b + r * sin θ| ≤ ε} ≤
      ENNReal.ofReal (3 * (π * Real.sqrt (ε / r))) := by
  have hπ := pi_pos
  have hsub : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |b + r * sin θ| ≤ ε} ⊆
      ({θ : ℝ | θ ∈ Icc (0 - π / 2) (0 + π / 2) ∧ |b + r * sin θ| ≤ ε} ∪
        {θ : ℝ | θ ∈ Icc (π - π / 2) (π + π / 2) ∧ |b + r * sin θ| ≤ ε}) ∪
        {θ : ℝ | θ ∈ Icc (2 * π - π / 2) (2 * π + π / 2) ∧ |b + r * sin θ| ≤ ε} := by
    rintro θ ⟨hθ, hb⟩
    by_cases h1 : θ ≤ π / 2
    · exact Or.inl (Or.inl ⟨⟨by linarith [hθ.1], by linarith⟩, hb⟩)
    by_cases h2 : θ ≤ 3 * π / 2
    · exact Or.inl (Or.inr ⟨⟨by linarith, by linarith⟩, hb⟩)
    · exact Or.inr ⟨⟨by linarith, by linarith [hθ.2]⟩, hb⟩
  have p0 := volume_strip_piece_le (b := b) (c := 0) hr hε fun _ _ => by simp
  have p1 := volume_strip_piece_le (b := b) (c := π) hr hε fun a b => by
    rw [sin_sub_pi, sin_sub_pi, ← abs_neg]; ring_nf
  have p2 := volume_strip_piece_le (b := b) (c := 2 * π) hr hε fun _ _ => by
    rw [sin_sub_two_pi, sin_sub_two_pi]
  have hq : 0 ≤ π * Real.sqrt (ε / r) := by positivity
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (π * Real.sqrt (ε / r)) + ENNReal.ofReal (π * Real.sqrt (ε / r)) +
        ENNReal.ofReal (π * Real.sqrt (ε / r)) := add_le_add (add_le_add p0 p1) p2
    _ = ENNReal.ofReal (3 * (π * Real.sqrt (ε / r))) := by
        rw [← ENNReal.ofReal_add hq hq, ← ENNReal.ofReal_add (by positivity) hq]; ring_nf

theorem circleMap_im_eq (d : ℂ) (r θ : ℝ) : (circleMap d r θ).im = d.im + r * sin θ := by
  simp [circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **The circle measure of a horizontal strip.** -/
theorem circleUnif_strip_le (d : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) :
    circleUnif d r {u : ℂ | |u.im| ≤ ε} ≤ ENNReal.ofReal (3 / 2 * Real.sqrt (ε / r)) := by
  have hπ := pi_pos
  have hG : MeasurableSet {u : ℂ | |u.im| ≤ ε} :=
    measurableSet_le (Complex.continuous_im.abs.measurable) measurable_const
  unfold circleUnif
  rw [Measure.smul_apply, Measure.map_apply (measurable_circleMap d r) hG,
    Measure.restrict_apply' measurableSet_Ico, smul_eq_mul]
  have hset : circleMap d r ⁻¹' {u : ℂ | |u.im| ≤ ε} ∩ Ico 0 (2 * π) =
      {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |d.im + r * sin θ| ≤ ε} := by
    ext θ; simp [circleMap_im_eq, and_comm]
  rw [hset]
  calc (ENNReal.ofReal (2 * π))⁻¹ * volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |d.im + r * sin θ| ≤ ε}
      ≤ (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (3 * (π * Real.sqrt (ε / r))) :=
        by gcongr; exact volume_strip_le hr hε
    _ = ENNReal.ofReal (3 / 2 * Real.sqrt (ε / r)) := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end RTBeur
end QuantumZipper
