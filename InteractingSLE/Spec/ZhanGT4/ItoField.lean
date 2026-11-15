/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTilde
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cut-off exponential fields: the space-regular random fields of the Itô step

Packet PROVE-ZHAN-GT4-A7. The density `M̃` of (D6) is `exp ℓ(t, W_t)` where `ℓ(t, ·)` is regular only near the driver
(the conformal maps are analytic only near the real image interval of the own hull). The Itô theorem of
PROVE-ZHAN-GT4-A5 (`Ito.integral_mul_fieldStopped_sub_eq_zero`) needs a field defined on the whole line with global
bounds. On a time piece `[b, c]` with a frozen center `y` we use the **cut-off field** `χ((x − y)/ρ) e^{ℓ(t, x)}`
(`χ` a smooth bump, `1` on `[−1, 1]`, `0` off `(−2, 2)`), which equals `M̃` as long as `|W_t − y| < ρ`.

This file is deterministic and generic in `ℓ`: if `ℓ` and its space derivatives up to order three and its time
derivative are continuous and bounded on `[b, c] × (y − 3ρ, y + 3ρ)`, the cut-off field is `C²` in space with a
Lipschitz second derivative, `C¹` in time (integrated form), with jointly continuous `∂_t` and `∂²_x`, and bounded —
exactly the pathwise hypotheses of the A5 theorem.

## Main results

* `stdBump`, `cutChi` (the scaled cutoff and its derivatives), `hasDerivAt_cutChi`, `cutChi_zero_eq_one`,
  `cutChi_succ_eq_zero`, `cutChi_eq_zero_of_lt`, `exists_bound_cutChi`;
* `cutField`, `cutField1`, `cutField2`, `cutField3`, `cutFieldT` and `IsLogField` (the hypotheses on `ℓ`);
* `IsLogField.hasDerivAt_cutField`, `…_cutField1`, `…_cutField2` (space derivatives everywhere),
  `IsLogField.lipschitz_cutField2`, `IsLogField.cutField_sub_eq_integral` (time),
  `IsLogField.continuousOn_cutFieldT`, `IsLogField.continuousOn_cutField2`, and the bounds.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace InteractingSLE.ZhanGT4

/-! ### The cutoff -/

/-- The standard bump on `ℝ`: smooth, `1` on `[−1, 1]`, `0` off `(−2, 2)`. -/
def stdBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem contDiff_stdBump : ContDiff ℝ ∞ (⇑stdBump) := stdBump.contDiff

theorem differentiable_iterDeriv_stdBump (k : ℕ) : Differentiable ℝ (deriv^[k] (⇑stdBump)) :=
  (contDiff_stdBump.iterate_deriv k).differentiable (by simp)

theorem continuous_iterDeriv_stdBump (k : ℕ) : Continuous (deriv^[k] (⇑stdBump)) :=
  (differentiable_iterDeriv_stdBump k).continuous

/-- Off `[−2, 2]` the bump and all its derivatives vanish. -/
theorem iterDeriv_stdBump_eq_zero (k : ℕ) {u : ℝ} (hu : 2 < |u|) : deriv^[k] (⇑stdBump) u = 0 := by
  have hO : IsOpen {u : ℝ | 2 < |u|} := isOpen_lt continuous_const continuous_abs
  have key : ∀ j : ℕ, ∀ u ∈ {u : ℝ | 2 < |u|}, deriv^[j] (⇑stdBump) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro u hu
      filter_upwards [hO.mem_nhds hu] with v hv
      refine stdBump.zero_of_le_dist ?_
      show (2 : ℝ) ≤ dist v 0
      rw [Real.dist_eq, sub_zero]
      exact hv.le
    | succ j ih =>
      intro u hu
      filter_upwards [hO.mem_nhds hu] with v hv
      rw [Function.iterate_succ_apply', (ih v hv).deriv_eq, deriv_const]
  exact (key k u hu).eq_of_nhds

/-- On `(−1, 1)` the bump is `1` and its derivatives vanish. -/
theorem iterDeriv_stdBump_of_lt_one {u : ℝ} (hu : |u| < 1) :
    stdBump u = 1 ∧ ∀ k, 0 < k → deriv^[k] (⇑stdBump) u = 0 := by
  have hO : IsOpen {u : ℝ | |u| < 1} := isOpen_lt continuous_abs continuous_const
  have h1 : ∀ v ∈ {u : ℝ | |u| < 1}, stdBump v = 1 := fun v hv => by
    refine stdBump.one_of_mem_closedBall ?_
    show dist v 0 ≤ 1
    rw [Real.dist_eq, sub_zero]
    exact hv.le
  have key : ∀ j : ℕ, 0 < j → ∀ u ∈ {u : ℝ | |u| < 1}, deriv^[j] (⇑stdBump) =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    intro j hj
    induction j with
    | zero => exact absurd hj (lt_irrefl 0)
    | succ j ih =>
      intro u hu
      filter_upwards [hO.mem_nhds hu] with v hv
      rw [Function.iterate_succ_apply']
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have : (⇑stdBump) =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
          filter_upwards [hO.mem_nhds hv] with w hw using h1 w hw
        simp only [Function.iterate_zero, id_eq]
        rw [this.deriv_eq, deriv_const]
      · rw [(ih hpos v hv).deriv_eq, deriv_const]
  exact ⟨h1 u hu, fun k hk => (key k hk u hu).eq_of_nhds⟩

theorem exists_bound_iterDeriv_stdBump (k : ℕ) : ∃ C, ∀ u, |deriv^[k] (⇑stdBump) u| ≤ C := by
  have hcs : HasCompactSupport (deriv^[k] (⇑stdBump)) := by
    induction k with
    | zero => exact stdBump.hasCompactSupport
    | succ j ih =>
      rw [Function.iterate_succ']
      exact ih.deriv
  obtain ⟨C, hC⟩ := (continuous_iterDeriv_stdBump k).bounded_above_of_compact_support hcs
  exact ⟨C, fun u => by simpa [Real.norm_eq_abs] using hC u⟩

/-- **The scaled cutoff and its derivatives**: `χ_k(x) = ρ^{−k} χ^{(k)}((x − y)/ρ)`. -/
def cutChi (k : ℕ) (y ρ x : ℝ) : ℝ := ρ⁻¹ ^ k * deriv^[k] (⇑stdBump) ((x - y) / ρ)

theorem hasDerivAt_cutChi (k : ℕ) (y ρ x : ℝ) : HasDerivAt (cutChi k y ρ) (cutChi (k + 1) y ρ x) x := by
  have h1 : HasDerivAt (fun x => (x - y) / ρ) ρ⁻¹ x := by
    have := ((hasDerivAt_id x).sub_const y).div_const ρ
    simpa [div_eq_mul_inv] using this
  have h2 := ((differentiable_iterDeriv_stdBump k ((x - y) / ρ)).hasDerivAt.comp x h1).const_mul (ρ⁻¹ ^ k)
  refine h2.congr_deriv ?_
  simp only [cutChi, Function.iterate_succ_apply']
  ring

theorem cutChi_zero_eq_one {y ρ x : ℝ} (hρ : 0 < ρ) (hx : |x - y| < ρ) : cutChi 0 y ρ x = 1 := by
  have hu : |(x - y) / ρ| < 1 := by rw [abs_div, abs_of_pos hρ, div_lt_one hρ]; exact hx
  simp [cutChi, (iterDeriv_stdBump_of_lt_one hu).1]

theorem cutChi_succ_eq_zero {y ρ x : ℝ} (hρ : 0 < ρ) (hx : |x - y| < ρ) {k : ℕ} (hk : 0 < k) :
    cutChi k y ρ x = 0 := by
  have hu : |(x - y) / ρ| < 1 := by rw [abs_div, abs_of_pos hρ, div_lt_one hρ]; exact hx
  simp [cutChi, (iterDeriv_stdBump_of_lt_one hu).2 k hk]

theorem cutChi_eq_zero_of_lt {y ρ x : ℝ} (hρ : 0 < ρ) (hx : 2 * ρ < |x - y|) (k : ℕ) : cutChi k y ρ x = 0 := by
  have hu : 2 < |(x - y) / ρ| := by rw [abs_div, abs_of_pos hρ, lt_div_iff₀ hρ]; exact hx
  simp [cutChi, iterDeriv_stdBump_eq_zero k hu]

theorem continuous_cutChi (k : ℕ) (y ρ : ℝ) : Continuous (cutChi k y ρ) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_cutChi k y ρ x).continuousAt

theorem exists_bound_cutChi (y ρ : ℝ) : ∃ C, 0 ≤ C ∧ ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ C := by
  choose C hC using fun k => exists_bound_iterDeriv_stdBump k
  refine ⟨∑ k ∈ Finset.range 5, |ρ⁻¹| ^ k * |C k|, Finset.sum_nonneg fun k _ => by positivity, fun k hk x => ?_⟩
  have hk5 : k ∈ Finset.range 5 := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  calc |cutChi k y ρ x| = |ρ⁻¹| ^ k * |deriv^[k] (⇑stdBump) ((x - y) / ρ)| := by
        rw [cutChi, abs_mul, abs_pow]
    _ ≤ |ρ⁻¹| ^ k * |C k| :=
        mul_le_mul_of_nonneg_left ((hC k _).trans (le_abs_self _)) (by positivity)
    _ ≤ ∑ k ∈ Finset.range 5, |ρ⁻¹| ^ k * |C k| :=
        Finset.single_le_sum (f := fun k => |ρ⁻¹| ^ k * |C k|) (fun k _ => by positivity) hk5

/-! ### Polynomial bounds -/

section Bounds

variable {C K : ℝ}

theorem abs_mul_le_of_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_cutCoef1_le {c0 c1 l1 : ℝ} (hc0 : |c0| ≤ C) (hc1 : |c1| ≤ C) (hl1 : |l1| ≤ K) :
    |c1 + c0 * l1| ≤ C * (1 + K) := by
  calc |c1 + c0 * l1| ≤ |c1| + |c0 * l1| := abs_add_le _ _
    _ ≤ C + C * K := add_le_add hc1 (abs_mul_le_of_le hc0 hl1)
    _ = C * (1 + K) := by ring

theorem abs_cutCoef2_le {c0 c1 c2 l1 l2 : ℝ} (hc0 : |c0| ≤ C) (hc1 : |c1| ≤ C) (hc2 : |c2| ≤ C) (hl1 : |l1| ≤ K)
    (hl2 : |l2| ≤ K) : |c2 + 2 * c1 * l1 + c0 * (l2 + l1 ^ 2)| ≤ C * (1 + 3 * K + K ^ 2) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hl1
  have h2 : |2 * c1 * l1| ≤ 2 * C * K := by
    rw [mul_assoc]; rw [abs_mul, abs_two]
    have := abs_mul_le_of_le hc1 hl1; linarith
  have h3 : |l2 + l1 ^ 2| ≤ K + K ^ 2 := (abs_add_le _ _).trans (add_le_add hl2 (by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hl1 2))
  calc |c2 + 2 * c1 * l1 + c0 * (l2 + l1 ^ 2)| ≤ |c2| + |2 * c1 * l1| + |c0 * (l2 + l1 ^ 2)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ C + 2 * C * K + C * (K + K ^ 2) := add_le_add (add_le_add hc2 h2) (abs_mul_le_of_le hc0 h3)
    _ = C * (1 + 3 * K + K ^ 2) := by ring

theorem abs_cutCoef3_le {c0 c1 c2 c3 l1 l2 l3 : ℝ} (hc0 : |c0| ≤ C) (hc1 : |c1| ≤ C) (hc2 : |c2| ≤ C)
    (hc3 : |c3| ≤ C) (hl1 : |l1| ≤ K) (hl2 : |l2| ≤ K) (hl3 : |l3| ≤ K) :
    |c3 + 3 * c2 * l1 + 3 * c1 * (l2 + l1 ^ 2) + c0 * (l3 + 3 * l1 * l2 + l1 ^ 3)| ≤
      C * (1 + 7 * K + 6 * K ^ 2 + K ^ 3) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hl1
  have h2 : |3 * c2 * l1| ≤ 3 * C * K := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := abs_mul_le_of_le hc2 hl1; linarith
  have hsq : |l1 ^ 2| ≤ K ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hl1 2
  have hcb : |l1 ^ 3| ≤ K ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hl1 3
  have h3 : |3 * c1 * (l2 + l1 ^ 2)| ≤ 3 * C * (K + K ^ 2) := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := abs_mul_le_of_le hc1 ((abs_add_le _ _).trans (add_le_add hl2 hsq)); linarith
  have h12 : |3 * l1 * l2| ≤ 3 * K * K := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := abs_mul_le_of_le hl1 hl2; linarith
  have h4 : |c0 * (l3 + 3 * l1 * l2 + l1 ^ 3)| ≤ C * (K + 3 * K * K + K ^ 3) :=
    abs_mul_le_of_le hc0 ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hl3 h12)) hcb))
  calc _ ≤ |c3| + |3 * c2 * l1| + |3 * c1 * (l2 + l1 ^ 2)| + |c0 * (l3 + 3 * l1 * l2 + l1 ^ 3)| :=
        (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
          (add_le_add_left (abs_add_le _ _) _)) _)
    _ ≤ C + 3 * C * K + 3 * C * (K + K ^ 2) + C * (K + 3 * K * K + K ^ 3) :=
        add_le_add (add_le_add (add_le_add hc3 h2) h3) h4
    _ = C * (1 + 7 * K + 6 * K ^ 2 + K ^ 3) := by ring

theorem cutBound_le (hC : 0 ≤ C) (hK : 0 ≤ K) :
    C * (1 + K) ≤ 8 * C * (1 + K) ^ 3 ∧ C * (1 + 3 * K + K ^ 2) ≤ 8 * C * (1 + K) ^ 3 ∧
      C * (1 + 7 * K + 6 * K ^ 2 + K ^ 3) ≤ 8 * C * (1 + K) ^ 3 ∧ C ≤ 8 * C * (1 + K) ^ 3 ∧
      C * K ≤ 8 * C * (1 + K) ^ 3 := by
  have e1 : (1 + K) ≤ 8 * (1 + K) ^ 3 := by nlinarith [sq_nonneg K, mul_nonneg hK (sq_nonneg K)]
  have e2 : (1 + 3 * K + K ^ 2) ≤ 8 * (1 + K) ^ 3 := by nlinarith [sq_nonneg K, mul_nonneg hK (sq_nonneg K)]
  have e3 : (1 + 7 * K + 6 * K ^ 2 + K ^ 3) ≤ 8 * (1 + K) ^ 3 := by
    nlinarith [sq_nonneg K, mul_nonneg hK (sq_nonneg K)]
  have e4 : (1 : ℝ) ≤ 8 * (1 + K) ^ 3 := by nlinarith [sq_nonneg K, mul_nonneg hK (sq_nonneg K)]
  have e5 : K ≤ 8 * (1 + K) ^ 3 := by nlinarith [sq_nonneg K, mul_nonneg hK (sq_nonneg K)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left e1 hC; linarith
  · have := mul_le_mul_of_nonneg_left e2 hC; linarith
  · have := mul_le_mul_of_nonneg_left e3 hC; linarith
  · have := mul_le_mul_of_nonneg_left e4 hC; linarith
  · have := mul_le_mul_of_nonneg_left e5 hC; linarith

end Bounds

/-! ### Cut-off fields -/

/-- The cut-off field `χ((x − y)/ρ) e^{ℓ(t, x)}`. -/
def cutField (ℓ : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ := cutExp0 (cutChi 0 y ρ x) (ℓ t x)

/-- Its first space derivative. -/
def cutField1 (ℓ ℓx : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ :=
  cutExp1 (cutChi 0 y ρ x) (cutChi 1 y ρ x) (ℓ t x) (ℓx t x)

/-- Its second space derivative. -/
def cutField2 (ℓ ℓx ℓxx : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ :=
  cutExp2 (cutChi 0 y ρ x) (cutChi 1 y ρ x) (cutChi 2 y ρ x) (ℓ t x) (ℓx t x) (ℓxx t x)

/-- Its third space derivative. -/
def cutField3 (ℓ ℓx ℓxx ℓxxx : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ :=
  cutExp3 (cutChi 0 y ρ x) (cutChi 1 y ρ x) (cutChi 2 y ρ x) (cutChi 3 y ρ x) (ℓ t x) (ℓx t x) (ℓxx t x)
    (ℓxxx t x)

/-- Its time derivative. -/
def cutFieldT (ℓ ℓt : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ := cutChi 0 y ρ x * Real.exp (ℓ t x) * ℓt t x

/-- **A regular log-field on `[b, c] × (y − 3ρ, y + 3ρ)`**: three space derivatives and a time derivative, jointly
continuous where needed, with every value bounded by `K`. -/
structure IsLogField (ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ) (b c y ρ K : ℝ) : Prop where
  pos : 0 < ρ
  Knonneg : 0 ≤ K
  dx : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → HasDerivAt (ℓ t) (ℓx t x) x
  dxx : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → HasDerivAt (ℓx t) (ℓxx t x) x
  dxxx : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → HasDerivAt (ℓxx t) (ℓxxx t x) x
  dt : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → HasDerivWithinAt (fun s => ℓ s x) (ℓt t x) (Icc b c) t
  cont : ContinuousOn (fun p : ℝ × ℝ => ℓ p.1 p.2) (Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  contX : ContinuousOn (fun p : ℝ × ℝ => ℓx p.1 p.2) (Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  contXX : ContinuousOn (fun p : ℝ × ℝ => ℓxx p.1 p.2) (Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  contT : ContinuousOn (fun p : ℝ × ℝ => ℓt p.1 p.2) (Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  bound : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ →
    |ℓ t x| ≤ K ∧ |ℓx t x| ≤ K ∧ |ℓxx t x| ≤ K ∧ |ℓxxx t x| ≤ K ∧ |ℓt t x| ≤ K

namespace IsLogField

variable {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K : ℝ} (hL : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K)
include hL

omit hL in
theorem far_of_not_near {x y ρ : ℝ} (hρ : 0 < ρ) (hx : ¬ |x - y| < 3 * ρ) : 2 * ρ < |x - y| := by
  push Not at hx; linarith

omit hL in
/-- Far from the center every cut-off quantity vanishes on a neighbourhood. -/
theorem eventually_far {x y ρ : ℝ} (hx : 2 * ρ < |x - y|) : ∀ᶠ x' in 𝓝 x, 2 * ρ < |x' - y| :=
  (isOpen_lt continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))).mem_nhds hx

theorem hasDerivAt_cutField {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    HasDerivAt (cutField ℓ y ρ t) (cutField1 ℓ ℓx y ρ t x) x := by
  by_cases hx : |x - y| < 3 * ρ
  · exact hasDerivAt_cutExp0 (hasDerivAt_cutChi 0 y ρ x) (hL.dx t ht x hx)
  · have hfar := far_of_not_near hL.pos hx
    have h0 : cutField1 ℓ ℓx y ρ t x = 0 := by
      simp [cutField1, cutExp1, cutChi_eq_zero_of_lt hL.pos hfar]
    rw [h0]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_far hfar] with x' hx'
    simp [cutField, cutExp0, cutChi_eq_zero_of_lt hL.pos hx']

theorem hasDerivAt_cutField1 {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    HasDerivAt (cutField1 ℓ ℓx y ρ t) (cutField2 ℓ ℓx ℓxx y ρ t x) x := by
  by_cases hx : |x - y| < 3 * ρ
  · exact hasDerivAt_cutExp1 (hasDerivAt_cutChi 0 y ρ x) (hasDerivAt_cutChi 1 y ρ x) (hL.dx t ht x hx)
      (hL.dxx t ht x hx)
  · have hfar := far_of_not_near hL.pos hx
    have h0 : cutField2 ℓ ℓx ℓxx y ρ t x = 0 := by
      simp [cutField2, cutExp2, cutChi_eq_zero_of_lt hL.pos hfar]
    rw [h0]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_far hfar] with x' hx'
    simp [cutField1, cutExp1, cutChi_eq_zero_of_lt hL.pos hx']

theorem hasDerivAt_cutField2 {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    HasDerivAt (cutField2 ℓ ℓx ℓxx y ρ t) (cutField3 ℓ ℓx ℓxx ℓxxx y ρ t x) x := by
  by_cases hx : |x - y| < 3 * ρ
  · exact hasDerivAt_cutExp2 (hasDerivAt_cutChi 0 y ρ x) (hasDerivAt_cutChi 1 y ρ x) (hasDerivAt_cutChi 2 y ρ x)
      (hL.dx t ht x hx) (hL.dxx t ht x hx) (hL.dxxx t ht x hx)
  · have hfar := far_of_not_near hL.pos hx
    have h0 : cutField3 ℓ ℓx ℓxx ℓxxx y ρ t x = 0 := by
      simp [cutField3, cutExp3, cutChi_eq_zero_of_lt hL.pos hfar]
    rw [h0]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_far hfar] with x' hx'
    simp [cutField2, cutExp2, cutChi_eq_zero_of_lt hL.pos hx']

/-- **Uniform bounds** on the cut-off field and its derivatives, with `Cχ` a bound for `χ, …, χ''''`. -/
theorem abs_cutField_le {Cχ : ℝ} (hCχ : 0 ≤ Cχ) (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ) {t : ℝ}
    (ht : t ∈ Icc b c) (x : ℝ) :
    |cutField ℓ y ρ t x| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K ∧
      |cutField1 ℓ ℓx y ρ t x| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K ∧
      |cutField2 ℓ ℓx ℓxx y ρ t x| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K ∧
      |cutField3 ℓ ℓx ℓxx ℓxxx y ρ t x| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K ∧
      |cutFieldT ℓ ℓt y ρ t x| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K := by
  have hK := hL.Knonneg
  have hB : 0 ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K := by positivity
  by_cases hx : |x - y| < 3 * ρ
  · obtain ⟨b0, b1, b2, b3, bt⟩ := hL.bound t ht x hx
    have he : Real.exp (ℓ t x) ≤ Real.exp K := Real.exp_le_exp.2 ((le_abs_self _).trans b0)
    have hep := Real.exp_pos (ℓ t x)
    obtain ⟨e1, e2, e3, e4, e5⟩ := cutBound_le hCχ hK
    have hc : ∀ k ≤ 4, |cutChi k y ρ x| ≤ Cχ := fun k hk => hχ k hk x
    have fin : ∀ X : ℝ, |X| ≤ 8 * Cχ * (1 + K) ^ 3 →
        |X * Real.exp (ℓ t x)| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K := fun X hX => by
      rw [abs_mul, abs_of_pos hep]
      exact mul_le_mul hX he hep.le (by positivity)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fin _ ((hc 0 (by norm_num)).trans e4)
    · exact fin _ ((abs_cutCoef1_le (hc 0 (by norm_num)) (hc 1 (by norm_num)) b1).trans e1)
    · exact fin _ ((abs_cutCoef2_le (hc 0 (by norm_num)) (hc 1 (by norm_num)) (hc 2 (by norm_num)) b1 b2).trans e2)
    · exact fin _ ((abs_cutCoef3_le (hc 0 (by norm_num)) (hc 1 (by norm_num)) (hc 2 (by norm_num))
        (hc 3 (by norm_num)) b1 b2 b3).trans e3)
    · have : cutFieldT ℓ ℓt y ρ t x = (cutChi 0 y ρ x * ℓt t x) * Real.exp (ℓ t x) := by
        simp only [cutFieldT]; ring
      rw [this]
      exact fin _ ((abs_mul_le_of_le (hc 0 (by norm_num)) bt).trans e5)
  · have hfar := far_of_not_near hL.pos hx
    simp [cutField, cutField1, cutField2, cutField3, cutFieldT, cutExp0, cutExp1, cutExp2, cutExp3,
      cutChi_eq_zero_of_lt hL.pos hfar, hB]

/-- **The second space derivative is Lipschitz**, uniformly. -/
theorem lipschitz_cutField2 {Cχ : ℝ} (hCχ : 0 ≤ Cχ) (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ) {t : ℝ}
    (ht : t ∈ Icc b c) (x x' : ℝ) :
    |cutField2 ℓ ℓx ℓxx y ρ t x - cutField2 ℓ ℓx ℓxx y ρ t x'| ≤
      8 * Cχ * (1 + K) ^ 3 * Real.exp K * |x - x'| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := univ)
    (f := cutField2 ℓ ℓx ℓxx y ρ t) (f' := cutField3 ℓ ℓx ℓxx ℓxxx y ρ t)
    (fun z _ => (hL.hasDerivAt_cutField2 ht z).hasDerivWithinAt)
    (fun z _ => by rw [Real.norm_eq_abs]; exact (hL.abs_cutField_le hCχ hχ ht z).2.2.2.1)
    convex_univ (mem_univ x') (mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- **The time increments are integrals of `∂_t`** (fundamental theorem of calculus on `[b, c]`). -/
theorem cutField_sub_eq_integral (x : ℝ) {a₁ a₂ : ℝ} (h₁ : b ≤ a₁) (h₁₂ : a₁ ≤ a₂) (h₂ : a₂ ≤ c) :
    cutField ℓ y ρ a₂ x - cutField ℓ y ρ a₁ x = ∫ u in a₁..a₂, cutFieldT ℓ ℓt y ρ u x := by
  by_cases hx : |x - y| < 3 * ρ
  · have hsub : Icc a₁ a₂ ⊆ Icc b c := Icc_subset_Icc h₁ h₂
    have hder : ∀ u ∈ Icc b c, HasDerivWithinAt (fun s => cutField ℓ y ρ s x) (cutFieldT ℓ ℓt y ρ u x)
        (Icc b c) u := fun u hu => by
      have := ((hL.dt u hu x hx).exp).const_mul (cutChi 0 y ρ x)
      refine this.congr_deriv ?_
      simp only [cutFieldT]; ring
    have hcont : ContinuousOn (fun u => cutFieldT ℓ ℓt y ρ u x) (Icc a₁ a₂) := by
      have hc : ContinuousOn (fun u => (u, x)) (Icc a₁ a₂) := (continuous_id.prodMk continuous_const).continuousOn
      have hm : MapsTo (fun u => (u, x)) (Icc a₁ a₂) (Icc b c ×ˢ {x | |x - y| < 3 * ρ}) :=
        fun u hu => ⟨hsub hu, hx⟩
      have h1 := hL.cont.comp hc hm
      have h2 := hL.contT.comp hc hm
      simp only [Function.comp_def] at h1 h2
      exact (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn h1)).mul h2
    have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h₁₂
      (fun u hu => (hder u (hsub hu)).continuousWithinAt.mono hsub) (fun u hu => ?_)
      (hcont.intervalIntegrable_of_Icc h₁₂)
    · exact key.symm
    · exact (hder u (hsub (Ioo_subset_Icc_self hu))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT_of_mem ⟨h₁.trans hu.1.le, lt_of_lt_of_le hu.2 h₂⟩)
  · have hfar := far_of_not_near hL.pos hx
    simp [cutField, cutFieldT, cutExp0, cutChi_eq_zero_of_lt hL.pos hfar]

omit hL in
/-- A function continuous near the center and vanishing far from it is continuous on `[b, c] × ℝ`. -/
theorem continuousOn_of_near_far {F : ℝ × ℝ → ℝ} (hρ : 0 < ρ)
    (hnear : ContinuousOn F (Icc b c ×ˢ {x | |x - y| < 3 * ρ})) (hfar : ∀ p : ℝ × ℝ, 2 * ρ < |p.2 - y| → F p = 0) :
    ContinuousOn F (Icc b c ×ˢ univ) := by
  intro p hp
  by_cases h : |p.2 - y| < 3 * ρ
  · have hO : IsOpen {x : ℝ | |x - y| < 3 * ρ} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    refine (hnear p ⟨hp.1, h⟩).mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨univ ×ˢ {x | |x - y| < 3 * ρ},
      isOpen_univ.prod hO, ⟨trivial, h⟩, fun q hq => ⟨hq.2.1, hq.1.2⟩⟩)
  · have hfar' := far_of_not_near hρ h
    have hO : IsOpen {q : ℝ × ℝ | 2 * ρ < |q.2 - y|} :=
      isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.sub continuous_const))
    have hev : F =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
      filter_upwards [hO.mem_nhds hfar'] with q hq using hfar q hq
    have hc : ContinuousAt F p := continuousAt_const.congr hev.symm
    exact hc.continuousWithinAt

theorem continuousOn_cutFieldT :
    ContinuousOn (fun p : ℝ × ℝ => cutFieldT ℓ ℓt y ρ p.1 p.2) (Icc b c ×ˢ univ) := by
  refine continuousOn_of_near_far (b := b) (c := c) (y := y) hL.pos ?_ fun p (hp : 2 * ρ < |p.2 - y|) => by
    simp [cutFieldT, cutChi_eq_zero_of_lt hL.pos hp]
  exact (((continuous_cutChi 0 y ρ).comp continuous_snd).continuousOn.mul
    (Real.continuous_exp.comp_continuousOn hL.cont)).mul hL.contT

theorem continuousOn_cutField2 :
    ContinuousOn (fun p : ℝ × ℝ => cutField2 ℓ ℓx ℓxx y ρ p.1 p.2) (Icc b c ×ˢ univ) := by
  refine continuousOn_of_near_far (b := b) (c := c) (y := y) hL.pos ?_ fun p (hp : 2 * ρ < |p.2 - y|) => by
    simp [cutField2, cutExp2, cutChi_eq_zero_of_lt hL.pos hp]
  have c0 := ((continuous_cutChi 0 y ρ).comp continuous_snd).continuousOn (s := Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  have c1 := ((continuous_cutChi 1 y ρ).comp continuous_snd).continuousOn (s := Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  have c2 := ((continuous_cutChi 2 y ρ).comp continuous_snd).continuousOn (s := Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  exact ((c2.add ((continuousOn_const.mul c1).mul hL.contX)).add (c0.mul (hL.contXX.add (hL.contX.pow 2)))).mul
    (Real.continuous_exp.comp_continuousOn hL.cont)

end IsLogField

/-! ### The field in the Brownian variable: `W = σ B` -/

namespace IsLogField

variable {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K : ℝ} (hL : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K)
include hL

/-- **The scaled cut-off field satisfies the pathwise hypotheses of the A5 Itô theorem.** With `W = σ B` the field in
the Brownian variable is `Φ(t, x) = Φ_W(t, σx)`, with `∂_x Φ = σ ∂Φ_W`, `∂²_x Φ = σ² ∂²Φ_W`, `∂_t Φ = ∂_t Φ_W`.
All constants are explicit: `B₀ = 8 Cχ (1 + K)³ e^K`. -/
theorem scaled {σ Cχ : ℝ} (hσ : 0 ≤ σ) (hCχ : 0 ≤ Cχ) (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ) :
    (∀ r ∈ Icc b c, ∀ x, HasDerivAt (fun x => cutField ℓ y ρ r (σ * x)) (σ * cutField1 ℓ ℓx y ρ r (σ * x)) x) ∧
    (∀ r ∈ Icc b c, ∀ x, HasDerivAt (fun x => σ * cutField1 ℓ ℓx y ρ r (σ * x))
      (σ ^ 2 * cutField2 ℓ ℓx ℓxx y ρ r (σ * x)) x) ∧
    (∀ r ∈ Icc b c, ∀ x x', |σ ^ 2 * cutField2 ℓ ℓx ℓxx y ρ r (σ * x) - σ ^ 2 * cutField2 ℓ ℓx ℓxx y ρ r (σ * x')| ≤
      σ ^ 3 * (8 * Cχ * (1 + K) ^ 3 * Real.exp K) * |x - x'|) ∧
    (∀ x a₁ a₂, b ≤ a₁ → a₁ ≤ a₂ → a₂ ≤ c →
      cutField ℓ y ρ a₂ (σ * x) - cutField ℓ y ρ a₁ (σ * x) = ∫ u in a₁..a₂, cutFieldT ℓ ℓt y ρ u (σ * x)) ∧
    ContinuousOn (fun p : ℝ × ℝ => cutFieldT ℓ ℓt y ρ p.1 (σ * p.2)) (Icc b c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => σ ^ 2 * cutField2 ℓ ℓx ℓxx y ρ p.1 (σ * p.2)) (Icc b c ×ˢ univ) ∧
    (∀ r ∈ Icc b c, ∀ x, |cutField ℓ y ρ r (σ * x)| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K ∧
      |σ * cutField1 ℓ ℓx y ρ r (σ * x)| ≤ σ * (8 * Cχ * (1 + K) ^ 3 * Real.exp K) ∧
      |σ ^ 2 * cutField2 ℓ ℓx ℓxx y ρ r (σ * x)| ≤ σ ^ 2 * (8 * Cχ * (1 + K) ^ 3 * Real.exp K) ∧
      |cutFieldT ℓ ℓt y ρ r (σ * x)| ≤ 8 * Cχ * (1 + K) ^ 3 * Real.exp K) := by
  have hlin : ∀ x, HasDerivAt (fun x : ℝ => σ * x) σ x := fun x => by
    simpa using (hasDerivAt_id x).const_mul σ
  have hcs : Continuous fun p : ℝ × ℝ => (p.1, σ * p.2) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hms : MapsTo (fun p : ℝ × ℝ => (p.1, σ * p.2)) (Icc b c ×ˢ univ) (Icc b c ×ˢ univ) :=
    fun p hp => ⟨hp.1, trivial⟩
  refine ⟨fun r hr x => ?_, fun r hr x => ?_, fun r hr x x' => ?_, fun x a₁ a₂ h₁ h₁₂ h₂ => ?_, ?_, ?_,
    fun r hr x => ?_⟩
  · have := (hL.hasDerivAt_cutField hr (σ * x)).comp x (hlin x)
    exact this.congr_deriv (mul_comm _ _)
  · have := ((hL.hasDerivAt_cutField1 hr (σ * x)).comp x (hlin x)).const_mul σ
    exact this.congr_deriv (by ring)
  · have h1 := hL.lipschitz_cutField2 hCχ hχ hr (σ * x) (σ * x')
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2)]
    calc σ ^ 2 * |cutField2 ℓ ℓx ℓxx y ρ r (σ * x) - cutField2 ℓ ℓx ℓxx y ρ r (σ * x')|
        ≤ σ ^ 2 * (8 * Cχ * (1 + K) ^ 3 * Real.exp K * |σ * x - σ * x'|) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = σ ^ 3 * (8 * Cχ * (1 + K) ^ 3 * Real.exp K) * |x - x'| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hσ]; ring
  · exact hL.cutField_sub_eq_integral (σ * x) h₁ h₁₂ h₂
  · have := hL.continuousOn_cutFieldT.comp hcs.continuousOn hms
    simpa only [Function.comp_def] using this
  · have h2 := hL.continuousOn_cutField2.comp hcs.continuousOn hms
    simp only [Function.comp_def] at h2
    exact continuousOn_const.mul h2
  · obtain ⟨b0, b1, b2, -, bt⟩ := hL.abs_cutField_le hCχ hχ hr (σ * x)
    refine ⟨b0, ?_, ?_, bt⟩
    · rw [abs_mul, abs_of_nonneg hσ]; exact mul_le_mul_of_nonneg_left b1 hσ
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ σ ^ 2)]
      exact mul_le_mul_of_nonneg_left b2 (by positivity)

end IsLogField

end InteractingSLE.ZhanGT4
