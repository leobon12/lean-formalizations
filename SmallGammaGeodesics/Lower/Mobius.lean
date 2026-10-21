import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Segment

/-!
# Möbius maps, tubes and midline windows of source §7 (packet P-L1)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7 (proof of Proposition 7.1); corrected
mathematics in planning audit GA4 (`planning/audits/GA4-sections-7-8.md`), "Details for later use",
items **A1** (Möbius maps) and **A2** (tubes, windows, constants `R₀ = 10⁻³`, `K = 100`).

* `mobPhi θ` is `φ_θ(z) = e^{iθ} z / (1 + (e^{iθ} − 1) z)`; `ψ_θ = mobPhi (-θ)` is its inverse
  (`mobPhi_neg_mobPhi`). It fixes `0` and `1` (`mobPhi_zero`, `mobPhi_one`), has derivative
  `e^{iθ} / (1 + (e^{iθ} − 1) z)²` (`hasDerivAt_mobPhi`), and maps the midline `Re z = 1/2` to itself:
  `φ_θ(1/2 + iy) = 1/2 + i (y + t/2)/(1 − 2ty)` with `t = tan(θ/2)` (`mobPhi_midline`, source (7.2)).
* A2: with `0 < r ≤ R ≤ 1/1000` and `|θ| ≤ 64 R`, `φ_θ(T_r) ⊆ U_R` and `T_r ⊆ ψ_θ(U_R)`
  (`mobPhi_image_tube_subset`, `tube_subset_image_rectU`); the denominators do not vanish on
  `B_5(0)` for `|θ| ≤ 1/10` (`denom_ne_zero_of_norm_le`); the window centres `tan(32 k r)/2` are
  `16 r`-separated (`sub_le_tan_sub_tan`, `windows_disjoint`; in the form of (W3):
  `window_centres_separated`); and a midline point of `U_R` outside
  the window of radius `2r` around `tan(θ/2)/2` is pulled back by `ψ_θ` to a midline point with
  `|Im| > 5r/3` (`midline_preimage`), with `|Im| ≤ 1` (`abs_im_mobPhi_neg_le_one`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Real

namespace SmallGammaGeodesics

/-- `φ_θ(z) = e^{iθ} z / (1 + (e^{iθ} − 1) z)` (source §7); `ψ_θ = φ_{−θ}` is its inverse. -/
def mobPhi (θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (θ * Complex.I) * z / (1 + (Complex.exp (θ * Complex.I) - 1) * z)

/-- `T_r = {z : dist(z, [0,1]) ≤ r}`. -/
def tube (r : ℝ) : Set ℂ := {z | Metric.infDist z (segment ℝ (0 : ℂ) 1) ≤ r}

/-- `U_R = {−1/4 < Re z < 5/4, |Im z| < K R}` (source §7 uses K = 100). -/
def rectU (K R : ℝ) : Set ℂ := {z | -1 / 4 < z.re ∧ z.re < 5 / 4 ∧ |z.im| < K * R}

/-- The closed midline window `{1/2 + iy : |y − c| ≤ ρ}`. -/
def window (c ρ : ℝ) : Set ℂ := {z | z.re = 1 / 2 ∧ |z.im - c| ≤ ρ}

/-! ### A1: the Möbius maps -/

theorem mobPhi_zero (θ : ℝ) : mobPhi θ 0 = 0 := by
  simp [mobPhi]

theorem mobPhi_one (θ : ℝ) : mobPhi θ 1 = 1 := by
  simp only [mobPhi, mul_one, add_sub_cancel]
  exact div_self (Complex.exp_ne_zero _)

/-- `|e^{iθ} − 1| ≤ |θ|`. -/
theorem norm_exp_mul_I_sub_one_le (θ : ℝ) : ‖Complex.exp (θ * Complex.I) - 1‖ ≤ |θ| := by
  rw [mul_comm, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- `e^{−iθ} = (e^{iθ})⁻¹`, in the form produced by unfolding `mobPhi (-θ)`. -/
theorem exp_neg_mul_I (θ : ℝ) :
    Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = (Complex.exp (θ * Complex.I))⁻¹ := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]

/-- `ψ_θ ∘ φ_θ = id` off the pole of `φ_θ` (source §7; GA4 A1(a)). -/
theorem mobPhi_neg_mobPhi {θ : ℝ} {z : ℂ} (hz : 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0) :
    mobPhi (-θ) (mobPhi θ z) = z := by
  unfold mobPhi
  rw [exp_neg_mul_I]
  set e := Complex.exp (θ * Complex.I) with he
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  set D := 1 + (e - 1) * z with hD
  have hD' : 1 + (e⁻¹ - 1) * (e * z / D) = D⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have h1 : (e⁻¹ - 1) * (e * z) = z - e * z := by
      rw [sub_mul (e⁻¹) 1 (e * z), inv_mul_cancel_left₀ he0, one_mul]
    rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hz, h1, hD]
    ring
  rw [hD', div_inv_eq_mul, mul_assoc, div_mul_cancel₀ _ hz, inv_mul_cancel_left₀ he0]

/-- `φ_θ′(z) = e^{iθ} / (1 + (e^{iθ} − 1) z)²` (GA4 A1(c)). -/
theorem hasDerivAt_mobPhi {θ : ℝ} {z : ℂ} (hz : 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0) :
    HasDerivAt (mobPhi θ)
      (Complex.exp (θ * Complex.I) / (1 + (Complex.exp (θ * Complex.I) - 1) * z) ^ 2) z := by
  set e := Complex.exp (θ * Complex.I) with he
  have h1 : HasDerivAt (fun w : ℂ => e * w) e z := by
    simpa using (hasDerivAt_id z).const_mul e
  have h2 : HasDerivAt (fun w : ℂ => 1 + (e - 1) * w) (e - 1) z := by
    simpa using ((hasDerivAt_id z).const_mul (e - 1)).const_add 1
  have h := h1.div h2 hz
  have hval : (e * (1 + (e - 1) * z) - e * z * (e - 1)) / (1 + (e - 1) * z) ^ 2 =
      e / (1 + (e - 1) * z) ^ 2 := by ring
  rw [hval] at h
  exact h

/-- `φ_θ` is injective off its pole. -/
theorem injOn_mobPhi (θ : ℝ) :
    Set.InjOn (mobPhi θ) {z | 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0} := by
  intro z hz w hw h
  rw [← mobPhi_neg_mobPhi hz, h, mobPhi_neg_mobPhi hw]

/-- `e^{iθ} (1 − i tan(θ/2)) = 1 + i tan(θ/2)` when `cos(θ/2) ≠ 0`. -/
theorem exp_mul_one_sub_I_tan (θ : ℝ) (hc : Real.cos (θ / 2) ≠ 0) :
    Complex.exp (θ * Complex.I) * (1 - Complex.I * (Real.tan (θ / 2) : ℂ)) =
      1 + Complex.I * (Real.tan (θ / 2) : ℂ) := by
  have h1 : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have he : Complex.exp (θ * Complex.I) =
      ((Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I) ^ 2 := by
    rw [← h1, sq, ← Complex.exp_add]; congr 1; push_cast; ring
  have ht : (Real.tan (θ / 2) : ℂ) = (Real.sin (θ / 2) : ℂ) / (Real.cos (θ / 2) : ℂ) := by
    rw [Real.tan_eq_sin_div_cos]; push_cast; ring
  have hcC : (Real.cos (θ / 2) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hpy : (Real.sin (θ / 2) : ℂ) ^ 2 + (Real.cos (θ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (θ / 2)
  rw [he, ht]
  generalize (Real.cos (θ / 2) : ℂ) = c at hcC hpy ⊢
  generalize (Real.sin (θ / 2) : ℂ) = s at hpy ⊢
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have key : (c + s * Complex.I) ^ 2 * (c - Complex.I * s) = c + Complex.I * s := by
    linear_combination (-c * s ^ 2 - s ^ 3 * Complex.I) * hI + (c + Complex.I * s) * hpy
  rw [mul_sub, mul_one, sub_eq_iff_eq_add]
  field_simp
  linear_combination key

/-- **Identity (7.2)** (GA4 A1(d)). With `t = tan(θ/2)`, `φ_θ(1/2 + iy) = 1/2 + i (y + t/2)/(1 − 2ty)`. -/
theorem mobPhi_midline (θ y : ℝ) (hc : Real.cos (θ / 2) ≠ 0)
    (hd : 1 - 2 * Real.tan (θ / 2) * y ≠ 0) :
    mobPhi θ (1 / 2 + y * Complex.I) =
      1 / 2 + (((y + Real.tan (θ / 2) / 2) / (1 - 2 * Real.tan (θ / 2) * y) : ℝ) : ℂ) *
        Complex.I := by
  set t := Real.tan (θ / 2) with ht
  set e := Complex.exp (θ * Complex.I) with he
  have key := exp_mul_one_sub_I_tan θ hc
  rw [← ht, ← he] at key
  set g : ℝ := (y + t / 2) / (1 - 2 * t * y) with hg_def
  have hg : g * (1 - 2 * t * y) = y + t / 2 := div_mul_cancel₀ _ hd
  have hdC : ((1 - 2 * t * y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  have hit : (1 - Complex.I * (t : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  -- the denominator times `(1 - i t)` is the real number `1 - 2 t y`
  have hden : (1 + (e - 1) * (1 / 2 + y * Complex.I)) * (1 - Complex.I * (t : ℂ)) =
      ((1 - 2 * t * y : ℝ) : ℂ) := by
    have : (1 + (e - 1) * (1 / 2 + y * Complex.I)) * (1 - Complex.I * (t : ℂ)) =
        (1 - Complex.I * (t : ℂ)) +
          (e * (1 - Complex.I * (t : ℂ)) - (1 - Complex.I * (t : ℂ))) * (1 / 2 + y * Complex.I) := by
      ring
    rw [this, key]
    push_cast
    linear_combination (2 * (t : ℂ) * (y : ℂ)) * hI
  have hne : (1 + (e - 1) * (1 / 2 + y * Complex.I)) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hden; exact hdC hden.symm
  unfold mobPhi
  rw [← he, div_eq_iff hne]
  -- multiply through by `(1 - i t) ≠ 0`
  apply mul_right_cancel₀ hit
  have lhs : e * (1 / 2 + y * Complex.I) * (1 - Complex.I * (t : ℂ)) =
      (1 + Complex.I * (t : ℂ)) * (1 / 2 + y * Complex.I) := by
    rw [← key]; ring
  have rhs : (1 / 2 + (g : ℂ) * Complex.I) * (1 + (e - 1) * (1 / 2 + y * Complex.I)) *
      (1 - Complex.I * (t : ℂ)) = (1 / 2 + (g : ℂ) * Complex.I) * ((1 - 2 * t * y : ℝ) : ℂ) := by
    rw [mul_assoc, hden]
  rw [lhs, rhs]
  have hgC : (g : ℂ) * (1 - 2 * (t : ℂ) * (y : ℂ)) = (y : ℂ) + (t : ℂ) / 2 := by
    exact_mod_cast hg
  push_cast
  linear_combination ((t : ℂ) * (y : ℂ)) * hI - Complex.I * hgC

/-! ### Elementary facts on the tube, the rectangle and the midline -/

@[simp] theorem re_half_add_mul_I (v : ℝ) : ((1 / 2 : ℂ) + (v : ℂ) * Complex.I).re = 1 / 2 := by
  simp

@[simp] theorem im_half_add_mul_I (v : ℝ) : ((1 / 2 : ℂ) + (v : ℂ) * Complex.I).im = v := by
  simp

/-- A midline point is `1/2 + i Im z`. -/
theorem eq_half_add_mul_I {u : ℂ} (h : u.re = 1 / 2) : u = 1 / 2 + (u.im : ℂ) * Complex.I :=
  Complex.ext (by simp [h]) (by simp)

theorem isCompact_unitSeg : IsCompact (segment ℝ (0 : ℂ) 1) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- A point of `T_r` is within `r` of a point `a ∈ [0, 1]`. -/
theorem exists_near_of_mem_tube {r : ℝ} {z : ℂ} (hz : z ∈ tube r) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ ‖z - a‖ ≤ r := by
  have hz' : Metric.infDist z (segment ℝ (0 : ℂ) 1) ≤ r := hz
  obtain ⟨p, hp, hpd⟩ := isCompact_unitSeg.exists_infDist_eq_dist ⟨0, left_mem_segment ℝ 0 1⟩ z
  rw [segment_eq_image] at hp
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := hp
  refine ⟨a, ha0, ha1, ?_⟩
  have hpa : (1 - a) • (0 : ℂ) + a • (1 : ℂ) = (a : ℂ) := by
    rw [smul_zero, zero_add, Complex.real_smul, mul_one]
  rw [← dist_eq_norm, ← hpa, ← hpd]
  exact hz'

theorem norm_le_of_mem_tube {r : ℝ} {z : ℂ} (hz : z ∈ tube r) : ‖z‖ ≤ 1 + r := by
  obtain ⟨a, ha0, ha1, hza⟩ := exists_near_of_mem_tube hz
  calc ‖z‖ = ‖(z - a) + (a : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - a‖ + ‖(a : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]; linarith

theorem norm_one_sub_le_of_mem_tube {r : ℝ} {z : ℂ} (hz : z ∈ tube r) : ‖1 - z‖ ≤ 1 + r := by
  obtain ⟨a, ha0, ha1, hza⟩ := exists_near_of_mem_tube hz
  calc ‖1 - z‖ = ‖((1 - a : ℝ) : ℂ) - (z - a)‖ := by push_cast; ring_nf
    _ ≤ ‖((1 - a : ℝ) : ℂ)‖ + ‖z - a‖ := norm_sub_le _ _
    _ ≤ 1 + r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith

/-- `|Im z| ≤ dist(z, [0, 1])`. -/
theorem abs_im_le_infDist (z : ℂ) : |z.im| ≤ Metric.infDist z (segment ℝ (0 : ℂ) 1) := by
  refine (Metric.le_infDist ⟨0, left_mem_segment ℝ 0 1⟩).2 fun p hp => ?_
  rw [segment_eq_image] at hp
  obtain ⟨a, -, rfl⟩ := hp
  rw [dist_eq_norm]
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  simp

theorem abs_im_le_of_mem_tube {r : ℝ} {z : ℂ} (hz : z ∈ tube r) : |z.im| ≤ r :=
  (abs_im_le_infDist z).trans hz

theorem zero_mem_tube {r : ℝ} (hr : 0 ≤ r) : (0 : ℂ) ∈ tube r := by
  show Metric.infDist 0 (segment ℝ (0 : ℂ) 1) ≤ r
  rw [Metric.infDist_zero_of_mem (left_mem_segment ℝ 0 1)]
  exact hr

theorem one_mem_tube {r : ℝ} (hr : 0 ≤ r) : (1 : ℂ) ∈ tube r := by
  show Metric.infDist 1 (segment ℝ (0 : ℂ) 1) ≤ r
  rw [Metric.infDist_zero_of_mem (right_mem_segment ℝ 0 1)]
  exact hr

theorem isOpen_rectU (K R : ℝ) : IsOpen (rectU K R) := by
  have h1 : IsOpen {z : ℂ | -1 / 4 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < 5 / 4} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | |z.im| < K * R} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter (h2.inter h3)

theorem zero_mem_rectU {K R : ℝ} (hKR : 0 < K * R) : (0 : ℂ) ∈ rectU K R :=
  ⟨by norm_num, by norm_num, by simpa using hKR⟩

theorem one_mem_rectU {K R : ℝ} (hKR : 0 < K * R) : (1 : ℂ) ∈ rectU K R :=
  ⟨by norm_num, by norm_num, by simpa using hKR⟩

theorem isClosed_window (c ρ : ℝ) : IsClosed (window c ρ) :=
  (isClosed_eq Complex.continuous_re continuous_const).inter
    (isClosed_le (continuous_abs.comp (Complex.continuous_im.sub continuous_const))
      continuous_const)

/-! ### A2 (ii): the denominators -/

/-- `‖1 + (e^{iθ} − 1) z‖ ≥ 1 − |θ| ‖z‖`. -/
theorem one_sub_abs_mul_norm_le_norm_denom (θ : ℝ) (z : ℂ) :
    1 - |θ| * ‖z‖ ≤ ‖1 + (Complex.exp (θ * Complex.I) - 1) * z‖ := by
  have h1 : ‖(Complex.exp (θ * Complex.I) - 1) * z‖ ≤ |θ| * ‖z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_exp_mul_I_sub_one_le θ) (norm_nonneg z)
  have h2 := norm_sub_norm_le (1 : ℂ) (-((Complex.exp (θ * Complex.I) - 1) * z))
  rw [norm_one, norm_neg, sub_neg_eq_add] at h2
  linarith

/-- **A2 (ii)**: for `|θ| ≤ 1/10` the pole of `φ_θ` lies outside `B̄_5(0)`. -/
theorem denom_ne_zero_of_norm_le {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10) (hz : ‖z‖ ≤ 5) :
    1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0 := by
  have h := one_sub_abs_mul_norm_le_norm_denom θ z
  have h' : |θ| * ‖z‖ ≤ 1 / 10 * 5 := mul_le_mul hθ hz (norm_nonneg z) (by norm_num)
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- **A2 (ii)** for `ψ_θ = φ_{−θ}`. -/
theorem denom_neg_ne_zero_of_norm_le {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10) (hz : ‖z‖ ≤ 5) :
    1 + (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) - 1) * z ≠ 0 :=
  denom_ne_zero_of_norm_le (by rwa [abs_neg]) hz

/-- `φ_θ ∘ ψ_θ = id` off the pole of `ψ_θ`. -/
theorem mobPhi_mobPhi_neg {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    mobPhi θ (mobPhi (-θ) z) = z := by
  have h := mobPhi_neg_mobPhi (θ := -θ) hz
  rwa [neg_neg] at h

/-- `φ_θ ∘ ψ_θ = id` on `B̄_5(0)` for `|θ| ≤ 1/10`. -/
theorem mobPhi_mobPhi_neg_of_norm_le {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10) (hz : ‖z‖ ≤ 5) :
    mobPhi θ (mobPhi (-θ) z) = z :=
  mobPhi_mobPhi_neg (denom_neg_ne_zero_of_norm_le hθ hz)

/-! ### A2 (i): the tube is mapped into the rectangle -/

/-- **A2 (i)**: `φ_θ(T_r) ⊆ U_R` (`K = 100`); in fact `|φ_θ(w) − w| ≤ 72 R` on `T_r`. -/
theorem mobPhi_image_tube_subset {r R θ : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1 / 1000)
    (hθ : |θ| ≤ 64 * R) : mobPhi θ '' tube r ⊆ rectU 100 R := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨a, ha0, ha1, hwa⟩ := exists_near_of_mem_tube hw
  have hR0 : 0 < R := hr.trans_le hrR
  have hwn : ‖w‖ ≤ 1 + r := norm_le_of_mem_tube hw
  have hw1n : ‖1 - w‖ ≤ 1 + r := norm_one_sub_le_of_mem_tube hw
  have hwim : |w.im| ≤ r := abs_im_le_of_mem_tube hw
  have hwre : |w.re - a| ≤ r := by
    have := (Complex.abs_re_le_norm (w - a)).trans hwa
    simpa using this
  set e := Complex.exp (θ * Complex.I) with he
  have hA : ‖e - 1‖ ≤ 64 * R := (norm_exp_mul_I_sub_one_le θ).trans hθ
  set Dn := 1 + (e - 1) * w with hDn
  have hDn9 : 9 / 10 ≤ ‖Dn‖ := by
    have h := one_sub_abs_mul_norm_le_norm_denom θ w
    have h1 : |θ| * ‖w‖ ≤ 64 * R * (1 + r) := mul_le_mul hθ hwn (norm_nonneg w) (by positivity)
    have h2 : 64 * R * (1 + r) ≤ 1 / 10 := by nlinarith
    linarith
  have hDn0 : Dn ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hDn9; norm_num at hDn9
  have hdiff : mobPhi θ w - w = (e - 1) * w * (1 - w) / Dn := by
    show e * w / Dn - w = _
    rw [eq_div_iff hDn0, sub_mul, div_mul_cancel₀ _ hDn0, hDn]
    ring
  have hE : ‖mobPhi θ w - w‖ ≤ 72 * R := by
    rw [hdiff, norm_div, norm_mul, norm_mul, div_le_iff₀ (by linarith)]
    have hsq : (64 * R) * (1 + r) * (1 + r) ≤ 72 * R * (9 / 10) := by
      have : 0 ≤ R * (1 / 80 - 2 * r - r * r) := mul_nonneg hR0.le (by nlinarith)
      nlinarith
    calc ‖e - 1‖ * ‖w‖ * ‖1 - w‖ ≤ (64 * R) * (1 + r) * (1 + r) := by gcongr
      _ ≤ 72 * R * (9 / 10) := hsq
      _ ≤ 72 * R * ‖Dn‖ := mul_le_mul_of_nonneg_left hDn9 (by linarith)
  have hre : |(mobPhi θ w).re - w.re| ≤ 72 * R := by
    have := (Complex.abs_re_le_norm (mobPhi θ w - w)).trans hE
    simpa using this
  have him : |(mobPhi θ w).im - w.im| ≤ 72 * R := by
    have := (Complex.abs_im_le_norm (mobPhi θ w - w)).trans hE
    simpa using this
  rw [abs_le] at hre him hwim hwre
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

/-- **A2 (i)**, equivalent form: `T_r ⊆ V := ψ_θ(U_R)`. -/
theorem tube_subset_image_rectU {r R θ : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1 / 1000)
    (hθ : |θ| ≤ 64 * R) : tube r ⊆ mobPhi (-θ) '' rectU 100 R := by
  intro w hw
  refine ⟨mobPhi θ w, mobPhi_image_tube_subset hr hrR hR hθ ⟨w, hw, rfl⟩, ?_⟩
  have hwn : ‖w‖ ≤ 1 + r := norm_le_of_mem_tube hw
  exact mobPhi_neg_mobPhi (denom_ne_zero_of_norm_le (by linarith) (by linarith))

/-! ### A2 (iii): separation of the window centres -/

/-- `tan b − tan a ≥ b − a` for `0 ≤ a ≤ b < π/2` (mean value theorem, `tan′ = 1/cos² ≥ 1`). -/
theorem sub_le_tan_sub_tan {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < π / 2) :
    b - a ≤ Real.tan b - Real.tan a := by
  have hcos : ∀ x ∈ Icc a b, 0 < Real.cos x := fun x hx =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2]⟩
  have hmono : MonotoneOn (fun x => Real.tan x - x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact (Real.continuousOn_tan.mono fun x hx => (hcos x hx).ne').sub continuousOn_id
    · intro x hx
      rw [interior_Icc] at hx
      have hc : Real.cos x ≠ 0 := (hcos x (Ioo_subset_Icc_self hx)).ne'
      exact ((Real.hasDerivAt_tan hc).sub (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hc : 0 < Real.cos x := hcos x (Ioo_subset_Icc_self hx)
      rw [Real.deriv_tan_sub_id x hc.ne']
      have h1 : Real.cos x ^ 2 ≤ 1 := Real.cos_sq_le_one x
      have h2 : 0 < Real.cos x ^ 2 := by positivity
      rw [sub_nonneg, le_div_iff₀ h2]
      linarith
  have := hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  simp only at this
  linarith

/-- **A2 (iii)**: the window centres `c_k = tan(θ_k/2)/2`, `θ_k = 64 k r`, satisfy
`c_k − c_j ≥ 16 r (k − j)`. -/
theorem windows_disjoint {r : ℝ} (hr : 0 < r) {j k : ℕ} (hjk : j < k) (hk : 32 * k * r < π / 2) :
    16 * r * (k - j) ≤ Real.tan (32 * k * r) / 2 - Real.tan (32 * j * r) / 2 := by
  have hj : (j : ℝ) ≤ k := by exact_mod_cast hjk.le
  have h := sub_le_tan_sub_tan (a := 32 * j * r) (b := 32 * k * r) (by positivity)
    (by gcongr) hk
  linarith

/-- **A2 (iii)**, in the form used by (W3): the windows `J_k` of radius `2r` around
`c_k = tan(θ_k/2)/2`, `θ_k = 64 k r`, satisfy `2 · (2r) < |c_j − c_k|` for `j ≠ k`. -/
theorem window_centres_separated {r : ℝ} (hr : 0 < r) {j k : ℕ} (hjk : j ≠ k)
    (hj : 32 * j * r < π / 2) (hk : 32 * k * r < π / 2) :
    2 * (2 * r) < |Real.tan (64 * j * r / 2) / 2 - Real.tan (64 * k * r / 2) / 2| := by
  have e : ∀ n : ℕ, 64 * (n : ℝ) * r / 2 = 32 * n * r := fun n => by ring
  rw [e j, e k]
  rcases lt_or_gt_of_ne hjk with h | h
  · have hsep := windows_disjoint hr h hk
    have h1 : (1 : ℝ) ≤ k - j := by
      have : j + 1 ≤ k := h
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast this
      linarith
    have h2 : 16 * r * 1 ≤ 16 * r * ((k : ℝ) - j) := mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · have hsep := windows_disjoint hr h hj
    have h1 : (1 : ℝ) ≤ j - k := by
      have : k + 1 ≤ j := h
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast this
      linarith
    have h2 : 16 * r * 1 ≤ 16 * r * ((j : ℝ) - k) := mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [abs_of_pos (by linarith)]
    linarith

/-! ### A2 (iv): pulled-back midline points outside the window -/

theorem half_le_cos_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : 1 / 2 ≤ Real.cos x := by
  have h := Real.one_sub_sq_div_two_le_cos (x := x)
  have : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  linarith

/-- `|tan x| ≤ 2 |x|` for `|x| ≤ 1`. -/
theorem abs_tan_le_two_mul_abs {x : ℝ} (hx : |x| ≤ 1) : |Real.tan x| ≤ 2 * |x| := by
  have hcos := half_le_cos_of_abs_le_one hx
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos (by linarith : 0 < Real.cos x),
    div_le_iff₀ (by linarith)]
  have h1 := Real.abs_sin_le_abs (x := x)
  have h2 : 0 ≤ |x| * (Real.cos x - 1 / 2) := mul_nonneg (abs_nonneg x) (by linarith)
  nlinarith

/-- For `|θ| ≤ 1/10`, `|tan(θ/2)| ≤ |θ| ≤ 1/10`. -/
theorem abs_tan_half_le {θ : ℝ} (hθ : |θ| ≤ 1 / 10) : |Real.tan (θ / 2)| ≤ |θ| := by
  have h2 : |θ / 2| = |θ| / 2 := by rw [abs_div, abs_two]
  have := abs_tan_le_two_mul_abs (x := θ / 2) (by rw [h2]; linarith)
  rw [h2] at this
  linarith

/-- `ψ_θ(1/2 + iv) = 1/2 + i (v − t/2)/(1 + 2tv)`, `t = tan(θ/2)` (source (7.2) for `−θ`). -/
theorem mobPhi_neg_midline {θ v : ℝ} (hθ : |θ| ≤ 1 / 10) (hv : |v| ≤ 1) :
    mobPhi (-θ) (1 / 2 + v * Complex.I) =
      1 / 2 + (((v - Real.tan (θ / 2) / 2) / (1 + 2 * Real.tan (θ / 2) * v) : ℝ) : ℂ) *
        Complex.I := by
  have ht : |Real.tan (θ / 2)| ≤ 1 / 10 := (abs_tan_half_le hθ).trans hθ
  have hc : Real.cos (-θ / 2) ≠ 0 := by
    rw [neg_div, Real.cos_neg]
    have : |θ / 2| ≤ 1 := by rw [abs_div, abs_two]; linarith
    linarith [half_le_cos_of_abs_le_one this]
  have htneg : Real.tan (-θ / 2) = -Real.tan (θ / 2) := by rw [neg_div, Real.tan_neg]
  have hprod : |2 * Real.tan (θ / 2) * v| ≤ 1 / 5 := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul ht hv (abs_nonneg v) (by norm_num)
    linarith
  have hd : 1 - 2 * Real.tan (-θ / 2) * v ≠ 0 := by
    rw [htneg]
    have := (abs_le.1 hprod).1
    intro h0
    linarith
  rw [mobPhi_midline (-θ) v hc hd, htneg]
  congr 3
  ring

/-- The pull-back by `ψ_θ` of a midline point `u = 1/2 + iv` of `U_R`: it is the midline point
`1/2 + iy` with `y (1 + 2tv) = v − t/2` (`t = tan(θ/2)`), and `|t| ≤ 1/10`, `|v| ≤ 1/10`. -/
theorem mobPhi_neg_midline_of_mem {R θ : ℝ} (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) {u : ℂ}
    (hu : u ∈ rectU 100 R) (hre : u.re = 1 / 2) :
    (mobPhi (-θ) u).re = 1 / 2 ∧
      (mobPhi (-θ) u).im * (1 + 2 * Real.tan (θ / 2) * u.im) = u.im - Real.tan (θ / 2) / 2 ∧
      |Real.tan (θ / 2)| ≤ 1 / 10 ∧ |u.im| ≤ 1 / 10 := by
  have hv : |u.im| ≤ 1 / 10 := by have := hu.2.2; linarith
  have hθ' : |θ| ≤ 1 / 10 := by linarith
  have ht : |Real.tan (θ / 2)| ≤ 1 / 10 := (abs_tan_half_le hθ').trans hθ'
  have hprod : |2 * Real.tan (θ / 2) * u.im| ≤ 1 / 50 := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul ht hv (abs_nonneg _) (by norm_num)
    linarith
  have hden : 0 < 1 + 2 * Real.tan (θ / 2) * u.im := by
    have := (abs_le.1 hprod).1
    linarith
  refine ⟨?_, ?_, ht, hv⟩
  · rw [eq_half_add_mul_I hre, mobPhi_neg_midline hθ' (by linarith), re_half_add_mul_I]
  · rw [eq_half_add_mul_I hre, mobPhi_neg_midline hθ' (by linarith), im_half_add_mul_I,
      im_half_add_mul_I]
    exact div_mul_cancel₀ _ hden.ne'

/-- **A2 (iv)**: a midline point `u ∈ U_R` outside the window `J = {1/2 + iy : |y − t/2| ≤ 2r}`
pulls back under `ψ_θ` to a midline point `z` with `|Im z| > 5r/3`. -/
theorem midline_preimage {r R θ : ℝ} (hr : 0 < r) (_hrR : r ≤ R) (hR : R ≤ 1 / 1000)
    (hθ : |θ| ≤ 64 * R) {u : ℂ} (hu : u ∈ rectU 100 R) (hre : u.re = 1 / 2)
    (hwin : u ∉ window (Real.tan (θ / 2) / 2) (2 * r)) :
    (mobPhi (-θ) u).re = 1 / 2 ∧ 5 * r / 3 < |(mobPhi (-θ) u).im| := by
  obtain ⟨hre', hy, ht, hv⟩ := mobPhi_neg_midline_of_mem hR hθ hu hre
  refine ⟨hre', ?_⟩
  by_contra hlt
  have hle := not_lt.1 hlt
  apply hwin
  refine ⟨hre, ?_⟩
  rw [← hy, abs_mul]
  have h1 : |1 + 2 * Real.tan (θ / 2) * u.im| ≤ 1 + 1 / 50 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul, abs_mul, abs_two]
    have := mul_le_mul ht hv (abs_nonneg _) (by norm_num)
    linarith
  calc |(mobPhi (-θ) u).im| * |1 + 2 * Real.tan (θ / 2) * u.im|
      ≤ (5 * r / 3) * (1 + 1 / 50) := mul_le_mul hle h1 (abs_nonneg _) (by positivity)
    _ ≤ 2 * r := by linarith

/-- The pulled-back midline points of `U_R` stay in `|Im| ≤ 1` (used for compactness in A7). -/
theorem abs_im_mobPhi_neg_le_one {R θ : ℝ} (hR : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) {u : ℂ}
    (hu : u ∈ rectU 100 R) (hre : u.re = 1 / 2) : |(mobPhi (-θ) u).im| ≤ 1 := by
  obtain ⟨-, hy, ht, hv⟩ := mobPhi_neg_midline_of_mem hR hθ hu hre
  have hprod : |2 * Real.tan (θ / 2) * u.im| ≤ 1 / 50 := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul ht hv (abs_nonneg _) (by norm_num)
    linarith
  have hden : 49 / 50 ≤ |1 + 2 * Real.tan (θ / 2) * u.im| := by
    have := (abs_le.1 hprod).1
    rw [abs_of_pos (by linarith)]
    linarith
  have hnum : |u.im - Real.tan (θ / 2) / 2| ≤ 3 / 20 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_two]
    linarith
  have key : |(mobPhi (-θ) u).im| * |1 + 2 * Real.tan (θ / 2) * u.im| ≤ 3 / 20 := by
    rw [← abs_mul, hy]; exact hnum
  by_contra hle
  have hlt := not_le.1 hle
  have : 1 * (49 / 50) ≤ |(mobPhi (-θ) u).im| * |1 + 2 * Real.tan (θ / 2) * u.im| :=
    mul_le_mul hlt.le hden (by norm_num) (by linarith)
  linarith

end SmallGammaGeodesics
