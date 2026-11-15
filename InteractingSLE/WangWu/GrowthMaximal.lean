/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.GrowthVariance
import QuantumZipper.Proofs.Zipper.UnifSWGaussSup
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Gaussian maximal estimate of Lemma 4.6 (Wang–Wu, §4.2)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.2, proof of
Lemma 4.6 (text dump lines 1071–1103): "The standard Gaussian maximal estimate gives an integrable
random variable `S` such that `sup_{B(z,2^{-n}) ⊂ D} |F_n(z)| ≤ S (n + 1)`, `n ≥ 1`. (*)"

Here, for the zero-boundary GFF `h` on `ℍ` and a window radius `R`, the mollified values
`F_n(z) = ⟨h, bump_{z,2^{-n}}/(4^{-n} m)⟩` at rational centres `z` with `B̄(z, 2^{-n}) ⊂ ℍ`,
`|z| ≤ R`, form a countable centred Gaussian process (`windowField`). The source's dyadic chaining
is replaced by QuantumZipper's Dudley/Borell–TIS bound `QuantumZipper.RegUnif.swg_exp_sup_le`,
applied on each cell of side `2^{-n}` (Hölder modulus with `β = 1`, `L² = C 2ⁿ (n + 1)`,
`σ² = C (n + 1)`); a union over the `O(4ⁿ)` cells and a sum over `n` give
`E[S] < ∞` for `S = sup_{n, z} F_n(z)/(n + 1)` (`lintegral_windowSup_lt_top`).

## Main definitions and results

* `dyScale n = 2^{-n}`, `ratPt a b = a + b i`, `IsWindowIdx R n a b`;
* `windowTest R i`, `windowField h R i ω = h ω (windowTest R i)` (index `i = (sign, n, a, b)`);
* `windowSup h R ω = sup_i F_i(ω)/(n_i + 1)` and `lintegral_windowSup_lt_top`;
* `abs_windowField_le`: `|F_n(z)| ≤ (n + 1) S`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace InteractingSLE.WangWu

open GFF (bumpFun bumpMass bumpMass_pos bumpTest coe_bumpTest)

/-! ### Dyadic scales and rational centres -/

/-- The dyadic scale `2^{-n}`. -/
def dyScale (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

lemma dyScale_pos (n : ℕ) : 0 < dyScale n := by unfold dyScale; positivity

lemma dyScale_le_one (n : ℕ) : dyScale n ≤ 1 := by
  unfold dyScale; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma dyScale_mul_two_pow (n : ℕ) : dyScale n * 2 ^ n = 1 := by
  unfold dyScale; rw [← mul_pow]; norm_num

/-- The rational point `a + b i`. -/
def ratPt (a b : ℚ) : ℂ := ⟨a, b⟩

/-- `(n, a + b i)` is an admissible window index: `B̄(a + bi, 2^{-n}) ⊂ ℍ` and `|a + bi| ≤ R`. -/
def IsWindowIdx (R : ℝ) (n : ℕ) (a b : ℚ) : Prop := dyScale n < (b : ℝ) ∧ ‖ratPt a b‖ ≤ R

lemma closedBall_subset_H_of_lt {z : ℂ} {δ : ℝ} (h : δ < z.im) :
    closedBall z δ ⊆ QuantumZipper.H := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  have h1 := Complex.abs_im_le_norm (y - z)
  rw [Complex.sub_im] at h1
  show 0 < y.im
  linarith [neg_abs_le (y.im - z.im)]

lemma IsWindowIdx.closedBall_subset {R : ℝ} {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b) :
    closedBall (ratPt a b) (dyScale n) ⊆ upperHalfPlaneOpens :=
  closedBall_subset_H_of_lt hi.1

/-- The window index type: sign, scale, rational centre. -/
abbrev WinIdx : Type := Bool × ℕ × ℚ × ℚ

/-- The sign `±1` of a window index. -/
def winSign (s : Bool) : ℝ := if s then 1 else -1

lemma abs_winSign (s : Bool) : |winSign s| = 1 := by cases s <;> simp [winSign]

open Classical in
/-- The window test function: `± bump_{z,δ}/(δ² m)` at an admissible index, `0` otherwise. -/
def windowTest (R : ℝ) (i : WinIdx) : LQGMetric.TestOn upperHalfPlaneOpens :=
  if hi : IsWindowIdx R i.2.1 i.2.2.1 i.2.2.2 then
    (winSign i.1 * (dyScale i.2.1 ^ 2 * bumpMass)⁻¹) •
      bumpTest (ratPt i.2.2.1 i.2.2.2) (dyScale_pos i.2.1) hi.closedBall_subset
  else 0

lemma windowTest_apply_of_isWindowIdx {R : ℝ} {i : WinIdx}
    (hi : IsWindowIdx R i.2.1 i.2.2.1 i.2.2.2) (y : ℂ) :
    windowTest R i y = winSign i.1 * normBump (ratPt i.2.2.1 i.2.2.2) (dyScale i.2.1) y := by
  simp only [windowTest, hi, ↓reduceDIte]
  change (winSign i.1 * (dyScale i.2.1 ^ 2 * bumpMass)⁻¹) * bumpFun _ _ y = _
  rw [normBump, mul_assoc, div_eq_inv_mul]

lemma windowTest_of_not {R : ℝ} {i : WinIdx} (hi : ¬ IsWindowIdx R i.2.1 i.2.2.1 i.2.2.2) :
    windowTest R i = 0 := by
  simp only [windowTest, hi, ↓reduceDIte]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The window field `F_i(ω) = h ω (windowTest R i)`. -/
def windowField (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (R : ℝ) (i : WinIdx) (ω : Ω) :
    ℝ :=
  h ω (windowTest R i)


/-! ### The window field as a Gaussian process -/

section Process

variable {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The reference index `(+, 0, 0, 0)`, which is never admissible: its field is `0`. -/
def winIdx0 : WinIdx := (true, 0, 0, 0)

lemma not_isWindowIdx_winIdx0 (R : ℝ) : ¬ IsWindowIdx R winIdx0.2.1 winIdx0.2.2.1 winIdx0.2.2.2 := by
  intro hi
  have := hi.1
  simp only [winIdx0, dyScale, pow_zero, Rat.cast_zero] at this
  linarith

omit [MeasurableSpace Ω] in
lemma windowField_winIdx0 (R : ℝ) (ω : Ω) : windowField h R winIdx0 ω = 0 := by
  rw [windowField, windowTest_of_not (not_isWindowIdx_winIdx0 R), map_zero]

omit [MeasurableSpace Ω] in
lemma windowField_sub (R : ℝ) (i j : WinIdx) (ω : Ω) :
    windowField h R i ω - windowField h R j ω = h ω (windowTest R i - windowTest R j) :=
  (map_sub (h ω) _ _).symm

theorem isGaussianProcess_windowField
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (R : ℝ) :
    IsGaussianProcess (windowField h R) P :=
  hh.process.gaussian.comp_right (windowTest R)

lemma integral_windowField (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (R : ℝ)
    (i : WinIdx) : ∫ ω, windowField h R i ω ∂P = 0 :=
  hh.process.centered _

lemma measurable_windowField (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (R : ℝ) (i : WinIdx) : Measurable (windowField h R i) :=
  hh.process.measurable _

lemma variance_windowField_sub (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (R : ℝ) (i j : WinIdx) :
    Var[fun ω => windowField h R i ω - windowField h R j ω; P] =
      QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens ⇑(windowTest R i - windowTest R j)
        ⇑(windowTest R i - windowTest R j) := by
  simp_rw [windowField_sub]
  rw [← covariance_self (hh.process.measurable _).aemeasurable, hh.process.covariance_eq]

/-- The variance constant `C_var = (eπ/m)² (log(R + 1) + 8)`. -/
def winVarConst (R : ℝ) : ℝ := (expNegInvGlue 1 * π / bumpMass) ^ 2 * (Real.log (R + 1) + 8)

/-- The increment constant `C_inc = 4 (9πL/m)² (log(R + 3) + 8)`. -/
def winIncConst (R : ℝ) : ℝ := 4 * (9 * π * bumpLip / bumpMass) ^ 2 * (Real.log (R + 3) + 8)

lemma winVarConst_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ winVarConst R := by
  have : 0 ≤ Real.log (R + 1) := Real.log_nonneg (by linarith)
  unfold winVarConst; positivity

lemma winIncConst_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ winIncConst R := by
  have : 0 ≤ Real.log (R + 3) := Real.log_nonneg (by linarith)
  unfold winIncConst; positivity

lemma log_div_dyScale_le {R : ℝ} (hR : 0 < R) (n : ℕ) :
    Real.log (R / dyScale n) ≤ Real.log R + n := by
  rw [Real.log_div hR.ne' (dyScale_pos n).ne']
  have h2 : Real.log (dyScale n) = -(n * Real.log 2) := by
    rw [dyScale, Real.log_pow, Real.log_inv]; ring
  rw [h2]
  have : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **`Var F_n(z) ≤ C_var (n + 1)`** at an admissible index. -/
theorem variance_windowField_le (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R : ℝ} (hR : 0 ≤ R) {i : WinIdx} (hi : IsWindowIdx R i.2.1 i.2.2.1 i.2.2.2) :
    Var[fun ω => windowField h R i ω - windowField h R winIdx0 ω; P] ≤
      winVarConst R * (i.2.1 + 1) := by
  rw [variance_windowField_sub hh, windowTest_of_not (not_isWindowIdx_winIdx0 R), sub_zero]
  set δ := dyScale i.2.1
  have hδ := dyScale_pos i.2.1
  refine (zeroGFFTestCov_le_of_abs_le_normBump (windowTest R i) (x := ratPt i.2.2.1 i.2.2.2) hδ
    fun y => by rw [windowTest_apply_of_isWindowIdx hi, abs_mul, abs_winSign, one_mul]).trans ?_
  have hlog : Real.log ((‖ratPt i.2.2.1 i.2.2.2‖ + δ) / δ) ≤ Real.log (R + 1) + i.2.1 := by
    refine (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right
      (show ‖ratPt i.2.2.1 i.2.2.2‖ + δ ≤ R + 1 by linarith [hi.2, dyScale_le_one i.2.1])
      hδ.le)).trans ?_
    exact log_div_dyScale_le (by linarith) _
  have hL0 : 0 ≤ Real.log (R + 1) := Real.log_nonneg (by linarith)
  have hn : (0 : ℝ) ≤ i.2.1 := Nat.cast_nonneg _
  unfold winVarConst
  have hc : 0 ≤ (expNegInvGlue 1 * π / bumpMass) ^ 2 := sq_nonneg _
  calc (expNegInvGlue 1 * π / bumpMass) ^ 2 * (Real.log ((‖ratPt i.2.2.1 i.2.2.2‖ + δ) / δ) + 8)
      ≤ (expNegInvGlue 1 * π / bumpMass) ^ 2 * (Real.log (R + 1) + i.2.1 + 8) := by gcongr
    _ ≤ _ := by
        rw [mul_assoc]
        gcongr
        nlinarith

/-- The parameter `(a, b) ∈ ℝ²` (sup norm) of a window index. -/
def winParam (i : WinIdx) : Fin 2 → ℝ := ![(i.2.2.1 : ℝ), (i.2.2.2 : ℝ)]

lemma norm_ratPt_sub_le (i j : WinIdx) :
    ‖ratPt i.2.2.1 i.2.2.2 - ratPt j.2.2.1 j.2.2.2‖ ≤ 2 * ‖winParam i - winParam j‖ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h0 := norm_le_pi_norm (winParam i - winParam j) 0
  have h1 := norm_le_pi_norm (winParam i - winParam j) 1
  have e0 : (winParam i - winParam j) 0 = (i.2.2.1 : ℝ) - j.2.2.1 := by simp [winParam]
  have e1 : (winParam i - winParam j) 1 = (i.2.2.2 : ℝ) - j.2.2.2 := by simp [winParam]
  rw [e0, Real.norm_eq_abs] at h0
  rw [e1, Real.norm_eq_abs] at h1
  simp only [ratPt, Complex.sub_re, Complex.sub_im]
  linarith

/-- **`Var(F_n(z) − F_n(w)) ≤ C_inc 2ⁿ (n + 1) |p_z − p_w|`** for admissible indices of the same
sign and scale whose parameters are within `2^{-n}`. -/
theorem variance_windowField_sub_le (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R : ℝ} (hR : 0 ≤ R) {i j : WinIdx} (hi : IsWindowIdx R i.2.1 i.2.2.1 i.2.2.2)
    (hj : IsWindowIdx R j.2.1 j.2.2.1 j.2.2.2) (hs : i.1 = j.1) (hn : i.2.1 = j.2.1)
    (hp : ‖winParam i - winParam j‖ ≤ dyScale i.2.1) :
    Var[fun ω => windowField h R i ω - windowField h R j ω; P] ≤
      winIncConst R * 2 ^ i.2.1 * (i.2.1 + 1) * ‖winParam i - winParam j‖ := by
  rw [variance_windowField_sub hh]
  set δ := dyScale i.2.1
  have hδ := dyScale_pos i.2.1
  set z := ratPt i.2.2.1 i.2.2.2
  set w := ratPt j.2.2.1 j.2.2.2
  set q := ‖winParam i - winParam j‖
  have hzw : ‖z - w‖ ≤ 2 * q := norm_ratPt_sub_le i j
  have hq0 : 0 ≤ q := norm_nonneg _
  have habs : ∀ y, |(windowTest R i - windowTest R j) y| ≤ |normBump z δ y - normBump w δ y| := by
    intro y
    change |windowTest R i y - windowTest R j y| ≤ _
    rw [windowTest_apply_of_isWindowIdx hi, windowTest_apply_of_isWindowIdx hj, ← hs, ← hn,
      ← mul_sub, abs_mul, abs_winSign, one_mul]
  refine (zeroGFFTestCov_le_of_abs_le_normBump_sub _ hδ habs (by linarith)).trans ?_
  have hlog : Real.log ((‖z‖ + 3 * δ) / (3 * δ)) ≤ Real.log (R + 3) + i.2.1 := by
    have h1 : (‖z‖ + 3 * δ) / (3 * δ) ≤ (R + 3) / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ]
      nlinarith [hi.2, dyScale_le_one i.2.1, norm_nonneg z]
    refine (Real.log_le_log (by positivity) h1).trans ?_
    exact log_div_dyScale_le (by linarith) _
  have hsq : (‖z - w‖ / δ) ^ 2 ≤ 4 * 2 ^ i.2.1 * q := by
    have h1 : ‖z - w‖ / δ ≤ 2 * (q / δ) := by
      rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hzw hδ.le
    have h2 : q / δ ≤ 1 := (div_le_one hδ).2 hp
    have h3 : 0 ≤ q / δ := div_nonneg hq0 hδ.le
    have h4 : (‖z - w‖ / δ) ^ 2 ≤ 4 * (q / δ) := by
      have h5 : 0 ≤ ‖z - w‖ / δ := div_nonneg (norm_nonneg _) hδ.le
      nlinarith
    have h6 : q / δ = 2 ^ i.2.1 * q := by
      have e := dyScale_mul_two_pow i.2.1
      rw [div_eq_iff hδ.ne']
      linear_combination (-q) * e
    rw [h6] at h4; linarith
  have hL0 : 0 ≤ Real.log (R + 3) := Real.log_nonneg (by linarith)
  have hn0 : (0 : ℝ) ≤ i.2.1 := Nat.cast_nonneg _
  have hc : 0 ≤ (9 * π * bumpLip / bumpMass) ^ 2 := sq_nonneg _
  have hlog8 : 0 ≤ Real.log ((‖z‖ + 3 * δ) / (3 * δ)) + 8 := by
    have : 0 ≤ Real.log ((‖z‖ + 3 * δ) / (3 * δ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith [norm_nonneg z])
    linarith
  calc (9 * π * bumpLip / bumpMass) ^ 2 * (‖z - w‖ / δ) ^ 2 *
        (Real.log ((‖z‖ + 3 * δ) / (3 * δ)) + 8)
      ≤ (9 * π * bumpLip / bumpMass) ^ 2 * (4 * 2 ^ i.2.1 * q) * (Real.log (R + 3) + i.2.1 + 8) := by
        gcongr
    _ ≤ winIncConst R * 2 ^ i.2.1 * (i.2.1 + 1) * q := by
        unfold winIncConst
        have h2n : (0 : ℝ) ≤ 2 ^ i.2.1 := by positivity
        have key : Real.log (R + 3) + i.2.1 + 8 ≤ (Real.log (R + 3) + 8) * (i.2.1 + 1) := by
          nlinarith
        calc (9 * π * bumpLip / bumpMass) ^ 2 * (4 * 2 ^ i.2.1 * q) *
              (Real.log (R + 3) + i.2.1 + 8)
            ≤ (9 * π * bumpLip / bumpMass) ^ 2 * (4 * 2 ^ i.2.1 * q) *
              ((Real.log (R + 3) + 8) * (i.2.1 + 1)) := by gcongr
          _ = _ := by ring

end Process

/-! ### Cells of side `2^{-n}` -/

/-- The cell of a window index at scale `n`: `(⌊(a + R) 2ⁿ⌋₊, ⌊(b + R) 2ⁿ⌋₊)`. -/
def winCellOf (R : ℝ) (n : ℕ) (a b : ℚ) : ℕ × ℕ :=
  (⌊((a : ℝ) + R) * 2 ^ n⌋₊, ⌊((b : ℝ) + R) * 2 ^ n⌋₊)

/-- The admissible indices of sign `s` and scale `n` in the cell `k`. -/
def winCell (R : ℝ) (s : Bool) (n : ℕ) (k : ℕ × ℕ) : Set WinIdx :=
  {i | i.1 = s ∧ i.2.1 = n ∧ IsWindowIdx R n i.2.2.1 i.2.2.2 ∧ winCellOf R n i.2.2.1 i.2.2.2 = k}

/-- The box of cells at scale `n`. -/
def winBox (R : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (⌊2 * R * 2 ^ n⌋₊ + 1) ×ˢ Finset.range (⌊2 * R * 2 ^ n⌋₊ + 1)

lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ⌊x⌋₊ = ⌊y⌋₊) :
    |x - y| < 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le hy
  have h4 := Nat.lt_floor_add_one y
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

lemma IsWindowIdx.abs_re_le {R : ℝ} {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b) :
    |(a : ℝ)| ≤ R := (Complex.abs_re_le_norm (ratPt a b)).trans hi.2

lemma IsWindowIdx.abs_im_le {R : ℝ} {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b) :
    |(b : ℝ)| ≤ R := (Complex.abs_im_le_norm (ratPt a b)).trans hi.2

lemma abs_sub_le_of_floor_eq {R a a' : ℝ} {n : ℕ} (ha : |a| ≤ R) (ha' : |a'| ≤ R)
    (h : ⌊(a + R) * 2 ^ n⌋₊ = ⌊(a' + R) * 2 ^ n⌋₊) : |a - a'| ≤ dyScale n := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hx : 0 ≤ (a + R) * 2 ^ n := mul_nonneg (by linarith [neg_abs_le a]) h2n.le
  have hy : 0 ≤ (a' + R) * 2 ^ n := mul_nonneg (by linarith [neg_abs_le a']) h2n.le
  have h1 := abs_sub_lt_one_of_floor_eq hx hy h
  rw [← sub_mul, add_sub_add_right_eq_sub, abs_mul, abs_of_pos h2n] at h1
  have e := dyScale_mul_two_pow n
  have : |a - a'| = |a - a'| * 2 ^ n * dyScale n := by
    rw [mul_assoc, mul_comm (2 ^ n : ℝ), e, mul_one]
  rw [this]
  have hδ := dyScale_pos n
  nlinarith

lemma norm_winParam_sub_le_of_mem_winCell {R : ℝ} {s : Bool} {n : ℕ} {k : ℕ × ℕ} {i j : WinIdx}
    (hi : i ∈ winCell R s n k) (hj : j ∈ winCell R s n k) :
    ‖winParam i - winParam j‖ ≤ dyScale n := by
  obtain ⟨-, hin, hiw, hik⟩ := hi
  obtain ⟨-, hjn, hjw, hjk⟩ := hj
  have hk : winCellOf R n i.2.2.1 i.2.2.2 = winCellOf R n j.2.2.1 j.2.2.2 := hik.trans hjk.symm
  simp only [winCellOf, Prod.mk.injEq] at hk
  refine (pi_norm_le_iff_of_nonneg (dyScale_pos n).le).2 fun c => ?_
  fin_cases c
  · simp only [winParam, Pi.sub_apply, Fin.zero_eta, Matrix.cons_val_zero, Real.norm_eq_abs]
    exact abs_sub_le_of_floor_eq hiw.abs_re_le hjw.abs_re_le hk.1
  · simp only [winParam, Pi.sub_apply, Fin.mk_one, Matrix.cons_val_one, Real.norm_eq_abs]
    exact abs_sub_le_of_floor_eq hiw.abs_im_le hjw.abs_im_le hk.2

lemma winCellOf_mem_winBox {R : ℝ} {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b) :
    winCellOf R n a b ∈ winBox R n := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hle : ∀ x : ℝ, |x| ≤ R → ⌊(x + R) * 2 ^ n⌋₊ < ⌊2 * R * 2 ^ n⌋₊ + 1 := by
    intro x hx
    refine Nat.lt_succ_of_le (Nat.floor_le_floor ?_)
    have := le_abs_self x
    nlinarith
  exact Finset.mem_product.2 ⟨Finset.mem_range.2 (hle _ hi.abs_re_le),
    Finset.mem_range.2 (hle _ hi.abs_im_le)⟩

lemma card_winBox_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((winBox R n).card : ℝ) ≤ (2 * R + 1) ^ 2 * 4 ^ n := by
  rw [winBox, Finset.card_product, Finset.card_range, Nat.cast_mul]
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hM : ((⌊2 * R * 2 ^ n⌋₊ + 1 : ℕ) : ℝ) ≤ (2 * R + 1) * 2 ^ n := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 2 * R * 2 ^ n by positivity)
    nlinarith
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [h4]
  have h0 : (0 : ℝ) ≤ ((⌊2 * R * 2 ^ n⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! ### The exponential moment on one cell -/

/-- The exponent constant `2 F (C_inc + 1) + 5 C_var` (`F` = QuantumZipper's chaining constant). -/
def winExpConst (R : ℝ) : ℝ :=
  2 * QuantumZipper.RegUnif.fgmChainConst 2 1 * (winIncConst R + 1) + 5 * winVarConst R

lemma winExpConst_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ winExpConst R := by
  have := QuantumZipper.RegUnif.fgmChainConst_nonneg 2 one_pos
  have := winIncConst_nonneg hR
  have := winVarConst_nonneg hR
  unfold winExpConst; positivity

lemma sqrt_le_add_one {y : ℝ} (hy : 0 ≤ y) : √y ≤ y + 1 := by
  calc √y ≤ √((y + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = y + 1 := Real.sqrt_sq (by linarith)

section Cell

variable {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **Exponential moment of the supremum over one cell** (QuantumZipper's Dudley/Borell–TIS bound,
`β = 1`, `L² = C_inc 2ⁿ (n + 1)`, diameter `2^{-n}`, `σ² = C_var (n + 1)`, `t = 2`). -/
theorem lintegral_iSup_exp_winCell_le (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R : ℝ} (hR : 0 ≤ R) (s : Bool) (n : ℕ) (k : ℕ × ℕ) :
    ∫⁻ ω, ⨆ i ∈ winCell R s n k, ENNReal.ofReal (Real.exp (2 * (windowField h R i ω -
      windowField h R winIdx0 ω))) ∂P ≤ ENNReal.ofReal (Real.exp (winExpConst R * (n + 1))) := by
  set Cv := winVarConst R
  set Ci := winIncConst R
  have hCv := winVarConst_nonneg hR
  have hCi := winIncConst_nonneg hR
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set L : ℝ := √(Ci * 2 ^ n * (n + 1)) with hL
  set σ : ℝ := √(Cv * (n + 1)) with hσ
  have hL2 : L ^ 2 = Ci * 2 ^ n * (n + 1) := Real.sq_sqrt (by positivity)
  have hσ2 : σ ^ 2 = Cv * (n + 1) := Real.sq_sqrt (by positivity)
  have key := QuantumZipper.RegUnif.swg_exp_sup_le (isGaussianProcess_windowField hh R)
    (integral_windowField hh R) winParam (L := L) (a := dyScale n) (β := 1) (σ := σ) (t := 2)
    one_pos le_rfl (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by norm_num) winIdx0
    (winCell R s n k) (fun i hi j hj => norm_winParam_sub_le_of_mem_winCell hi hj)
    (fun i hi j hj => by
      have hp := norm_winParam_sub_le_of_mem_winCell hi hj
      obtain ⟨his, hin, hiw, -⟩ := hi
      obtain ⟨hjs, hjn, hjw, -⟩ := hj
      rw [Real.rpow_one, hL2]
      rw [← hin] at hp hiw
      rw [← hjn] at hjw
      have := variance_windowField_sub_le hh hR hiw hjw (his.trans hjs.symm) (hin.trans hjn.symm)
        hp
      rw [hin] at this
      exact this)
    (fun i hi => by
      obtain ⟨-, hin, hiw, -⟩ := hi
      rw [hσ2]
      rw [← hin] at hiw
      have := variance_windowField_le hh hR hiw
      rw [hin] at this
      exact this)
  refine key.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  -- the exponent
  have hF := QuantumZipper.RegUnif.fgmChainConst_nonneg 2 one_pos
  have hsq : L * dyScale n ^ ((1 : ℝ) / 2) = √(Ci * (n + 1)) := by
    rw [hL, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    congr 1
    have e := dyScale_mul_two_pow n
    linear_combination (Ci * (n + 1)) * e
  have hsq' : √(Ci * (n + 1)) ≤ (Ci + 1) * (n + 1) := by
    refine (sqrt_le_add_one (by positivity)).trans ?_
    nlinarith
  have hpi : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [mul_assoc, hsq, hσ2, winExpConst]
  nlinarith [mul_le_mul_of_nonneg_left hsq' hF, mul_nonneg hCv (by linarith : (0 : ℝ) ≤ n + 1)]

end Cell

/-! ### The global supremum `S` and its integrability -/

/-- The admissible window indices. -/
def winAdm (R : ℝ) : Set WinIdx := {i | IsWindowIdx R i.2.1 i.2.2.1 i.2.2.2}

/-- `S(ω) = sup_i F_i(ω)/(n_i + 1)` over admissible indices (both signs). -/
def windowSup (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (R : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ i ∈ winAdm R, ENNReal.ofReal (windowField h R i ω / (i.2.1 + 1))

lemma ofReal_div_le_add_exp {K y : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    ENNReal.ofReal (y / (n + 1)) ≤
      ENNReal.ofReal K + ENNReal.ofReal (Real.exp (-(K * (n + 1)))) *
        ENNReal.ofReal (Real.exp (2 * y)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  by_cases hy : y / (n + 1) ≤ K
  · exact (ENNReal.ofReal_le_ofReal hy).trans le_self_add
  · push Not at hy
    refine le_add_left ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal ?_
    set u := y / (n + 1) with hu
    have hyu : y = u * (n + 1) := by rw [hu]; field_simp
    have h1 : 2 * u - K ≤ -(K * (n + 1)) + 2 * y := by
      rw [hyu]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    calc u ≤ 2 * u - K + 1 := by linarith
      _ ≤ Real.exp (2 * u - K) := by linarith [Real.add_one_le_exp (2 * u - K)]
      _ ≤ _ := Real.exp_le_exp.2 h1

section Sup

variable {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
lemma measurable_windowSup (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (R : ℝ) :
    Measurable (windowSup h R) :=
  Measurable.biSup _ (Set.to_countable _) fun i _ =>
    ENNReal.measurable_ofReal.comp ((measurable_windowField hh R i).div_const _)

/-- **The Gaussian maximal estimate (*)**: `E[S] < ∞`. -/
theorem lintegral_windowSup_lt_top (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R : ℝ} (hR : 0 ≤ R) : ∫⁻ ω, windowSup h R ω ∂P < ∞ := by
  set E := winExpConst R
  set K := E + 2
  have hE := winExpConst_nonneg hR
  have hK : 0 ≤ K := by positivity
  set T : ℕ → Bool → ℕ × ℕ → Ω → ℝ≥0∞ := fun n s k ω => ⨆ i ∈ winCell R s n k,
    ENNReal.ofReal (Real.exp (2 * (windowField h R i ω - windowField h R winIdx0 ω))) with hT
  set c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-(K * (n + 1)))) with hc
  have hTm : ∀ n s k, Measurable (T n s k) := fun n s k =>
    Measurable.biSup _ (Set.to_countable _) fun i _ =>
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (((measurable_windowField hh R i).sub (measurable_windowField hh R winIdx0)).const_mul 2))
  -- pointwise domination
  have hpt : ∀ ω, windowSup h R ω ≤
      ENNReal.ofReal K + ∑' n, ∑ s : Bool, ∑ k ∈ winBox R n, c n * T n s k ω := by
    intro ω
    refine iSup₂_le fun i hi => ?_
    refine (ofReal_div_le_add_exp hK i.2.1).trans (add_le_add le_rfl ?_)
    have hmem : i ∈ winCell R i.1 i.2.1 (winCellOf R i.2.1 i.2.2.1 i.2.2.2) :=
      ⟨rfl, rfl, hi, rfl⟩
    have h1 : ENNReal.ofReal (Real.exp (2 * windowField h R i ω)) ≤
        T i.2.1 i.1 (winCellOf R i.2.1 i.2.2.1 i.2.2.2) ω := by
      refine le_of_eq_of_le ?_ (le_iSup₂ (f := fun j (_ : j ∈ winCell R i.1 i.2.1
        (winCellOf R i.2.1 i.2.2.1 i.2.2.2)) => ENNReal.ofReal (Real.exp (2 *
          (windowField h R j ω - windowField h R winIdx0 ω)))) i hmem)
      rw [windowField_winIdx0, sub_zero]
    calc ENNReal.ofReal (Real.exp (-(K * (i.2.1 + 1)))) *
          ENNReal.ofReal (Real.exp (2 * windowField h R i ω))
        ≤ c i.2.1 * T i.2.1 i.1 (winCellOf R i.2.1 i.2.2.1 i.2.2.2) ω := mul_le_mul_right h1 _
      _ ≤ ∑ k ∈ winBox R i.2.1, c i.2.1 * T i.2.1 i.1 k ω :=
          Finset.single_le_sum (f := fun k => c i.2.1 * T i.2.1 i.1 k ω) (fun _ _ => zero_le)
            (winCellOf_mem_winBox hi)
      _ ≤ ∑ s : Bool, ∑ k ∈ winBox R i.2.1, c i.2.1 * T i.2.1 s k ω :=
          Finset.single_le_sum (f := fun s => ∑ k ∈ winBox R i.2.1, c i.2.1 * T i.2.1 s k ω)
            (fun _ _ => zero_le) (Finset.mem_univ _)
      _ ≤ _ := ENNReal.le_tsum (f := fun n => ∑ s : Bool, ∑ k ∈ winBox R n, c n * T n s k ω) _
  -- integrate
  have hint : ∀ n s k, c n * ∫⁻ ω, T n s k ω ∂P ≤ ENNReal.ofReal (Real.exp (-(2 * (n + 1)))) := by
    intro n s k
    refine (mul_le_mul_right (lintegral_iSup_exp_winCell_le hh hR s n k) _).trans (le_of_eq ?_)
    rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hsum : ∀ n, ∫⁻ ω, ∑ s : Bool, ∑ k ∈ winBox R n, c n * T n s k ω ∂P ≤
      ENNReal.ofReal (2 * (2 * R + 1) ^ 2 * Real.exp (-2)) * ENNReal.ofReal (4 * Real.exp (-2)) ^ n := by
    intro n
    rw [lintegral_finsetSum _ fun s _ =>
      Finset.measurable_sum _ fun k _ => (hTm n s k).const_mul _]
    calc ∑ s : Bool, ∫⁻ ω, ∑ k ∈ winBox R n, c n * T n s k ω ∂P
        = ∑ s : Bool, ∑ k ∈ winBox R n, c n * ∫⁻ ω, T n s k ω ∂P := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [lintegral_finsetSum _ fun k _ => (hTm n s k).const_mul _]
          exact Finset.sum_congr rfl fun k _ => lintegral_const_mul _ (hTm n s k)
      _ ≤ ∑ s : Bool, ∑ k ∈ winBox R n, ENNReal.ofReal (Real.exp (-(2 * (n + 1)))) :=
          Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k _ => hint n s k
      _ = ENNReal.ofReal (2 * (winBox R n).card * Real.exp (-(2 * (n + 1)))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
            nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          push_cast; ring_nf
      _ ≤ ENNReal.ofReal (2 * ((2 * R + 1) ^ 2 * 4 ^ n) * Real.exp (-(2 * (n + 1)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          gcongr
          exact card_winBox_le hR n
      _ = _ := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_pow, ← Real.exp_nat_mul]
          have : Real.exp (-(2 * ((n : ℝ) + 1))) = Real.exp (-2) * Real.exp (n * (-2)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
  have hq : ENNReal.ofReal (4 * Real.exp (-2)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    have h4 : 0 < Real.exp (-2) := Real.exp_pos _
    nlinarith
  calc ∫⁻ ω, windowSup h R ω ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal K + ∑' n, ∑ s : Bool, ∑ k ∈ winBox R n, c n * T n s k ω) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal K + ∑' n, ∫⁻ ω, ∑ s : Bool, ∑ k ∈ winBox R n, c n * T n s k ω ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun n => (Finset.measurable_sum _ fun s _ =>
            Finset.measurable_sum _ fun k _ => (hTm n s k).const_mul _).aemeasurable]
    _ ≤ ENNReal.ofReal K + ∑' n : ℕ, ENNReal.ofReal (2 * (2 * R + 1) ^ 2 * Real.exp (-2)) *
          ENNReal.ofReal (4 * Real.exp (-2)) ^ n :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hsum)
    _ < ∞ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        refine ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt hq

/-- `S` is a.s. finite. -/
lemma ae_windowSup_lt_top (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {R : ℝ}
    (hR : 0 ≤ R) : ∀ᵐ ω ∂P, windowSup h R ω < ∞ :=
  ae_lt_top (measurable_windowSup hh R) (lintegral_windowSup_lt_top hh hR).ne

/-- The real maximal variable `S = (windowSup).toReal` is integrable. -/
lemma integrable_windowSup_toReal (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {R : ℝ} (hR : 0 ≤ R) : Integrable (fun ω => (windowSup h R ω).toReal) P :=
  integrable_toReal_of_lintegral_ne_top (measurable_windowSup hh R).aemeasurable
    (lintegral_windowSup_lt_top hh hR).ne

end Sup

omit [MeasurableSpace Ω] in
/-- **(*)**: `|F_n(z)| ≤ (n + 1) S` at every admissible index where `S < ∞`. -/
theorem abs_windowField_le {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {R : ℝ} {ω : Ω}
    (hS : windowSup h R ω < ∞) {n : ℕ} {a b : ℚ} (hi : IsWindowIdx R n a b) :
    |windowField h R (true, n, a, b) ω| ≤ (n + 1) * (windowSup h R ω).toReal := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have key : ∀ s : Bool, windowField h R (s, n, a, b) ω / (n + 1) ≤ (windowSup h R ω).toReal := by
    intro s
    have hle : ENNReal.ofReal (windowField h R (s, n, a, b) ω / (n + 1)) ≤ windowSup h R ω :=
      le_iSup₂ (f := fun i (_ : i ∈ winAdm R) => ENNReal.ofReal (windowField h R i ω / (i.2.1 + 1)))
        (s, n, a, b) hi
    exact (ENNReal.ofReal_le_iff_le_toReal hS.ne).1 hle
  have hneg : windowField h R (false, n, a, b) ω = -windowField h R (true, n, a, b) ω := by
    simp only [windowField]
    rw [← map_neg]
    congr 1
    ext y
    rw [windowTest_apply_of_isWindowIdx (i := (false, n, a, b)) hi]
    change _ = -(windowTest R (true, n, a, b) y)
    rw [windowTest_apply_of_isWindowIdx (i := (true, n, a, b)) hi]
    simp [winSign]
  have h1 := key true
  have h2 := key false
  rw [hneg, div_le_iff₀ hn] at h2
  rw [div_le_iff₀ hn] at h1
  rw [abs_le]
  constructor <;> nlinarith

end InteractingSLE.WangWu
