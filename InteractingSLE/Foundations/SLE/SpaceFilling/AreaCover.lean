import QuantumZipper.Proofs.RS.KoebeLoewner
import QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Covering the boundary of a conformal image by tents (deterministic part of `area(∂K_t) = 0`)

Packet `planning/packets/PROVE-RS05-74c.md`. Replacement of the Jones–Makarov input of [RS05,
Corollary 5.3] (`area ∂K_t = 0`) by an elementary covering, recorded in
`planning/handoffs/PROVE-RS05-74.md`, "Details" item 6.

Let `f` be holomorphic and injective on `ℍ`. The **Whitney grid** is `z_{m,k} = (k + 1/2) 2^{-m} +
i 2^{-m}` (`whitneyPt`). For `n ∈ ℕ` and `j ∈ ℤ` the **tent** over `[j 2^{-n}, (j+1) 2^{-n})` is the set
of `w ∈ ℍ` with `Im w ≤ 2^{-n}` and `⌊2^n Re w⌋ = j`. Its image lies in the closed ball about
`f(z_{n,j})` of radius

`D(n, j) = Σ_{i ≥ 0} K² 2^{-(n+i)} max_{k ∈ [j 2^i, (j+1) 2^i)} |f'(z_{n+i,k})|`     (`tentRad`)

where `K` is the one-step Koebe distortion constant (`QuantumZipper.RS.koebeStepConst`): join `w` to
`Re w + i 2^{-n}` by the vertical segment, which crosses the Whitney boxes
`[k 2^{-m}, (k+1) 2^{-m}] × [2^{-m-1}, 2^{-m}]`, where `|f'| ≤ K² |f'(z_{m,k})|` (two Koebe steps,
`deriv_ratio_le_two`), then move horizontally to `z_{n,j}` (one Koebe step).

If moreover `|f(w) − w| ≤ C` on `ℍ`, every point `p ∈ \overline{f(ℍ)} \ f(ℍ)` lies, for every `n`, in
one of the balls `\bar B(f(z_{n,j}), D(n,j))` with `|j| ≤ M 2^n`, `M ≥ |p| + C + 1`: the image of the
compact part `{|w| ≤ R, Im w ≥ 2^{-n}}` is compact and contained in `f(ℍ)`, and the image of
`{|w| > R}` stays at distance `≥ 1` from `p`. Hence the area of `\overline{f(ℍ)} \ f(ℍ)` is at most
`π Σ_j D(n,j)²` for every `n`, after splitting according to `M`.

## Main results

* `norm_deriv_le_of_mem_whitneyBox`, `norm_sub_le_vertical`, `norm_sub_le_horizontal`;
* `norm_sub_le_sum_vertical` (telescoping), `edist_le_tentRad` (a tent lies in its ball);
* `exists_edist_le_tentRad_of_mem_closure` (covering), `volume_tentSet_le`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-- The **Whitney grid point** `z_{m,k} = (k + 1/2) 2^{-m} + i 2^{-m}`. -/
def whitneyPt (m : ℕ) (k : ℤ) : ℂ :=
  ((((k : ℝ) + 1 / 2) / 2 ^ m : ℝ) : ℂ) + ((1 / 2 ^ m : ℝ) : ℂ) * I

theorem re_add_im_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

theorem im_add_im_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

@[simp] theorem whitneyPt_re (m : ℕ) (k : ℤ) : (whitneyPt m k).re = ((k : ℝ) + 1 / 2) / 2 ^ m :=
  re_add_im_mul_I _ _

@[simp] theorem whitneyPt_im (m : ℕ) (k : ℤ) : (whitneyPt m k).im = 1 / 2 ^ m :=
  im_add_im_mul_I _ _

theorem dist_same_im (x x' y : ℝ) : dist ((x : ℂ) + (y : ℂ) * I) ((x' : ℂ) + (y : ℂ) * I) = |x - x'| := by
  rw [Complex.dist_of_im_eq (by simp)]
  simp [Real.dist_eq]

theorem dist_same_re (x y y' : ℝ) : dist ((x : ℂ) + (y : ℂ) * I) ((x : ℂ) + (y' : ℂ) * I) = |y - y'| := by
  rw [Complex.dist_of_re_eq (by simp)]
  simp [Real.dist_eq]

section Koebe

variable {f : ℂ → ℂ}

/-- **Koebe distortion on a Whitney box.** For `k 2^{-m} ≤ x ≤ (k+1) 2^{-m}` and
`2^{-m-1} ≤ y ≤ 2^{-m}`, `|f'(x + iy)| ≤ K² |f'(z_{m,k})|`. -/
theorem norm_deriv_le_of_mem_whitneyBox (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {m : ℕ} {k : ℤ} {x y : ℝ}
    (hx1 : (k : ℝ) / 2 ^ m ≤ x) (hx2 : x ≤ ((k : ℝ) + 1) / 2 ^ m)
    (hy1 : 1 / 2 ^ (m + 1) ≤ y) (hy2 : y ≤ 1 / 2 ^ m) :
    ‖deriv f ((x : ℂ) + (y : ℂ) * I)‖ ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt m k)‖ := by
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hhalf : (1 : ℝ) / 2 ^ (m + 1) = 1 / 2 ^ m / 2 := by rw [pow_succ]; field_simp
  have hz : 0 < (whitneyPt m k).im := by rw [whitneyPt_im]; positivity
  have hw : whitneyPt m k = ((((k : ℝ) + 1 / 2) / 2 ^ m : ℝ) : ℂ) + ((1 / 2 ^ m : ℝ) : ℂ) * I := rfl
  refine (deriv_ratio_le_two hd hinj (w := (x : ℂ) + ((1 / 2 ^ m : ℝ) : ℂ) * I) hz ?_ ?_).1
  · rw [hw, dist_same_im, im_add_im_mul_I, abs_le]
    have e1 : ((k : ℝ) + 1 / 2) / 2 ^ m = (k : ℝ) / 2 ^ m + 1 / 2 ^ m / 2 := by ring
    have e2 : ((k : ℝ) + 1) / 2 ^ m = (k : ℝ) / 2 ^ m + 1 / 2 ^ m := by ring
    constructor <;> linarith
  · rw [dist_same_re, im_add_im_mul_I, abs_le]
    constructor <;> linarith

/-- **Mean value inequality on a vertical segment.** -/
theorem norm_sub_le_vertical (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) {x a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hC : ∀ r ∈ Icc a b, ‖deriv f ((x : ℂ) + (r : ℂ) * I)‖ ≤ C) :
    ‖f ((x : ℂ) + (b : ℂ) * I) - f ((x : ℂ) + (a : ℂ) * I)‖ ≤ C * (b - a) := by
  have hderiv : ∀ r ∈ Icc a b, HasDerivWithinAt (fun r : ℝ => f ((x : ℂ) + (r : ℂ) * I))
      (deriv f ((x : ℂ) + (r : ℂ) * I) * I) (Icc a b) r := by
    intro r hr
    have hmem : (x : ℂ) + (r : ℂ) * I ∈ {z : ℂ | 0 < z.im} := by
      show 0 < ((x : ℂ) + (r : ℂ) * I).im
      rw [im_add_im_mul_I]; exact ha.trans_le hr.1
    have hfd : HasDerivAt f (deriv f ((x : ℂ) + (r : ℂ) * I)) ((x : ℂ) + (r : ℂ) * I) :=
      (hd.differentiableAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hmem)).hasDerivAt
    have hline : HasDerivAt (fun r : ℝ => (x : ℂ) + (r : ℂ) * I) I r := by
      simpa using ((hasDerivAt_id r).ofReal_comp.mul_const I).const_add (x : ℂ)
    exact (HasDerivAt.comp r hfd hline).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun r hr => by
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hC r (Ico_subset_Icc_self hr)) b ⟨hab, le_rfl⟩
  exact h

/-- **Mean value inequality on a horizontal segment.** -/
theorem norm_sub_le_horizontal (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) {y a b C : ℝ}
    (hy : 0 < y) (hab : a ≤ b) (hC : ∀ r ∈ Icc a b, ‖deriv f ((r : ℂ) + (y : ℂ) * I)‖ ≤ C) :
    ‖f ((b : ℂ) + (y : ℂ) * I) - f ((a : ℂ) + (y : ℂ) * I)‖ ≤ C * (b - a) := by
  have hderiv : ∀ r ∈ Icc a b, HasDerivWithinAt (fun r : ℝ => f ((r : ℂ) + (y : ℂ) * I))
      (deriv f ((r : ℂ) + (y : ℂ) * I) * 1) (Icc a b) r := by
    intro r _
    have hmem : (r : ℂ) + (y : ℂ) * I ∈ {z : ℂ | 0 < z.im} := by
      show 0 < ((r : ℂ) + (y : ℂ) * I).im
      rw [im_add_im_mul_I]; exact hy
    have hfd : HasDerivAt f (deriv f ((r : ℂ) + (y : ℂ) * I)) ((r : ℂ) + (y : ℂ) * I) :=
      (hd.differentiableAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hmem)).hasDerivAt
    have hline : HasDerivAt (fun r : ℝ => (r : ℂ) + (y : ℂ) * I) 1 r := by
      simpa using (hasDerivAt_id r).ofReal_comp.add_const ((y : ℂ) * I)
    exact (HasDerivAt.comp r hfd hline).hasDerivWithinAt
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun r hr => by
      rw [mul_one]
      exact hC r (Ico_subset_Icc_self hr)) b ⟨hab, le_rfl⟩

/-- **The horizontal move to the grid point.** For `k 2^{-n} ≤ x ≤ (k+1) 2^{-n}`,
`|f(x + i 2^{-n}) − f(z_{n,k})| ≤ K² |f'(z_{n,k})| 2^{-n-1}`. -/
theorem norm_sub_whitneyPt_le (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {n : ℕ} {k : ℤ} {x : ℝ}
    (hx1 : (k : ℝ) / 2 ^ n ≤ x) (hx2 : x ≤ ((k : ℝ) + 1) / 2 ^ n) :
    ‖f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I) - f (whitneyPt n k)‖
      ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt n k)‖ * (1 / 2 ^ (n + 1)) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  set c : ℝ := ((k : ℝ) + 1 / 2) / 2 ^ n with hc
  have hhalf : (1 : ℝ) / 2 ^ (n + 1) = 1 / 2 ^ n / 2 := by rw [pow_succ]; field_simp
  have hcx : |x - c| ≤ 1 / 2 ^ (n + 1) := by
    rw [abs_le, hhalf, hc]
    have e1 : ((k : ℝ) + 1 / 2) / 2 ^ n = (k : ℝ) / 2 ^ n + 1 / 2 ^ n / 2 := by ring
    have e2 : ((k : ℝ) + 1) / 2 ^ n = (k : ℝ) / 2 ^ n + 1 / 2 ^ n := by ring
    constructor <;> linarith
  have hz : 0 < (whitneyPt n k).im := by rw [whitneyPt_im]; positivity
  have hK : 0 ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt n k)‖ := by positivity
  have hbound : ∀ r ∈ Icc (min x c) (max x c),
      ‖deriv f ((r : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)‖ ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt n k)‖ := by
    intro r hr
    have hrc : |r - c| ≤ 1 / 2 ^ (n + 1) := by
      have h1 := hr.1; have h2 := hr.2
      rw [abs_le] at hcx ⊢
      constructor
      · rcases le_total x c with h | h
        · rw [min_eq_left h] at h1; linarith
        · rw [min_eq_right h] at h1; linarith
      · rcases le_total x c with h | h
        · rw [max_eq_right h] at h2; linarith
        · rw [max_eq_left h] at h2; linarith
    have hdist : dist ((r : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I) (whitneyPt n k) ≤ (whitneyPt n k).im / 2 := by
      rw [show whitneyPt n k = (c : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I from rfl, dist_same_im,
        im_add_im_mul_I, ← hhalf]
      exact hrc
    exact ((QuantumZipper.CA.Koebe.deriv_ratio_le hd hinj hz hdist).1).trans
      (mul_le_mul_of_nonneg_right le_koebeStepConst_sq (norm_nonneg _))
  have hmv := norm_sub_le_horizontal hd (y := 1 / 2 ^ n) (by positivity) (min_le_max) hbound
  have hmm : max x c - min x c = |x - c| := by
    rcases le_total x c with h | h
    · rw [max_eq_right h, min_eq_left h, abs_sub_comm, abs_of_nonneg (by linarith)]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]
  rw [hmm] at hmv
  have hg : whitneyPt n k = (c : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I := rfl
  calc ‖f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I) - f (whitneyPt n k)‖
      = ‖f ((max x c : ℝ) + ((1 / 2 ^ n : ℝ) : ℂ) * I) - f ((min x c : ℝ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)‖ := by
        rw [hg]
        rcases le_total x c with h | h
        · rw [max_eq_right h, min_eq_left h, norm_sub_rev]
        · rw [max_eq_left h, min_eq_right h]
    _ ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt n k)‖ * |x - c| := hmv
    _ ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt n k)‖ * (1 / 2 ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hcx hK

/-- The dyadic cell of `x` at level `m`: `⌊2^m x⌋ 2^{-m} ≤ x ≤ (⌊2^m x⌋ + 1) 2^{-m}`. -/
theorem dyadic_floor_div_le (x : ℝ) (m : ℕ) : ((⌊x * 2 ^ m⌋ : ℤ) : ℝ) / 2 ^ m ≤ x := by
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem dyadic_le_floor_add_one_div (x : ℝ) (m : ℕ) : x ≤ (((⌊x * 2 ^ m⌋ : ℤ) : ℝ) + 1) / 2 ^ m := by
  rw [le_div_iff₀ (by positivity)]
  exact (Int.lt_floor_add_one _).le

/-- **One vertical Whitney step.** For `2^{-m-1} ≤ y ≤ 2^{-m}`,
`|f(x + i2^{-m}) − f(x + iy)| ≤ K² |f'(z_{m,⌊2^m x⌋})| 2^{-m-1}`. -/
theorem norm_sub_le_whitney_step (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) (x : ℝ) {m : ℕ} {y : ℝ}
    (hy1 : 1 / 2 ^ (m + 1) ≤ y) (hy2 : y ≤ 1 / 2 ^ m) :
    ‖f ((x : ℂ) + ((1 / 2 ^ m : ℝ) : ℂ) * I) - f ((x : ℂ) + (y : ℂ) * I)‖
      ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt m ⌊x * 2 ^ m⌋)‖ * (1 / 2 ^ (m + 1)) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy1
  have h := norm_sub_le_vertical hd (x := x) hy0 hy2 (C := koebeStepConst ^ 2 *
    ‖deriv f (whitneyPt m ⌊x * 2 ^ m⌋)‖) fun r hr =>
      norm_deriv_le_of_mem_whitneyBox hd hinj (dyadic_floor_div_le x m) (dyadic_le_floor_add_one_div x m)
        (hy1.trans hr.1) hr.2
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have : (1 : ℝ) / 2 ^ (m + 1) = 1 / 2 ^ m / 2 := by rw [pow_succ]; field_simp
  linarith

/-- **Telescoping along the vertical segment.** For `2^{-(n+L+1)} ≤ y ≤ 2^{-n}`,
`|f(x + iy) − f(x + i2^{-n})| ≤ Σ_{i ≤ L} K² |f'(z_{n+i, ⌊2^{n+i} x⌋})| 2^{-(n+i)-1}`. -/
theorem norm_sub_le_sum_vertical (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) (x : ℝ) (n : ℕ) :
    ∀ L : ℕ, ∀ y : ℝ, 1 / 2 ^ (n + L + 1) ≤ y → y ≤ 1 / 2 ^ n →
      ‖f ((x : ℂ) + (y : ℂ) * I) - f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)‖ ≤
        ∑ i ∈ Finset.range (L + 1), koebeStepConst ^ 2 *
          ‖deriv f (whitneyPt (n + i) ⌊x * 2 ^ (n + i)⌋)‖ * (1 / 2 ^ (n + i + 1)) := by
  intro L
  induction L with
  | zero =>
    intro y hy1 hy2
    rw [norm_sub_rev, Finset.sum_range_one, add_zero]
    exact norm_sub_le_whitney_step hd hinj x hy1 hy2
  | succ L ih =>
    intro y hy1 hy2
    rw [Finset.sum_range_succ]
    have hterm : 0 ≤ koebeStepConst ^ 2 * ‖deriv f (whitneyPt (n + (L + 1)) ⌊x * 2 ^ (n + (L + 1))⌋)‖ *
        (1 / 2 ^ (n + (L + 1) + 1)) := by positivity
    by_cases hy : 1 / 2 ^ (n + L + 1) ≤ y
    · exact (ih y hy hy2).trans (le_add_of_nonneg_right hterm)
    · push Not at hy
      have hmid1 : (1 : ℝ) / 2 ^ (n + L + 1) ≤ 1 / 2 ^ n :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      have h1 := ih (1 / 2 ^ (n + L + 1)) le_rfl hmid1
      have hy1' : 1 / 2 ^ (n + (L + 1) + 1) ≤ y := by
        rw [show n + (L + 1) + 1 = n + L + 1 + 1 by ring]; exact hy1
      have h2 := norm_sub_le_whitney_step hd hinj x (m := n + (L + 1)) hy1'
        (by rw [show n + (L + 1) = n + L + 1 by ring]; exact hy.le)
      rw [show ((1 / 2 ^ (n + (L + 1)) : ℝ) : ℂ) = ((1 / 2 ^ (n + L + 1) : ℝ) : ℂ) by
        rw [show n + (L + 1) = n + L + 1 by ring]] at h2
      calc ‖f ((x : ℂ) + (y : ℂ) * I) - f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)‖
          ≤ ‖f ((x : ℂ) + ((1 / 2 ^ (n + L + 1) : ℝ) : ℂ) * I) - f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)‖
            + ‖f ((x : ℂ) + ((1 / 2 ^ (n + L + 1) : ℝ) : ℂ) * I) - f ((x : ℂ) + (y : ℂ) * I)‖ := by
            have := norm_sub_le_norm_sub_add_norm_sub (f ((x : ℂ) + (y : ℂ) * I))
              (f ((x : ℂ) + ((1 / 2 ^ (n + L + 1) : ℝ) : ℂ) * I))
              (f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I))
            rw [norm_sub_rev (f ((x : ℂ) + (y : ℂ) * I))
              (f ((x : ℂ) + ((1 / 2 ^ (n + L + 1) : ℝ) : ℂ) * I))] at this
            linarith
        _ ≤ _ := add_le_add h1 h2

/-- The maximum of `|f'|` over the level-`(n+i)` grid points above `[j 2^{-n}, (j+1) 2^{-n})`. -/
def gridSup (f : ℂ → ℂ) (n : ℕ) (j : ℤ) (i : ℕ) : ℝ≥0 :=
  (Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i)).sup fun k => ‖deriv f (whitneyPt (n + i) k)‖₊

/-- The **tent radius** `D(n, j) = Σ_i K² 2^{-(n+i)} max_{k} |f'(z_{n+i,k})|`. -/
def tentRad (f : ℂ → ℂ) (n : ℕ) (j : ℤ) : ℝ≥0∞ :=
  ∑' i : ℕ, ENNReal.ofReal (koebeStepConst ^ 2 / 2 ^ (n + i)) * (gridSup f n j i : ℝ≥0∞)

theorem floor_mem_Ico (x : ℝ) (n i : ℕ) :
    ⌊x * 2 ^ (n + i)⌋ ∈ Finset.Ico (⌊x * 2 ^ n⌋ * 2 ^ i) ((⌊x * 2 ^ n⌋ + 1) * 2 ^ i) := by
  rw [Finset.mem_Ico]
  have h1 : ((⌊x * 2 ^ n⌋ : ℤ) : ℝ) ≤ x * 2 ^ n := Int.floor_le _
  have h2 : x * 2 ^ n < ((⌊x * 2 ^ n⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hp : (0 : ℝ) < 2 ^ i := by positivity
  have e : x * 2 ^ (n + i) = x * 2 ^ n * 2 ^ i := by rw [pow_add]; ring
  constructor
  · apply Int.le_floor.2
    push_cast
    rw [e]; exact mul_le_mul_of_nonneg_right h1 hp.le
  · apply Int.floor_lt.2
    push_cast
    rw [e]; exact mul_lt_mul_of_pos_right h2 hp

/-- **The image of a tent lies in its ball.** For `0 < Im w ≤ 2^{-n}` and `j = ⌊2^n Re w⌋`,
`|f(w) − f(z_{n,j})| ≤ D(n, j)`. -/
theorem edist_le_tentRad (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {w : ℂ} (hw : 0 < w.im) {n : ℕ}
    (hwn : w.im ≤ 1 / 2 ^ n) :
    edist (f w) (f (whitneyPt n ⌊w.re * 2 ^ n⌋)) ≤ tentRad f n ⌊w.re * 2 ^ n⌋ := by
  set x := w.re with hx
  set y := w.im with hy
  have hw' : w = (x : ℂ) + (y : ℂ) * I := (Complex.re_add_im w).symm
  obtain ⟨L, hL⟩ : ∃ L : ℕ, 1 / 2 ^ (n + L + 1) ≤ y := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hw (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, le_trans ?_ (le_of_lt (by rwa [one_div_pow] at hN))⟩
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  set K2 := koebeStepConst ^ 2 with hK2
  set a : ℕ → ℝ := fun i => K2 * ‖deriv f (whitneyPt (n + i) ⌊x * 2 ^ (n + i)⌋)‖ with ha
  have hv := norm_sub_le_sum_vertical hd hinj x n L y hL hwn
  have hh := norm_sub_whitneyPt_le hd hinj (dyadic_floor_div_le x n) (dyadic_le_floor_add_one_div x n) (f := f)
  have ha0 : 0 ≤ a 0 := by positivity
  have hreal : ‖f w - f (whitneyPt n ⌊x * 2 ^ n⌋)‖ ≤
      ∑ i ∈ Finset.range (L + 1), a i * (1 / 2 ^ (n + i)) := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (f w)
      (f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)) (f (whitneyPt n ⌊x * 2 ^ n⌋))
    rw [hw'] at htri ⊢
    have hsplit : ∑ i ∈ Finset.range (L + 1), a i * (1 / 2 ^ (n + i)) =
        ∑ i ∈ Finset.range (L + 1), a i * (1 / 2 ^ (n + i + 1)) +
          ∑ i ∈ Finset.range (L + 1), a i * (1 / 2 ^ (n + i + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ]; ring
    have hfirst : a 0 * (1 / 2 ^ (n + 0 + 1)) ≤
        ∑ i ∈ Finset.range (L + 1), a i * (1 / 2 ^ (n + i + 1)) :=
      Finset.single_le_sum (f := fun i => a i * (1 / 2 ^ (n + i + 1)))
        (fun i _ => by positivity) (Finset.mem_range.2 (Nat.succ_pos L))
    have hh' : ‖f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I) - f (whitneyPt n ⌊x * 2 ^ n⌋)‖ ≤
        a 0 * (1 / 2 ^ (n + 0 + 1)) := by
      simpa [ha, mul_assoc] using hh
    have hv' : ‖f ((x : ℂ) + (y : ℂ) * I) - f ((x : ℂ) + ((1 / 2 ^ n : ℝ) : ℂ) * I)‖ ≤
        ∑ i ∈ Finset.range (L + 1), a i * (1 / 2 ^ (n + i + 1)) := by
      simpa [ha, mul_assoc] using hv
    rw [hsplit]
    linarith
  rw [edist_dist, dist_eq_norm]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (ENNReal.sum_le_tsum (Finset.range (L + 1)))
  have hle : ‖deriv f (whitneyPt (n + i) ⌊x * 2 ^ (n + i)⌋)‖₊ ≤ gridSup f n ⌊x * 2 ^ n⌋ i :=
    Finset.le_sup (f := fun k => ‖deriv f (whitneyPt (n + i) k)‖₊) (floor_mem_Ico x n i)
  rw [show a i * (1 / 2 ^ (n + i)) = K2 / 2 ^ (n + i) *
      ‖deriv f (whitneyPt (n + i) ⌊x * 2 ^ (n + i)⌋)‖ by rw [ha]; ring,
    ENNReal.ofReal_mul (by positivity), ofReal_norm]
  exact mul_le_mul_right (by exact_mod_cast hle) _

/-- The union of the tent balls at level `n` over `j ∈ [−M 2^n, M 2^n)`. -/
def tentSet (f : ℂ → ℂ) (M n : ℕ) : Set ℂ :=
  ⋃ j ∈ Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n),
    Metric.closedEBall (f (whitneyPt n j)) (tentRad f n j)

/-- **Covering of the boundary of `f(ℍ)` by tent balls.** Let `f` be holomorphic and injective on
`ℍ`, with `|f(w) − w| ≤ C` there. If `p ∈ \overline{f(ℍ)} \ f(ℍ)` and `|p| + C + 2 ≤ M`, then for
every `n`, `p` lies in one of the tent balls `\bar B(f(z_{n,j}), D(n,j))`, `j ∈ [−M 2^n, M 2^n)`. -/
theorem mem_tentSet_of_mem_closure (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {C : ℝ} (hC : ∀ w ∈ H, ‖f w - w‖ ≤ C) {p : ℂ}
    (hp : p ∈ closure (f '' H)) (hpn : p ∉ f '' H) {M : ℕ} (hM : ‖p‖ + C + 2 ≤ M) (n : ℕ) :
    p ∈ tentSet f M n := by
  set R : ℝ := ‖p‖ + C + 1 with hR
  have h2n : (0 : ℝ) < 1 / 2 ^ n := by positivity
  set S1 : Set ℂ := {w | 0 < w.im ∧ R < ‖w‖}
  set S2 : Set ℂ := closedBall 0 R ∩ {w | 1 / 2 ^ n ≤ w.im}
  set S3 : Set ℂ := {w | 0 < w.im ∧ ‖w‖ ≤ R ∧ w.im ≤ 1 / 2 ^ n}
  have hcover : f '' H ⊆ (f '' S1 ∪ f '' S2) ∪ f '' S3 := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : 0 < w.im := hw
    by_cases h1 : R < ‖w‖
    · exact Or.inl (Or.inl ⟨w, ⟨hw', h1⟩, rfl⟩)
    push Not at h1
    by_cases h2 : 1 / 2 ^ n ≤ w.im
    · exact Or.inl (Or.inr ⟨w, ⟨mem_closedBall_zero_iff.2 h1, h2⟩, rfl⟩)
    · push Not at h2
      exact Or.inr ⟨w, ⟨hw', h1, h2.le⟩, rfl⟩
  have hcl := closure_mono hcover hp
  rw [closure_union, closure_union] at hcl
  -- the far part stays at distance `≥ 1` from `p`
  have hfar : p ∉ closure (f '' S1) := by
    have hsub : f '' S1 ⊆ {q | 1 ≤ dist q p} := by
      rintro _ ⟨w, ⟨hw, hwR⟩, rfl⟩
      have := hC w hw
      show 1 ≤ dist (f w) p
      rw [dist_eq_norm]
      have h1 := norm_sub_norm_le w (w - f w)
      have h2 := norm_sub_norm_le (f w) p
      rw [norm_sub_rev] at this
      simp only [sub_sub_cancel] at h1
      linarith
    intro hcp
    have := closure_minimal hsub (isClosed_le continuous_const (continuous_id.dist continuous_const)) hcp
    simp only [mem_ofPred_eq, dist_self] at this
    linarith
  -- the compact part has a compact image inside `f(ℍ)`
  have hcpt : p ∉ closure (f '' S2) := by
    have hS2 : IsCompact S2 := (isCompact_closedBall 0 R).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
    have hS2H : S2 ⊆ {z : ℂ | 0 < z.im} := fun w hw => lt_of_lt_of_le h2n hw.2
    have hK := hS2.image_of_continuousOn (hd.continuousOn.mono hS2H)
    rw [hK.isClosed.closure_eq]
    rintro ⟨w, hw, rfl⟩
    exact hpn ⟨w, hS2H hw, rfl⟩
  have hp3 : p ∈ closure (f '' S3) := by
    rcases hcl with (h | h) | h
    · exact absurd h hfar
    · exact absurd h hcpt
    · exact h
  -- the low part lies in the tent balls
  have htent : f '' S3 ⊆ tentSet f M n := by
    rintro _ ⟨w, ⟨hw, hwR, hwn⟩, rfl⟩
    have hre : |w.re| ≤ R := (Complex.abs_re_le_norm w).trans hwR
    have hRM : R < M := by linarith
    refine mem_iUnion₂.2 ⟨⌊w.re * 2 ^ n⌋, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      have h2p : (0 : ℝ) < 2 ^ n := by positivity
      constructor
      · apply Int.le_floor.2
        push_cast
        have := (abs_le.1 hre).1
        nlinarith
      · apply Int.floor_lt.2
        push_cast
        have := (abs_le.1 hre).2
        nlinarith
    · rw [Metric.mem_closedEBall]
      exact edist_le_tentRad hd hinj hw hwn
  have hclosed : IsClosed (tentSet f M n) :=
    isClosed_biUnion_finset fun j _ => Metric.isClosed_closedEBall
  exact closure_minimal htent hclosed hp3

/-- `\overline{f(ℍ)} \ f(ℍ)` is covered by `⋃_M ⋂_n (tent balls at level n)`. -/
theorem closure_diff_subset_iUnion_iInter_tentSet (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {C : ℝ} (hC : ∀ w ∈ H, ‖f w - w‖ ≤ C) :
    closure (f '' H) \ f '' H ⊆ ⋃ M : ℕ, ⋂ n : ℕ, tentSet f M n := by
  rintro p ⟨hp, hpn⟩
  obtain ⟨M, hM⟩ := exists_nat_ge (‖p‖ + C + 2)
  exact mem_iUnion.2 ⟨M, mem_iInter.2 fun n =>
    mem_tentSet_of_mem_closure hd hinj hC hp hpn hM n⟩

/-- `area(\bar B(c, r)) ≤ π r²` for an extended radius. -/
theorem volume_emetric_closedBall_le (c : ℂ) (r : ℝ≥0∞) :
    volume (Metric.closedEBall c r) ≤ ENNReal.ofReal Real.pi * r ^ 2 := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top (by simp [Real.pi_pos])]
    exact le_top
  · rw [← ENNReal.ofReal_toReal hr, Metric.closedEBall_ofReal ENNReal.toReal_nonneg,
      Complex.volume_closedBall, mul_comm]
    gcongr
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

/-- **Area of the tent union**: `area(⋃_j \bar B(f(z_{n,j}), D(n,j))) ≤ π Σ_j D(n,j)²`. -/
theorem volume_tentSet_le (f : ℂ → ℂ) (M n : ℕ) :
    volume (tentSet f M n) ≤ ∑ j ∈ Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n),
      ENNReal.ofReal Real.pi * tentRad f n j ^ 2 :=
  (measure_biUnion_finset_le _ _).trans
    (Finset.sum_le_sum fun _ _ => volume_emetric_closedBall_le _ _)

end Koebe

end InteractingSLE
