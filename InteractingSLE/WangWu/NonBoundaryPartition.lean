/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.GrowthVariance
import InteractingSLE.Spec.Dimension.BoxCounting

/-!
# A smooth dyadic partition of unity (Wang–Wu Lemma 4.14, Proposition R1: the deterministic part)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.4, proof of Lemma 4.14
(text dump lines 1399–1440), and its restatement as Proposition R1 of the specification supplement
(`source/spec/p433-480.md#id-R1`): "Approximate a smooth test function `p` by its square averages `p_δ` …
Square indicators can equivalently be replaced by fixed smooth approximations in the Green-energy norm."

We use smooth square cut-offs that sum to one, so the decomposition of a test function is exact, with no
approximation error: with `θ(x) = st(x + 1) − st(x)` (`st` = `Real.smoothTransition`), `θ` is smooth,
`0 ≤ θ ≤ 1`, vanishes off `(−1, 1)`, and its integer translates telescope to `1`. The square cut-off of
scale `n` and index `k ∈ ℤ²` is `ψ_{n,k}(z) = θ(2ⁿ Re z − k₁) θ(2ⁿ Im z − k₂)`, supported in the closed square
of side `2 · 2^{-n}` centred at `k 2^{-n}`.

## Main results

* `pouBump`, `sum_pouBump`: the one-dimensional cut-off and its telescoping sum;
* `pouSq`, `sum_pouSq`: the square cut-offs sum to `1` on the box `|2ⁿ Re z|, |2ⁿ Im z| ≤ M`;
* `pouTest φ n k = φ ψ_{n,k}`, a test function on `ℍ`, and `sum_pouTest`: `φ = ∑_{k ∈ pouIdx M} φ ψ_{n,k}`
  when `tsupport φ ⊆ B̄(0, R)` and `R 2ⁿ ≤ M`;
* `zeroGFFTestCov_pouTest_le`: `Var⟨h, φ ψ_{n,k}⟩ ≤ 16 π² B² 16^{-n} (log(‖k 2^{-n}‖ + 2) + n + 8)` for
  `|φ| ≤ B`;
* `card_bad_le`: at most `9 N_n(A ∩ tsupport φ)` of the pieces `φ ψ_{n,k}` have support meeting `A`, where
  `N_n` is the dyadic box count (`Dimension.dyadicCount`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory
open scoped ENNReal Real

namespace InteractingSLE.WangWu

/-! ### The one-dimensional cut-off -/

/-- `θ(x) = st(x + 1) − st(x)`: smooth, in `[0, 1]`, supported in `[−1, 1]`; its integer translates sum to
`1`. -/
def pouBump (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

lemma pouBump_nonneg (x : ℝ) : 0 ≤ pouBump x :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma pouBump_le_one (x : ℝ) : pouBump x ≤ 1 := by
  unfold pouBump
  linarith [Real.smoothTransition.le_one (x + 1), Real.smoothTransition.nonneg x]

lemma abs_pouBump_le_one (x : ℝ) : |pouBump x| ≤ 1 := by
  rw [abs_of_nonneg (pouBump_nonneg x)]; exact pouBump_le_one x

lemma pouBump_eq_zero_of_le {x : ℝ} (hx : x ≤ -1) : pouBump x = 0 := by
  unfold pouBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

lemma pouBump_eq_zero_of_ge {x : ℝ} (hx : 1 ≤ x) : pouBump x = 0 := by
  unfold pouBump
  rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le hx,
    sub_self]

/-- `θ(x) ≠ 0` forces `|x| < 1`. -/
lemma abs_lt_one_of_pouBump_ne_zero {x : ℝ} (hx : pouBump x ≠ 0) : |x| < 1 := by
  rw [abs_lt]
  constructor
  · by_contra h
    exact hx (pouBump_eq_zero_of_le (by linarith))
  · by_contra h
    exact hx (pouBump_eq_zero_of_ge (by linarith))

lemma contDiff_pouBump {n : ℕ∞} : ContDiff ℝ n pouBump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

/-- The telescoping sum over `i < N` of `θ(y − i) `, with `f i = st(y + 1 − i)`. -/
lemma sum_range_pouBump (y : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, pouBump (y - i) =
      Real.smoothTransition (y + 1) - Real.smoothTransition (y + 1 - N) := by
  have h := Finset.sum_range_sub' (fun i : ℕ => Real.smoothTransition (y + 1 - i)) N
  simp only [Nat.cast_zero, sub_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pouBump, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The shift `i ↦ i − M`, an embedding `ℕ ↪ ℤ`. -/
def shiftEmb (M : ℕ) : ℕ ↪ ℤ := ⟨fun i => (i : ℤ) - M, by intro a b h; simpa using h⟩

@[simp] lemma shiftEmb_apply (M i : ℕ) : shiftEmb M i = (i : ℤ) - M := rfl

/-- The integer interval `[−M, M]` as the shifted range `{i − M : i < 2M + 1}`. -/
lemma Icc_neg_eq_map (M : ℕ) :
    Finset.Icc (-(M : ℤ)) M = (Finset.range (2 * M + 1)).map (shiftEmb M) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, shiftEmb_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(j + M).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

/-- **The cut-offs telescope to one.** For `|x| ≤ M`, `∑_{j = −M}^{M} θ(x − j) = 1`. -/
theorem sum_pouBump {M : ℕ} {x : ℝ} (hx : |x| ≤ M) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) M, pouBump (x - j) = 1 := by
  rw [Icc_neg_eq_map, Finset.sum_map]
  simp only [shiftEmb_apply, Int.cast_sub, Int.cast_natCast]
  have h := sum_range_pouBump (x + M) (2 * M + 1)
  have e : ∀ i : ℕ, x + (M : ℝ) - i = x - ((i : ℝ) - M) := fun i => by ring
  simp only [e] at h
  rw [h]
  have hx' := abs_le.1 hx
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith), sub_zero]

/-! ### Square cut-offs -/

/-- The square cut-off `ψ_{n,k}(z) = θ(2ⁿ Re z − k₁) θ(2ⁿ Im z − k₂)` (with the coordinate convention
`x.re * 2 ^ n` of `Dimension.dyadicSquare`). -/
def pouSq (n : ℕ) (k : ℤ × ℤ) (z : ℂ) : ℝ :=
  pouBump (z.re * 2 ^ n - k.1) * pouBump (z.im * 2 ^ n - k.2)

/-- The index box `[−M, M]²`. -/
def pouIdx (M : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M

lemma card_pouIdx (M : ℕ) : (pouIdx M).card = (2 * M + 1) ^ 2 := by
  rw [pouIdx, Finset.card_product, Icc_neg_eq_map, Finset.card_map, Finset.card_range, sq]

lemma pouSq_nonneg (n : ℕ) (k : ℤ × ℤ) (z : ℂ) : 0 ≤ pouSq n k z :=
  mul_nonneg (pouBump_nonneg _) (pouBump_nonneg _)

lemma abs_pouSq_le_one (n : ℕ) (k : ℤ × ℤ) (z : ℂ) : |pouSq n k z| ≤ 1 := by
  rw [pouSq, abs_mul]
  calc |pouBump (z.re * 2 ^ n - k.1)| * |pouBump (z.im * 2 ^ n - k.2)| ≤ 1 * 1 :=
        mul_le_mul (abs_pouBump_le_one _) (abs_pouBump_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma contDiff_pouSq {m : ℕ∞} (n : ℕ) (k : ℤ × ℤ) : ContDiff ℝ m (pouSq n k) := by
  unfold pouSq
  refine ContDiff.mul ?_ ?_
  · exact contDiff_pouBump.comp
      ((reCLM.contDiff.mul contDiff_const).sub contDiff_const)
  · exact contDiff_pouBump.comp
      ((imCLM.contDiff.mul contDiff_const).sub contDiff_const)

/-- **The square cut-offs sum to one** on the box `|2ⁿ Re z|, |2ⁿ Im z| ≤ M`. -/
theorem sum_pouSq {n M : ℕ} {z : ℂ} (hre : |z.re * 2 ^ n| ≤ M) (him : |z.im * 2 ^ n| ≤ M) :
    ∑ k ∈ pouIdx M, pouSq n k z = 1 := by
  rw [pouIdx, Finset.sum_product]
  simp only [pouSq]
  rw [← Finset.sum_mul_sum, sum_pouBump hre, sum_pouBump him, mul_one]

/-- The closed square of side `2 · 2^{-n}` centred at `k 2^{-n}` (in scaled coordinates). -/
def pouCell (n : ℕ) (k : ℤ × ℤ) : Set ℂ :=
  {z | |z.re * 2 ^ n - k.1| ≤ 1 ∧ |z.im * 2 ^ n - k.2| ≤ 1}

lemma isClosed_pouCell (n : ℕ) (k : ℤ × ℤ) : IsClosed (pouCell n k) := by
  refine IsClosed.inter ?_ ?_
  · exact isClosed_le ((continuous_re.mul continuous_const).sub continuous_const).abs
      continuous_const
  · exact isClosed_le ((continuous_im.mul continuous_const).sub continuous_const).abs
      continuous_const

lemma pouSq_eq_zero_of_notMem {n : ℕ} {k : ℤ × ℤ} {z : ℂ} (hz : z ∉ pouCell n k) :
    pouSq n k z = 0 := by
  by_contra h
  apply hz
  rw [pouSq] at h
  exact ⟨(abs_lt_one_of_pouBump_ne_zero (left_ne_zero_of_mul h)).le,
    (abs_lt_one_of_pouBump_ne_zero (right_ne_zero_of_mul h)).le⟩

lemma tsupport_pouSq_subset (n : ℕ) (k : ℤ × ℤ) : tsupport (pouSq n k) ⊆ pouCell n k :=
  closure_minimal (fun _ hz => by_contra fun h => hz (pouSq_eq_zero_of_notMem h))
    (isClosed_pouCell n k)

/-- The centre `k 2^{-n}` of the cell. -/
def pouCentre (n : ℕ) (k : ℤ × ℤ) : ℂ := ⟨(k.1 : ℝ) / 2 ^ n, (k.2 : ℝ) / 2 ^ n⟩

/-- The square cut-off vanishes off the ball `B(k 2^{-n}, 2 · 2^{-n})`. -/
lemma pouSq_eq_zero_of_notMem_ball {n : ℕ} {k : ℤ × ℤ} {z : ℂ}
    (hz : z ∉ ball (pouCentre n k) (2 / 2 ^ n)) : pouSq n k z = 0 := by
  by_contra h
  apply hz
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  rw [pouSq] at h
  have h1 := abs_lt_one_of_pouBump_ne_zero (left_ne_zero_of_mul h)
  have h3 := abs_lt_one_of_pouBump_ne_zero (right_ne_zero_of_mul h)
  have hre : |z.re - (k.1 : ℝ) / 2 ^ n| < 1 / 2 ^ n := by
    rw [show z.re - (k.1 : ℝ) / 2 ^ n = (z.re * 2 ^ n - k.1) / 2 ^ n by field_simp, abs_div,
      abs_of_pos h2]
    exact div_lt_div_of_pos_right h1 h2
  have him : |z.im - (k.2 : ℝ) / 2 ^ n| < 1 / 2 ^ n := by
    rw [show z.im - (k.2 : ℝ) / 2 ^ n = (z.im * 2 ^ n - k.2) / 2 ^ n by field_simp, abs_div,
      abs_of_pos h2]
    exact div_lt_div_of_pos_right h3 h2
  rw [mem_ball, dist_eq_norm]
  calc ‖z - pouCentre n k‖ ≤ |(z - pouCentre n k).re| + |(z - pouCentre n k).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < 1 / 2 ^ n + 1 / 2 ^ n := by
        rw [Complex.sub_re, Complex.sub_im]
        exact add_lt_add hre him
    _ = 2 / 2 ^ n := by ring

/-! ### The pieces `φ ψ_{n,k}` of a test function -/

/-- The piece `φ ψ_{n,k}` of a test function on `ℍ`. -/
def pouTest (φ : LQGMetric.TestOn upperHalfPlaneOpens) (n : ℕ) (k : ℤ × ℤ) :
    LQGMetric.TestOn upperHalfPlaneOpens :=
  ⟨fun z => φ z * pouSq n k z, φ.contDiff.mul (contDiff_pouSq n k),
    φ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans φ.tsupport_subset⟩

@[simp] lemma pouTest_apply (φ : LQGMetric.TestOn upperHalfPlaneOpens) (n : ℕ) (k : ℤ × ℤ)
    (z : ℂ) : pouTest φ n k z = φ z * pouSq n k z := rfl

lemma tsupport_pouTest_subset (φ : LQGMetric.TestOn upperHalfPlaneOpens) (n : ℕ) (k : ℤ × ℤ) :
    tsupport (pouTest φ n k) ⊆ tsupport φ ∩ pouCell n k :=
  subset_inter tsupport_mul_subset_left
    (tsupport_mul_subset_right.trans (tsupport_pouSq_subset n k))

/-- Evaluation of a finite sum of test functions. -/
lemma testOn_sum_apply {ι : Type*} (s : Finset ι) (f : ι → LQGMetric.TestOn upperHalfPlaneOpens)
    (z : ℂ) : (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- **The exact decomposition.** If `tsupport φ ⊆ B̄(0, R)` and `R 2ⁿ ≤ M`, then
`φ = ∑_{k ∈ [−M, M]²} φ ψ_{n,k}`. -/
theorem sum_pouTest {φ : LQGMetric.TestOn upperHalfPlaneOpens} {R : ℝ}
    (hR : tsupport φ ⊆ closedBall 0 R) {n M : ℕ} (hM : R * 2 ^ n ≤ M) :
    ∑ k ∈ pouIdx M, pouTest φ n k = φ := by
  ext z
  rw [testOn_sum_apply]
  simp only [pouTest_apply]
  rw [← Finset.mul_sum]
  by_cases hz : z ∈ tsupport φ
  · have hzR : ‖z‖ ≤ R := by simpa using hR hz
    have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
    have hre : |z.re * 2 ^ n| ≤ M := by
      rw [abs_mul, abs_of_pos h2]
      exact (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z).trans hzR) h2.le).trans hM
    have him : |z.im * 2 ^ n| ≤ M := by
      rw [abs_mul, abs_of_pos h2]
      exact (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm z).trans hzR) h2.le).trans hM
    rw [sum_pouSq hre him, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

/-- **Variance of a piece.** For `|φ| ≤ B`, `Var⟨h, φ ψ_{n,k}⟩ ≤ 16 π² B² 16^{-n}
(log (‖k 2^{-n}‖ + 2) + n + 8)`. -/
theorem zeroGFFTestCov_pouTest_le (φ : LQGMetric.TestOn upperHalfPlaneOpens) {B : ℝ}
    (hB : ∀ z, |φ z| ≤ B) (n : ℕ) (k : ℤ × ℤ) :
    QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens (pouTest φ n k) (pouTest φ n k) ≤
      16 * π ^ 2 * B ^ 2 / 16 ^ n * (Real.log (‖pouCentre n k‖ + 2) + n + 8) := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  set r : ℝ := 2 / 2 ^ n with hr
  have hr0 : 0 < r := by positivity
  have hB' : ∀ z, |pouTest φ n k z| ≤ B := fun z => by
    rw [pouTest_apply, abs_mul]
    calc |φ z| * |pouSq n k z| ≤ B * 1 :=
          mul_le_mul (hB z) (abs_pouSq_le_one n k z) (abs_nonneg _) ((abs_nonneg _).trans (hB z))
      _ = B := mul_one B
  have hsupp : ∀ z, z ∉ ball (pouCentre n k) r → pouTest φ n k z = 0 := fun z hz => by
    rw [pouTest_apply, pouSq_eq_zero_of_notMem_ball hz, mul_zero]
  have hmain := zeroGFFTestCov_self_le_of_ball (pouTest φ n k) hr0 hB' hsupp
  set c := ‖pouCentre n k‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hn1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hL : Real.log ((c + r) / r) ≤ Real.log (c + 2) + n := by
    have hle : (c + r) / r ≤ (c + 2) * 2 ^ n := by
      rw [div_le_iff₀ hr0, hr]
      field_simp
      nlinarith
    have hpos : 0 < (c + r) / r := by positivity
    calc Real.log ((c + r) / r) ≤ Real.log ((c + 2) * 2 ^ n) := Real.log_le_log hpos hle
      _ = Real.log (c + 2) + n * Real.log 2 := by
          rw [Real.log_mul (by positivity) h2.ne', Real.log_pow]
      _ ≤ Real.log (c + 2) + n := by
          have := Real.log_two_lt_d9
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
  have hr4 : r ^ 4 = 16 / 16 ^ n := by
    rw [hr, div_pow, ← pow_mul, mul_comm n 4, pow_mul]
    norm_num
  calc QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens (pouTest φ n k) (pouTest φ n k)
      ≤ B ^ 2 * (π * r ^ 2) * (π * r ^ 2 * Real.log ((c + r) / r) + 8 * π * r ^ 2) := hmain
    _ = π ^ 2 * B ^ 2 * r ^ 4 * (Real.log ((c + r) / r) + 8) := by ring
    _ ≤ π ^ 2 * B ^ 2 * r ^ 4 * (Real.log (c + 2) + n + 8) := by
        gcongr
    _ = 16 * π ^ 2 * B ^ 2 / 16 ^ n * (Real.log (c + 2) + n + 8) := by
        rw [hr4]; ring

/-! ### Counting the pieces whose support meets a set -/

/-- The offsets `{−1, 0, 1}²`. -/
def pouOff : Finset (ℤ × ℤ) := Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1

lemma card_pouOff : pouOff.card = 9 := by decide

/-- An integer within distance `1` of a real point lies within `1` of its floor. -/
lemma sub_floor_mem_Icc {x : ℝ} {k : ℤ} (hx : |x - k| ≤ 1) : k - ⌊x⌋ ∈ Finset.Icc (-1 : ℤ) 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := abs_le.1 hx
  rw [Finset.mem_Icc]
  constructor
  · have : ((⌊x⌋ : ℤ) : ℝ) - 1 ≤ k := by linarith
    have : (⌊x⌋ : ℤ) - 1 ≤ k := by exact_mod_cast this
    omega
  · have : (k : ℝ) < ⌊x⌋ + 2 := by linarith
    have : k < ⌊x⌋ + 2 := by exact_mod_cast this
    omega

open Classical Dimension in
/-- **Few bad pieces.** At most `9 N_n(A ∩ tsupport φ)` of the pieces `φ ψ_{n,k}` have support meeting
`A` (each such support point lies in a dyadic square of side `2^{-n}` whose index is within `1` of `k` in
each coordinate). -/
theorem card_bad_le (φ : LQGMetric.TestOn upperHalfPlaneOpens) (A : Set ℂ) (n M : ℕ) :
    ((pouIdx M).filter (fun k => ¬ Disjoint (tsupport (pouTest φ n k)) A)).card ≤
      9 * dyadicCount n (A ∩ tsupport φ) := by

  have hfin : (dyadicHits n (A ∩ tsupport φ)).Finite :=
    dyadicHits_finite (φ.hasCompactSupport.isCompact.isBounded.subset inter_subset_right)
  set S := hfin.toFinset with hS
  have hsub : (pouIdx M).filter (fun k => ¬ Disjoint (tsupport (pouTest φ n k)) A) ⊆
      (S ×ˢ pouOff).image (fun p => p.1 + p.2) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨z, hzt, hzA⟩ := Set.not_disjoint_iff.1 hk.2
    obtain ⟨hzφ, hzc⟩ := tsupport_pouTest_subset φ n k hzt
    set j : ℤ × ℤ := (⌊z.re * 2 ^ n⌋, ⌊z.im * 2 ^ n⌋) with hj
    have hjS : j ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      exact ⟨z, mem_dyadicSquare_floor n z, hzA, hzφ⟩
    rw [Finset.mem_image]
    refine ⟨(j, k - j), Finset.mem_product.2 ⟨hjS, ?_⟩, by simp⟩
    exact Finset.mem_product.2 ⟨sub_floor_mem_Icc hzc.1, sub_floor_mem_Icc hzc.2⟩
  calc ((pouIdx M).filter _).card ≤ ((S ×ˢ pouOff).image (fun p => p.1 + p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (S ×ˢ pouOff).card := Finset.card_image_le
    _ = 9 * dyadicCount n (A ∩ tsupport φ) := by
        rw [Finset.card_product, card_pouOff, mul_comm, dyadicCount,
          Set.ncard_eq_toFinset_card _ hfin]

end InteractingSLE.WangWu
