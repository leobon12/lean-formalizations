import InteractingSLE.Foundations.SLE.SpaceFilling.AreaMoment
import InteractingSLE.Foundations.SLE.SpaceFilling.AreaCover
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# `area(∂K_t) = 0` almost surely for `κ > 8`

Packet `planning/packets/PROVE-RS05-74c.md`. This replaces [RS05, Corollary 5.3] (which uses the
Jones–Makarov theorem) in the proof of [RS05, Lemma 7.3] for `κ > 8`, by the elementary route of
`planning/handoffs/PROVE-RS05-74.md`, "Details" item 6.

Let `F = F_T = fwdMapInv (drive κ B ω) T`, so `F(ℍ) = ℍ \ K_T`. By `AreaCover.lean`,
`\overline{F(ℍ)} \ F(ℍ) ⊆ ⋃_M ⋂_n ⋃_{|j| ≤ M 2^n} \bar B(F(z_{n,j}), D(n,j))`, so it suffices that
`E Σ_{|j| ≤ M 2^n} D(n,j)² → 0` as `n → ∞` for each `M`. With weights `ρ^i`, `ρ > 1`,

`D(n,j)² ≤ (Σ_i ρ^{-i})² Σ_i ρ^{2i} (K² 2^{-(n+i)})² Σ_{k} |F'(z_{n+i,k})|²`   (`sq_tsum_le`)

and `E |F'(z_{m,k})|² ≤ ((M+1) 2^m)^{8/κ}` (`AreaMoment.lean`), so with `q = 2^{8/κ} < 2` (`κ > 8`)
and `ρ² = r = (1 + 2/q)/2`,

`E Σ_j D(n,j)² ≤ C_M (q/2)^n Σ_i (r q / 2)^i → 0`.

Fatou's lemma then gives `area = 0` almost surely.

## Main results

* `sq_tsum_le`: `(Σ b_i)² ≤ (Σ ρ^{-i})² Σ (ρ^i b_i)²` in `ℝ≥0∞`.
* `lintegral_sum_tentRad_sq_le`: the expectation bound.
* `ae_volume_closure_diff_eq_zero`: almost surely `area(\overline{ℍ \ K_T} \ (ℍ \ K_T)) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### A weighted square-of-sum inequality -/

/-- `(Σ b_i)² ≤ (Σ ρ^{-i})² Σ (ρ^i b_i)²` for `0 < ρ < ∞` (bound each `b_i` by `ρ^{-i}` times the
supremum of `ρ^j b_j`, and the square of the supremum by the sum of squares). -/
theorem sq_tsum_le (b : ℕ → ℝ≥0∞) {ρ : ℝ≥0∞} (h0 : ρ ≠ 0) (hT : ρ ≠ ⊤) :
    (∑' i, b i) ^ 2 ≤ (∑' i, ρ⁻¹ ^ i) ^ 2 * ∑' i, (ρ ^ i * b i) ^ 2 := by
  set x : ℕ → ℝ≥0∞ := fun i => ρ ^ i * b i with hx
  set S : ℝ≥0∞ := ⨆ i, x i with hS
  have hb : ∀ i, b i ≤ ρ⁻¹ ^ i * S := by
    intro i
    have h1 : b i = ρ⁻¹ ^ i * x i := by
      rw [hx, ← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel h0 hT, one_pow, one_mul]
    rw [h1]
    exact mul_le_mul_right (le_iSup x i) _
  have hsum : ∑' i, b i ≤ (∑' i, ρ⁻¹ ^ i) * S := by
    rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_le_tsum hb
  have hS2 : S ^ 2 ≤ ∑' i, x i ^ 2 := by
    rw [sq, hS, ENNReal.iSup_mul]
    refine iSup_le fun j => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun k => ?_
    rcases le_total (x j) (x k) with h | h
    · calc x j * x k ≤ x k * x k := mul_le_mul_left h _
        _ = x k ^ 2 := (sq _).symm
        _ ≤ ∑' i, x i ^ 2 := ENNReal.le_tsum (f := fun i => x i ^ 2) k
    · calc x j * x k ≤ x j * x j := mul_le_mul_right h _
        _ = x j ^ 2 := (sq _).symm
        _ ≤ ∑' i, x i ^ 2 := ENNReal.le_tsum (f := fun i => x i ^ 2) j
  calc (∑' i, b i) ^ 2 ≤ ((∑' i, ρ⁻¹ ^ i) * S) ^ 2 := by gcongr
    _ = (∑' i, ρ⁻¹ ^ i) ^ 2 * S ^ 2 := mul_pow _ _ _
    _ ≤ (∑' i, ρ⁻¹ ^ i) ^ 2 * ∑' i, x i ^ 2 := by gcongr

/-- The square of a finite supremum is at most the sum of the squares. -/
theorem coe_finset_sup_sq_le {ι : Type*} (s : Finset ι) (g : ι → ℝ≥0) :
    ((s.sup g : ℝ≥0) : ℝ≥0∞) ^ 2 ≤ ∑ k ∈ s, ((g k : ℝ≥0) : ℝ≥0∞) ^ 2 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup s hs g
  rw [hmax]
  exact Finset.single_le_sum (f := fun k => ((g k : ℝ≥0) : ℝ≥0∞) ^ 2) (fun _ _ => zero_le) hk

/-- **Pointwise bound for `D(n,j)²`** with weights `ρ = √r`:
`D(n,j)² ≤ (Σ ρ^{-i})² Σ_i r^i (K² 2^{-(n+i)})² Σ_{k ∈ [j2^i, (j+1)2^i)} |f'(z_{n+i,k})|²`. -/
theorem tentRad_sq_le (f : ℂ → ℂ) (n : ℕ) (j : ℤ) {r : ℝ} (hr : 0 < r) :
    tentRad f n j ^ 2 ≤ (∑' i, (ENNReal.ofReal (Real.sqrt r))⁻¹ ^ i) ^ 2 *
      ∑' i : ℕ, ENNReal.ofReal r ^ i * ENNReal.ofReal (koebeStepConst ^ 2 / 2 ^ (n + i)) ^ 2 *
        ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i),
          ((‖deriv f (whitneyPt (n + i) k)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
  have hρ0 : ENNReal.ofReal (Real.sqrt r) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.sqrt_pos.2 hr
  refine (sq_tsum_le _ hρ0 ENNReal.ofReal_ne_top).trans ?_
  gcongr with i
  have hρ2 : ENNReal.ofReal (Real.sqrt r) ^ (2 * i) = ENNReal.ofReal r ^ i := by
    rw [pow_mul, ← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr.le]
  calc (ENNReal.ofReal (Real.sqrt r) ^ i *
        (ENNReal.ofReal (koebeStepConst ^ 2 / 2 ^ (n + i)) * (gridSup f n j i : ℝ≥0∞))) ^ 2
      = ENNReal.ofReal r ^ i * ENNReal.ofReal (koebeStepConst ^ 2 / 2 ^ (n + i)) ^ 2 *
          (gridSup f n j i : ℝ≥0∞) ^ 2 := by
        rw [← hρ2, mul_pow, mul_pow, ← pow_mul, mul_comm i 2, mul_assoc]
    _ ≤ _ := by
        gcongr
        exact coe_finset_sup_sq_le _ _

/-- `|z_{m,k}| / Im z_{m,k} ≤ (M+1) 2^m` when `−M 2^m ≤ k < M 2^m`. -/
theorem norm_div_im_whitneyPt_le {m M : ℕ} {k : ℤ} (hk1 : -((M : ℤ) * 2 ^ m) ≤ k)
    (hk2 : k < (M : ℤ) * 2 ^ m) :
    ‖whitneyPt m k‖ / (whitneyPt m k).im ≤ ((M : ℝ) + 1) * 2 ^ m := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hk1' : -((M : ℝ) * 2 ^ m) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : (k : ℝ) + 1 ≤ (M : ℝ) * 2 ^ m := by exact_mod_cast hk2
  have hre : |(whitneyPt m k).re| ≤ M := by
    rw [whitneyPt_re, abs_div, abs_of_pos h2, div_le_iff₀ h2, abs_le]
    constructor <;> linarith
  have him : |(whitneyPt m k).im| ≤ 1 := by
    rw [whitneyPt_im, abs_of_pos (by positivity)]
    exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) h2.le
  have hn : ‖whitneyPt m k‖ ≤ (M : ℝ) + 1 :=
    (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)
  rw [whitneyPt_im, div_le_iff₀ (by positivity)]
  calc ‖whitneyPt m k‖ ≤ (M : ℝ) + 1 := hn
    _ = ((M : ℝ) + 1) * 2 ^ m * (1 / 2 ^ m) := by field_simp

/-- `((M+1) 2^m)^{8/κ} = (M+1)^{8/κ} (2^{8/κ})^m`. -/
theorem rpow_mul_two_pow (M : ℝ) (hM : 0 ≤ M) (m : ℕ) (a : ℝ) :
    ((M + 1) * 2 ^ m) ^ a = (M + 1) ^ a * ((2 : ℝ) ^ a) ^ m := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (2 : ℝ) m,
    ← Real.rpow_mul (by norm_num), mul_comm (m : ℝ) a, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Second moment at a grid point**: `E|F'(z_{m,k})|² ≤ (M+1)^{8/κ} (2^{8/κ})^m` for
`−M 2^m ≤ k < M 2^m`. -/
theorem lintegral_sq_deriv_whitneyPt_le (hB : IsBrownianReal B P) {κ T : ℝ} (hκ : 0 < κ)
    (hT : 0 ≤ T) {m M : ℕ} {k : ℤ} (hk1 : -((M : ℤ) * 2 ^ m) ≤ k) (hk2 : k < (M : ℤ) * 2 ^ m) :
    ∫⁻ ω, ((‖deriv (fwdMapInv (drive κ B ω) T) (whitneyPt m k)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (((M : ℝ) + 1) ^ (8 / κ)) * ENNReal.ofReal ((2 : ℝ) ^ (8 / κ)) ^ m := by
  have hz : whitneyPt m k ∈ H := by
    show 0 < (whitneyPt m k).im
    rw [whitneyPt_im]; positivity
  have h := lintegral_norm_deriv_fwdMapInv_sq_le hB hκ hT hz
  have e : ∀ ω, ((‖deriv (fwdMapInv (drive κ B ω) T) (whitneyPt m k)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (‖deriv (fwdMapInv (drive κ B ω) T) (whitneyPt m k)‖ ^ 2) := fun ω => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rfl
  simp_rw [e]
  refine h.trans ?_
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
    ← rpow_mul_two_pow (M : ℝ) (Nat.cast_nonneg M)]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
    (div_nonneg (norm_nonneg _) (by rw [whitneyPt_im]; positivity)) ?_ (div_nonneg (by norm_num) hκ.le))
  exact norm_div_im_whitneyPt_le hk1 hk2

/-- For a good version of `B`, `ω ↦ F_T'(z)` is measurable. -/
theorem measurable_deriv_fwdMapInv (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    Measurable fun ω => deriv (fwdMapInv (drive κ B ω) t) z := by
  have hrm : ∀ s, Measurable (UnzipInvariance.revBM B t.toNNReal s) := fun s => by
    simp only [UnzipInvariance.revBM]
    exact ((hBm _).add (hBm _)).sub ((hBm _).const_smul _)
  have hrc : ∀ ω, Continuous (UnzipInvariance.revBM B t.toNNReal · ω) := fun ω => by
    simp only [UnzipInvariance.revBM_apply]
    fun_prop
  have h := measurable_deriv_revMap_drive κ hrm hrc hz ht
  have e : (fun ω => deriv (fwdMapInv (drive κ B ω) t) z) =
      fun ω => deriv (revMap (drive κ (UnzipInvariance.revBM B t.toNNReal) ω) t) z :=
    funext fun ω => by rw [deriv_fwdMapInv_eq_deriv_revMap_revBM κ ht (hBc ω) (hB0 ω) hz]
  rw [e]
  exact h

theorem measurable_sq_nnnorm_deriv_fwdMapInv (hBm : ∀ s, Measurable (B s))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (κ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ H) :
    Measurable fun ω => ((‖deriv (fwdMapInv (drive κ B ω) t) z‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 :=
  ((measurable_deriv_fwdMapInv hBm hBc hB0 κ ht hz).nnnorm.coe_nnreal_ennreal).pow_const 2

theorem card_Ico_mul_two_pow (j : ℤ) (i : ℕ) :
    ((Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i)).card : ℝ≥0∞) = 2 ^ i := by
  rw [Int.card_Ico, show (j + 1) * 2 ^ i - j * 2 ^ i = (2 : ℤ) ^ i by ring]
  norm_cast

theorem card_Ico_neg_mul_two_pow (M n : ℕ) :
    ((Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n)).card : ℝ≥0∞) = 2 * M * 2 ^ n := by
  rw [Int.card_Ico, show (M : ℤ) * 2 ^ n - -((M : ℤ) * 2 ^ n) = ((2 * M * 2 ^ n : ℕ) : ℤ) by
    push_cast; ring, Int.toNat_natCast]
  push_cast
  ring

/-- The `i`-th term of the expectation bound, in closed form. -/
theorem term_eq {r q A K2 : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hA : 0 ≤ A) (hK : 0 ≤ K2) (n i : ℕ) :
    ENNReal.ofReal r ^ i * ENNReal.ofReal (K2 / 2 ^ (n + i)) ^ 2 *
        (2 ^ i * (ENNReal.ofReal A * ENNReal.ofReal q ^ (n + i)))
      = ENNReal.ofReal (A * K2 ^ 2) * ENNReal.ofReal (q / 4) ^ n *
          ENNReal.ofReal (r * q / 2) ^ i := by
  have hK' : 0 ≤ K2 / 2 ^ (n + i) := div_nonneg hK (by positivity)
  have hri : 0 ≤ r ^ i := pow_nonneg hr i
  have hqn : 0 ≤ q ^ (n + i) := pow_nonneg hq _
  have h2 : (2 : ℝ≥0∞) ^ i = ENNReal.ofReal (2 ^ i) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have key : r ^ i * (K2 / 2 ^ (n + i)) ^ 2 * (2 ^ i * (A * q ^ (n + i))) =
      A * K2 ^ 2 * (q / 4) ^ n * (r * q / 2) ^ i := by
    have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    rw [pow_add, pow_add, div_pow, div_pow, div_pow, mul_pow, mul_pow, h4]
    field_simp
  rw [h2, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_pow hK', ← ENNReal.ofReal_pow hq,
    ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ i),
    ← ENNReal.ofReal_mul hri, ← ENNReal.ofReal_mul (mul_nonneg hri (sq_nonneg _)),
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ q / 4),
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ r * q / 2),
    ← ENNReal.ofReal_mul (mul_nonneg hA (sq_nonneg _)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hA (sq_nonneg _)) (by positivity)), key]

theorem whitneyPt_mem_H (m : ℕ) (k : ℤ) : whitneyPt m k ∈ H := by
  show 0 < (whitneyPt m k).im
  rw [whitneyPt_im]; positivity

/-- The grid indices under the tents `j ∈ [−M 2^n, M 2^n)` lie in `[−M 2^{n+i}, M 2^{n+i})`. -/
theorem mem_range_of_mem_tent {M n i : ℕ} {j k : ℤ}
    (hj : j ∈ Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n))
    (hk : k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i)) :
    -((M : ℤ) * 2 ^ (n + i)) ≤ k ∧ k < (M : ℤ) * 2 ^ (n + i) := by
  rw [Finset.mem_Ico] at hj hk
  have h2 : (0 : ℤ) < 2 ^ i := by positivity
  rw [pow_add]
  constructor
  · nlinarith [hj.1, hk.1]
  · nlinarith [hj.2, hk.2]

/-- **Expectation of the tent sum** (`κ > 8`): there is a finite `C` with
`E Σ_{j ∈ [−M 2^n, M 2^n)} D(n,j)² ≤ C (q/2)^n`, `q = 2^{8/κ} < 2`. -/
theorem lintegral_sum_tentRad_sq_le (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {κ T : ℝ} (hκ : 8 < κ) (hT : 0 ≤ T)
    (M : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n : ℕ,
      ∫⁻ ω, ∑ j ∈ Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n),
          tentRad (fwdMapInv (drive κ B ω) T) n j ^ 2 ∂P
        ≤ C * ENNReal.ofReal ((2 : ℝ) ^ (8 / κ) / 2) ^ n := by
  have hκ0 : 0 < κ := by linarith
  set q : ℝ := (2 : ℝ) ^ (8 / κ) with hq
  have h8 : 0 < 8 / κ := by positivity
  have h81 : 8 / κ < 1 := by rw [div_lt_one hκ0]; exact hκ
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) h8
  have hq2 : q < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h81
    rwa [Real.rpow_one] at this
  have hq0 : 0 ≤ q := by linarith
  set r : ℝ := (1 + 2 / q) / 2 with hr
  have h2q : 1 < 2 / q := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hr1 : 1 < r := by rw [hr]; linarith
  have hrq : r * q / 2 < 1 := by
    have : r * q / 2 = (q + 2) / 4 := by rw [hr]; field_simp; ring
    rw [this]; linarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r) with hρ
  have hρ1 : 1 < ρ := by
    rw [hρ, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.2 (by linarith))).2
      (by rw [Real.lt_sqrt zero_le_one]; linarith)
  set Cρ : ℝ≥0∞ := (∑' i, ρ⁻¹ ^ i) ^ 2 with hCρdef
  have hCρ : Cρ ≠ ⊤ := by
    have hinv : ρ⁻¹ < 1 := ENNReal.inv_lt_one.2 hρ1
    rw [hCρdef, ENNReal.tsum_geometric]
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hinv).ne')
  set A : ℝ := ((M : ℝ) + 1) ^ (8 / κ) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  set K2 : ℝ := koebeStepConst ^ 2 with hK2
  have hK0 : 0 ≤ K2 := by positivity
  set S : ℝ≥0∞ := ∑' i : ℕ, ENNReal.ofReal (r * q / 2) ^ i with hSdef
  have hS : S ≠ ⊤ := by
    have hlt : ENNReal.ofReal (r * q / 2) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hrq
    rw [hSdef, ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne'
  refine ⟨2 * M * Cρ * (ENNReal.ofReal (A * K2 ^ 2) * S), ?_, fun n => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hCρ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS)
  set F : Ω → ℂ → ℂ := fun ω => fwdMapInv (drive κ B ω) T with hF
  set g : ℕ → ℤ → Ω → ℝ≥0∞ := fun m k ω => ((‖deriv (F ω) (whitneyPt m k)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2
    with hg
  have hgm : ∀ m k, Measurable (g m k) := fun m k =>
    measurable_sq_nnnorm_deriv_fwdMapInv hBm hBc hB0 κ hT (whitneyPt_mem_H m k)
  set J := Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n) with hJ
  set a : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal r ^ i * ENNReal.ofReal (K2 / 2 ^ (n + i)) ^ 2 with ha
  have hpt : ∀ ω, ∑ j ∈ J, tentRad (F ω) n j ^ 2 ≤
      ∑ j ∈ J, Cρ * ∑' i : ℕ, a i *
        ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i), g (n + i) k ω := fun ω =>
    Finset.sum_le_sum fun j _ => tentRad_sq_le (F ω) n j (by linarith : (0 : ℝ) < r)
  have hmk : ∀ j : ℤ, ∀ i : ℕ, Measurable fun ω =>
      ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i), g (n + i) k ω := fun j i =>
    Finset.measurable_sum _ fun k _ => hgm _ _
  calc ∫⁻ ω, ∑ j ∈ J, tentRad (F ω) n j ^ 2 ∂P
      ≤ ∫⁻ ω, ∑ j ∈ J, Cρ * ∑' i : ℕ, a i *
          ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i), g (n + i) k ω ∂P := lintegral_mono hpt
    _ = ∑ j ∈ J, Cρ * ∑' i : ℕ, a i *
          ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i), ∫⁻ ω, g (n + i) k ω ∂P := by
        rw [lintegral_finsetSum _ fun j _ =>
          (Measurable.tsum fun i => (hmk j i).const_mul _).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul _ (Measurable.tsum fun i => (hmk j i).const_mul _),
          lintegral_tsum fun i => ((hmk j i).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun i => ?_
        rw [lintegral_const_mul _ (hmk j i), lintegral_finsetSum _ fun k _ => hgm _ _]
    _ ≤ ∑ j ∈ J, Cρ * ∑' i : ℕ, a i *
          (2 ^ i * (ENNReal.ofReal A * ENNReal.ofReal q ^ (n + i))) := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_right (ENNReal.tsum_le_tsum fun i =>
          mul_le_mul_right ?_ _) _
        calc ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i), ∫⁻ ω, g (n + i) k ω ∂P
            ≤ ∑ k ∈ Finset.Ico (j * 2 ^ i) ((j + 1) * 2 ^ i),
                ENNReal.ofReal A * ENNReal.ofReal q ^ (n + i) :=
              Finset.sum_le_sum fun k hk =>
                lintegral_sq_deriv_whitneyPt_le hB hκ0 hT (mem_range_of_mem_tent hj hk).1
                  (mem_range_of_mem_tent hj hk).2
          _ = 2 ^ i * (ENNReal.ofReal A * ENNReal.ofReal q ^ (n + i)) := by
              rw [Finset.sum_const, nsmul_eq_mul, card_Ico_mul_two_pow]
    _ = ∑ j ∈ J, Cρ * (ENNReal.ofReal (A * K2 ^ 2) * ENNReal.ofReal (q / 4) ^ n * S) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp_rw [ha, term_eq (le_of_lt (by linarith : (0 : ℝ) < r)) hq0 hA0 hK0 n]
        rw [ENNReal.tsum_mul_left]
    _ = 2 * M * Cρ * (ENNReal.ofReal (A * K2 ^ 2) * S) * ENNReal.ofReal (q / 2) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul, hJ, card_Ico_neg_mul_two_pow]
        have h2 : (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (q / 4) ^ n = ENNReal.ofReal (q / 2) ^ n := by
          rw [← mul_pow, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 2
          ring
        rw [← h2]
        ring

theorem measurable_finset_sup_nnreal {ι : Type*} (s : Finset ι) {g : ι → Ω → ℝ≥0}
    (hg : ∀ k, Measurable (g k)) : Measurable fun ω => s.sup fun k => g k ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    simp only [Finset.sup_insert]
    exact (hg a).sup ih

theorem measurable_tentRad (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (j : ℤ) :
    Measurable fun ω => tentRad (fwdMapInv (drive κ B ω) T) n j := by
  refine Measurable.tsum fun i => Measurable.const_mul ?_ _
  have hm : Measurable fun ω => gridSup (fwdMapInv (drive κ B ω) T) n j i :=
    measurable_finset_sup_nnreal _ fun k =>
      (measurable_deriv_fwdMapInv hBm hBc hB0 κ hT (whitneyPt_mem_H _ k)).nnnorm
  exact hm.coe_nnreal_ennreal

/-- **`area(∂K_T) = 0` almost surely, `κ > 8`** (replacement of [RS05, Corollary 5.3]): almost
surely the points of `\overline{ℍ \ K_T}` outside `ℍ \ K_T` (in particular `∂K_T ∩ ℍ`) form a
Lebesgue-null set. -/
theorem ae_volume_closure_diff_eq_zero (hB : IsBrownianReal B P) {κ T : ℝ} (hκ : 8 < κ)
    (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, volume (closure (H \ fwdHull (drive κ B ω) T) \ (H \ fwdHull (drive κ B ω) T)) = 0 := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hB''br, hB''eq⟩ := exists_good_version0 hB
  have hdr : ∀ᵐ ω ∂P, drive κ B ω = drive κ B'' ω :=
    hB''eq.mono fun ω h => funext fun s => by simp [drive, h]
  have hq : ENNReal.ofReal ((2 : ℝ) ^ (8 / κ) / 2) < 1 := by
    have hκ0 : 0 < κ := by linarith
    have h81 : 8 / κ < 1 := by rw [div_lt_one hκ0]; exact hκ
    have hq2 : (2 : ℝ) ^ (8 / κ) < 2 := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h81
      rwa [Real.rpow_one] at this
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have key : ∀ M : ℕ, ∀ᵐ ω ∂P,
      volume (⋂ n : ℕ, tentSet (fwdMapInv (drive κ B'' ω) T) M n) = 0 := by
    intro M
    obtain ⟨C, hC, hbound⟩ := lintegral_sum_tentRad_sq_le hB''br hB''m hB''c hB''0 hκ hT M
    set Ψ : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal Real.pi *
      ∑ j ∈ Finset.Ico (-((M : ℤ) * 2 ^ n)) ((M : ℤ) * 2 ^ n),
        tentRad (fwdMapInv (drive κ B'' ω) T) n j ^ 2 with hΨ
    have hΨm : ∀ n, Measurable (Ψ n) := fun n =>
      (Finset.measurable_sum _ fun j _ =>
        (measurable_tentRad hB''m hB''c hB''0 κ hT n j).pow_const 2).const_mul _
    have hlim : ∫⁻ ω, liminf (fun n => Ψ n ω) atTop ∂P = 0 := by
      refine le_antisymm ((lintegral_liminf_le hΨm).trans ?_) zero_le
      have ht : Tendsto (fun n : ℕ => ENNReal.ofReal Real.pi *
          (C * ENNReal.ofReal ((2 : ℝ) ^ (8 / κ) / 2) ^ n)) atTop (𝓝 0) := by
        have h1 := ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Or.inr hC)
        rw [mul_zero] at h1
        have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Real.pi) h1
          (Or.inr ENNReal.ofReal_ne_top)
        rwa [mul_zero] at h2
      calc liminf (fun n => ∫⁻ ω, Ψ n ω ∂P) atTop
          ≤ liminf (fun n : ℕ => ENNReal.ofReal Real.pi *
              (C * ENNReal.ofReal ((2 : ℝ) ^ (8 / κ) / 2) ^ n)) atTop := by
            refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
            rw [hΨ, lintegral_const_mul _ (Finset.measurable_sum _ fun j _ =>
              (measurable_tentRad hB''m hB''c hB''0 κ hT n j).pow_const 2)]
            exact mul_le_mul_right (hbound n) _
        _ = 0 := ht.liminf_eq
    have hae := (lintegral_eq_zero_iff (Measurable.liminf hΨm)).1 hlim
    filter_upwards [hae] with ω hω
    refine le_antisymm ?_ zero_le
    have hle : volume (⋂ n : ℕ, tentSet (fwdMapInv (drive κ B'' ω) T) M n) ≤
        liminf (fun n => Ψ n ω) atTop :=
      le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n =>
        (measure_mono (iInter_subset _ n)).trans ((volume_tentSet_le _ M n).trans
          (by simp only [hΨ, Finset.mul_sum]; exact le_rfl)))
    rw [hω, Pi.zero_apply] at hle
    exact hle
  filter_upwards [ae_all_iff.2 key, hdr] with ω hM hω
  rw [hω]
  have hW : Continuous (drive κ B'' ω) := drive_continuous (hB''c ω)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, hB''0 ω]
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hT
  rw [← image_fwdMapInv_H hW hW0 hT]
  refine measure_mono_null (closure_diff_subset_iUnion_iInter_tentSet
    (differentiableOn_fwdMapInv hW hW0 hT) (injOn_fwdMapInv hW hW0 hT) hC)
    (measure_iUnion_null hM)

end Expectation

end InteractingSLE
