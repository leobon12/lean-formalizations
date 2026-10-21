import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# NIC, part 1 (T4, algebra): binomial series of operators

Packet P-G1, target T4; GA2 D5 Step 5. Mathlib's continuous functional calculus for operator
square roots needs complex scalars, so on a real Banach space `E` we use the binomial series

  `binomOp a D := ∑ₙ binom(a, n) Dⁿ`   (`Ring.choose a n`, the coefficients of
  `PowerSeries.binomialSeries ℝ a`),

norm-convergent for `|a| ≤ 1` and `‖D‖ < 1` (`|binom(a, n)| ≤ 1`, `abs_choose_le_one`).

* `binomOp_mul`: `binomOp a D · binomOp b D = binomOp (a + b) D` (Cauchy product of norm-summable
  series, `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, and Vandermonde
  `Ring.add_choose_eq`, i.e. `binomialSeries_add`);
* `binomOp_one`: `binomOp 1 D = 1 + D`; `binomOp_zero`: `binomOp 0 D = 1`;
* `binomOp_apply_of_eq_zero`: `D x = 0 → binomOp a D x = x`;
* `norm_binomOp_sub_one_le`: `‖binomOp a D − 1‖ ≤ M ‖D‖ / (1 − ‖D‖)` if `|binom(a, n)| ≤ M` for
  `n ≥ 1`; with `|binom(1/2, n)| ≤ 1/2` (`abs_choose_half_le`) this is `‖S − 1‖ ≤ ‖D‖` for
  `‖D‖ ≤ 1/2`;
* `isSelfAdjoint_binomOp`: on a real Hilbert space, `D` self-adjoint ⇒ `binomOp a D` self-adjoint.

Hence `S := binomOp (1/2) D`, `S⁻ := binomOp (−1/2) D` satisfy `S² = 1 + D` and
`S S⁻ = S⁻ S = 1` (`binomOp_half_mul_self`, `binomOp_half_mul_neg_half`,
`binomOp_neg_half_mul_half`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology

namespace SmallGammaGeodesics
namespace NIC

/-! ## Binomial coefficients -/

lemma smeval_descPochhammer_eq (a : ℝ) (n : ℕ) :
    (descPochhammer ℤ n).smeval a = (descPochhammer ℝ n).eval a := by
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    descPochhammer_map]

/-- `binom(a, n + 1) (n + 1) = binom(a, n) (a − n)` -/
lemma choose_succ_mul (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) * (n + 1) = Ring.choose a n * (a - n) := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, smeval_descPochhammer_eq,
    smeval_descPochhammer_eq, descPochhammer_succ_eval, Nat.factorial_succ]
  simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have h1 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

lemma abs_choose_succ_le {a : ℝ} (ha : |a| ≤ 1) (n : ℕ) :
    |Ring.choose a (n + 1)| ≤ |Ring.choose a n| := by
  have h := congrArg abs (choose_succ_mul a n)
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [abs_mul, abs_mul, abs_of_pos hn] at h
  have hb : |a - n| ≤ n + 1 := by
    rw [abs_le] at ha ⊢
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    constructor <;> linarith [ha.1, ha.2]
  have h3 : |Ring.choose a (n + 1)| * (n + 1) ≤ |Ring.choose a n| * (n + 1) := by
    rw [h]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  exact le_of_mul_le_mul_right h3 hn

/-- `|binom(a, n)| ≤ 1` for `|a| ≤ 1` -/
lemma abs_choose_le_one {a : ℝ} (ha : |a| ≤ 1) : ∀ n : ℕ, |Ring.choose a n| ≤ 1
  | 0 => by rw [Ring.choose_zero_right, abs_one]
  | n + 1 => (abs_choose_succ_le ha n).trans (abs_choose_le_one ha n)

/-- `|binom(1/2, n)| ≤ 1/2` for `n ≥ 1` -/
lemma abs_choose_half_le : ∀ n : ℕ, 1 ≤ n → |Ring.choose (1 / 2 : ℝ) n| ≤ 1 / 2
  | 0, h => absurd h (by norm_num)
  | 1, _ => by rw [Ring.choose_one_right, abs_of_pos (by norm_num)]
  | n + 2, _ => (abs_choose_succ_le (by rw [abs_of_pos (by norm_num)]; norm_num) (n + 1)).trans
      (abs_choose_half_le (n + 1) (by omega))

lemma abs_half_le_one : |(1 / 2 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num

lemma abs_neg_half_le_one : |(-1 / 2 : ℝ)| ≤ 1 := by
  rw [abs_of_neg (by norm_num)]; norm_num

/-! ## Binomial series in `E →L[ℝ] E` -/

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma norm_pow_le_pow (D : E →L[ℝ] E) (n : ℕ) : ‖D ^ n‖ ≤ ‖D‖ ^ n := by
  rcases n with _ | n
  · rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' D (Nat.succ_pos n)

/-- **The binomial series** `(1 + D)^a := ∑ₙ binom(a, n) Dⁿ` -/
def binomOp (a : ℝ) (D : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, Ring.choose a n • D ^ n

variable {a b : ℝ} {D : E →L[ℝ] E}

omit [CompleteSpace E] in
lemma norm_binom_term_le (ha : |a| ≤ 1) (D : E →L[ℝ] E) (n : ℕ) :
    ‖Ring.choose a n • D ^ n‖ ≤ ‖D‖ ^ n := by
  rw [norm_smul, Real.norm_eq_abs]
  calc |Ring.choose a n| * ‖D ^ n‖ ≤ 1 * ‖D‖ ^ n :=
        mul_le_mul (abs_choose_le_one ha n) (norm_pow_le_pow D n) (norm_nonneg _) zero_le_one
    _ = ‖D‖ ^ n := one_mul _

omit [CompleteSpace E] in
lemma summable_norm_binom (ha : |a| ≤ 1) (hD : ‖D‖ < 1) :
    Summable fun n : ℕ => ‖Ring.choose a n • D ^ n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_binom_term_le ha D)
    (summable_geometric_of_lt_one (norm_nonneg _) hD)

lemma summable_binom (ha : |a| ≤ 1) (hD : ‖D‖ < 1) :
    Summable fun n : ℕ => Ring.choose a n • D ^ n :=
  (summable_norm_binom ha hD).of_norm

/-- **Product rule**: `binomOp a D · binomOp b D = binomOp (a + b) D`. -/
theorem binomOp_mul (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hD : ‖D‖ < 1) :
    binomOp a D * binomOp b D = binomOp (a + b) D := by
  unfold binomOp
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_binom ha hD)
    (summable_norm_binom hb hD)]
  congr 1
  funext n
  rw [Ring.add_choose_eq n (Commute.all a b), Finset.sum_smul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [smul_mul_smul, ← pow_add, hkl]

omit [CompleteSpace E] in
/-- `binomOp 1 D = 1 + D` -/
theorem binomOp_one : binomOp 1 D = 1 + D := by
  unfold binomOp
  have h0 : ∀ n ∉ Finset.range 2, Ring.choose (1 : ℝ) n • D ^ n = 0 := fun n hn => by
    have hn2 : 2 ≤ n := by simp only [Finset.mem_range, not_lt] at hn; omega
    have : Ring.choose (1 : ℝ) n = 0 := by
      have e := Ring.choose_natCast (R := ℝ) 1 n
      rw [Nat.cast_one] at e
      rw [e, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    rw [this, zero_smul]
  rw [tsum_eq_sum h0]
  simp [Finset.sum_range_succ]

omit [CompleteSpace E] in
/-- `binomOp 0 D = 1` -/
theorem binomOp_zero : binomOp 0 D = 1 := by
  unfold binomOp
  rw [tsum_eq_single 0 fun n hn => by simp [Ring.choose_zero_ite, hn],
    Ring.choose_zero_right, one_smul, pow_zero]

/-- `(binomOp a D) x = ∑ binom(a, n) Dⁿ x` -/
lemma binomOp_apply (ha : |a| ≤ 1) (hD : ‖D‖ < 1) (x : E) :
    binomOp a D x = ∑' n : ℕ, Ring.choose a n • (D ^ n) x :=
  (summable_binom ha hD).map_tsum (ContinuousLinearMap.apply ℝ E x)
    (ContinuousLinearMap.apply ℝ E x).continuous

/-- **`D x = 0 → binomOp a D x = x`** -/
theorem binomOp_apply_of_eq_zero (ha : |a| ≤ 1) (hD : ‖D‖ < 1) {x : E} (hx : D x = 0) :
    binomOp a D x = x := by
  rw [binomOp_apply ha hD, tsum_eq_single 0]
  · rw [Ring.choose_zero_right, one_smul, pow_zero, one_apply_eq_self]
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ, mul_apply_eq_comp, hx, map_zero, smul_zero]

/-- `‖binomOp a D − 1‖ ≤ M ‖D‖ / (1 − ‖D‖)` when `|binom(a, n)| ≤ M` for `n ≥ 1` -/
theorem norm_binomOp_sub_one_le (ha : |a| ≤ 1) (hD : ‖D‖ < 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ n : ℕ, 1 ≤ n → |Ring.choose a n| ≤ M) :
    ‖binomOp a D - 1‖ ≤ M * ‖D‖ * (1 - ‖D‖)⁻¹ := by
  have hs := summable_binom ha hD
  have h1 : binomOp a D - 1 = ∑' n : ℕ, Ring.choose a (n + 1) • D ^ (n + 1) := by
    unfold binomOp
    rw [hs.tsum_eq_zero_add, Ring.choose_zero_right, one_smul, pow_zero, add_sub_cancel_left]
  have hb : ∀ n : ℕ, ‖Ring.choose a (n + 1) • D ^ (n + 1)‖ ≤ M * ‖D‖ * ‖D‖ ^ n := fun n => by
    rw [norm_smul, Real.norm_eq_abs]
    calc |Ring.choose a (n + 1)| * ‖D ^ (n + 1)‖ ≤ M * ‖D‖ ^ (n + 1) :=
          mul_le_mul (hM (n + 1) (by omega)) (norm_pow_le_pow D _) (norm_nonneg _) hM0
      _ = M * ‖D‖ * ‖D‖ ^ n := by rw [pow_succ]; ring
  have hg : Summable fun n : ℕ => M * ‖D‖ * ‖D‖ ^ n :=
    (summable_geometric_of_lt_one (norm_nonneg _) hD).mul_left _
  have hsn : Summable fun n : ℕ => ‖Ring.choose a (n + 1) • D ^ (n + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg
  rw [h1]
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine (hsn.tsum_le_tsum hb hg).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) hD]

/-- `‖binomOp (1/2) D − 1‖ ≤ ‖D‖` for `‖D‖ ≤ 1/2` -/
theorem norm_binomOp_half_sub_one_le (hD : ‖D‖ ≤ 1 / 2) : ‖binomOp (1 / 2) D - 1‖ ≤ ‖D‖ := by
  have hD1 : ‖D‖ < 1 := by linarith
  refine (norm_binomOp_sub_one_le abs_half_le_one hD1 (by norm_num) abs_choose_half_le).trans ?_
  have h2 : (1 - ‖D‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc 1 / 2 * ‖D‖ * (1 - ‖D‖)⁻¹ ≤ 1 / 2 * ‖D‖ * 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖D‖ := by ring

/-- `‖binomOp (−1/2) D − 1‖ ≤ 2 ‖D‖` for `‖D‖ ≤ 1/2` -/
theorem norm_binomOp_neg_half_sub_one_le (hD : ‖D‖ ≤ 1 / 2) :
    ‖binomOp (-1 / 2) D - 1‖ ≤ 2 * ‖D‖ := by
  have hD1 : ‖D‖ < 1 := by linarith
  refine (norm_binomOp_sub_one_le abs_neg_half_le_one hD1 zero_le_one
    fun n _ => abs_choose_le_one abs_neg_half_le_one n).trans ?_
  have h2 : (1 - ‖D‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc 1 * ‖D‖ * (1 - ‖D‖)⁻¹ ≤ 1 * ‖D‖ * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * ‖D‖ := by ring

/-- `S² = 1 + D` for `S = binomOp (1/2) D` -/
theorem binomOp_half_mul_self (hD : ‖D‖ < 1) :
    binomOp (1 / 2) D * binomOp (1 / 2) D = 1 + D := by
  rw [binomOp_mul abs_half_le_one abs_half_le_one hD, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    binomOp_one]

/-- `S S⁻ = 1` -/
theorem binomOp_half_mul_neg_half (hD : ‖D‖ < 1) :
    binomOp (1 / 2) D * binomOp (-1 / 2) D = 1 := by
  rw [binomOp_mul abs_half_le_one abs_neg_half_le_one hD,
    show (1 / 2 : ℝ) + -1 / 2 = 0 by norm_num, binomOp_zero]

/-- `S⁻ S = 1` -/
theorem binomOp_neg_half_mul_half (hD : ‖D‖ < 1) :
    binomOp (-1 / 2) D * binomOp (1 / 2) D = 1 := by
  rw [binomOp_mul abs_neg_half_le_one abs_half_le_one hD,
    show (-1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, binomOp_zero]

end Banach

/-! ## Self-adjointness on a real Hilbert space -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `D` self-adjoint ⇒ `binomOp a D` self-adjoint -/
theorem isSelfAdjoint_binomOp (a : ℝ) {D : E →L[ℝ] E} (hD : IsSelfAdjoint D) :
    IsSelfAdjoint (binomOp a D) := by
  unfold binomOp IsSelfAdjoint
  rw [tsum_star]
  congr 1
  funext n
  exact ((IsSelfAdjoint.all (Ring.choose a n)).smul (hD.pow n)).star_eq

end Hilbert

end NIC
end SmallGammaGeodesics
