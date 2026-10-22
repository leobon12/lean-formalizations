import HigherDimLQGMetric.Sec4.Lemma43Meas

/-!
# The dyadic radii `N^ε` of [1] Lemma 4.4 (packet L9b)

`N^ε` (indices `k`, radii `2^{-k}`) is the run of `m(ε) = ⌊log₂(ε^{-ζ/2}/20)⌋` consecutive dyadic radii starting at
the largest dyadic radius `≤ ε^{1-ζ}/10`; all its radii lie in `[ε^{1-ζ/2}, ε^{1-ζ}/10]` (so `N^ε` is contained
in [1]'s `[ε^{1-ζ/2}, ε^{1-ζ}/10] ∩ {2^{-k}}` and differs from it by at most two indices), and
`m(ε) ≥ c log ε⁻¹` for small `ε`. Being an interval of indices, `N^ε` feeds the shell decoupling directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

/-- the dyadic radius `2^{-k}` -/
def dyad (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem dyad_pos (k : ℕ) : 0 < dyad k := by unfold dyad; positivity

theorem dyad_le_one (k : ℕ) : dyad k ≤ 1 := by
  unfold dyad
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem dyad_succ (k : ℕ) : dyad (k + 1) = dyad k / 2 := by
  unfold dyad
  rw [pow_succ]
  ring

theorem dyad_antitone : Antitone dyad := fun _ _ h =>
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem dyad_eq_inv_pow (k : ℕ) : dyad k = ((2 : ℝ) ^ k)⁻¹ := by
  unfold dyad
  rw [one_div, inv_pow]

/-- lowest index with `2^{-k} ≤ ε^{1-ζ}/10` -/
def kLo (ζ ε : ℝ) : ℕ := ⌈Real.logb 2 (10 / ε ^ (1 - ζ))⌉₊

/-- the number of radii `⌊log₂(ε^{-ζ/2}/20)⌋` -/
def mCnt (ζ ε : ℝ) : ℕ := ⌊Real.logb 2 (ε ^ (-(ζ / 2)) / 20)⌋₊

/-- **`N^ε`**: the indices of the dyadic radii used in [1] Lemma 4.4 -/
def nIdx (ζ ε : ℝ) : Finset ℕ := Finset.Ico (kLo ζ ε) (kLo ζ ε + mCnt ζ ε)

theorem card_nIdx (ζ ε : ℝ) : (nIdx ζ ε).card = mCnt ζ ε := by
  simp [nIdx]

theorem two_pow_logb {x : ℝ} (hx : 0 < x) : (2 : ℝ) ^ Real.logb 2 x = x :=
  Real.rpow_logb (by norm_num) (by norm_num) hx

theorem dyad_kLo_le {ζ ε : ℝ} (hε : 0 < ε) : dyad (kLo ζ ε) ≤ ε ^ (1 - ζ) / 10 := by
  have hX : 0 < 10 / ε ^ (1 - ζ) := by positivity
  have h1 : Real.logb 2 (10 / ε ^ (1 - ζ)) ≤ (kLo ζ ε : ℝ) := Nat.le_ceil _
  have h2 : 10 / ε ^ (1 - ζ) ≤ (2 : ℝ) ^ kLo ζ ε := by
    rw [← two_pow_logb hX, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [dyad_eq_inv_pow]
  calc ((2 : ℝ) ^ kLo ζ ε)⁻¹ ≤ (10 / ε ^ (1 - ζ))⁻¹ := inv_anti₀ hX h2
    _ = ε ^ (1 - ζ) / 10 := by rw [inv_div]

theorem lt_dyad_kLo {ζ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ1 : ζ < 1) :
    ε ^ (1 - ζ) / 20 < dyad (kLo ζ ε) := by
  have hX : 0 < 10 / ε ^ (1 - ζ) := by positivity
  have hX1 : 1 ≤ 10 / ε ^ (1 - ζ) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have : ε ^ (1 - ζ) ≤ 1 := Real.rpow_le_one hε.le hε1 (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.logb 2 (10 / ε ^ (1 - ζ)) :=
    Real.logb_nonneg (by norm_num) hX1
  have h1 : (kLo ζ ε : ℝ) < Real.logb 2 (10 / ε ^ (1 - ζ)) + 1 := Nat.ceil_lt_add_one hlog0
  have h2 : (2 : ℝ) ^ kLo ζ ε < 2 * (10 / ε ^ (1 - ζ)) := by
    rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (kLo ζ ε : ℝ) < 2 ^ (Real.logb 2 (10 / ε ^ (1 - ζ)) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
      _ = 2 * (10 / ε ^ (1 - ζ)) := by
          rw [Real.rpow_add (by norm_num), two_pow_logb hX, Real.rpow_one]; ring
  rw [dyad_eq_inv_pow]
  calc ε ^ (1 - ζ) / 20 = (2 * (10 / ε ^ (1 - ζ)))⁻¹ := by field_simp; ring
    _ < ((2 : ℝ) ^ kLo ζ ε)⁻¹ := inv_strictAnti₀ (by positivity) h2

/-- the radii of `N^ε` are at most `ε^{1-ζ}/10` -/
theorem dyad_le_of_mem_nIdx {ζ ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : k ∈ nIdx ζ ε) :
    dyad k ≤ ε ^ (1 - ζ) / 10 :=
  (dyad_antitone (Finset.mem_Ico.1 hk).1).trans (dyad_kLo_le hε)

/-- the radii of `N^ε` are at least `ε^{1-ζ/2}` -/
theorem le_dyad_of_mem_nIdx {ζ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ1 : ζ < 1) {k : ℕ}
    (hk : k ∈ nIdx ζ ε) : ε ^ (1 - ζ / 2) ≤ dyad k := by
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.1 hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk1
  have hj : j < mCnt ζ ε := by omega
  have hY : 0 < ε ^ (-(ζ / 2)) / 20 := by positivity
  have hm : (mCnt ζ ε : ℝ) ≤ Real.logb 2 (ε ^ (-(ζ / 2)) / 20) := by
    have hm0 : 0 < mCnt ζ ε := by omega
    have hpos : 0 ≤ Real.logb 2 (ε ^ (-(ζ / 2)) / 20) := by
      by_contra hneg
      push Not at hneg
      have : mCnt ζ ε = 0 := Nat.floor_eq_zero.2 (hneg.trans zero_lt_one)
      omega
    exact Nat.floor_le hpos
  have h2j : (2 : ℝ) ^ j ≤ ε ^ (-(ζ / 2)) / 20 := by
    have hjm : (j : ℝ) ≤ Real.logb 2 (ε ^ (-(ζ / 2)) / 20) :=
      (by exact_mod_cast hj.le : (j : ℝ) ≤ mCnt ζ ε).trans hm
    rw [← two_pow_logb hY, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hjm
  have hdy : dyad (kLo ζ ε + j) = dyad (kLo ζ ε) * ((2 : ℝ) ^ j)⁻¹ := by
    unfold dyad
    rw [pow_add]
    simp only [one_div, inv_pow]
  rw [hdy]
  have hk0 := lt_dyad_kLo (ζ := ζ) hε hε1 hζ1
  have e1 : ε ^ (1 - ζ / 2) = ε ^ (1 - ζ) * (ε ^ (-(ζ / 2)))⁻¹ := by
    rw [← Real.rpow_neg hε.le, neg_neg, ← Real.rpow_add hε]
    ring_nf
  have hpow0 : 0 < ε ^ (-(ζ / 2)) := Real.rpow_pos_of_pos hε _
  calc ε ^ (1 - ζ / 2) = ε ^ (1 - ζ) / 20 * (ε ^ (-(ζ / 2)) / 20)⁻¹ := by
        rw [e1]; field_simp
    _ ≤ dyad (kLo ζ ε) * ((2 : ℝ) ^ j)⁻¹ :=
        mul_le_mul hk0.le (inv_anti₀ (by positivity) h2j) (by positivity)
          (dyad_pos _).le

/-- `m(ε) ≥ c log ε⁻¹` for small `ε` -/
theorem eventually_mCnt_ge {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ζ / (4 * Real.log 2) * Real.log ε⁻¹ ≤ mCnt ζ ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := tendsto_log_inv_nhdsGT_zero
  have hbig : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 4 * (Real.log 20 + Real.log 2) / ζ ≤ Real.log ε⁻¹ :=
    hL.eventually (eventually_ge_atTop _)
  filter_upwards [self_mem_nhdsWithin, hbig] with ε hε hLε
  have hε0 : 0 < ε := hε
  set L := Real.log ε⁻¹ with hLdef
  have hY : 0 < ε ^ (-(ζ / 2)) / 20 := by positivity
  have hlogY : Real.log (ε ^ (-(ζ / 2)) / 20) = ζ / 2 * L - Real.log 20 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hε0, hLdef, Real.log_inv]
    ring
  have hlb : Real.logb 2 (ε ^ (-(ζ / 2)) / 20) = (ζ / 2 * L - Real.log 20) / Real.log 2 := by
    rw [← Real.log_div_log, hlogY]
  have hfl := Nat.lt_floor_add_one (Real.logb 2 (ε ^ (-(ζ / 2)) / 20))
  rw [hlb] at hfl
  have hL0 : 0 ≤ L := le_trans (by positivity) hLε
  have key : ζ / (4 * Real.log 2) * L ≤ (ζ / 2 * L - Real.log 20) / Real.log 2 - 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div,
      div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ζ)] at hLε
    field_simp
    nlinarith
  change ζ / (4 * Real.log 2) * L ≤ (⌊Real.logb 2 (ε ^ (-(ζ / 2)) / 20)⌋₊ : ℝ)
  rw [hlb]
  linarith

end HigherDimLQGMetric
