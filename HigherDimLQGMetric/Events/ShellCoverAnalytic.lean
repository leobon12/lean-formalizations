import HigherDimLQGMetric.Events.ShellCoverTail

/-!
# Real logarithm and power estimates for shell covering
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

variable {d : ℕ}

private theorem shellCover_log64_pos : 0 < Real.log (64 : ℝ) :=
  Real.log_pos (by norm_num)

theorem shellCover_count_pos {ρ C₀ ε : ℝ} (hρ : 0 < ρ)
    (hε : 0 < ε)
    (hεsmall : ε < Real.exp (-((C₀ + 1) * Real.log 64 / ρ)))
    {n : ℕ} (hn : ρ * Real.logb 64 ε⁻¹ - C₀ ≤ n) : 0 < n := by
  have hlog := Real.log_lt_log hε hεsmall
  rw [Real.log_exp] at hlog
  have hlog64 := shellCover_log64_pos
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hlog0 : Real.log (64 : ℝ) ≠ 0 := hlog64.ne'
  have hlogInv : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  rw [Real.logb, hlogInv] at hn
  by_contra hn0
  have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
  rw [hnzero, Nat.cast_zero] at hn
  have hlog' : Real.log ε < -((C₀ + 1) * Real.log 64) / ρ := by
    convert hlog using 1; ring
  have hlogmul := (lt_div_iff₀ hρ).mp hlog'
  have hn' : ρ * (-Real.log ε / Real.log 64) ≤ C₀ := by linarith
  have heq : ρ * (-Real.log ε / Real.log 64) =
      -(ρ * Real.log ε) / Real.log 64 := by ring
  rw [heq] at hn'
  have hbound := (div_le_iff₀ hlog64).mp hn'
  nlinarith

theorem shellCover_exp_bound {ρ s C₀ ε : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hε : 0 < ε) {n : ℕ}
    (hn : ρ * Real.logb 64 ε⁻¹ - C₀ ≤ n) :
    Real.exp (-((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * n) ≤
      Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) *
        ε ^ (2 * (d : ℝ) + s + 1) := by
  let t : ℝ := 2 * (d : ℝ) + s + 1
  let A : ℝ := t * Real.log 64 / ρ
  have ht : 0 < t := by dsimp [t]; positivity
  have hlog64 := shellCover_log64_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hlogInv : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  rw [Real.logb, hlogInv] at hn
  have hmul := mul_le_mul_of_nonneg_left hn hA.le
  have hid2 : A * (ρ * (-Real.log ε / Real.log 64)) = -t * Real.log ε := by
    dsimp [A]
    field_simp
  have hkey : -A * (n : ℝ) ≤ A * C₀ + t * Real.log ε := by
    rw [mul_sub, hid2] at hmul
    nlinarith
  have hexp := Real.exp_le_exp.mpr hkey
  rw [Real.exp_add] at hexp
  have hrpow : Real.exp (t * Real.log ε) = ε ^ t := by
    rw [Real.rpow_def_of_pos hε]
    congr 1
    ring
  rw [hrpow] at hexp
  exact hexp

theorem shellCover_combine {ρ s C₀ ε K M : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M)
    (hcard : M * ε ^ (2 * d) ≤ K)
    {n : ℕ} (hn : ρ * Real.logb 64 ε⁻¹ - C₀ ≤ n) :
    M * Real.exp (-((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * n) ≤
      K * Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) * ε ^ s := by
  have hexp := shellCover_exp_bound (d := d) hρ hs hε hn
  have hpow : ε ^ (2 * (d : ℝ) + s + 1) = ε ^ (2 * d) * ε ^ s * ε := by
    have heq : 2 * (d : ℝ) = ((2 * d : ℕ) : ℝ) := by push_cast; ring
    rw [heq, Real.rpow_add hε, Real.rpow_add hε,
      Real.rpow_natCast, Real.rpow_one]
  calc
    M * Real.exp (-((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * n) ≤
      M * (Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) *
        ε ^ (2 * (d : ℝ) + s + 1)) := mul_le_mul_of_nonneg_left hexp hM
    _ = (M * ε ^ (2 * d)) *
        Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) *
        (ε ^ s * ε) := by rw [hpow]; ring
    _ ≤ K * Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) *
        (ε ^ s * ε) := by
          have hfactor : 0 ≤ Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) *
              (ε ^ s * ε) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcard hfactor]
    _ ≤ K * Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) * ε ^ s := by
      have hK : 0 ≤ K := le_trans (mul_nonneg hM (pow_nonneg hε.le _)) hcard
      have hfac : 0 ≤ K * Real.exp (((2 * (d : ℝ) + s + 1) * Real.log 64 / ρ) * C₀) * ε ^ s := by
        positivity
      calc
        K * Real.exp _ * (ε ^ s * ε) =
            (K * Real.exp _ * ε ^ s) * ε := by ring
        _ ≤ (K * Real.exp _ * ε ^ s) * 1 :=
          mul_le_mul_of_nonneg_left hε1 hfac
        _ = _ := by ring

end HigherDimLQGMetric
