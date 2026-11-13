import InteractingSLE.SLE8.AL14.Theorem4
import InteractingSLE.SLE8.AL14.DerivComparison
import QuantumZipper.Proofs.RS.TraceShift
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Alvisio–Lawler, Corollary 1 (convergent half)

Source: [AL14] (pinned preprint, `source/external/AL14/AL14.md`, anchor `cor-1`, p. 6), with the
notation of `InteractingSLE/SLE8/AL14/DerivComparison.lean`: `f_t = barInv U t` (the centred
inverse `ḡ_t^{-1}(U_t + ·)` of the `a = 1/4` Loewner chain driven by `U`), `2^{-n} = alHeight n`,
`𝒟_n = {j 4^{-n} : 0 ≤ j ≤ 4^n}` (`alTime n j`).

**Corollary 1 (convergent half).** For `β < 1/4`,
`∑_n ∑_{t ∈ 𝒟_n} P{|f_t'(i 2^{-n})| ≥ 2^n n^{-β}} < ∞` (`al14_corollary1_summable`).

## Proof (with the repair of errata ledger E7)

[AL14] derive Corollary 1 from Theorem 3, which is stated at time `t = 1` only; Corollary 1 needs
every `t ∈ 𝒟_n` (ledger E7). We use instead the core estimate of `Theorem4.lean`, which holds
uniformly in the terminal time `T ∈ [0, 1]`:
* `f_t'(i 2^{-n}) = F_t'(i y)` with `y = √8 · 2^{-n}` and `F_t = fwdMapInv (drive 8 B ω) t`
  (`deriv_barInv`), and `F_t = revMap (drive 8 B' ω) t` on `ℍ` for the time-reversed Brownian
  motion `B' = revBM B t` (QuantumZipper, `RS.fwdMapInv_drive_eq_revMap_revBM`), which is again a
  Brownian motion (`UnzipInvariance.isBrownianReal_revBM`);
* with `a = √8 n^{-β}` the event is `{a ≤ y Φ_t}`; it is empty if `a > √(y² + 4t)`
  (`measure_deriv_revMap_ge_eq_zero`), and otherwise the core estimate gives
  `≤ e^{9/8} 4^{-n} n^{2β} (30Λ²/D)^{3/2} + 2e^{-2n}` with `Λ = 2 + log n`, `D = n log 2 / 2`,
  `m = √(128 n)`;
* the `4^n + 1` terms of `𝒟_n` cost a factor `2 · 4^n`, so the `n`-th term is
  `O(n^{2β - 3/2} (log n)³) + O((4/e²)^n)`, summable for `β < 1/4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped ENNReal NNReal

namespace InteractingSLE.SLE8.AL14

open QuantumZipper

/-! ## From `f_t` to the reverse flow of the reversed Brownian motion -/

/-- **Bridge.** For a continuous path with `B 0 = 0` and `t ≥ 0`,
`|f_t'(i y)| = |∂_z revMap (drive 8 (revBM B t) ω) t (i √8 y)|`. -/
theorem norm_deriv_barInv_eq_revMap {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω = 0) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : 0 < y) :
    ‖deriv (barInv (fun r => B r.toNNReal ω) t) ((y : ℂ) * I)‖ =
      ‖deriv (revMap (drive 8 (UnzipInvariance.revBM B t.toNNReal) ω) t)
        (((Real.sqrt 8 * y : ℝ) : ℂ) * I)‖ := by
  rw [deriv_barInv]
  have hw : ((Real.sqrt 8 * y : ℝ) : ℂ) * I ∈ H := by
    show 0 < (((Real.sqrt 8 * y : ℝ) : ℂ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have he : (Real.sqrt 8 : ℂ) * ((y : ℂ) * I) = ((Real.sqrt 8 * y : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [he]
  have hev : fwdMapInv (drive 8 B ω) t =ᶠ[𝓝 (((Real.sqrt 8 * y : ℝ) : ℂ) * I)]
      revMap (drive 8 (UnzipInvariance.revBM B t.toNNReal) ω) t :=
    Filter.mem_of_superset (isOpen_H.mem_nhds hw) fun w hw' =>
      RS.fwdMapInv_drive_eq_revMap_revBM 8 B ht hc h0 hw'
  exact congrArg norm hev.deriv_eq

/-! ## One term of the series -/

theorem alTime_mem_Icc {n j : ℕ} (hj : j ≤ 4 ^ n) : alTime n j ∈ Icc (0 : ℝ) 1 := by
  refine ⟨alTime_nonneg n j, ?_⟩
  rw [alTime, alHeight_sq]
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [← div_eq_mul_inv, div_le_one h4]
  exact_mod_cast hj

theorem alHeight_le_one (n : ℕ) : alHeight n ≤ 1 := by
  unfold alHeight
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- `n^β ≤ n < 2^n` for `n ≥ 1`, `β ≤ 1`. -/
theorem rpow_lt_two_pow {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β ≤ 1) : (n : ℝ) ^ β < 2 ^ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ β ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hβ
    _ = n := Real.rpow_one _
    _ < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self

/-- `log x ≤ x/4 ≤ x log 2 / 2`-type bound used for the denominator. -/
theorem beta_log_le {n : ℕ} (hn : 1 ≤ n) {β : ℝ} (hβ : β < 1 / 4) :
    β * Real.log n ≤ n * Real.log 2 / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hl : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  calc β * Real.log n ≤ 1 / 4 * Real.log n := mul_le_mul_of_nonneg_right hβ.le hl0
    _ ≤ 1 / 4 * n := by linarith
    _ ≤ n * Real.log 2 / 2 := by nlinarith

/-- **One term of Corollary 1** (`n ≥ 1`, `0 < β < 1/4`, `t = j 4^{-n} ∈ 𝒟_n`). -/
theorem measure_cor1_term_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 4)
    {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ 4 ^ n) :
    P {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
        ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime n j)) ((alHeight n : ℂ) * I)‖} ≤
      ENNReal.ofReal (Real.exp (9 / 8) * ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β) *
        (60 * (2 + Real.log n) ^ 2 / (n * Real.log 2)) ^ (3 / 2 : ℝ) +
        2 * Real.exp (-(2 * n))) := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hB''eq⟩ := RS.exists_good_version0 hB
  set t := alTime n j with htdef
  obtain ⟨ht0, ht1⟩ := alTime_mem_Icc hj
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set B' := UnzipInvariance.revBM B'' t.toNNReal with hB'def
  have hB' : IsBrownianReal B' P :=
    UnzipInvariance.isBrownianReal_revBM hB''.toIsPreBrownianReal hB''c _
  set y := Real.sqrt 8 * alHeight n with hydef
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hy : 0 < y := mul_pos h8 (alHeight_pos n)
  set lam := (2 : ℝ) ^ n * (n : ℝ) ^ (-β) with hlam
  have hlam0 : 0 < lam := by positivity
  set a := y * lam with hadef
  have ha : 0 < a := mul_pos hy hlam0
  have hya : y * (2 : ℝ) ^ n = Real.sqrt 8 := by
    rw [hydef, alHeight, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have ha' : a = Real.sqrt 8 * (n : ℝ) ^ (-β) := by
    rw [hadef, hlam, ← mul_assoc, hya]
  -- the event in terms of the reverse flow of `B'`
  have hev : P {ω | lam ≤
        ‖deriv (barInv (fun r => B r.toNNReal ω) t) ((alHeight n : ℂ) * I)‖} ≤
      P {ω | a ≤ y * ‖deriv (revMap (drive 8 B' ω) t) ((y : ℂ) * I)‖} := by
    refine measure_mono_ae ?_
    filter_upwards [hB''eq] with ω hω hmem
    have hU : (fun r : ℝ => B r.toNNReal ω) = fun r : ℝ => B'' r.toNNReal ω :=
      funext fun r => (hω _).symm
    simp only [hU] at hmem ⊢
    rw [norm_deriv_barInv_eq_revMap (hB''c ω) (hB''0 ω) ht0 (alHeight_pos n)] at hmem
    rw [hadef]
    exact mul_le_mul_of_nonneg_left hmem hy.le
  refine hev.trans ?_
  set Ys := Real.sqrt (y ^ 2 + 4 * t) with hYs
  by_cases hcase : Ys < a
  · rw [measure_deriv_revMap_ge_eq_zero hB' ht0 hy hcase]
    exact zero_le
  replace hcase : a ≤ Ys := not_lt.1 hcase
  -- `y < a` and hence `t > 0`
  have hlam1 : 1 < lam := by
    have h1 := rpow_lt_two_pow hn (β := β) (by linarith)
    have hpos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn0 β
    rw [hlam, Real.rpow_neg hn0.le, ← div_eq_mul_inv, one_lt_div hpos]
    exact h1
  have hay : y < a := by rw [hadef]; nlinarith
  have ht : 0 < t := by
    have h1 : a ^ 2 ≤ y ^ 2 + 4 * t := (Real.le_sqrt ha.le (by positivity)).1 hcase
    nlinarith
  -- parameters
  set m := Real.sqrt (128 * n) with hmdef
  have hm : 0 < m := Real.sqrt_pos.2 (by positivity)
  have hm2 : m ^ 2 = 128 * n := Real.sq_sqrt (by positivity)
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  set ℓ := 1 + β * Real.log n with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hy8 : y ^ 2 ≤ 8 := by
    rw [hydef, mul_pow, Real.sq_sqrt (by norm_num)]
    have := alHeight_le_one n
    have := alHeight_pos n
    nlinarith
  have hYs4 : Ys ≤ 4 := by
    rw [hYs, Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hloga : Real.log a = Real.log 8 / 2 - β * Real.log n := by
    rw [ha', Real.log_mul h8.ne' (Real.rpow_pos_of_pos hn0 _).ne', Real.log_sqrt (by norm_num),
      Real.log_rpow hn0]
    ring
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hYa : Real.log (Ys / a) ≤ 2 * ℓ := by
    have hYs0 : 0 < Ys := ha.trans_le hcase
    rw [Real.log_div hYs0.ne' ha.ne', hloga]
    have : Real.log Ys ≤ Real.log 4 := Real.log_le_log hYs0 hYs4
    have : 0 ≤ β * Real.log n := by positivity
    rw [hℓdef]
    linarith
  have hmain := measure_deriv_revMap_ge_le hB' ht hy ha hm hℓ hYa
  -- the polylogarithmic form
  have hΛ1 : 1 ≤ 2 + Real.log n := by linarith
  have hℓΛ : ℓ ≤ 2 + Real.log n := by
    rw [hℓdef]
    have : β * Real.log n ≤ Real.log n := by nlinarith
    linarith
  have ha2 : a ^ 2 = 8 * (n : ℝ) ^ (-(2 * β)) := by
    rw [ha', mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul hn0.le]
    push_cast; ring_nf
  have hmΛ : Real.log (1 + m ^ 2 / a ^ 2) / 2 ≤ 2 + Real.log n := by
    have hq : m ^ 2 / a ^ 2 = 16 * (n : ℝ) * (n : ℝ) ^ (2 * β) := by
      rw [hm2, ha2, Real.rpow_neg hn0.le]
      field_simp
      ring
    have hnb : (n : ℝ) ^ (2 * β) ≤ n := by
      calc (n : ℝ) ^ (2 * β) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = n := Real.rpow_one _
    have hle : 1 + m ^ 2 / a ^ 2 ≤ 17 * (n : ℝ) ^ 2 := by
      rw [hq]; nlinarith
    have h17 : Real.log 17 ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (17 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
        _ ≤ Real.exp 1 ^ 4 := by gcongr
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    push_cast at hlog
    linarith
  have hD : 0 < (n : ℝ) * Real.log 2 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hDY : (n : ℝ) * Real.log 2 / 2 ≤ Real.log (Ys / y) := by
    have h1 : Real.log (a / y) ≤ Real.log (Ys / y) :=
      Real.log_le_log (div_pos ha hy) (div_le_div_of_nonneg_right hcase hy.le)
    have h2 : a / y = lam := by rw [hadef]; field_simp
    rw [h2, hlam, Real.log_mul (by positivity) (Real.rpow_pos_of_pos hn0 _).ne', Real.log_pow,
      Real.log_rpow hn0] at h1
    have := beta_log_le hn hβ
    linarith
  have hcb := coreBound_le hℓ hℓΛ hmΛ hΛ1 hD hDY
  have hya2 : (y / a) ^ 2 = ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β) := by
    have h2 : y / a = lam⁻¹ := by rw [hadef]; field_simp
    rw [h2, hlam, inv_pow, mul_pow, Real.rpow_neg hn0.le, inv_pow, ← Real.rpow_natCast
      ((n : ℝ) ^ β), ← Real.rpow_mul hn0.le, ← pow_mul]
    push_cast
    rw [show (2 : ℝ) ^ (n * 2) = 4 ^ n by rw [pow_mul']; norm_num]
    field_simp
  have hD' : 30 * (2 + Real.log n) ^ 2 / ((n : ℝ) * Real.log 2 / 2) =
      60 * (2 + Real.log n) ^ 2 / (n * Real.log 2) := by
    field_simp; ring
  rw [hya2, hD'] at hcb
  have htail : 2 * Real.exp (-(m ^ 2) / (64 * t)) ≤ 2 * Real.exp (-(2 * n)) := by
    have h64 : 0 < 64 * t := by linarith
    have h1 : 2 * (n : ℝ) ≤ m ^ 2 / (64 * t) := by
      rw [hm2, le_div_iff₀ h64]
      have := mul_le_mul_of_nonneg_left ht1 hn0.le
      linarith
    have h2 : -(m ^ 2) / (64 * t) ≤ -(2 * n) := by rw [neg_div]; linarith
    have h3 := Real.exp_le_exp.2 h2
    linarith
  have hc0 := coreBound_nonneg y a m ℓ Ys hℓ (by linarith)
  have hcb' : coreBound y a m ℓ Ys ≤ Real.exp (9 / 8) * ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β) *
      (60 * (2 + Real.log n) ^ 2 / (n * Real.log 2)) ^ (3 / 2 : ℝ) := by
    rw [mul_assoc (Real.exp (9 / 8))]; exact hcb
  refine hmain.trans ?_
  rw [ENNReal.ofReal_add (hc0.trans hcb') (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal hcb') (ENNReal.ofReal_le_ofReal htail)

/-! ## Summation -/

/-- `x^{2β} (60 (2 + log x)²/(x log 2))^{3/2} ≤ C x^{β − 5/4}` for `x ≥ 1`, `0 < β < 1/4`,
with `C = (60 (2 + 1/δ)²/log 2)^{3/2}`, `δ = (1/4 − β)/3`. -/
theorem rpow_mul_polylog_le {β x : ℝ} (hβ : β < 1 / 4) (hx : 1 ≤ x) :
    x ^ (2 * β) * (60 * (2 + Real.log x) ^ 2 / (x * Real.log 2)) ^ (3 / 2 : ℝ) ≤
      (60 * (2 + 1 / ((1 / 4 - β) / 3)) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) *
        x ^ (β - 5 / 4) := by
  set δ := (1 / 4 - β) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hx0 : 0 < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ0.le
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 2 + Real.log x ≤ (2 + 1 / δ) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  have h2 : 60 * (2 + Real.log x) ^ 2 / (x * Real.log 2) ≤
      60 * (2 + 1 / δ) ^ 2 / Real.log 2 * x ^ (2 * δ - 1) := by
    have hsq : (2 + Real.log x) ^ 2 ≤ ((2 + 1 / δ) * x ^ δ) ^ 2 := by
      have : 0 ≤ 2 + Real.log x := by linarith
      exact pow_le_pow_left₀ this h1 2
    have e : ((2 + 1 / δ) * x ^ δ) ^ 2 = (2 + 1 / δ) ^ 2 * (x ^ (2 * δ - 1) * x) := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ δ), ← Real.rpow_mul hx0.le, ← Real.rpow_add_one hx0.ne']
      push_cast; ring_nf
    rw [div_le_iff₀ (by positivity)]
    calc 60 * (2 + Real.log x) ^ 2 ≤ 60 * ((2 + 1 / δ) * x ^ δ) ^ 2 := by gcongr
      _ = 60 * (2 + 1 / δ) ^ 2 / Real.log 2 * x ^ (2 * δ - 1) * (x * Real.log 2) := by
        rw [e]; field_simp
  have h3 : (60 * (2 + Real.log x) ^ 2 / (x * Real.log 2)) ^ (3 / 2 : ℝ) ≤
      (60 * (2 + 1 / δ) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) * x ^ ((2 * δ - 1) * (3 / 2)) := by
    rw [Real.rpow_mul hx0.le, ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  calc x ^ (2 * β) * (60 * (2 + Real.log x) ^ 2 / (x * Real.log 2)) ^ (3 / 2 : ℝ)
      ≤ x ^ (2 * β) * ((60 * (2 + 1 / δ) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) *
        x ^ ((2 * δ - 1) * (3 / 2))) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (60 * (2 + 1 / δ) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) *
        (x ^ (2 * β) * x ^ ((2 * δ - 1) * (3 / 2))) := by ring
    _ = (60 * (2 + 1 / δ) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) * x ^ (β - 5 / 4) := by
        rw [← Real.rpow_add hx0, hδ]
        ring_nf

/-- **[AL14] Corollary 1, convergent half.** For every `β < 1/4` and every standard Brownian
motion `B` (the driver `U = B`, normalization `a = 1/4` of [AL14] §2.1),
`∑_n ∑_{t ∈ 𝒟_n} P{|f_t'(i 2^{-n})| ≥ 2^n n^{-β}} < ∞`, where `f_t = barInv U t`,
`2^{-n} = alHeight n` and `𝒟_n = {alTime n j : j ≤ 4^n}`. (The sum over `n` starts at `0`; the
term `n = 0` is finite, so this is [AL14]'s sum over `n ≥ 1` up to a finite term.) -/
theorem al14_corollary1_summable {β : ℝ} (hβ : β < 1 / 4) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∑' n : ℕ, ∑ j ∈ Finset.range (4 ^ n + 1), P {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
      ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime n j)) ((alHeight n : ℂ) * I)‖} ≠ ∞ := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set β₁ := max β (1 / 8) with hβ₁
  have hβ₁0 : 0 < β₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ₁4 : β₁ < 1 / 4 := max_lt hβ (by norm_num)
  have hββ₁ : β ≤ β₁ := le_max_left _ _
  set C := (60 * (2 + 1 / ((1 / 4 - β₁) / 3)) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) with hC
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ₁δ : 0 < (1 / 4 - β₁) / 3 := by linarith
  have hC0 : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  set r := 4 * Real.exp (-2) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    have := Real.exp_one_gt_d9
    calc (4 : ℝ) < 2.7182818283 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  set H : ℕ → ℝ := fun n => (if n = 0 then 2 else 0) +
    (2 * Real.exp (9 / 8) * C * (n : ℝ) ^ (β₁ - 5 / 4) + 4 * r ^ n) with hH
  have hH0 : ∀ n, 0 ≤ H n := fun n => by
    simp only [hH]
    have := Real.rpow_nonneg (Nat.cast_nonneg n) (β₁ - 5 / 4)
    split_ifs <;> positivity
  have hHs : Summable H := by
    refine (summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_)).add
      ((((Real.summable_nat_rpow.2 (by linarith)).mul_left (2 * Real.exp (9 / 8) * C))).add
        ((summable_geometric_of_lt_one hr0 hr1).mul_left 4))
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  -- termwise bound
  have hterm : ∀ n : ℕ, ∑ j ∈ Finset.range (4 ^ n + 1), P {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
      ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime n j)) ((alHeight n : ℂ) * I)‖} ≤
      ENNReal.ofReal (H n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      simp only [pow_zero, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      refine (add_le_add prob_le_one prob_le_one).trans ?_
      rw [show (1 : ℝ≥0∞) + 1 = ENNReal.ofReal 2 by norm_num]
      refine ENNReal.ofReal_le_ofReal ?_
      have e : H 0 = 2 + (2 * Real.exp (9 / 8) * C * ((0 : ℕ) : ℝ) ^ (β₁ - 5 / 4) + 4 * r ^ 0) := by
        simp only [hH, ite_true]
      have := Real.rpow_nonneg (Nat.cast_nonneg 0) (β₁ - 5 / 4)
      have : 0 ≤ 2 * Real.exp (9 / 8) * C * ((0 : ℕ) : ℝ) ^ (β₁ - 5 / 4) := by positivity
      have : 0 ≤ r ^ 0 := by positivity
      linarith
    · have hn1 : 1 ≤ n := hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hn0 : (0 : ℝ) < n := by linarith
      set b : ℝ := Real.exp (9 / 8) * ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β₁) *
        (60 * (2 + Real.log n) ^ 2 / (n * Real.log 2)) ^ (3 / 2 : ℝ) +
        2 * Real.exp (-(2 * n)) with hb
      have hb0 : 0 ≤ b := by
        have := Real.log_pos (by norm_num : (1:ℝ) < 2)
        positivity
      have hj : ∀ j ∈ Finset.range (4 ^ n + 1), P {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
          ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime n j)) ((alHeight n : ℂ) * I)‖} ≤
          ENNReal.ofReal b := by
        intro j hj
        refine (measure_mono fun ω hω => ?_).trans
          (measure_cor1_term_le hB hβ₁0 hβ₁4 hn1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
        have : (n : ℝ) ^ (-β₁) ≤ (n : ℝ) ^ (-β) :=
          Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
        exact le_trans (mul_le_mul_of_nonneg_left this (by positivity))
          (show (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤ _ from hω)
      refine (Finset.sum_le_sum hj).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hpl := rpow_mul_polylog_le hβ₁4 hnR
      have h4 : (0 : ℝ) < 4 ^ n := by positivity
      have hgeo : (4 : ℝ) ^ n * Real.exp (-(2 * n)) = r ^ n := by
        rw [hr, mul_pow, ← Real.exp_nat_mul]; ring_nf
      have hcast : ((4 ^ n + 1 : ℕ) : ℝ) ≤ 2 * 4 ^ n := by
        push_cast
        have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
        linarith
      have hH' : H n = 2 * Real.exp (9 / 8) * C * (n : ℝ) ^ (β₁ - 5 / 4) + 4 * r ^ n := by
        simp only [hH, hn.ne', ite_false, zero_add]
      rw [hH']
      calc ((4 ^ n + 1 : ℕ) : ℝ) * b ≤ 2 * 4 ^ n * b := mul_le_mul_of_nonneg_right hcast hb0
        _ = 2 * Real.exp (9 / 8) * ((n : ℝ) ^ (2 * β₁) *
            (60 * (2 + Real.log n) ^ 2 / (n * Real.log 2)) ^ (3 / 2 : ℝ)) +
            4 * ((4 : ℝ) ^ n * Real.exp (-(2 * n))) := by
          rw [hb]; field_simp; ring
        _ ≤ 2 * Real.exp (9 / 8) * (C * (n : ℝ) ^ (β₁ - 5 / 4)) + 4 * r ^ n := by
          rw [hgeo]
          gcongr
        _ = 2 * Real.exp (9 / 8) * C * (n : ℝ) ^ (β₁ - 5 / 4) + 4 * r ^ n := by ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
  rw [← ENNReal.ofReal_tsum_of_nonneg hH0 hHs]
  exact ENNReal.ofReal_ne_top

/-- **Borel–Cantelli form of Corollary 1** (the form used in the SLE₈ note's Lemma 2.1): for
`β < 1/4`, almost surely `D_n = max_{t ∈ 𝒟_n} |f_t'(i 2^{-n})| < 2^n n^{-β}` for all large `n`
(`D_n = derivGridMax U n`). -/
theorem ae_eventually_derivGridMax_lt {β : ℝ} (hβ : β < 1 / 4) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      derivGridMax (fun r => B r.toNNReal ω) n < (2 : ℝ) ^ n * (n : ℝ) ^ (-β) := by
  set s : ℕ → Set Ω := fun n => ⋃ j ∈ Finset.range (4 ^ n + 1), {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
    ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime n j)) ((alHeight n : ℂ) * I)‖} with hs
  have hsum : ∑' n, P (s n) ≠ ∞ :=
    ne_top_of_le_ne_top (al14_corollary1_summable hβ hB)
      (ENNReal.tsum_le_tsum fun n => measure_biUnion_finset_le _ _)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simp only [hs, mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hn
  unfold derivGridMax
  rw [Finset.sup'_lt_iff]
  exact fun j hj => hn j hj

/-! ## [AL14] Theorem 3, upper bound -/

/-- **Reduction to the reverse flow of a Brownian motion.** For `t ≥ 0` the event
`{λ ≤ |f_t'(i y_n)|}` is, up to a null set, contained in `{yλ ≤ y |∂_z revMap V t (iy)|}` for
`y = √8 y_n` and `V = drive 8 B'` with `B'` a standard Brownian motion. -/
theorem exists_measure_barInv_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (lam : ℝ) :
    ∃ B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B' P ∧
      P {ω | lam ≤ ‖deriv (barInv (fun r => B r.toNNReal ω) t) ((alHeight n : ℂ) * I)‖} ≤
        P {ω | Real.sqrt 8 * alHeight n * lam ≤ Real.sqrt 8 * alHeight n *
          ‖deriv (revMap (drive 8 B' ω) t) (((Real.sqrt 8 * alHeight n : ℝ) : ℂ) * I)‖} := by
  obtain ⟨B'', -, hB''c, hB''0, hB'', hB''eq⟩ := RS.exists_good_version0 hB
  refine ⟨UnzipInvariance.revBM B'' t.toNNReal,
    UnzipInvariance.isBrownianReal_revBM hB''.toIsPreBrownianReal hB''c _, ?_⟩
  have hy : 0 < Real.sqrt 8 * alHeight n := mul_pos (Real.sqrt_pos.2 (by norm_num)) (alHeight_pos n)
  refine measure_mono_ae ?_
  filter_upwards [hB''eq] with ω hω hmem
  have hU : (fun r : ℝ => B r.toNNReal ω) = fun r : ℝ => B'' r.toNNReal ω :=
    funext fun r => (hω _).symm
  simp only [hU] at hmem ⊢
  rw [norm_deriv_barInv_eq_revMap (hB''c ω) (hB''0 ω) ht (alHeight_pos n)] at hmem
  exact mul_le_mul_of_nonneg_left hmem hy.le

/-- The constant of our proof of the upper bound of [AL14, Theorem 3]. -/
def thm3Const (β : ℝ) : ℝ :=
  Real.exp (9 / 8) * (60 * (3 / Real.log 2 + 3 + β) ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) /
    Real.log 2 ^ 2 + 2 / Real.log 2 ^ 5

/-- `e^{−4n} ≤ 4^{−n} n^{−3/2}` for `n ≥ 1`. -/
theorem exp_neg_four_mul_le {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(4 * n)) ≤ ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h2 : (n : ℝ) ^ 2 ≤ 4 ^ n := by
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc (n : ℝ) ^ 2 ≤ (2 ^ n) ^ 2 := pow_le_pow_left₀ hn0.le this 2
      _ = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h3 : (16 : ℝ) ^ n ≤ Real.exp (4 * n) := by
    have he : (16 : ℝ) ≤ Real.exp 4 := by
      have := Real.add_one_le_exp 1
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ Real.exp 1 ^ 4 := by gcongr; linarith
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    calc (16 : ℝ) ^ n ≤ Real.exp 4 ^ n := pow_le_pow_left₀ (by norm_num) he n
      _ = Real.exp (4 * n) := by rw [← Real.exp_nat_mul]; ring_nf
  have h4 : (4 : ℝ) ^ n * (n : ℝ) ^ (3 / 2 : ℝ) ≤ Real.exp (4 * n) := by
    calc (4 : ℝ) ^ n * (n : ℝ) ^ (3 / 2 : ℝ) ≤ 4 ^ n * 4 ^ n := by gcongr; linarith
      _ = 16 ^ n := by rw [← mul_pow]; norm_num
      _ ≤ _ := h3
  rw [Real.rpow_neg hn0.le, Real.exp_neg, ← mul_inv]
  exact inv_anti₀ (by positivity) h4

section Thm3Params

variable {β : ℝ} {n : ℕ} {y lam a m Ys : ℝ}

theorem thm3_ha (hy : y = Real.sqrt 8 * alHeight n)
    (hlam : lam = (2 : ℝ) ^ n * (n : ℝ) ^ (-β)) (ha : a = y * lam) :
    a = Real.sqrt 8 * (n : ℝ) ^ (-β) := by
  have hya : y * (2 : ℝ) ^ n = Real.sqrt 8 := by
    rw [hy, alHeight, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  rw [ha, hlam, ← mul_assoc, hya]

theorem thm3_hmΛ (hβ0 : 0 < β) (hβ2 : β < 2) (hn : 1 ≤ n) (hy : y = Real.sqrt 8 * alHeight n)
    (hlam : lam = (2 : ℝ) ^ n * (n : ℝ) ^ (-β)) (ha : a = y * lam)
    (hm : m = 16 * Real.sqrt n) :
    Real.log (1 + m ^ 2 / a ^ 2) / 2 ≤ 3 + (3 + β) * Real.log n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm2 : m ^ 2 = 256 * n := by rw [hm, mul_pow, Real.sq_sqrt hn0.le]; norm_num
  have ha2 : a ^ 2 = 8 * ((n : ℝ) ^ (2 * β))⁻¹ := by
    rw [thm3_ha hy hlam ha, mul_pow, Real.sq_sqrt (by norm_num),
      ← Real.rpow_natCast ((n : ℝ) ^ (-β)), ← Real.rpow_mul hn0.le, ← Real.rpow_neg hn0.le]
    push_cast; ring_nf
  have hnb : (n : ℝ) ^ (2 * β) ≤ (n : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn1 (by push_cast; linarith)
  have hq : m ^ 2 / a ^ 2 = 32 * n * (n : ℝ) ^ (2 * β) := by
    rw [hm2, ha2]; field_simp; norm_num
  have hn5 : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hn1
  have hle : 1 + m ^ 2 / a ^ 2 ≤ 33 * (n : ℝ) ^ 5 := by
    rw [hq]
    have : (n : ℝ) * (n : ℝ) ^ (2 * β) ≤ (n : ℝ) ^ 5 := by
      calc (n : ℝ) * (n : ℝ) ^ (2 * β) ≤ n * (n : ℝ) ^ 4 := by gcongr
        _ = (n : ℝ) ^ 5 := by ring
    linarith
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have h33 : Real.log 33 ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    calc (33 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := by gcongr
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.log_nonneg hn1
  push_cast at hlog
  nlinarith

theorem thm3_hDY (hn : 1 ≤ n) (hy : y = Real.sqrt 8 * alHeight n)
    (hYs : Ys = Real.sqrt (y ^ 2 + 4)) : (n : ℝ) * Real.log 2 / 2 ≤ Real.log (Ys / y) := by
  have hy0 : 0 < y := by rw [hy]; exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (alHeight_pos n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hYs2 : 2 ≤ Ys := by
    rw [hYs]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hlogy : Real.log y = 3 * Real.log 2 / 2 - n * Real.log 2 := by
    rw [hy, alHeight, Real.log_mul (Real.sqrt_pos.2 (by norm_num)).ne' (by positivity),
      Real.log_sqrt (by norm_num), Real.log_inv, Real.log_pow,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  have h1 := Real.log_le_log (div_pos (by norm_num) hy0) (div_le_div_of_nonneg_right hYs2 hy0.le)
  rw [Real.log_div (by norm_num) hy0.ne', hlogy] at h1
  nlinarith

theorem thm3_hya2 (hn : 1 ≤ n) (hy : y = Real.sqrt 8 * alHeight n)
    (hlam : lam = (2 : ℝ) ^ n * (n : ℝ) ^ (-β)) (ha : a = y * lam) :
    (y / a) ^ 2 = ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < y := by rw [hy]; exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (alHeight_pos n)
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have h1 : y / a = lam⁻¹ := by rw [ha]; field_simp
  have hl2' : lam ^ 2 = (4 : ℝ) ^ n * ((n : ℝ) ^ (2 * β))⁻¹ := by
    rw [hlam, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-β)), ← Real.rpow_mul hn0.le,
      ← Real.rpow_neg hn0.le, ← pow_mul, show (2 : ℝ) ^ (n * 2) = 4 ^ n by
        rw [pow_mul']; norm_num]
    push_cast; ring_nf
  rw [h1, inv_pow, hl2', mul_inv, inv_inv]

/-- The scalar part of Theorem 3 (`T = 1`, `y = √8·2^{−n}`, `a = √8 n^{−β}`, `m = 16√n`,
`ℓ = 1 + β log n`, `Λ = 3 + (3 + β) log n`, `D = n log 2/2`). -/
theorem thm3_scalar (hβ0 : 0 < β) (hβ2 : β < 2) (hn : 2 ≤ n) (hy : y = Real.sqrt 8 * alHeight n)
    (hlam : lam = (2 : ℝ) ^ n * (n : ℝ) ^ (-β)) (ha : a = y * lam) (hm : m = 16 * Real.sqrt n)
    (hYs : Ys = Real.sqrt (y ^ 2 + 4)) :
    coreBound y a m (1 + β * Real.log n) Ys + 2 * Real.exp (-(m ^ 2) / (64 * 1)) ≤
      thm3Const β * ((2 : ℝ) ^ (2 * n))⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2) * Real.log n ^ 5 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl2a, hl2b⟩ := log_two_bounds
  have hl2 : 0 < Real.log 2 := by linarith
  have hlt := log_ge_log_two hnR
  have hlt0 : 0 < Real.log n := by linarith
  have hℓ0 : 0 < 1 + β * Real.log n := by positivity
  have hℓΛ : 1 + β * Real.log n ≤ 3 + (3 + β) * Real.log n := by nlinarith
  have hΛ1 : 1 ≤ 3 + (3 + β) * Real.log n := by nlinarith
  have hD0 : 0 < (n : ℝ) * Real.log 2 / 2 := by positivity
  have hcb := coreBound_le hℓ0 hℓΛ (thm3_hmΛ hβ0 hβ2 hn1 hy hlam ha hm) hΛ1 hD0
    (thm3_hDY hn1 hy hYs)
  rw [thm3_hya2 hn1 hy hlam ha] at hcb
  set K := 3 / Real.log 2 + 3 + β with hK
  have hΛK : 3 + (3 + β) * Real.log n ≤ K * Real.log n := by
    have h1 : 1 ≤ Real.log n / Real.log 2 := (one_le_div hl2).2 hlt
    have e : K * Real.log n = 3 * (Real.log n / Real.log 2) + (3 + β) * Real.log n := by
      rw [hK]; field_simp; ring
    rw [e]; linarith
  have hq : 30 * (3 + (3 + β) * Real.log n) ^ 2 / ((n : ℝ) * Real.log 2 / 2) ≤
      60 * K ^ 2 / Real.log 2 * Real.log n ^ 2 / n := by
    rw [div_le_div_iff₀ hD0 hn0]
    have hsq : (3 + (3 + β) * Real.log n) ^ 2 ≤ (K * Real.log n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hΛK 2
    calc 30 * (3 + (3 + β) * Real.log n) ^ 2 * n ≤ 30 * (K * Real.log n) ^ 2 * n := by gcongr
      _ = 60 * K ^ 2 / Real.log 2 * Real.log n ^ 2 * ((n : ℝ) * Real.log 2 / 2) := by
        field_simp; ring
  have hK2 : 0 ≤ 60 * K ^ 2 / Real.log 2 := by positivity
  have hq' : (30 * (3 + (3 + β) * Real.log n) ^ 2 / ((n : ℝ) * Real.log 2 / 2)) ^ (3 / 2 : ℝ) ≤
      (60 * K ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) * Real.log n ^ 3 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← rpow_three_halves_eq hK2 hlt0.le hn0]
    exact Real.rpow_le_rpow (div_nonneg (by positivity) hD0.le) hq (by norm_num)
  have hl3 := thm4_log_cube_le hnR
  have h4 : ((2 : ℝ) ^ (2 * n))⁻¹ = ((4 : ℝ) ^ n)⁻¹ := by
    rw [pow_mul]; norm_num
  have hm2 : m ^ 2 = 256 * n := by rw [hm, mul_pow, Real.sq_sqrt hn0.le]; norm_num
  have htail : 2 * Real.exp (-(m ^ 2) / (64 * 1)) = 2 * Real.exp (-(4 * n)) := by
    rw [hm2]; congr 2; ring
  have he := exp_neg_four_mul_le hn1
  have hβt : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (n : ℝ) ^ (2 * β - 3 / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hl5 : 1 ≤ Real.log n ^ 5 / Real.log 2 ^ 5 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hl2.le hlt 5
  have hsplit : (n : ℝ) ^ (2 * β - 3 / 2) = (n : ℝ) ^ (2 * β) * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have h4p : 0 < ((4 : ℝ) ^ n)⁻¹ := by positivity
  have hcore : Real.exp (9 / 8) * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β)) *
      (30 * (3 + (3 + β) * Real.log n) ^ 2 / ((n : ℝ) * Real.log 2 / 2)) ^ (3 / 2 : ℝ) ≤
      Real.exp (9 / 8) * (60 * K ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) / Real.log 2 ^ 2 *
        ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2) * Real.log n ^ 5 := by
    have hE : 0 ≤ Real.exp (9 / 8) * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β)) := by positivity
    calc _ ≤ Real.exp (9 / 8) * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β)) *
          ((60 * K ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) * Real.log n ^ 3 * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hq' hE
      _ ≤ Real.exp (9 / 8) * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β)) *
          ((60 * K ^ 2 / Real.log 2) ^ (3 / 2 : ℝ) * (Real.log n ^ 5 / Real.log 2 ^ 2) *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by rw [hsplit]; field_simp
  have htl : 2 * Real.exp (-(4 * n)) ≤
      2 / Real.log 2 ^ 5 * ((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2) * Real.log n ^ 5 := by
    have hT : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hn0.le _
    calc 2 * Real.exp (-(4 * n)) ≤ 2 * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by linarith
      _ ≤ 2 * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2)) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ 2 * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2)) *
          (Real.log n ^ 5 / Real.log 2 ^ 5) := by
          have : 0 ≤ 2 * (((4 : ℝ) ^ n)⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2)) := by
            have := Real.rpow_nonneg hn0.le (2 * β - 3 / 2); positivity
          exact mul_le_mul_of_nonneg_left hl5 this
      _ = _ := by field_simp
  rw [htail, h4]
  unfold thm3Const
  rw [← hK]
  linarith

end Thm3Params

/-- **[AL14] Theorem 3, upper bound.** For `0 < β < 2` there is `c₂` such that, for every
standard Brownian motion `B` and every `n ≥ 2`,
`P{|f_1'(2^{-n} i)| ≥ 2^n n^{-β}} ≤ c₂ 2^{-2n} n^{2β - 3/2} (log n)^5`, where `f_1 = barInv U 1`.
(At `n = 1` the right side is `0` because `log 1 = 0`; the event is then empty, since
`|f_1'(i/2)| ≤ Y_1/y < 2` by Lemma 2.2 of the note. So the bound holds for every `n ≥ 1`, while
[AL14]'s two-sided statement fails at `n = 1`.) -/
theorem al14_theorem3_upper {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) :
    ∃ c₂ : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ},
      IsBrownianReal B P → ∀ n : ℕ, 1 ≤ n →
        P {ω | (2 : ℝ) ^ n * (n : ℝ) ^ (-β) ≤
            ‖deriv (barInv (fun r => B r.toNNReal ω) 1) ((alHeight n : ℂ) * I)‖} ≤
          ENNReal.ofReal (c₂ * ((2 : ℝ) ^ (2 * n))⁻¹ * (n : ℝ) ^ (2 * β - 3 / 2) *
            Real.log n ^ 5) := by
  refine ⟨thm3Const β, fun {Ω} _ {P} {B} hB n hn1 => ?_⟩
  obtain ⟨B', hB', hle⟩ := exists_measure_barInv_le hB zero_le_one n
    ((2 : ℝ) ^ n * (n : ℝ) ^ (-β))
  refine hle.trans ?_
  rcases eq_or_lt_of_le hn1 with h1 | hn
  · -- `n = 1`: the event is empty
    subst h1
    have hy0 : 0 < Real.sqrt 8 * alHeight 1 :=
      mul_pos (Real.sqrt_pos.2 (by norm_num)) (alHeight_pos 1)
    have hz : Real.sqrt ((Real.sqrt 8 * alHeight 1) ^ 2 + 4 * 1) <
        Real.sqrt 8 * alHeight 1 * ((2 : ℝ) ^ 1 * ((1 : ℕ) : ℝ) ^ (-β)) := by
      have hh : alHeight 1 = 1 / 2 := by simp [alHeight]
      rw [hh, mul_pow, Real.sq_sqrt (by norm_num)]
      simp only [Nat.cast_one, Real.one_rpow, mul_one, pow_one]
      rw [show Real.sqrt 8 * (1 / 2) * 2 = Real.sqrt 8 by ring]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [measure_deriv_revMap_ge_eq_zero hB' zero_le_one hy0 hz]
    exact zero_le
  replace hn : 2 ≤ n := hn
  obtain ⟨y, hy⟩ : ∃ y, y = Real.sqrt 8 * alHeight n := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (2 : ℝ) ^ n * (n : ℝ) ^ (-β) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 16 * Real.sqrt n := ⟨_, rfl⟩
  obtain ⟨Ys, hYs⟩ : ∃ Ys, Ys = Real.sqrt (y ^ 2 + 4) := ⟨_, rfl⟩
  rw [← hy, ← hlam]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := by rw [hy]; exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (alHeight_pos n)
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have ha0 : 0 < y * lam := mul_pos hy0 hlam0
  have hm0 : 0 < m := by rw [hm]; have := Real.sqrt_pos.2 hn0; positivity
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hℓ0 : 0 < 1 + β * Real.log n := by positivity
  -- `log(Y*/a) ≤ 2ℓ`
  have hYa : Real.log (Real.sqrt (y ^ 2 + 4 * 1) / (y * lam)) ≤ 2 * (1 + β * Real.log n) := by
    have hy8 : y ^ 2 ≤ 8 := by
      rw [hy, mul_pow, Real.sq_sqrt (by norm_num)]
      have := alHeight_le_one n
      have := alHeight_pos n
      nlinarith
    have hYs4 : Real.sqrt (y ^ 2 + 4 * 1) ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    have hYs0 : 0 < Real.sqrt (y ^ 2 + 4 * 1) := Real.sqrt_pos.2 (by positivity)
    have hloga : Real.log (y * lam) = Real.log 8 / 2 - β * Real.log n := by
      rw [thm3_ha hy hlam rfl, Real.log_mul (Real.sqrt_pos.2 (by norm_num)).ne'
        (Real.rpow_pos_of_pos hn0 _).ne', Real.log_sqrt (by norm_num), Real.log_rpow hn0]
      ring
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    rw [Real.log_div hYs0.ne' ha0.ne', hloga]
    have h1 : Real.log (Real.sqrt (y ^ 2 + 4 * 1)) ≤ 2 * Real.log 2 := by
      rw [← hlog4]; exact Real.log_le_log hYs0 hYs4
    have h2 : 0 ≤ β * Real.log n := by positivity
    have h3 : Real.log 8 / 2 = 3 * Real.log 2 / 2 := by rw [hlog8]
    calc Real.log (Real.sqrt (y ^ 2 + 4 * 1)) - (Real.log 8 / 2 - β * Real.log n)
        ≤ 2 * Real.log 2 - (3 * Real.log 2 / 2 - β * Real.log n) := by
          rw [h3]; exact sub_le_sub_right h1 _
      _ ≤ 2 * (1 + β * Real.log n) := by linarith
  have hmain := measure_deriv_revMap_ge_le hB' zero_lt_one hy0 ha0 hm0 hℓ0 hYa
  refine hmain.trans ?_
  have hYs' : Real.sqrt (y ^ 2 + 4 * 1) = Ys := by rw [hYs, mul_one]
  rw [hYs']
  have hsc := thm3_scalar hβ0 hβ2 hn hy hlam rfl hm hYs
  have hc0 := coreBound_nonneg y (y * lam) m (1 + β * Real.log n) Ys hℓ0 (by
    rw [hYs]; exact Real.log_nonneg (by
      rw [le_div_iff₀ hy0, one_mul]; exact Real.le_sqrt_of_sq_le (by linarith)))
  rw [← ENNReal.ofReal_add hc0 (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsc

end InteractingSLE.SLE8.AL14
