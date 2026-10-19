import GaussianLQG.Uniform.UpperTail.Leaves
import LQGMetric.Papers.DDDF.P18Step4

/-!
# DDDF Proposition 18, Step 4 (large tails), uniform in `ξ`: the constant fix

Phase B, packet B-3 (worker PB-U6). Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`,
U6 and Finding `fd:step4`. Template (not edited): `dddf_p18_step4`
(`LQGMetric/Papers/DDDF/P18Step4.lean`; DDDF20 `tightness.tex` l. 930–936).

The template takes `c = 1/(16ξ²)` and `C = exp(c s₀²/log 2)` with `s₀ = A(ξ)²`,
`A(ξ) = 8ξ(log 4 + C₁)/log 2 + 2(log 3 + 1) + 8ξ² + 1` (`C₁` the `ξ`-free constant of the
a-priori bound `p18_ell_lower_W`). Since `s₀ ≥ (2 log 3 + 3)²`, `C ≥ exp(729/(16ξ² log 2))`,
which is unbounded as `ξ ↓ 0`: this is the only non-uniform constant of the whole chain.

The fix: the proof uses `c` only through `c ≤ 1/(16ξ²)` (the key step of the main branch, an
equality in the template) and `C` only through `C ≥ exp(c s₀²/log 2)` (the branch `s < s₀`) and
`C ≥ 1`; and `A(ξ)` is nondecreasing in `ξ`. So

* `p18_step4_of_consts`: the template's proof with `A`, `c`, `C` as parameters satisfying exactly
  `A ≥ A(ξ)`, `0 < c`, `16ξ²c ≤ 1`, `C ≥ exp(c (A²)²/log 2)`;
* `p18_step4_unif` (ledger U6): the constants `c* = 1/(16ξs²)` and
  `C* = exp(c* A(ξs)⁴/log 2)`, chosen before the probability space and before `ξ`, work for every
  `ξ ∈ (0, ξs]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **DDDF Prop 18, Step 4, with its constants as parameters** (template `dddf_p18_step4`, same
proof; ledger Finding `fd:step4`). For `n ≥ 1`, `s > 2`, `2^n ≤ s²`:
`P(L^{(n)}_{3,1} ≥ e^s Λ_n(p) ℓ_n(p)) ≤ C e^{-c s²/log s}`, for any `A ≥ A(ξ)`, `0 < c ≤ 1/(16ξ²)`
and `C ≥ exp(c A⁴/log 2)`. -/
theorem p18_step4_of_consts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) {p : ℝ} (hp0 : 0 < p)
    (hp : p ≤ 1 / 2) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hell : ∀ n : ℕ, 1 ≤ n → Real.exp (-(ξ * (n * Real.log 4 + C₁ * √n))) ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB 1 1) (ENNReal.ofReal p))
    {A c C : ℝ}
    (hA : 8 * (ξ * (Real.log 4 + C₁)) / Real.log 2 + 2 * (Real.log 3 + 1) + 8 * ξ ^ 2 + 1 ≤ A)
    (hc0 : 0 < c) (hc : 16 * ξ ^ 2 * c ≤ 1) (hC : Real.exp (c * (A ^ 2) ^ 2 / Real.log 2) ≤ C)
    (n : ℕ) (s : ℝ) (hn : 1 ≤ n) (hs2 : 2 < s) (hns : (2 : ℝ) ^ n ≤ s ^ 2) :
    P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
      ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  have := hW.isProbabilityMeasure
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set K : ℝ := ξ * (Real.log 4 + C₁) with hKdef
  have hK : 0 < K := by positivity
  set D₀ : ℝ := Real.log 3 + 1 with hD₀def
  have hK8 : 0 ≤ 8 * K / Real.log 2 := by positivity
  have hA1 : 1 ≤ A := by nlinarith [sq_nonneg ξ]
  have hC1 : 1 ≤ C := (Real.one_le_exp (by positivity)).trans hC
  have hs0 : 0 < s := by linarith
  have hls : Real.log 2 < Real.log s := Real.log_lt_log (by norm_num) hs2
  have hls0 : 0 < Real.log s := hl2.trans hls
  by_cases hss : s < A ^ 2
  · -- small `s`: the probability is at most `1 ≤ C e^{-c s²/log s}`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : c * s ^ 2 / Real.log s ≤ c * (A ^ 2) ^ 2 / Real.log 2 := by
      have hsq : s ^ 2 ≤ (A ^ 2) ^ 2 := pow_le_pow_left₀ hs0.le hss.le 2
      calc c * s ^ 2 / Real.log s ≤ c * (A ^ 2) ^ 2 / Real.log s :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc0.le) hls0.le
        _ ≤ c * (A ^ 2) ^ 2 / Real.log 2 :=
            div_le_div_of_nonneg_left (by positivity) hl2 hls.le
    calc (1 : ℝ) ≤ Real.exp (c * (A ^ 2) ^ 2 / Real.log 2 + -c * s ^ 2 / Real.log s) :=
          Real.one_le_exp (by rw [neg_mul, neg_div]; linarith)
      _ = Real.exp (c * (A ^ 2) ^ 2 / Real.log 2) * Real.exp (-c * s ^ 2 / Real.log s) :=
          Real.exp_add _ _
      _ ≤ C * Real.exp (-c * s ^ 2 / Real.log s) :=
          mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
  push Not at hss
  -- large `s`: `√s ≥ A`
  have hsA : A ≤ √s := by
    rw [show A = √(A ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hss
  have hsq1 : 1 ≤ √s := hA1.trans hsA
  have hss2 : √s * √s = s := Real.mul_self_sqrt hs0.le
  have hlog := log_le_two_sqrt hs0
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnl : n * Real.log 2 ≤ 2 * Real.log s := by
    have := Real.log_le_log (by positivity) hns
    rwa [Real.log_pow, Real.log_pow] at this
  have hsqn : √(n : ℝ) ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hKn : ξ * (n * Real.log 4 + C₁ * √n) ≤ K * n := by
    simp only [K]; nlinarith [mul_le_mul_of_nonneg_left hsqn (by positivity : (0 : ℝ) ≤ ξ * C₁)]
  have hnK : K * n ≤ 4 * K / Real.log 2 * √s := by
    have h1 : n ≤ 2 * Real.log s / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    have h2 : 2 * Real.log s / Real.log 2 ≤ 4 * √s / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hl2.le
    calc K * n ≤ K * (4 * √s / Real.log 2) := mul_le_mul_of_nonneg_left (h1.trans h2) hK.le
      _ = 4 * K / Real.log 2 * √s := by ring
  set s'' : ℝ := s - K * n - D₀
  have hs'' : s / 2 ≤ s'' := by
    have : (8 * K / Real.log 2 + 2 * D₀) * √s ≤ s :=
      calc (8 * K / Real.log 2 + 2 * D₀) * √s ≤ √s * √s :=
            mul_le_mul_of_nonneg_right (by linarith [hA, sq_nonneg ξ, hsA])
              (Real.sqrt_nonneg _)
        _ = s := hss2
    have h8 : 8 * K / Real.log 2 * √s = 2 * (4 * K / Real.log 2 * √s) := by ring
    nlinarith
  set s' : ℝ := s'' / ξ
  have hs'ξ : ξ * s' = s'' := by simp only [s']; field_simp
  have hlev : ξ * (n * Real.log 2) < s' := by
    rw [lt_div_iff₀ hξ]
    have : 8 * ξ ^ 2 * √s ≤ s :=
      calc 8 * ξ ^ 2 * √s ≤ √s * √s :=
            mul_le_mul_of_nonneg_right (by
              have : 0 ≤ 8 * K / Real.log 2 + 2 * D₀ := by positivity
              linarith [hA, hsA]) (Real.sqrt_nonneg _)
        _ = s := hss2
    have e1 : ξ * (n * Real.log 2) * ξ = ξ ^ 2 * (n * Real.log 2) := by ring
    have e2 := mul_le_mul_of_nonneg_left hnl (sq_nonneg ξ)
    have e3 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ξ)
    have hξ2 : 0 < ξ ^ 2 := by positivity
    rw [e1]
    nlinarith
  have hstr := dddf_p18_straight hW hξ (a := 3) (b := 1) (by norm_num) zero_le_one hn hlev
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hℓ := hell n hn
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) := lt_of_lt_of_le (Real.exp_pos _) hℓ
  have hΛ := ellN_le_LambdaN_mul (ξ := ξ) (P := P) (W := W) hp0 hp hℓ0
  refine le_trans (measure_mono fun ω hω => ?_) (hstr.trans (ENNReal.ofReal_le_ofReal ?_))
  · have hω' : Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
        ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω := hω
    have hlt : 3 * Real.exp (ξ * s') < lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω := by
      rw [hs'ξ]
      have e3 : 3 * Real.exp s'' = Real.exp (s - K * n - 1) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]; congr 1
        simp only [s'', D₀]; ring
      rw [e3]
      calc Real.exp (s - K * n - 1) < Real.exp (s - K * n) := Real.exp_lt_exp.2 (by linarith)
        _ ≤ Real.exp s * Real.exp (-(ξ * (n * Real.log 4 + C₁ * √n))) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
        _ ≤ Real.exp s * ellN ξ W P n (ENNReal.ofReal p) :=
          mul_le_mul_of_nonneg_left hℓ (Real.exp_pos _).le
        _ ≤ Real.exp s * (LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)) :=
          mul_le_mul_of_nonneg_left hΛ (Real.exp_pos _).le
        _ ≤ _ := by rw [← mul_assoc]; exact hω'
    have hne := rectLen_ne_top (ξ := ξ) (rectAB 3 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hφ.cont ω)
    show ENNReal.ofReal (3 * Real.exp (ξ * s')) <
      rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB 3 1)
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hlt)).2 hlt
  · have hs'2 : s ^ 2 / (4 * ξ ^ 2) ≤ s' ^ 2 := by
      have : (s / 2) ^ 2 ≤ s'' ^ 2 := pow_le_pow_left₀ (by positivity) hs'' 2
      simp only [s']
      rw [div_pow, le_div_iff₀ (by positivity)]
      have e : s ^ 2 / (4 * ξ ^ 2) * ξ ^ 2 = (s / 2) ^ 2 := by field_simp; ring
      rw [e]; exact this
    have hden : 0 < 2 * (n * Real.log 2) := by positivity
    have hξne : ξ ≠ 0 := hξ.ne'
    have hlsne : Real.log s ≠ 0 := hls0.ne'
    -- the fix: `c ≤ 1/(16ξ²)` replaces the template's equality `c = 1/(16ξ²)`
    have hc' : c ≤ 1 / (16 * ξ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hkey : c * s ^ 2 / Real.log s ≤ s' ^ 2 / (2 * (n * Real.log 2)) := by
      calc c * s ^ 2 / Real.log s ≤ 1 / (16 * ξ ^ 2) * s ^ 2 / Real.log s :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc' (sq_nonneg s)) hls0.le
        _ = s ^ 2 / (4 * ξ ^ 2) / (4 * Real.log s) := by field_simp; ring
        _ ≤ s' ^ 2 / (4 * Real.log s) := div_le_div_of_nonneg_right hs'2 (by positivity)
        _ ≤ s' ^ 2 / (2 * (n * Real.log 2)) :=
            div_le_div_of_nonneg_left (sq_nonneg _) hden (by linarith)
    calc Real.exp (-(s' ^ 2 / (2 * (n * Real.log 2)))) ≤ Real.exp (-c * s ^ 2 / Real.log s) := by
          refine Real.exp_le_exp.2 ?_
          rw [neg_mul, neg_div]; linarith
      _ ≤ C * Real.exp (-c * s ^ 2 / Real.log s) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hC1

/-- **DDDF Prop 18, Step 4, uniform in `ξ ∈ (0, ξs]` and in the white noise, with the constant
fix** (ledger U6 `p18_step4_unif`, Finding `fd:step4`): for `p ∈ (0, 1/2]` the constants
`c* = 1/(16ξs²)` and `C* = exp(c* A(ξs)⁴/log 2)`, chosen before the probability space and before
`ξ`, satisfy, for `n ≥ 1`, `s > 2`, `2^n ≤ s²`,
`P(L^{(n)}_{3,1} ≥ e^s Λ_n(p) ℓ_n(p)) ≤ C* e^{-c* s²/log s}`. -/
theorem p18_step4_unif (ξs : ℝ) (hξs : 0 < ξs) {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ (n : ℕ) (s : ℝ), 1 ≤ n → 2 < s → (2 : ℝ) ^ n ≤ s ^ 2 →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  obtain ⟨C₁, hC₁, hell⟩ := p18_ell_lower_W hp0 (by linarith : p < 1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 8 * (ξs * (Real.log 4 + C₁)) / Real.log 2 +
      2 * (Real.log 3 + 1) + 8 * ξs ^ 2 + 1 := ⟨_, rfl⟩
  refine ⟨Real.exp (1 / (16 * ξs ^ 2) * (A ^ 2) ^ 2 / Real.log 2), 1 / (16 * ξs ^ 2),
    Real.exp_pos _, by positivity, fun {Ω} _ {P} {W} hW ξ hξ n s hn hs hns => ?_⟩
  have hξ2 : ξ ^ 2 ≤ ξs ^ 2 := pow_le_pow_left₀ hξ.1.le hξ.2 2
  refine p18_step4_of_consts hW hξ.1 hp0 hp hC₁ (hell hW ξ hξ.1) ?_ (by positivity) ?_ le_rfl
    n s hn hs hns
  · -- `A(ξ) ≤ A(ξs)`
    have h1 : 8 * (ξ * (Real.log 4 + C₁)) / Real.log 2 ≤
        8 * (ξs * (Real.log 4 + C₁)) / Real.log 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hξ.2 (by positivity)) (by norm_num)) hl2.le
    rw [hAdef]
    linarith
  · -- `16 ξ² c* ≤ 1`
    rw [mul_one_div, div_le_one (by positivity)]
    linarith

end Uniform
end GaussianLQG
