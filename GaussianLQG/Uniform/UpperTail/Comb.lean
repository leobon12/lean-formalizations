import GaussianLQG.Uniform.UpperTail.Step1
import GaussianLQG.Uniform.UpperTail.Step3
import GaussianLQG.Uniform.UpperTail.Step4
import LQGMetric.Papers.DDDF.P18Zero

/-!
# DDDF Proposition 18, uniform in `ξ`: the combination (Route U, item U6)

Phase B, packet B-3 (worker PB-U6). Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`,
U6 and §5 (row `dddf_prop18_of_steps`). Template (not edited): `dddf_prop18_of_steps`
(`LQGMetric/Papers/DDDF/P18Comb.lean`; DDDF20 `tightness.tex` l. 929, 937–938). Steps 2–3 at one
scale (`p18_mid`) and the case `n = 0` (`dddf_p18_zero`) are reused unchanged.

The template's constants are `D = ξ(1+C₂)(log 4+1) + log 2 + ξC₁ + |log C₁| + 2ξ log 2 + C₃`,
`B = (2D²+1)/log 2`, `c' = min(1/log 4, c₁)`, `c = min(c₄, c'/(2B))`, `s₀ = 2B` and
`C = C₄ + 3C₂ + C₁ + exp(c s₀²/log 2)`, from Step 1 at level `2p` (`C₁, c₁`), Prop 2 on `R_{3,1}`
(`C₂`), Step 3 (`C₃`) and Step 4 (`C₄, c₄`). `D` is affine and nondecreasing in `ξ`, and every
other constant is uniform once the steps are; the only unbounded one was `C₄` (fixed in
`p18_step4_unif`).

* `prop18_of_consts`: the template's proof with `D, B, c, C` as parameters, used only through
  `D ≥ D(ξ)`, `2D² + 1 ≤ B log 2`, `0 < c ≤ c₄`, `2Bc ≤ 1/log 4`, `2Bc ≤ c₁` and
  `C ≥ C₄ + 3C₂ + C₁ + exp(c(2B)²/log 2)`; the scale `m` is chosen from `B`, and `D(ξ) ≤ D` is
  used only in the threshold of `p18_mid`.
* `prop18_unif_of_cor17` (ledger U6 `prop18_unif`, conditional on uniform Cor 17,
  `IfaceCor17U ξs`): the template's constants with `D* = D(ξs)`, all chosen before the probability
  space and before `ξ`. The unconditional `prop18_unif` is in `GaussianLQG/Uniform/UpperTail.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **DDDF Proposition 18 from its steps, with the constants as parameters** (template
`dddf_prop18_of_steps`, same proof): from Step 1 at level `p` (`C₁, c₁`), Prop 2 on `R_{3,1}`
(`C₂`), Step 3 (`C₃`), `ℓ_n > 0` and Step 4 (`C₄, c₄`),
`P(L^{(n)}_{3,1}(φ) ≥ e^s Λ_n(p) ℓ_n(p)) ≤ C e^{-c s²/log s}` for all `n` and `s > 2`, for any
`D ≥ D(ξ)`, `B ≥ (2D²+1)/log 2`, `0 < c ≤ min(c₄, min(1/log 4, c₁)/(2B))` and
`C ≥ C₄ + 3C₂ + C₁ + exp(c(2B)²/log 2)`. -/
theorem prop18_of_consts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) {p : ℝ} (hp0 : 0 < p)
    (hp4 : p ≤ 1 / 4) {C₁ c₁ C₂ C₃ C₄ c₄ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hC₄ : 0 < C₄)
    (hS1 : ∀ n k : ℕ, 1 ≤ k →
      P {ω | Real.exp (ξ * C₁ * √k) * C₁ * k ^ 2 * ellBarN ξ W P n (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ≤
        ENNReal.ofReal (C₁ * Real.exp (-(c₁ * k))))
    (hS2 : ∀ (m : ℕ) (α : ℝ), 0 < α →
      P.real {ω | α * (m + C₂ * Real.sqrt m) ≤
        ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ≤
        3 * (C₂ * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4)))
    (hS3 : ∀ n k : ℕ, k ≤ n → (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) *
        Real.exp (-(C₃ * √k)) ≤ ellN ξ W P n (ENNReal.ofReal p))
    (hℓ : ∀ n : ℕ, 1 ≤ n → 0 < ellN ξ W P n (ENNReal.ofReal p))
    (hS4 : ∀ (n : ℕ) (s : ℝ), 1 ≤ n → 2 < s → (2 : ℝ) ^ n ≤ s ^ 2 →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C₄ * Real.exp (-c₄ * s ^ 2 / Real.log s)))
    {D B c C : ℝ}
    (hD : ξ * (1 + C₂) * (Real.log 4 + 1) + Real.log 2 + ξ * C₁ + |Real.log C₁| +
      2 * ξ * Real.log 2 + C₃ ≤ D)
    (hB : 2 * D ^ 2 + 1 ≤ B * Real.log 2) (hc0 : 0 < c) (hc4 : c ≤ c₄)
    (hcB1 : 2 * B * c ≤ 1 / Real.log 4) (hcB2 : 2 * B * c ≤ c₁)
    (hC : C₄ + (3 * C₂ + C₁) + Real.exp (c * (2 * B) ^ 2 / Real.log 2) ≤ C)
    (n : ℕ) (s : ℝ) (hs : 2 < s) :
    P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
      ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  have := hW.isProbabilityMeasure
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hB0 : 0 < B :=
    lt_of_mul_lt_mul_right (by rw [zero_mul]; nlinarith [sq_nonneg D]) hl2.le
  have hCe := Real.exp_pos (c * (2 * B) ^ 2 / Real.log 2)
  have hC0 : 0 < C := by linarith
  have hs0 : 0 < s := by linarith
  have hls : Real.log 2 < Real.log s := Real.log_lt_log (by norm_num) hs
  have hls0 : 0 < Real.log s := hl2.trans hls
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = s ^ 2 / Real.log s := ⟨_, rfl⟩
  have hX : 0 < X := by rw [hXdef]; positivity
  have hform : ∀ c₀ : ℝ, -c₀ * s ^ 2 / Real.log s = -(c₀ * X) := fun c₀ => by
    rw [hXdef]; ring
  rw [hform c]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dddf_p18_zero hW hp0 (by linarith) hs]; exact bot_le
  by_cases hns : (2 : ℝ) ^ n ≤ s ^ 2
  · -- Step 4
    refine (hS4 n s hn hs hns).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hform c₄]
    refine mul_le_mul (by linarith) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hC0.le
    have := mul_le_mul_of_nonneg_right hc4 hX.le
    linarith
  push Not at hns
  by_cases hss : s < 2 * B
  · -- small `s`: the probability is at most `1 ≤ C e^{-cX}`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : c * X ≤ c * (2 * B) ^ 2 / Real.log 2 := by
      have hsq : s ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left₀ hs0.le hss.le 2
      rw [hXdef, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc0.le
      calc s ^ 2 / Real.log s ≤ (2 * B) ^ 2 / Real.log s := div_le_div_of_nonneg_right hsq hls0.le
        _ ≤ (2 * B) ^ 2 / Real.log 2 := div_le_div_of_nonneg_left (by positivity) hl2 hls.le
    calc (1 : ℝ) ≤ Real.exp (c * (2 * B) ^ 2 / Real.log 2 + -(c * X)) :=
          Real.one_le_exp (by linarith)
      _ = Real.exp (c * (2 * B) ^ 2 / Real.log 2) * Real.exp (-(c * X)) := Real.exp_add _ _
      _ ≤ C * Real.exp (-(c * X)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  push Not at hss
  -- the scale `m`: `2^m ≤ s²/(B log s) < 2^{m+1}`
  have hBl : 1 ≤ B * Real.log s := by
    have h := mul_le_mul_of_nonneg_left hls.le hB0.le
    nlinarith [sq_nonneg D]
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = s ^ 2 / (B * Real.log s) := ⟨_, rfl⟩
  have hlogs : Real.log s ≤ s := (Real.log_le_sub_one_of_pos hs0).trans (by linarith)
  have hy2 : 2 ≤ y := by
    rw [hydef, le_div_iff₀ (mul_pos hB0 hls0)]
    have h1 := mul_le_mul_of_nonneg_left hlogs hB0.le
    have h2 := mul_le_mul_of_nonneg_right hss hs0.le
    linarith
  have hys : y ≤ s ^ 2 := by rw [hydef]; exact div_le_self (by positivity) hBl
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ y)
    (by norm_num : (1 : ℝ) < 2)
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [zero_add, pow_one] at hm2; linarith
    · exact h
  have hmn : m < n := by
    have : (2 : ℝ) ^ m < 2 ^ n := by linarith
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
  have hml : (m : ℝ) * Real.log 2 ≤ 2 * Real.log s := by
    have := Real.log_le_log (by positivity) (hm1.trans hys)
    rwa [Real.log_pow, Real.log_pow] at this
  have hDQ : D * √((2 : ℝ) ^ m * m) ≤ s := by
    have hsq : (D * √((2 : ℝ) ^ m * m)) ^ 2 ≤ s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hm' : (m : ℝ) ≤ 2 * Real.log s / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
      have hne1 := hls0.ne'
      have hne2 := hl2.ne'
      have hne3 := hB0.ne'
      calc D ^ 2 * (2 ^ m * m) ≤ D ^ 2 * (y * (2 * Real.log s / Real.log 2)) := by
            gcongr
        _ = s ^ 2 * (2 * D ^ 2 / (B * Real.log 2)) := by rw [hydef]; field_simp
        _ ≤ s ^ 2 * 1 := by
            gcongr
            rw [div_le_one (mul_pos hB0 hl2)]; linarith
        _ = s ^ 2 := mul_one _
    exact (pow_le_pow_iff_left₀ (mul_nonneg hD0 (Real.sqrt_nonneg _)) hs0.le two_ne_zero).1 hsq
  -- the threshold of `p18_mid`, with `D(ξ) ≤ D`
  have hDQ' : (ξ * (1 + C₂) * (Real.log 4 + 1) + Real.log 2 + ξ * C₁ + |Real.log C₁| +
      2 * ξ * Real.log 2 + C₃) * √((2 : ℝ) ^ m * m) ≤ s :=
    (mul_le_mul_of_nonneg_right hD (Real.sqrt_nonneg _)).trans hDQ
  have hmid := p18_mid hW hξ hp0 (by linarith) hC₁ hC₂ hC₃ hS1 hS2 hS3 hℓ hm hmn hDQ'
  refine hmid.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hym : y / 2 < 2 ^ m := by rw [pow_succ] at hm2; linarith
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hcX : c * X ≤ 2 * B * c * 2 ^ m := by
    have hXy : X = B * y := by
      rw [hXdef, hydef]; field_simp
    have h := mul_le_mul_of_nonneg_left hym.le (by positivity : (0 : ℝ) ≤ 2 * B * c)
    rw [hXy]
    linarith
  have ha : Real.exp (-((2 : ℝ) ^ m / Real.log 4)) ≤ Real.exp (-(c * X)) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_right hcB1 h2m
    have e : (2 : ℝ) ^ m / Real.log 4 = 1 / Real.log 4 * 2 ^ m := by ring
    rw [e]; linarith
  have hb : Real.exp (-(c₁ * (2 : ℝ) ^ m)) ≤ Real.exp (-(c * X)) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_right hcB2 h2m
    linarith
  calc 3 * C₂ * Real.exp (-((2 : ℝ) ^ m / Real.log 4)) + C₁ * Real.exp (-(c₁ * (2 : ℝ) ^ m))
      ≤ 3 * C₂ * Real.exp (-(c * X)) + C₁ * Real.exp (-(c * X)) := by gcongr
    _ = (3 * C₂ + C₁) * Real.exp (-(c * X)) := by ring
    _ ≤ C * Real.exp (-(c * X)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- **DDDF Proposition 18, uniform in `ξ ∈ (0, ξs]` and in the white noise, from uniform Cor 17**
(ledger U6 `prop18_unif`, conditional form; template `dddf_prop18`): there is `p₀ > 0` such that
for every `p ∈ (0, p₀]` there are `C, c > 0`, chosen before the probability space and before
`ξ`, with `P(L^{(n)}_{3,1}(φ) ≥ e^s Λ_n(φ,p) ℓ_n(φ,p)) ≤ C e^{-c s²/log s}` for all `n` and
`s > 2`. Witnesses: the template's formulas with `D* = D(ξs)`, and Step 4 from
`p18_step4_unif`. -/
theorem prop18_unif_of_cor17 (ξs : ℝ) (hξs : 0 < ξs) (h17 : IfaceCor17U ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 2 < s →
          P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
              ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
            ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  obtain ⟨p₁, hp₁, h1'⟩ := p18_step1_unif ξs hξs
  obtain ⟨p₃, hp₃, h3'⟩ := p18_step3_unif_of_cor17 ξs hξs h17
  refine ⟨min (min (p₁ / 2) p₃) (1 / 4), by positivity, fun p hp0 hp => ?_⟩
  have hpp₁ : 2 * p ≤ p₁ := by have := (le_min_iff.1 (le_min_iff.1 hp).1).1; linarith
  have hpp₃ : p ≤ p₃ := (le_min_iff.1 (le_min_iff.1 hp).1).2
  have hp4 : p ≤ 1 / 4 := (le_min_iff.1 hp).2
  obtain ⟨C₁, c₁, hC₁, hc₁, hS1⟩ := h1' (2 * p) (by positivity) hpp₁
  obtain ⟨C₃, hC₃, hS3⟩ := h3' p hp0 hpp₃
  obtain ⟨C₂, hC₂, hS2⟩ := prop2_tail_R31_W.{0}
  obtain ⟨Cℓ, -, hell⟩ := p18_ell_lower_W.{0} hp0 (by linarith : p < 1)
  obtain ⟨C₄, c₄, hC₄, hc₄, hS4⟩ := p18_step4_unif.{0} ξs hξs hp0 (by linarith : p ≤ 1 / 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ξs * (1 + C₂) * (Real.log 4 + 1) + Real.log 2 + ξs * C₁ +
      |Real.log C₁| + 2 * ξs * Real.log 2 + C₃ := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (2 * D ^ 2 + 1) / Real.log 2 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hBdef]; positivity
  have hBl2 : B * Real.log 2 = 2 * D ^ 2 + 1 := by rw [hBdef]; field_simp
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = min (1 / Real.log 4) c₁ := ⟨_, rfl⟩
  have hc' : 0 < c' := by rw [hc'def]; exact lt_min (by positivity) hc₁
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min c₄ (c' / (2 * B)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min hc₄ (by positivity)
  have hcB : 2 * B * c ≤ c' := by
    have h := min_le_right c₄ (c' / (2 * B))
    rw [← hcdef, le_div_iff₀ (by positivity)] at h
    linarith
  refine ⟨C₄ + (3 * C₂ + C₁) + Real.exp (c * (2 * B) ^ 2 / Real.log 2), c, by positivity, hc,
    fun {Ω} _ {P} {W} hW ξ hξ n s hs => ?_⟩
  have hS1' := hS1 hW ξ hξ
  rw [show 2 * p / 2 = p by ring] at hS1'
  refine prop18_of_consts hW hξ.1 hp0 hp4 hC₁ hC₂ hC₃ hC₄ hS1' (hS2 hW) (hS3 hW ξ hξ)
    (fun n hn => lt_of_lt_of_le (Real.exp_pos _) (hell hW ξ hξ.1 n hn)) (hS4 hW ξ hξ) ?_
    hBl2.ge hc (by rw [hcdef]; exact min_le_left _ _)
    (hcB.trans (by rw [hc'def]; exact min_le_left _ _))
    (hcB.trans (by rw [hc'def]; exact min_le_right _ _)) le_rfl n s hs
  -- `D(ξ) ≤ D(ξs)`
  have h1 : ξ * (1 + C₂) * (Real.log 4 + 1) ≤ ξs * (1 + C₂) * (Real.log 4 + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hξ.2 (by positivity)) (by positivity)
  have h2 : ξ * C₁ ≤ ξs * C₁ := mul_le_mul_of_nonneg_right hξ.2 hC₁.le
  have h3 : 2 * ξ * Real.log 2 ≤ 2 * ξs * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hξ.2]) hl2.le
  rw [hDdef]
  linarith

/-- uniform Cor 17 implies the orchestrator's interface `IfaceProp18U ξs` (conditional form of
`ifaceProp18U`) -/
theorem ifaceProp18U_of_cor17 (ξs : ℝ) (hξs : 0 < ξs) (h17 : IfaceCor17U ξs) :
    IfaceProp18U ξs :=
  prop18_unif_of_cor17 ξs hξs h17

/-- uniform Cor 17 implies the orchestrator's interface `IfaceStep3U ξs` (conditional form of
`ifaceStep3U`) -/
theorem ifaceStep3U_of_cor17 (ξs : ℝ) (hξs : 0 < ξs) (h17 : IfaceCor17U ξs) :
    IfaceStep3U ξs :=
  p18_step3_unif_of_cor17 ξs hξs h17

end Uniform
end GaussianLQG
