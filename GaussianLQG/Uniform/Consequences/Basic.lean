import GaussianLQG.Uniform.InterfacesCons
import LQGMetric.Papers.DDDF.S6TailsAB3
import LQGMetric.Papers.DDDF.S6P21Mom

/-!
# Consequences of the uniform DDDF core, helper lemmas: tails and moments (Route U, U10)

Phase B, packet PB-U10 (ledger packet B-7). Mathematical source: the uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U10 and the constant ledger
§`subsec:ledger-cons`. The lemmas here hold at one white noise and one `ξ`, with every constant a
parameter; the uniform statements are assembled in `GaussianLQG/Uniform/Consequences.lean`.

* `bounds_of_mem_shapeSet`, `lenObs_shape_bounds`: the shapes of ledger U7 lie in `[1,3]²`, so
  pathwise `L(R_{1,3}) ≤ L(R_{a,b}) ≤ L(R_{3,1})` (`lenObs_rectAB_mono`).
* `exp_shift_log_le`, `exp_shift_sq_le`: shifting the threshold of a tail by `σ = log B` costs a
  factor `1/4` in the rate once `s > 2σ + 4` (the ledger's "thresholds shifted by `log B`").
* `tails_core`: the two tails of `L_n(R)` relative to `λ_n`, from Cor 17 and Prop 18 at a level
  `p ≤ 1/2` and the quantile-ratio bound `Λ_n(p) ≤ B` (`S6AB.quantile_facts`:
  `ℓ_n(p) ≤ λ_n ≤ B ℓ_n(p)`, `Λ_n(p) ℓ_n(p) ≤ B λ_n`).
* `moments_of_tails`: positive and negative moments of order `q > 0` from the two tails, with the
  explicit constants of `T20B.lintegral_exp_le_of_tail_logsq` (templates `S6P28U.moment_of_tail`,
  `S6.invMoment_L11`; real exponent).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Cons

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-! ### The shapes -/

/-- the shapes of ledger U7 lie in `[1,3]²` -/
lemma bounds_of_mem_shapeSet {a b : ℝ} (h : (a, b) ∈ shapeSet) :
    1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 := by
  simp only [shapeSet, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

omit [MeasurableSpace Ω] in
/-- `L(R_{1,3}) ≤ L(R_{a,b}) ≤ L(R_{3,1})` for `a, b ∈ [1,3]` (`lenObs_rectAB_mono`, pathwise) -/
lemma lenObs_shape_bounds {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) {a b : ℝ}
    (ha : 1 ≤ a) (ha3 : a ≤ 3) (hb : 1 ≤ b) (hb3 : b ≤ 3) (ω : Ω) :
    lenObs ξ Y (rectAB 1 3) ω ≤ lenObs ξ Y (rectAB a b) ω ∧
      lenObs ξ Y (rectAB a b) ω ≤ lenObs ξ Y (rectAB 3 1) ω :=
  ⟨lenObs_rectAB_mono hYc zero_le_one ha (by linarith) hb3 ω,
    lenObs_rectAB_mono hYc (by linarith) ha3 zero_le_one hb ω⟩

/-! ### Shifted thresholds -/

/-- `c s²/4 ≤ c (s - σ)²` for `0 ≤ 2σ ≤ s` -/
lemma quarter_sq_le {c σ s : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hs : 2 * σ ≤ s) :
    c / 4 * s ^ 2 ≤ c * (s - σ) ^ 2 := by
  have h1 : 0 ≤ s / 2 - σ := by linarith
  have h2 : 0 ≤ 3 * s / 2 - σ := by linarith
  have h3 : s ^ 2 / 4 ≤ (s - σ) ^ 2 := by nlinarith [mul_nonneg h1 h2]
  calc c / 4 * s ^ 2 = c * (s ^ 2 / 4) := by ring
    _ ≤ c * (s - σ) ^ 2 := mul_le_mul_of_nonneg_left h3 hc

/-- shifting the threshold of an `e^{-cs²/log s}` tail by `σ ≥ 0`: for `s > 2σ + 4`,
`e^{-c(s-σ)²/log(s-σ)} ≤ e^{-(c/4)s²/log s}` -/
lemma exp_shift_log_le {c σ s : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hs : 2 * σ + 4 < s) :
    Real.exp (-c * (s - σ) ^ 2 / Real.log (s - σ)) ≤
      Real.exp (-(c / 4) * s ^ 2 / Real.log s) := by
  have hl1 : 0 < Real.log (s - σ) := Real.log_pos (by linarith)
  have hl2 : Real.log (s - σ) ≤ Real.log s := Real.log_le_log (by linarith) (by linarith)
  have hsq := quarter_sq_le (s := s) hc.le hσ (by linarith)
  refine Real.exp_le_exp.2 ?_
  rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff]
  calc c / 4 * s ^ 2 / Real.log s ≤ c / 4 * s ^ 2 / Real.log (s - σ) :=
        div_le_div_of_nonneg_left (by positivity) hl1 hl2
    _ ≤ c * (s - σ) ^ 2 / Real.log (s - σ) := div_le_div_of_nonneg_right hsq hl1.le

/-- shifting the threshold of an `e^{-cs²}` tail by `σ ≥ 0`: for `s ≥ 2σ`,
`e^{-c(s-σ)²} ≤ e^{-(c/4)s²}` -/
lemma exp_shift_sq_le {c σ s : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hs : 2 * σ ≤ s) :
    Real.exp (-c * (s - σ) ^ 2) ≤ Real.exp (-(c / 4) * s ^ 2) := by
  have hsq := quarter_sq_le hc.le hσ hs
  refine Real.exp_le_exp.2 ?_
  linarith

/-- a smaller rate gives a larger `e^{-cs²/log s}` bound (`s > 1`) -/
lemma exp_rate_log_mono {c c' s : ℝ} (hcc : c ≤ c') (hs : 1 < s) :
    Real.exp (-c' * s ^ 2 / Real.log s) ≤ Real.exp (-c * s ^ 2 / Real.log s) := by
  refine Real.exp_le_exp.2 ?_
  have hl : 0 < Real.log s := Real.log_pos hs
  rw [neg_mul, neg_div, neg_mul, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc (sq_nonneg s)) hl.le

/-- a smaller rate gives a larger `e^{-cs²}` bound -/
lemma exp_rate_sq_mono {c c' s : ℝ} (hcc : c ≤ c') :
    Real.exp (-c' * s ^ 2) ≤ Real.exp (-c * s ^ 2) := by
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_right hcc (sq_nonneg s)
  linarith

/-! ### Tails relative to `λ_n` at one noise -/

/-- **Core of U10, tails** (ledger §`subsec:ledger-cons`, row `tails_lambda_unif`), at one noise
and one `ξ`: if at a level `p ≤ 1/2` the quantile ratios are bounded, `Λ_k(p) ≤ B` with `B ≥ 1`,
and Cor 17 and Prop 18 hold at `p` with constants `(C₇, c₇)` and `(C₈, c₈)`, then for every shape
`R_{a,b}` with `a, b ∈ [1,3]` and every `s > 2 log B + 4`,
`P(e^s λ_n ≤ L_n(R_{a,b})) ≤ C₈ e^{-(c₈/4)s²/log s}` and
`P(L_n(R_{a,b}) ≤ e^{-s} λ_n) ≤ C₇ e^{-(c₇/4)s²}`. -/
lemma tails_core (hW : IsWhiteNoise P W) {p B C₇ c₇ C₈ c₈ : ℝ} (hp : 0 < p) (hph : p ≤ 1 / 2)
    (hB1 : 1 ≤ B) (hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) (hC₇ : 0 < C₇)
    (hc₇ : 0 < c₇) (hC₈ : 0 < C₈) (hc₈ : 0 < c₈)
    (t17 : ∀ (n : ℕ) (s : ℝ), 0 < s →
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
          Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)}
        ≤ ENNReal.ofReal (C₇ * Real.exp (-c₇ * s ^ 2)))
    (t18 : ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω}
        ≤ ENNReal.ofReal (C₈ * Real.exp (-c₈ * s ^ 2 / Real.log s)))
    (n : ℕ) {a b : ℝ} (ha : 1 ≤ a) (ha3 : a ≤ 3) (hb : 1 ≤ b) (hb3 : b ≤ 3) {s : ℝ}
    (hs : 2 * Real.log B + 4 < s) :
    P {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω} ≤
        ENNReal.ofReal (C₈ * Real.exp (-(c₈ / 4) * s ^ 2 / Real.log s)) ∧
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ Real.exp (-s) * lambdaN ξ W P n} ≤
        ENNReal.ofReal (C₇ * Real.exp (-(c₇ / 4) * s ^ 2)) := by
  obtain ⟨-, -, hlamB, hΛℓ⟩ := S6AB.quantile_facts hW hp hph hB1 hB n
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hσ0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hBσ : Real.exp (Real.log B) = B := Real.exp_log (by linarith)
  constructor
  · have hsub : {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω} ⊆
        {ω | Real.exp (s - Real.log B) * LambdaN ξ W P n (ENNReal.ofReal p) *
            ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      have h1 := (lenObs_shape_bounds (ξ := ξ) hφ.cont ha ha3 hb hb3 ω).2
      have h2 : Real.exp (s - Real.log B) * LambdaN ξ W P n (ENNReal.ofReal p) *
          ellN ξ W P n (ENNReal.ofReal p) ≤ Real.exp s * lambdaN ξ W P n := by
        calc Real.exp (s - Real.log B) * LambdaN ξ W P n (ENNReal.ofReal p) *
              ellN ξ W P n (ENNReal.ofReal p)
            = Real.exp (s - Real.log B) *
                (LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)) :=
              mul_assoc _ _ _
          _ ≤ Real.exp (s - Real.log B) * (B * lambdaN ξ W P n) :=
              mul_le_mul_of_nonneg_left hΛℓ (Real.exp_pos _).le
          _ = Real.exp s * lambdaN ξ W P n := by
              rw [Real.exp_sub, hBσ]; field_simp
      linarith
    refine (measure_mono hsub).trans ((t18 n (s - Real.log B) (by linarith)).trans
      (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_left (exp_shift_log_le hc₈ hσ0 hs) hC₈.le
  · have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ Real.exp (-s) * lambdaN ξ W P n} ⊆
        {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-(s - Real.log B)) * ellN ξ W P n (ENNReal.ofReal p)} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      have h1 := (lenObs_shape_bounds (ξ := ξ) hφ.cont ha ha3 hb hb3 ω).1
      have h2 : Real.exp (-s) * lambdaN ξ W P n ≤
          Real.exp (-(s - Real.log B)) * ellN ξ W P n (ENNReal.ofReal p) := by
        calc Real.exp (-s) * lambdaN ξ W P n
            ≤ Real.exp (-s) * (B * ellN ξ W P n (ENNReal.ofReal p)) :=
              mul_le_mul_of_nonneg_left hlamB (Real.exp_pos _).le
          _ = Real.exp (-(s - Real.log B)) * ellN ξ W P n (ENNReal.ofReal p) := by
              rw [show -(s - Real.log B) = -s + Real.log B by ring, Real.exp_add, hBσ]; ring
      linarith
    refine (measure_mono hsub).trans ((t17 n (s - Real.log B) (by linarith)).trans
      (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_left (exp_shift_sq_le hc₇ hσ0 (by linarith)) hC₇.le

/-! ### Moments from the tails -/

/-- **Moments from two-sided tails** (ledger row `moments_lambda_unif`; templates
`S6P28U.moment_of_tail` and `S6.invMoment_L11`, here for a real exponent `q > 0` through
`T20B.lintegral_exp_le_of_tail_logsq`): if `L > 0`, `m > 0`,
`P(e^s m ≤ L) ≤ C e^{-cs²/log s}` and `P(L ≤ e^{-s} m) ≤ C e^{-cs²}` for `s > 2`, then
`E (L/m)^q ≤ e^{q x₀} + 1` and `E (m/L)^q ≤ e^{q x₀'} + 1` with `x₀ = tailX0 q 1 C c`,
`x₀' = tailX0 q 1 C (c/2)`. -/
lemma moments_of_tails [IsProbabilityMeasure P] {L : Ω → ℝ} (hLm : Measurable L)
    (hL0 : ∀ ω, 0 < L ω) {m C c q : ℝ} (hm : 0 < m) (hC : 0 < C) (hc : 0 < c) (hq : 0 < q)
    (hr : ∀ s, 2 < s → P {ω | Real.exp s * m ≤ L ω} ≤
      ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)))
    (hl : ∀ s, 2 < s → P {ω | L ω ≤ Real.exp (-s) * m} ≤
      ENNReal.ofReal (C * Real.exp (-c * s ^ 2))) :
    ∫⁻ ω, ENNReal.ofReal ((L ω / m) ^ q) ∂P ≤
        ENNReal.ofReal (Real.exp (q * T20B.tailX0 q 1 C c) + 1) ∧
      ∫⁻ ω, ENNReal.ofReal ((m / L ω) ^ q) ∂P ≤
        ENNReal.ofReal (Real.exp (q * T20B.tailX0 q 1 C (c / 2)) + 1) := by
  constructor
  · set X : Ω → ℝ := fun ω => max 0 (Real.log (L ω) - Real.log m) with hXdef
    have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_left _ _
    have hXm : Measurable X :=
      measurable_const.max ((Real.measurable_log.comp hLm).sub measurable_const)
    have hpt : ∀ ω, ENNReal.ofReal ((L ω / m) ^ q) ≤ ENNReal.ofReal (Real.exp (q * X ω)) := by
      intro ω
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_def_of_pos (div_pos (hL0 ω) hm), Real.log_div (hL0 ω).ne' hm.ne']
      refine Real.exp_le_exp.2 ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hq.le
    have htail : ∀ t, 2 < t → P {ω | t ≤ X ω} ≤
        ENNReal.ofReal (1 * C * Real.exp (-c * t ^ 2 / Real.log t)) := by
      intro t ht
      rw [one_mul]
      refine (measure_mono fun ω hω => ?_).trans (hr t ht)
      simp only [mem_ofPred_eq] at hω ⊢
      have h2 : t ≤ Real.log (L ω) - Real.log m := by
        rcases le_total 0 (Real.log (L ω) - Real.log m) with h | h
        · simpa only [hXdef, max_eq_right h] using hω
        · simp only [hXdef, max_eq_left h] at hω; linarith
      have h3 := Real.exp_le_exp.2 h2
      rw [Real.exp_sub, Real.exp_log (hL0 ω), Real.exp_log hm, le_div_iff₀ hm] at h3
      exact h3
    exact (lintegral_mono hpt).trans
      (T20B.lintegral_exp_le_of_tail_logsq hX0 hXm.aemeasurable hq zero_le_one hC hc htail)
  · set X : Ω → ℝ := fun ω => max 0 (Real.log m - Real.log (L ω)) with hXdef
    have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_left _ _
    have hXm : Measurable X :=
      measurable_const.max (measurable_const.sub (Real.measurable_log.comp hLm))
    have hpt : ∀ ω, ENNReal.ofReal ((m / L ω) ^ q) ≤ ENNReal.ofReal (Real.exp (q * X ω)) := by
      intro ω
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_def_of_pos (div_pos hm (hL0 ω)), Real.log_div hm.ne' (hL0 ω).ne']
      refine Real.exp_le_exp.2 ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hq.le
    have htail : ∀ t, 2 < t → P {ω | t ≤ X ω} ≤
        ENNReal.ofReal (1 * C * Real.exp (-(c / 2) * t ^ 2 / Real.log t)) := by
      intro t ht
      rw [one_mul]
      refine (measure_mono fun ω hω => ?_).trans ((hl t ht).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (S6.gauss_le_logsq hc ht) hC.le)))
      simp only [mem_ofPred_eq] at hω ⊢
      have h2 : t ≤ Real.log m - Real.log (L ω) := by
        rcases le_total 0 (Real.log m - Real.log (L ω)) with h | h
        · simpa only [hXdef, max_eq_right h] using hω
        · simp only [hXdef, max_eq_left h] at hω; linarith
      have h3 : Real.log (L ω) ≤ -t + Real.log m := by linarith
      have h4 := Real.exp_le_exp.2 h3
      rwa [Real.exp_log (hL0 ω), Real.exp_add, Real.exp_log hm] at h4
    exact (lintegral_mono hpt).trans
      (T20B.lintegral_exp_le_of_tail_logsq hX0 hXm.aemeasurable hq zero_le_one hC
        (by positivity) htail)

end Cons
end Uniform
end GaussianLQG
