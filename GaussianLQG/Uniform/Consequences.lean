import GaussianLQG.Uniform.Consequences.Scale
import GaussianLQG.Uniform.LowerTail

/-!
# Uniform consequences of the DDDF core: tails, moments and scales of `λ_n` (U10–U11)

Phase B, packet PB-U10 (ledger packet B-7). Mathematical source: the uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statements U10 (`tails_lambda_unif`,
`moments_lambda_unif`, the source's (A.10)) and U11 (`scale_unif`), constant ledger
§`subsec:ledger-cons`. Every statement is in the ledger's U-form: the constants come before the
probability space `(Ω, P, W)` and before `ξ ∈ (0, 1/8]`.

Inputs: uniform Cor 17 is a theorem (`ifaceCor17U`, `GaussianLQG/Uniform/LowerTail.lean`);
uniform Prop 18, its a-priori scale bound (Step 3) and uniform Theorem 20 enter as the
orchestrator's interface hypotheses `IfaceProp18U (1/8)`, `IfaceStep3U (1/8)` and `IfaceThm20U`
(`GaussianLQG/Uniform/Interfaces.lean`), which other packets prove. Nothing else is assumed.

Proof outline (ledger U10–U11). Fix a level
`p_* = min(p₀(Cor 17), p₀(Prop 18), [p₀(Step 3),] p₀(Thm 20), 1/4)` and `B = max(B(p_*), 1)`
from Theorem 20. Since `p_* ≤ 1/2`, `ℓ_n(p_*) ≤ λ_n ≤ ℓ̄_n(p_*) ≤ B ℓ_n(p_*)`
(`T20B.ellN_le_lambdaN`, `T20B.lambdaN_le_ellBarN`, `S6AB.quantile_facts`).

* `tails_lambda_unif`: pathwise `L(R_{1,3}) ≤ L(R_{a,b}) ≤ L(R_{3,1})` for the shapes, Prop 18
  and Cor 17 at `p_*` with thresholds shifted by `log B`, then the small `s` are absorbed into
  the constant (`S6AB.absorb_log`, `S6AB.absorb_sq`).
* `moments_lambda_unif`: integration of the two tails (`Cons.moments_of_tails`).
* `scale_unif`: (a) P18 Step 3 with `Λ ≤ B`; (b) DDDF (6.98) at `r = 1` (upper half) and (a) at
  `k = 1` (lower half); (c) comparison with the infimum of the field (`n ≥ 1`) and `λ_0 ≥ 1`;
  (d) Markov on a straight crossing.

The corollaries `ifaceTailsLambdaU`, `ifaceMomentsLambdaU`, `ifaceScaleU` give the interfaces of
`GaussianLQG/Uniform/InterfacesCons.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail Cons

/-- **U10, tails** (ledger `tails_lambda_unif`; the source's (A.10)): uniformly in the white
noise, in `ξ ∈ (0, 1/8]`, in `n` and in the shapes `R_{1,3}, R_{1,1}, R_{2,1}, R_{3,1}`, for
`s > 2`, `P(e^s λ_n ≤ L_n(R)) ≤ C e^{-cs²/log s}` and `P(L_n(R) ≤ e^{-s} λ_n) ≤ C e^{-cs²}`. -/
theorem tails_lambda_unif (h18 : IfaceProp18U (1 / 8)) (h20 : IfaceThm20U) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
        IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ (n : ℕ) (a b : ℝ), (a, b) ∈ shapeSet →
          ∀ s : ℝ, 2 < s →
            P {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω}
                ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) ∧
              P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ Real.exp (-s) * lambdaN ξ W P n}
                ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨p₁, hp₁, H17⟩ := ifaceCor17U (1 / 8) (by norm_num)
  obtain ⟨p₂, hp₂, H18⟩ := h18
  obtain ⟨p₃, hp₃, H20⟩ := h20
  set p : ℝ := min (min p₁ p₂) (min p₃ (1 / 4)) with hp_def
  have hp : 0 < p := lt_min (lt_min hp₁ hp₂) (lt_min hp₃ (by norm_num))
  have hp1 : p ≤ p₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hp2 : p ≤ p₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hp3 : p ≤ p₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨C₇, c₇, hC₇, hc₇, T17⟩ := H17 p hp hp1
  obtain ⟨C₈, c₈, hC₈, hc₈, T18⟩ := H18 p hp hp2
  obtain ⟨B₀, T20⟩ := H20 p hp hp3
  set B : ℝ := max B₀ 1 with hB_def
  have hB1 : 1 ≤ B := le_max_right _ _
  set c : ℝ := min c₇ c₈ / 4 with hc_def
  have hc : 0 < c := div_pos (lt_min hc₇ hc₈) (by norm_num)
  have hc7 : c ≤ c₇ / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hc8 : c ≤ c₈ / 4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  set S₀ : ℝ := 2 * Real.log B + 4 with hS₀
  have hS₀4 : 4 ≤ S₀ := by have := Real.log_nonneg hB1; linarith
  refine ⟨max (max C₈ (Real.exp (c * max S₀ 2 ^ 2 / Real.log 2)))
      (max C₇ (Real.exp (c * max S₀ 2 ^ 2))), c,
    lt_max_of_lt_left (lt_max_of_lt_left hC₈), hc, ?_⟩
  intro Ω _ P W hW ξ hξ n a b hab s hs
  have hP := hW.isProbabilityMeasure
  obtain ⟨ha, ha3, hb, hb3⟩ := bounds_of_mem_shapeSet hab
  have hB : ∀ k, LambdaN ξ W P k (ENNReal.ofReal p) ≤ B :=
    fun k => (T20 hW ξ hξ k).trans (le_max_left _ _)
  have core := fun (s : ℝ) (hs : S₀ < s) => tails_core hW hp hph hB1 hB hC₇ hc₇ hC₈ hc₈
    (T17 hW ξ hξ) (T18 hW ξ hξ) n ha ha3 hb hb3 hs
  constructor
  · have hr := S6AB.absorb_log (P := P)
      (E := fun s => {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω})
      (C := C₈) (S₀ := S₀) hc (fun s hs' => (core s hs').1.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (exp_rate_log_mono hc8 (by linarith)) hC₈.le))) s hs
    exact hr.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  · have hl := S6AB.absorb_sq (P := P)
      (E := fun s =>
        {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ Real.exp (-s) * lambdaN ξ W P n})
      (C := C₇) (S₀ := S₀) hc (fun s hs' => (core s hs').2.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (exp_rate_sq_mono hc7) hC₇.le))) s hs
    exact hl.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le))

/-- **U10, moments** (ledger `moments_lambda_unif`; the source's (A.10)): for every `q ≥ 1`
there is `C` such that, uniformly in the white noise, in `ξ ∈ (0, 1/8]`, in `n` and in the
shapes, `E (L_n(R)/λ_n)^q ≤ C` and `E (λ_n/L_n(R))^q ≤ C`. -/
theorem moments_lambda_unif (h18 : IfaceProp18U (1 / 8)) (h20 : IfaceThm20U) (q : ℝ)
    (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ (n : ℕ) (a b : ℝ), (a, b) ∈ shapeSet →
        (∫⁻ ω, ENNReal.ofReal ((lenObs ξ (phiMN W P 0 n) (rectAB a b) ω / lambdaN ξ W P n) ^ q)
            ∂P) ≤ ENNReal.ofReal C ∧
          (∫⁻ ω, ENNReal.ofReal ((lambdaN ξ W P n / lenObs ξ (phiMN W P 0 n) (rectAB a b) ω) ^ q)
            ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, c, hC, hc, ht⟩ := tails_lambda_unif h18 h20
  have hq0 : 0 < q := by linarith
  refine ⟨max (Real.exp (q * T20B.tailX0 q 1 C c) + 1)
    (Real.exp (q * T20B.tailX0 q 1 C (c / 2)) + 1), ?_⟩
  intro Ω _ P W hW ξ hξ n a b hab
  have hP := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  obtain ⟨ha, -, hb, -⟩ := bounds_of_mem_shapeSet hab
  have hL0 : ∀ ω, 0 < lenObs ξ (phiMN W P 0 n) (rectAB a b) ω := fun ω =>
    lenObs_pos hφ.cont _ (by simpa [rectAB] using (by linarith : (0 : ℝ) ≤ a))
      (by simpa [rectAB] using (by linarith : (0 : ℝ) ≤ b))
      (by simpa [MarkedRect.crossWidth, rectAB] using (by linarith : (0 : ℝ) < a)) ω
  obtain ⟨h1, h2⟩ := moments_of_tails (measurable_lenObs hφ.cont hφ.meas _) hL0
    (lambdaN_pos hW n) hC hc hq0 (fun s hs => (ht hW ξ hξ n a b hab s hs).1)
    (fun s hs => (ht hW ξ hξ n a b hab s hs).2)
  exact ⟨h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
    h2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩

/-- **U11, scale relations** (ledger `scale_unif`): one `C > 0` such that, uniformly in the
white noise, in `ξ ∈ (0, 1/8]` and in `n`,
(a) `λ_{n-k} ≤ C 2^{2ξk} e^{C√k} λ_n` for `k ≤ n`;
(b) `e^{-C} λ_n ≤ λ_{n+1} ≤ e^C λ_n`;
(c) `λ_n ≥ e^{-ξ(C + 2(n+1) log 2)}`;
(d) `λ_n ≤ 3 e^{ξ² n log 2/2}`. -/
theorem scale_unif (h18 : IfaceProp18U (1 / 8)) (h3 : IfaceStep3U (1 / 8))
    (h20 : IfaceThm20U) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
        IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ n : ℕ,
          (∀ k : ℕ, k ≤ n → lambdaN ξ W P (n - k) ≤
              C * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C * Real.sqrt k) * lambdaN ξ W P n) ∧
          Real.exp (-C) * lambdaN ξ W P n ≤ lambdaN ξ W P (n + 1) ∧
          lambdaN ξ W P (n + 1) ≤ Real.exp C * lambdaN ξ W P n ∧
          Real.exp (-(ξ * (C + 2 * (n + 1) * Real.log 2))) ≤ lambdaN ξ W P n ∧
          lambdaN ξ W P n ≤ 3 * Real.exp (ξ ^ 2 * n * Real.log 2 / 2) := by
  obtain ⟨p₂, hp₂, H18⟩ := h18
  obtain ⟨p₄, hp₄, H3⟩ := h3
  obtain ⟨p₃, hp₃, H20⟩ := h20
  set p : ℝ := min (min p₂ p₄) (min p₃ (1 / 4)) with hp_def
  have hp : 0 < p := lt_min (lt_min hp₂ hp₄) (lt_min hp₃ (by norm_num))
  have hp2 : p ≤ p₂ := (min_le_left _ _).trans (min_le_left _ _)
  have hp4 : p ≤ p₄ := (min_le_left _ _).trans (min_le_right _ _)
  have hp3 : p ≤ p₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨C₈, c₈, hC₈, hc₈, T18⟩ := H18 p hp hp2
  obtain ⟨C₃, hC₃, T3⟩ := H3 p hp hp4
  obtain ⟨B₀, T20⟩ := H20 p hp hp3
  set B : ℝ := max B₀ 1 with hB_def
  have hB1 : 1 ≤ B := le_max_right _ _
  -- the threshold of (6.98): `C₈ e^{-c₈ s²/log s} ≤ 1/8` (as in `s6_eq6_98_of_Lambda`)
  set s : ℝ := max 3 (Real.log (2 * C₈ / (1 / 4)) / c₈) with hs_def
  have hs3 : 3 ≤ s := le_max_left _ _
  have hs8 : Real.log (2 * C₈ / (1 / 4)) / c₈ ≤ s := le_max_right _ _
  have e8 : C₈ * Real.exp (-c₈ * s ^ 2 / Real.log s) ≤ 1 / 8 := by
    have h := T20B.mul_exp_neg_le_half hC₈ hc₈ (by norm_num : (0 : ℝ) < 1 / 4) hs8
    have hl : 0 < Real.log s := Real.log_pos (by linarith)
    have hls : Real.log s ≤ s := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hq : s ≤ s ^ 2 / Real.log s := by
      rw [le_div_iff₀ hl]
      nlinarith
    have h' : C₈ * Real.exp (-c₈ * s ^ 2 / Real.log s) ≤ C₈ * Real.exp (-(c₈ * s)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₈.le
      rw [neg_mul, neg_div, neg_le_neg_iff, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hq hc₈.le
    linarith
  -- the sup level of `φ_{0,1}` (`prob_sup_phiMN01_le`)
  set M₁ : ℝ := ferniqueCF * Real.sqrt 6 + (2 * (((1 : ℕ) : ℝ) + 1) * Real.log 2 + 2)
    with hM₁_def
  have hCF : 0 ≤ ferniqueCF * Real.sqrt 6 := by have := ferniqueCF_pos; positivity
  have hM₁ : 0 ≤ M₁ := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    rw [hM₁_def]; positivity
  set C : ℝ := B + C₃ + M₁ + s + ferniqueCF * Real.sqrt 6 + 1 with hC_def
  have hCB : B ≤ C := by linarith
  have hC3 : C₃ ≤ C := by linarith
  refine ⟨C, by linarith, ?_⟩
  intro Ω _ P W hW ξ hξ n
  have hP := hW.isProbabilityMeasure
  have hξ0 : 0 < ξ := hξ.1
  have hξ8 : ξ ≤ 1 / 8 := hξ.2
  have hB : ∀ k, LambdaN ξ W P k (ENNReal.ofReal p) ≤ B :=
    fun k => (T20 hW ξ hξ k).trans (le_max_left _ _)
  have hT3 := T3 hW ξ hξ
  have hlam : ∀ k, 0 < lambdaN ξ W P k := fun k => lambdaN_pos hW k
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, lambdaN_le_three_exp hW ξ n⟩
  · -- (a)
    refine (lambdaN_sub_le hW hp hph hB1 hB hT3 hk).trans ?_
    have hA : 0 < (2 : ℝ) ^ (2 * ξ * k) := Real.rpow_pos_of_pos two_pos _
    have hE : Real.exp (C₃ * Real.sqrt k) ≤ Real.exp (C * Real.sqrt k) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC3 (Real.sqrt_nonneg _))
    have h1 : B * (2 : ℝ) ^ (2 * ξ * k) ≤ C * (2 : ℝ) ^ (2 * ξ * k) :=
      mul_le_mul_of_nonneg_right hCB hA.le
    have h2 : B * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C₃ * Real.sqrt k) ≤
        C * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C * Real.sqrt k) :=
      mul_le_mul h1 hE (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_right h2 (hlam n).le
  · -- (b), lower half: (a) at `k = 1`
    refine le_trans ?_ (exp_neg_mul_lambdaN_le_succ hW hp hph hB1 hB hT3 (by linarith) n)
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hlam n).le
    linarith
  · -- (b), upper half: (6.98) at `r = 1`
    have h18' : ∀ k : ℕ, P {ω | Real.exp s * LambdaN ξ W P k (ENNReal.ofReal p) *
        ellN ξ W P k (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 k) (rectAB 3 1) ω} ≤
          ENNReal.ofReal (1 / 8) :=
      fun k => (T18 hW ξ hξ k s (by linarith)).trans (ENNReal.ofReal_le_ofReal e8)
    refine (lambdaN_succ_le hW hp hph hB1 hB h18' (prob_sup_phiMN01_le hW) n).trans ?_
    have h1 : Real.exp (|ξ| * M₁) ≤ Real.exp M₁ := by
      refine Real.exp_le_exp.2 ?_
      rw [abs_of_pos hξ0]
      have := mul_le_mul_of_nonneg_right (show ξ ≤ 1 by linarith) hM₁
      linarith
    have h2 : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    have hl0 := (hlam n).le
    calc Real.exp (|ξ| * M₁) * (2⁻¹ * (Real.exp s * B * lambdaN ξ W P n))
        ≤ Real.exp M₁ * (1 * (Real.exp s * Real.exp B * lambdaN ξ W P n)) := by
          refine mul_le_mul h1 ?_ (by positivity) (Real.exp_pos _).le
          refine mul_le_mul (by norm_num) ?_ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hl0
      _ = Real.exp (M₁ + s + B) * lambdaN ξ W P n := by
          rw [Real.exp_add (M₁ + s) B, Real.exp_add M₁ s]; ring
      _ ≤ Real.exp C * lambdaN ξ W P n :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hl0
  · -- (c)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine le_trans ?_ (one_le_lambdaN_zero hW)
      rw [Real.exp_le_one_iff, neg_nonpos]
      have hl2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      have h0 : 0 ≤ C + 2 * (((0 : ℕ) : ℝ) + 1) * Real.log 2 := by
        rw [Nat.cast_zero, zero_add]; linarith
      exact mul_nonneg hξ0.le h0
    · refine le_trans ?_ (lambdaN_ge_inf_field hW hξ0.le hn)
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hξ0.le))
      linarith

/-! ### The interfaces of `InterfacesCons.lean` -/

/-- `tails_lambda_unif` gives the interface `IfaceTailsLambdaU`. -/
theorem ifaceTailsLambdaU (h18 : IfaceProp18U (1 / 8)) (h20 : IfaceThm20U) :
    IfaceTailsLambdaU :=
  tails_lambda_unif h18 h20

/-- `moments_lambda_unif` gives the interface `IfaceMomentsLambdaU`. -/
theorem ifaceMomentsLambdaU (h18 : IfaceProp18U (1 / 8)) (h20 : IfaceThm20U) :
    IfaceMomentsLambdaU :=
  fun q hq => moments_lambda_unif h18 h20 q hq

/-- `scale_unif` gives the interface `IfaceScaleU`. -/
theorem ifaceScaleU (h18 : IfaceProp18U (1 / 8)) (h3 : IfaceStep3U (1 / 8))
    (h20 : IfaceThm20U) : IfaceScaleU :=
  scale_unif h18 h3 h20

end Uniform
end GaussianLQG
