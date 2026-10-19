import LQGMetric.Papers.DDDF.P18S1Conv

/-!
# Uniform-in-`ξ` predicates for DDDF Proposition 18 (Route U, item U6)

Phase B, packet B-3 (worker PB-U6). Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`,
U0 (table of uniform predicates) and U6. The fixed-`ξ` predicates `P18Step1Psi`, `P18Step1`,
`P18Step3` of `LQGMetric/Papers/DDDF/` (`P18S1Conv.lean`, `P18Comb.lean`; DDDF20 Prop 18, Steps 1
and 3) put their existential constants after `(ξ, P, W)`. Their uniform copies move the
existential block in front of the probability space and of `∀ ξ ∈ (0, ξs]` (ledger §2, U-form):

* `P18Step1PsiU ξs`: Step 1 for `ψ` (percolation; display after DDDF l. 905);
* `P18Step1U ξs`: Step 1 for `φ` (display after DDDF l. 906);
* `P18Step3U ξs`: the a-priori scale bound of Step 3 (DDDF l. 921); its body is that of the
  orchestrator's interface `IfaceStep3U ξs` (`GaussianLQG/Uniform/Interfaces.lean`).

As in the interfaces, the white noises range over probability spaces `Ω : Type` (every noise of
Route U lives in `Type`, ledger §OP-3, "Universe"). The bridges `….p18Step1Psi`, `….p18Step1`,
`….p18Step3` recover the fixed-`ξ` predicates at every `ξ ∈ (0, ξs]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **DDDF Prop 18, Step 1 for `ψ`, uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U0,
U6; template `P18Step1Psi`, `LQGMetric/Papers/DDDF/P18S1Conv.lean`):
`P(L^{(n)}_{3k,k}(ψ) ≥ C k² ℓ̄_n(ψ,p)) ≤ C e^{-ck}`, with `p₀` and, for each `p ≤ p₀`, `C, c`
chosen before the probability space and before `ξ`. -/
def P18Step1PsiU (ξs : ℝ) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n k : ℕ), 1 ≤ k →
        P {ω | C * k ^ 2 * ellBarQ ξ P (psiMN psiQ₀ W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
            lenObs ξ (psiMN psiQ₀ W P 0 n) (rectAB (3 * k) k) ω} ≤
          ENNReal.ofReal (C * Real.exp (-(c * k)))

/-- **DDDF Prop 18, Step 1, uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U0, U6;
template `P18Step1`, `LQGMetric/Papers/DDDF/P18Comb.lean`):
`P(L^{(n)}_{3k,k}(φ) ≥ e^{ξC√k} C k² ℓ̄_n(φ,p/2)) ≤ C e^{-ck}`. -/
def P18Step1U (ξs : ℝ) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n k : ℕ), 1 ≤ k →
        P {ω | Real.exp (ξ * C * √k) * C * k ^ 2 * ellBarN ξ W P n (ENNReal.ofReal (p / 2)) ≤
            lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ≤
          ENNReal.ofReal (C * Real.exp (-(c * k)))

/-- **DDDF Prop 18, Step 3 (the a-priori scale bound), uniform in `ξ ∈ (0, ξs]` and in the white
noise** (ledger U0, U6, `P18Step3U ξs`; template `P18Step3`, `LQGMetric/Papers/DDDF/P18Comb.lean`):
`2^{-2ξk} ℓ_{n-k}(φ,p) e^{-C√k} ≤ ℓ_n(φ,p)` for `k ≤ n`. -/
def P18Step3U (ξs : ℝ) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ n k : ℕ, k ≤ n →
        (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) * Real.exp (-(C * √k))
          ≤ ellN ξ W P n (ENNReal.ofReal p)

section Bridges

variable {ξs : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the uniform predicate gives DDDF's Step 1 for `ψ` at every `ξ ∈ (0, ξs]` -/
theorem P18Step1PsiU.p18Step1Psi (h : P18Step1PsiU ξs) (hW : IsWhiteNoise P W) {ξ : ℝ}
    (hξ : ξ ∈ Ioc (0 : ℝ) ξs) : P18Step1Psi ξ W P := by
  obtain ⟨p₀, hp₀, h⟩ := h
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := h p hp hpp
  exact ⟨C, c, hC, hc, h hW ξ hξ⟩

/-- the uniform predicate gives DDDF's Step 1 for `φ` at every `ξ ∈ (0, ξs]` -/
theorem P18Step1U.p18Step1 (h : P18Step1U ξs) (hW : IsWhiteNoise P W) {ξ : ℝ}
    (hξ : ξ ∈ Ioc (0 : ℝ) ξs) : P18Step1 ξ W P := by
  obtain ⟨p₀, hp₀, h⟩ := h
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C, c, hC, hc, h⟩ := h p hp hpp
  exact ⟨C, c, hC, hc, h hW ξ hξ⟩

/-- the uniform predicate gives DDDF's Step 3 at every `ξ ∈ (0, ξs]` -/
theorem P18Step3U.p18Step3 (h : P18Step3U ξs) (hW : IsWhiteNoise P W) {ξ : ℝ}
    (hξ : ξ ∈ Ioc (0 : ℝ) ξs) : P18Step3 ξ W P := by
  obtain ⟨p₀, hp₀, h⟩ := h
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C, hC, h⟩ := h p hp hpp
  exact ⟨C, hC, h hW ξ hξ⟩

end Bridges

end Uniform
end GaussianLQG
