/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawInterval
import InteractingSLE.Spec.ZhanGT4.DualSeedImageGirsanov

/-!
# The seeded stochastic logarithm from finite Taylor estimates

Packet PROVE-ZHAN-GT4-A22. The remaining input is exposed at the level
of deterministic partition estimates. The integral identification, the
Doléans identity and the general-filtration change of measure are proved
from that input. This is a conditional helper, not a source-facing theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}

/-- The negative seeded logarithm compensated by half the noise energy.
Its desired stochastic coefficient is `θ`, with the Girsanov sign convention. -/
def seedCompensatedLog {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (θ : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  -(d ω).normEll (min u (S ω)) - Girsanov.quadInt θ u ω / 2

/-- A precise finite-Taylor input for the seeded log field. The second
coefficient is bounded and adapted; the summed Taylor errors are bounded
by cubic increments and a bounded modulus tending to zero pathwise.
Only positive-time increments are tested; no entrance Taylor bound is assumed.
No stochastic integral, density identity or image law occurs in the input. -/
structure SeedLogTaylorControl {n : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (B θ : ℝ≥0 → Ω → ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : Prop where
  estimate : ∀ ε t : ℝ≥0, 0 < ε → ε ≤ t →
    ∃ (c₂ : ℝ≥0 → Ω → ℝ) (C₂ C K : ℝ) (R : ℕ → Ω → ℝ),
      StronglyAdapted 𝓕 c₂ ∧ 0 ≤ C₂ ∧ (∀ u ω, |c₂ u ω| ≤ C₂) ∧ 0 ≤ C ∧
        (∀ j, Measurable (fun ω =>
          seedDyadicDefect (seedCompensatedLog d S θ) θ c₂ B j t ω -
          seedDyadicDefect (seedCompensatedLog d S θ) θ c₂ B j ε ω)) ∧
        (∀ j, Measurable (R j)) ∧ (∀ j ω, 0 ≤ R j ω) ∧ (∀ j ω, R j ω ≤ K) ∧
        (∀ ω, Tendsto (fun j => R j ω) atTop (𝓝 0)) ∧
        ∀ j ω, |seedDyadicDefect (seedCompensatedLog d S θ) θ c₂ B j t ω -
          seedDyadicDefect (seedCompensatedLog d S θ) θ c₂ B j ε ω| ≤
            C * seedCubicError B j t ω + R j ω

/-- The stochastic logarithm is identified from the finite Taylor input.
The Brownian quadratic errors and the cubic and modulus limits are internal. -/
theorem seed_compensatedLog_ae_of_taylorControl {n : ℕ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hθ : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hr : Girsanov.IsRiemannRegular P θ)
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hT : SeedLogTaylorControl P 𝓕 B θ d S) {ε t : ℝ≥0} (hε : 0 < ε) (hεt : ε ≤ t) :
    (fun ω => seedCompensatedLog d S θ t ω - seedCompensatedLog d S θ ε ω) =ᵐ[P]
      fun ω => Girsanov.stochIntegral P 𝓕 B θ t ω - Girsanov.stochIntegral P 𝓕 B θ ε ω := by
  obtain ⟨c₂, C₂, C₃, K, R, h₂, hC₂, hb₂, hC₃, hm, hR, hR0, hRb, hRl, he⟩ := hT.estimate ε t hε hεt
  exact seed_stochIntegral_sub_eq_of_dyadicDefect
    (Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB) hθ hb hr h₂ hC₂ hb₂ hεt
    (tendstoInMeasure_seedTaylorError hB hm hR hC₃ t hR0 hRb hRl he)

/-- `SeedPositiveLogIto` follows from finite deterministic Taylor estimates.
This theorem does not assert that the actual Loewner fields satisfy those
estimates; that localization step remains separate. -/
theorem seedPositiveLogIto_of_taylorControl {n : ℕ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hθ : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hr : Girsanov.IsRiemannRegular P θ)
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hT : SeedLogTaylorControl P 𝓕 B θ d S) : SeedPositiveLogIto P 𝓕 B θ d S := by
  intro ε t hε hεt
  filter_upwards [seed_compensatedLog_ae_of_taylorControl hB hθ hb hr hT hε hεt] with ω hω
  dsimp [seedCompensatedLog] at hω
  linarith only [hω]

/-- The actual seeded density gives the full Brownian change of measure
once the finite Taylor estimates for its log field are supplied. -/
theorem seed_girsanov_of_taylorControl {n : ℕ} [IsProbabilityMeasure P]
    (hB : IsFilteredBrownianReal 𝓕 B P) {κ : ℝ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hpred : IsStronglyPredictable 𝓕 (seedNoise κ d S)) {C : ℝ}
    (hb : ∀ u ω, |seedNoise κ d S u ω| ≤ C)
    (hr : Girsanov.IsRiemannRegular P (seedNoise κ d S))
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω)))
    (hT : SeedLogTaylorControl P 𝓕 B (seedNoise κ d S) d S)
    {U : ℝ≥0} (hSU : ∀ ω, S ω < U) :
    IsFilteredBrownianReal 𝓕 (Girsanov.girsanovProcess B (seedNoise κ d S)) (seedMeasure P d S) ∧
      MathFin.IsEquivProbMeasure P (seedMeasure P d S) :=
  seed_girsanov_of_positiveIto hB hpred hb hr hc
    (seedPositiveLogIto_of_taylorControl hB hpred.isStronglyProgressive.stronglyAdapted hb hr hT) hSU

end InteractingSLE.ZhanGT4
