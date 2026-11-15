/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Meas

/-!
# Finite laws of the explicit seeded height field

Packet PROVE-ZHAN-GT4-A22. The source density martingales give the
finite column laws of one explicit two-time formula. Both axes and the
D11 identification are checked directly. The normalized opposite-view
field remains the exact named input to the two-view coupling assembly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω₁ Ω₂ ι : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} [Fintype ι]

/-- With the identity-chart zero-height normalization, the concrete
terminal finite density is literally the D11 patch of the same field. -/
theorem seedHeightPatch_eq_D11 {n : ℕ} (d : ℝ → Ω₁ × Ω₂ → SeedData n)
    {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0} {Tm : ℝ}
    (h0 : ∀ ω s, (d 0 ω).normEll s = (d 0 ω).normEll 0)
    {U : ℝ≥0} (ω : Ω₁ × Ω₂) (hU : ∀ i, S₁ i ω.1 ≤ U) :
    seedFinitePatch (seedHeightField d) S₁ S₂ Tm ω =
      patch (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (seedHeightField d ω) U Tm :=
  seedFinitePatch_eq_D11 (seedHeightField_pos d) (seedHeightField_zero_right h0)
    (seedHeightField_zero_left d) ω hU

/-- Actual source martingales at the finitely many frozen heights give
column martingales of the concrete two-time density. -/
theorem seedHeightField_columns {n : ℕ} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} (d : ℝ → Ω₁ × Ω₂ → SeedData n)
    {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0} {Tm : ℝ}
    (hS : ∀ i, IsStoppingTime 𝓕₁ fun ω => (S₁ i ω : WithTop ℝ≥0)) (i₀ : ι)
    (hM : ∀ ω₂ i, Martingale
      (seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i)) 𝓕₁ P₁)
    (hc : ∀ ω₂ i ω₁, Continuous
      (seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i) · ω₁))
    (hb : ∀ ω₂ i, ∃ K : ℝ, ∀ u ω₁,
      Real.exp (-K) ≤ seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i) u ω₁ ∧
      seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i) u ω₁ ≤ Real.exp K) :
    ∀ ω₂, Martingale (colProd (fun ω₁ => seedHeightField d (ω₁, ω₂)) S₁
      (fun i => (S₂ i ω₂ : ℝ)) Tm) 𝓕₁ P₁ := by
  intro ω₂
  exact (seed_height_column_law (fun t ω₁ => d t (ω₁, ω₂)) hS (fun i => (S₂ i ω₂).coe_nonneg)
    i₀ (hM ω₂) (hc ω₂) (hb ω₂)).1

/-- Concrete seeded finite-law assembly. The input is the actual
normalized t-view of this specific finite patch; neither an arbitrary
field nor finite-column compatibility nor either normalization integral
is an input. The resulting dual hypothesis supplies the landed coupling API. -/
theorem seedDualHyp_seedHeightData {n : ℕ} {κ : ℝ} {rr : Fin n → ℝ}
    {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₁ : Filtration ℝ≥0 m₁} (d : ℝ → Ω₁ × Ω₂ → SeedData n)
    {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0} {Tm : ℝ} {a₂ : Ω₂ → ℝ≥0∞}
    (hS : ∀ i, IsStoppingTime 𝓕₁ fun ω => (S₁ i ω : WithTop ℝ≥0)) (i₀ : ι)
    (hM : ∀ ω₂ i, Martingale
      (seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i)) 𝓕₁ P₁)
    (hc : ∀ ω₂ i ω₁, Continuous
      (seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i) · ω₁))
    (hb : ∀ ω₂ i, ∃ K : ℝ, ∀ u ω₁,
      Real.exp (-K) ≤ seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i) u ω₁ ∧
      seedDensityProcess (fun ω₁ => d (min (S₂ i ω₂ : ℝ) Tm) (ω₁, ω₂)) (S₁ i) u ω₁ ≤ Real.exp K)
    {U : ℝ≥0} (hU : ∀ i ω, S₁ i ω ≤ U)
    (hm : Measurable (fun ω => ENNReal.ofReal (seedFinitePatch (seedHeightField d) S₁ S₂ Tm ω)))
    (ha : Measurable a₂) {𝓕₂ : Filtration ℝ≥0 m₂} {B₂ D₂ : ℝ≥0 → Ω₂ → ℝ}
    {V₂ : Ω₂ → ℝ → ℝ} {T₂ : Ω₂ → ℝ≥0}
    (htview : SeedNormalizedTView κ rr 𝓕₂ B₂ D₂ V₂ T₂
      (fun ω => ENNReal.ofReal (seedFinitePatch (seedHeightField d) S₁ S₂ Tm ω)) a₂)
    (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hB₂c : ∀ ω, Continuous (B₂ · ω))
    (hT₂ : IsStoppingTime 𝓕₂ fun ω => (T₂ ω : WithTop ℝ≥0))
    {U₂ : ℝ≥0} (hT₂U : ∀ ω, T₂ ω ≤ U₂) :
    SeedDualHyp P₁ P₂ (fun ω => ENNReal.ofReal (seedFinitePatch (seedHeightField d) S₁ S₂ Tm ω)) a₂ :=
  seedDualHyp_seedFiniteColumns (seedHeightField_pos d)
    (seedHeightField_columns d hS i₀ hM hc hb) hU hm ha htview hB₂ hB₂c hT₂ hT₂U

end InteractingSLE.ZhanGT4
