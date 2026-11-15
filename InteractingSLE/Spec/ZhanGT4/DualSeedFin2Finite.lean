/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Columns
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalTView
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Finite seeded density laws and their capped prefixes

Packet PROVE-ZHAN-GT4-A22. Successive columns give the finite normalized
patch. Optional sampling identifies every first-coordinate stopping prefix.
The two-view coupling still requires the exact normalized t-view field;
this named geometric input is retained without a normalization hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω₁ Ω₂ ι : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} [Fintype ι]

/-- The finite normalized seed density given by the closed column product. -/
def seedFinitePatch (N : Ω₁ × Ω₂ → ℝ → ℝ → ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω : Ω₁ × Ω₂) : ℝ :=
  colProdT (fun ω₁ => N (ω₁, ω.2)) S₁ (fun i => (S₂ i ω.2 : ℝ)) Tm ω.1

/-- When both normalized axes are one, the terminal column density is
literally the D11 patch of the same two-time field. -/
theorem seedFinitePatch_eq_D11 {N : Ω₁ × Ω₂ → ℝ → ℝ → ℝ}
    {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0} {Tm : ℝ}
    (hN : ∀ ω x y, 0 < N ω x y)
    (hx : ∀ ω x, N ω x 0 = 1) (hy : ∀ ω y, N ω 0 y = 1)
    {U : ℝ≥0} (ω : Ω₁ × Ω₂) (hU : ∀ i, S₁ i ω.1 ≤ U) :
    seedFinitePatch N S₁ S₂ Tm ω =
      patch (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (N ω) U Tm := by
  have he := patch_mul_marginal (S₂ := fun i => (S₂ i ω.2 : ℝ))
    (fun i => (S₁ i ω.1).coe_nonneg) (hN ω) U.coe_nonneg Tm
  simp only [hx, hy, mul_one, div_one] at he
  unfold seedFinitePatch
  rw [← colProd_eq_colProdT (fun ω₁ => N (ω₁, ω.2)) (fun i => (S₂ i ω.2 : ℝ)) Tm hU]
  exact he.symm

/-- A capped stopping prefix of the finite seeded law has the sampled
column density. This is the first optional sampling used for rectangle laws. -/
theorem seed_finite_column_prefix {P : Measure Ω₁} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 m₁} {N : Ω₁ → ℝ → ℝ → ℝ}
    {S : ι → Ω₁ → ℝ≥0} {H : ι → ℝ} {tb : ℝ}
    (hM : Martingale (colProd N S H tb) 𝓕 P)
    (hc : ∀ ω u, ContinuousWithinAt (colProd N S H tb · ω) (Ici u) u)
    {U : ℝ≥0} (hU : ∀ i ω, S i ω ≤ U)
    {τ : Ω₁ → ℝ≥0} (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0))
    (hτU : ∀ ω, τ ω ≤ U) {A : Set Ω₁} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, colProdT N S H tb ω ∂P) =
      ∫ ω in A, colProd N S H tb (τ ω) ω ∂P := by
  have he := setIntegral_stoppedValue_eq_of_rightContinuous hM hc hτ
    (isStoppingTime_const 𝓕 U) (fun ω => WithTop.coe_le_coe.2 (hτU ω))
    (T := U) (fun _ => le_rfl) hA
  simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] at he
  have hterm : colProd N S H tb U = colProdT N S H tb :=
    funext fun ω => colProd_eq_colProdT N H tb (fun i => hU i ω)
  rw [hterm] at he
  exact he.symm

/-- Finite seeded column laws and a normalized t-view give the full seeded
dual hypothesis. Column and row masses are conclusions of the respective
martingale calculations. Compatibility and the actual t-view construction
remain the distinct deterministic inputs described in the handoff. -/
theorem seedDualHyp_seedFiniteColumns
    {n : ℕ} {κ : ℝ} {rr : Fin n → ℝ}
    {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₁ : Filtration ℝ≥0 m₁} {N : Ω₁ × Ω₂ → ℝ → ℝ → ℝ}
    {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0} {Tm : ℝ} {a₂ : Ω₂ → ℝ≥0∞}
    (hN : ∀ ω x y, 0 < N ω x y)
    (hM : ∀ ω₂, Martingale
      (colProd (fun ω₁ => N (ω₁, ω₂)) S₁ (fun i => (S₂ i ω₂ : ℝ)) Tm) 𝓕₁ P₁)
    {U : ℝ≥0} (hU : ∀ i ω, S₁ i ω ≤ U)
    (hm : Measurable (fun ω => ENNReal.ofReal (seedFinitePatch N S₁ S₂ Tm ω)))
    (ha : Measurable a₂)
    {𝓕₂ : Filtration ℝ≥0 m₂} {B₂ D₂ : ℝ≥0 → Ω₂ → ℝ}
    {V₂ : Ω₂ → ℝ → ℝ} {T₂ : Ω₂ → ℝ≥0}
    (htview : SeedNormalizedTView κ rr 𝓕₂ B₂ D₂ V₂ T₂
      (fun ω => ENNReal.ofReal (seedFinitePatch N S₁ S₂ Tm ω)) a₂)
    (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hB₂c : ∀ ω, Continuous (B₂ · ω))
    (hT₂ : IsStoppingTime 𝓕₂ fun ω => (T₂ ω : WithTop ℝ≥0))
    {U₂ : ℝ≥0} (hT₂U : ∀ ω, T₂ ω ≤ U₂) :
    SeedDualHyp P₁ P₂ (fun ω => ENNReal.ofReal (seedFinitePatch N S₁ S₂ Tm ω)) a₂ := by
  refine ⟨hm, ha, htview.row_mass hB₂ hB₂c hT₂ hT₂U hm ha, fun ω₂ => ?_⟩
  have hp := seed_finite_column_probability (fun ω₁ x y => hN (ω₁, ω₂) x y) (hM ω₂) hU
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, seedFinitePatch]
    using hp.measure_univ

end InteractingSLE.ZhanGT4
