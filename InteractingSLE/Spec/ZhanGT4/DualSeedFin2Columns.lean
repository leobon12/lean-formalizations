/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Protected
import InteractingSLE.Spec.ZhanGT4.DualCols

/-!
# Finite columns of the normalized seeded density

Packet PROVE-ZHAN-GT4-A22. Apply the existing staircase concatenation to
the actual seeded density martingales. The remaining identification with
one common two-time field is named explicitly; no ordinary protected-mark
hypothesis is imposed on a seed at its source.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι]

/-- Exact deterministic compatibility between a two-time normalized seed
field and the one-height source records. This is a distinct named input;
constructing the actual two-time field remains a geometric obligation. -/
def SeedFiniteColumnAgreement {n : ℕ} (N : Ω → ℝ → ℝ → ℝ)
    (S : ι → Ω → ℝ≥0) (H : ι → ℝ) (tb : ℝ) (d : ι → Ω → SeedData n) : Prop :=
  ∀ i u ω, frzHeightProc N S H tb i u ω = seedDensityProcess (d i) (S i) u ω

/-- Finite seeded column laws, including their deterministic uniform bound
and unit terminal mass. The one-height inputs are conclusions of
`seeded_source_calculus_right`; compatibility is purely deterministic. -/
theorem seed_finite_column_law {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {N : Ω → ℝ → ℝ → ℝ}
    {S : ι → Ω → ℝ≥0} {H : ι → ℝ} {tb : ℝ} {d : ι → Ω → SeedData n}
    (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S i ω : WithTop ℝ≥0))
    (hH : ∀ i, 0 ≤ H i) (i₀ : ι) (hN : ∀ ω x y, 0 < N ω x y)
    (ha : SeedFiniteColumnAgreement N S H tb d)
    (hM : ∀ i, Martingale (seedDensityProcess (d i) (S i)) 𝓕 P)
    (hc : ∀ i ω, Continuous (seedDensityProcess (d i) (S i) · ω))
    (hb : ∀ i, ∃ K : ℝ, ∀ u ω, Real.exp (-K) ≤ seedDensityProcess (d i) (S i) u ω ∧
      seedDensityProcess (d i) (S i) u ω ≤ Real.exp K) :
    Martingale (colProd N S H tb) 𝓕 P ∧
      (∀ ω u, ContinuousWithinAt (colProd N S H tb · ω) (Ici u) u) ∧
      (∃ C : ℝ, ∀ u ω, |colProd N S H tb u ω| ≤ C) ∧
      ∀ U : ℝ≥0, (∀ i ω, S i ω ≤ U) → (∫ ω, colProdT N S H tb ω ∂P) = 1 := by
  classical
  choose K hK using hb
  let L := ∑ i, |K i|
  have hKL (i : ι) : K i ≤ L := (le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (K j)) (Finset.mem_univ i))
  have he : ∀ i, frzHeightProc N S H tb i = seedDensityProcess (d i) (S i) :=
    fun i => funext fun u => funext fun ω => ha i u ω
  have hf := martingale_colProd hS hH i₀ hN tb
    (fun i => by rw [he i]; exact hM i)
    (fun i ω u => by rw [he i]; exact (hc i ω).continuousWithinAt)
    (Real.exp_pos (-L)) (fun i u ω => by
      rw [he i]
      exact ⟨(Real.exp_le_exp.2 (neg_le_neg (hKL i))).trans (hK i u ω).1,
        ((hK i u ω).2).trans (Real.exp_le_exp.2 (hKL i))⟩)
  exact ⟨hf.1, hf.2.1, ⟨_, hf.2.2⟩, (integral_colProd_eq_one hN hf.1).2⟩

/-- The terminal finite-column density defines a probability measure.
The mass and measurability are proved from the column martingale. -/
theorem seed_finite_column_probability {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {N : Ω → ℝ → ℝ → ℝ}
    {S : ι → Ω → ℝ≥0} {H : ι → ℝ} {tb : ℝ}
    (hN : ∀ ω x y, 0 < N ω x y) (hM : Martingale (colProd N S H tb) 𝓕 P)
    {U : ℝ≥0} (hU : ∀ i ω, S i ω ≤ U) :
    IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (colProdT N S H tb ω)) := by
  have he : colProdT N S H tb = colProd N S H tb U :=
    funext fun ω => (colProd_eq_colProdT N H tb (fun i => hU i ω)).symm
  have hi : Integrable (colProdT N S H tb) P := he ▸ hM.integrable U
  have hp (ω : Ω) : 0 ≤ colProdT N S H tb ω := by
    unfold colProdT
    exact (Finset.prod_pos fun _ _ => div_pos (hN _ _ _) (hN _ _ _)).le
  have hm := (integral_colProd_eq_one hN hM).2 U hU
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp), hm, ENNReal.ofReal_one]

end InteractingSLE.ZhanGT4
