/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageDoleans
import MathFin.Probability.Brownian.WeightedQuadraticVariation

/-!
# Weighted Brownian quadratic errors in the original filtration

Packet PROVE-ZHAN-GT4-A22. The port's weighted fluctuation estimate is
private and specialized to the natural filtration. This partition version
uses the port's independence and Gaussian moment lemmas in an arbitrary
Brownian filtration, as required by the random seeded log field.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A past-measurable multiplier has zero pairing with the centered square
of the next increment, including unbounded multipliers. -/
theorem integral_seed_mul_centered_sq (hB : IsFilteredPreBrownian B 𝓕 P)
    {a b : ℝ≥0} (hab : a ≤ b) {χ : Ω → ℝ} (hχ : Measurable[𝓕 a] χ) :
    ∫ ω, χ ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a)) ∂P = 0 := by
  have hm := hχ.mono (𝓕.le a) le_rfl
  rw [(MathFin.ItoIsometryAdapted.adapted_indepFun_increment hB hab hχ).integral_mul_comp
    (g := fun x => x ^ 2 - ((b : ℝ) - a)) (by fun_prop) hm.aestronglyMeasurable
    ((hB.measurable_eval b).sub (hB.measurable_eval a)).aemeasurable,
    MathFin.QuadraticVariationL2.integral_increment_centered_mean hB.toIsPreBrownianReal hab, mul_zero]

/-- The weighted centered quadratic sum has variance at most
`2 C² ∑ Δt²`. Neither the partition nor the filtration is specialized. -/
theorem integral_sq_seed_quadratic_le (hB : IsFilteredPreBrownian B 𝓕 P)
    {π : ℕ → ℝ≥0} (hπ : Monotone π) {w : ℕ → Ω → ℝ}
    (hw : ∀ k, Measurable[𝓕 (π k)] (w k)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k ω, |w k ω| ≤ C) (N : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range N, w k ω *
        ((B (π (k + 1)) ω - B (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k))) ^ 2 ∂P ≤
      ∑ k ∈ Finset.range N, C ^ 2 * (2 * ((π (k + 1) : ℝ) - π k) ^ 2) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Y : ℕ → Ω → ℝ := fun k ω =>
    (B (π (k + 1)) ω - B (π k) ω) ^ 2 - ((π (k + 1) : ℝ) - π k)
  let v : ℕ → Ω → ℝ := fun k ω => w k ω * Y k ω
  have hYL2 : ∀ k, MemLp (Y k) 2 P := fun k =>
    MathFin.QuadraticVariationL2.memLp_increment_sq_centered_two hB.toIsPreBrownianReal _ _ _
  have hvL2 : ∀ k, MemLp (v k) 2 P := fun k =>
    MemLp.mono ((hYL2 k).const_mul C)
      (((hw k).mono (𝓕.le _) le_rfl).aestronglyMeasurable.mul (hYL2 k).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        simp only [v, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hb k ω) (abs_nonneg _))
  have hi : ∀ k l, Integrable (fun ω => v k ω * v l ω) P :=
    fun k l => (hvL2 k).integrable_mul (hvL2 l)
  have hva : ∀ k, Measurable[𝓕 (π (k + 1))] (v k) := fun k =>
    ((hw k).mono (𝓕.mono (hπ (Nat.le_succ k))) le_rfl).mul
      (MathFin.QuadraticVariationL2.measurable_increment_sq_sub hB
        (hπ (Nat.le_succ k)) le_rfl _)
  have hcross (k l : ℕ) (hlk : l < k) : ∫ ω, v l ω * v k ω ∂P = 0 := by
    have hm : Measurable[𝓕 (π k)] (fun ω => v l ω * w k ω) :=
      ((hva l).mono (𝓕.mono (hπ hlk)) le_rfl).mul (hw k)
    have hz := integral_seed_mul_centered_sq hB (hπ (Nat.le_succ k)) hm
    convert hz using 1
    congr 1
    funext ω
    dsimp [v, Y]
    ring
  have hdiag (k : ℕ) : ∫ ω, v k ω * v k ω ∂P ≤
      C ^ 2 * (2 * ((π (k + 1) : ℝ) - π k) ^ 2) := by
    have hsq : ∀ ω, w k ω ^ 2 ≤ C ^ 2 := fun ω => by
      nlinarith [hb k ω, abs_nonneg (w k ω), sq_abs (w k ω)]
    calc ∫ ω, v k ω * v k ω ∂P
        ≤ ∫ ω, C ^ 2 * (Y k ω * Y k ω) ∂P :=
          integral_mono (hi k k) (((hYL2 k).integrable_mul (hYL2 k)).const_mul _) fun ω => by
            dsimp [v]
            nlinarith [hsq ω, mul_self_nonneg (Y k ω)]
      _ = C ^ 2 * ∫ ω, Y k ω * Y k ω ∂P := integral_const_mul _ _
      _ = _ := by
        simp only [Y, ← sq]
        rw [MathFin.QuadraticVariationL2.integral_increment_sq_centered
          hB.toIsPreBrownianReal (hπ (Nat.le_succ k))]
  calc ∫ ω, (∑ k ∈ Finset.range N, v k ω) ^ 2 ∂P
      = ∫ ω, ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, v k ω * v l ω ∂P := by
        simp_rw [sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∫ ω, v k ω * v l ω ∂P := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi k l]
        exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hi k l
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.sum_eq_single k ?_ (fun h => absurd hk h)]
        · exact hdiag k
        · intro l _ hlk
          rcases lt_or_gt_of_ne hlk with hlt | hgt
          · simpa only [mul_comm] using hcross k l hlt
          · exact hcross l k hgt

end InteractingSLE.ZhanGT4
