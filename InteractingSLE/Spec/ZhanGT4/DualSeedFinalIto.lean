/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalLocal
import InteractingSLE.Spec.ZhanGT4.DualSeedLawLog

/-!
# Integral identification after pathwise localization

Packet PROVE-ZHAN-GT4-A22. The second coefficient needs only local
pathwise bounds. Taylor constants and remainders need neither uniform
bounds nor measurable choices.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B X c₁ c₂ : ℝ≥0 → Ω → ℝ}

/-- Removing the second coefficient adds exactly half its quadratic error. -/
theorem seedDyadicDefect_zero_second (X c₁ c₂ B : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    seedDyadicDefect X c₁ (fun _ _ => 0) B n t ω =
      seedDyadicDefect X c₁ c₂ B n t ω + seedQuadraticError B c₂ n t ω / 2 := by
  unfold seedDyadicDefect seedQuadraticError
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Ito.itoDefect, NNReal.coe_min]
  ring

/-- Measurability of the finite Taylor sum. -/
theorem measurable_seedDyadicDefect (hX : ∀ u, Measurable (X u))
    (h₁ : ∀ u, Measurable (c₁ u)) (h₂ : ∀ u, Measurable (c₂ u))
    (hB : ∀ u, Measurable (B u)) (n : ℕ) (t : ℝ≥0) :
    Measurable (seedDyadicDefect X c₁ c₂ B n t) := by
  unfold seedDyadicDefect Ito.itoDefect
  exact Finset.measurable_sum _ fun _ _ =>
    (((hX _).sub (hX _)).sub ((h₁ _).mul ((hB _).sub (hB _)))).sub
      ((measurable_const.mul (h₂ _)).mul ((((hB _).sub (hB _)).pow_const 2).sub measurable_const))

/-- The positive-time integral formula with a pathwise bounded second coefficient. -/
theorem seed_stochIntegral_sub_eq_of_local_taylor
    (hB : IsFilteredBrownianReal 𝓕 B P) (hX : ∀ u, Measurable (X u))
    (h₁ : StronglyAdapted 𝓕 c₁) {C₁ : ℝ} (hb₁ : ∀ u ω, |c₁ u ω| ≤ C₁)
    (hr₁ : IsRiemannRegular P c₁) (h₂ : StronglyAdapted 𝓕 c₂)
    {ε t : ℝ≥0} (hεt : ε ≤ t)
    (hb₂ : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ u ≤ t, |c₂ u ω| ≤ C)
    (he : ∀ᵐ ω ∂P, ∃ (C : ℝ) (R : ℕ → ℝ), Tendsto R atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, |seedDyadicDefect X c₁ c₂ B n t ω -
        seedDyadicDefect X c₁ c₂ B n ε ω| ≤ C * seedCubicError B n t ω + R n) :
    (fun ω => X t ω - X ε ω) =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B c₁ t ω - stochIntegral P 𝓕 B c₁ ε ω := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hpre := isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hQt := seedQuadraticError_tendsto_ae_of_pathwiseBounded hpre h₂ t hb₂
  have hQe := seedQuadraticError_tendsto_ae_of_pathwiseBounded hpre h₂ ε (by
    filter_upwards [hb₂] with ω ⟨C, hC⟩
    exact ⟨C, fun u hu => hC u (hu.trans hεt)⟩)
  have hD := seedTaylorError_tendsto_ae_of_pathwiseBounded hB t he
  have hl : ∀ᵐ ω ∂P, Tendsto (fun n => seedDyadicDefect X c₁ (fun _ _ => 0) B n t ω -
      seedDyadicDefect X c₁ (fun _ _ => 0) B n ε ω) atTop (𝓝 0) := by
    filter_upwards [hQt, hQe, hD] with ω ht he hd
    simpa only [seedDyadicDefect_zero_second X c₁ c₂, sub_self, zero_div, add_zero,
      add_sub_add_comm, sub_div] using hd.add ((ht.sub he).div_const 2)
  apply seed_stochIntegral_sub_eq_of_dyadicDefect (c₂ := fun _ _ => 0) hpre h₁ hb₁ hr₁
    (fun _ => stronglyMeasurable_const) (C₂ := 0) le_rfl (fun _ _ => by simp) hεt
  apply tendstoInMeasure_of_tendsto_ae (fun n => ?_) hl
  exact ((measurable_seedDyadicDefect hX (fun u => (h₁ u).measurable.mono (𝓕.le u) le_rfl)
    (fun _ => measurable_const) hB.measurable' n t).sub
      (measurable_seedDyadicDefect hX (fun u => (h₁ u).measurable.mono (𝓕.le u) le_rfl)
        (fun _ => measurable_const) hB.measurable' n ε)).aestronglyMeasurable

/-- Exact remaining finite-pasting input for the actual seeded field.
It contains only finite sums and pathwise limits, and permits random bounds. -/
structure SeedLogPathwiseTaylor {n : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (B θ : ℝ≥0 → Ω → ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : Prop where
  measurable_log : ∀ u, Measurable (seedCompensatedLog d S θ u)
  estimate : ∀ ε t : ℝ≥0, 0 < ε → ε ≤ t → ∃ c₂ : ℝ≥0 → Ω → ℝ,
    StronglyAdapted 𝓕 c₂ ∧
      (∀ᵐ ω ∂P, ∃ C : ℝ, ∀ u ≤ t, |c₂ u ω| ≤ C) ∧
      ∀ᵐ ω ∂P, ∃ (C : ℝ) (R : ℕ → ℝ), Tendsto R atTop (𝓝 0) ∧
        ∀ᶠ j in atTop, |seedDyadicDefect (seedCompensatedLog d S θ) θ c₂ B j t ω -
          seedDyadicDefect (seedCompensatedLog d S θ) θ c₂ B j ε ω| ≤
            C * seedCubicError B j t ω + R j

/-- Local pathwise Taylor estimates identify the positive seeded logarithm. -/
theorem seedPositiveLogIto_of_pathwiseTaylor {n : ℕ}
    (hB : IsFilteredBrownianReal 𝓕 B P) {θ : ℝ≥0 → Ω → ℝ}
    (hθ : StronglyAdapted 𝓕 θ) {Cθ : ℝ} (hb : ∀ u ω, |θ u ω| ≤ Cθ)
    (hr : IsRiemannRegular P θ) {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hT : SeedLogPathwiseTaylor P 𝓕 B θ d S) : SeedPositiveLogIto P 𝓕 B θ d S := by
  intro ε t hε hεt
  obtain ⟨c₂, h₂, hb₂, he⟩ := hT.estimate ε t hε hεt
  filter_upwards [seed_stochIntegral_sub_eq_of_local_taylor hB hT.measurable_log
    hθ hb hr h₂ hεt hb₂ he] with ω hω
  dsimp [seedCompensatedLog] at hω
  linarith only [hω]

end InteractingSLE.ZhanGT4
