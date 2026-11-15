/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkClock7First
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianAdapt

/-!
# Stopped local retargeting coefficients

The generic running-integral and stopped-measurability results of the existing
retargeting proof apply to any finite stop before separation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Adapt8

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {a : ℝ} {W V : ℝ≥0 → Ω → ℝ} {G : Set Ω} {σ : Ω → ℝ≥0}

/-- Adaptedness of the existing alpha coefficient of a continuous gap. -/
theorem measurable_alphaK {g : ℝ≥0 → Ω → ℝ}
    (hm : ∀ s, Measurable[𝓕 s] (g s)) (hc : ∀ ω, Continuous (g · ω)) (s : ℝ≥0) :
    Measurable[𝓕 s] (alphaK a g s) := by
  have hg := StronglyAdapted.isStronglyProgressive_of_continuous
    (fun r => (hm r).stronglyMeasurable) hc
  have hi := (Girsanov.stronglyMeasurable_integral_comp hg
    (g := fun x : ℝ => (x ^ 2)⁻¹) (by fun_prop) s).measurable
  exact (Real.measurable_exp.comp (hi.const_mul (-2))).const_mul _

/-- Adaptedness of the existing beta coefficient of a continuous nonzero gap. -/
theorem measurable_betaK {g : ℝ≥0 → Ω → ℝ}
    (hm : ∀ s, Measurable[𝓕 s] (g s)) (hc : ∀ ω, Continuous (g · ω))
    (h0 : ∀ ω s, g s ω ≠ 0) (s : ℝ≥0) : Measurable[𝓕 s] (betaK a g s) := by
  have hg := StronglyAdapted.isStronglyProgressive_of_continuous
    (fun r => (hm r).stronglyMeasurable) hc
  have hα := StronglyAdapted.isStronglyProgressive_of_continuous
    (fun r => (measurable_alphaK (a := a) hm hc r).stronglyMeasurable)
    (fun ω => continuous_alphaK (hc ω) (h0 ω))
  have hi := (stronglyMeasurable_integral_comp₂ hα hg
    (g := fun p : ℝ × ℝ => p.1 / p.2 ^ 3) (by fun_prop) s).measurable
  exact measurable_const.sub (hi.const_mul 2)

/-- Stopping a positive local gap gives a continuous adapted nonzero gap everywhere. -/
theorem stopped_gap_regular {e : Ω → ℝ≥0∞}
    (hW : AdaptedBefore 𝓕 e W) (hV : AdaptedBefore 𝓕 e V)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    (hG : MeasurableSet[𝓕 0] G) (hσe : ∀ ω ∈ G, (σ ω : ℝ≥0∞) < e ω)
    (hc : ∀ ω ∈ G, ContinuousOn (fun s => V s ω - W s ω) (Iic (σ ω)))
    (hpos : ∀ ω ∈ G, ∀ s ≤ σ ω, 0 < V s ω - W s ω) :
    let g := gapStopR (0 : Fin 1) G W (fun _ => V) σ
    (∀ s, Measurable[𝓕 s] (g s)) ∧ (∀ ω, Continuous (g · ω)) ∧ (∀ ω s, g s ω ≠ 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hk : ∀ r, Measurable[𝓕 r] fun ω =>
        (if (r : ℝ≥0∞) < e ω then V r ω else 0) -
          (if (r : ℝ≥0∞) < e ω then W r ω else 0) :=
      fun r => (Sec2.TwoSeed.measurable_killed hV r).sub (Sec2.TwoSeed.measurable_killed hW r)
    exact Ito.measurable_stopped_of_agree hσ hk hG 1 (fun ω hω r hr => by
      have he := (ENNReal.coe_le_coe.2 hr).trans_lt (hσe ω hω)
      simp only [he, ↓reduceIte]) hc s
  · intro ω
    by_cases hω : ω ∈ G
    · simp only [gapStopR, hω, ↓reduceIte]
      exact (hc ω hω).comp_continuous (continuous_id.min continuous_const)
        fun s => mem_Iic.2 (min_le_right _ _)
    · simp only [gapStopR, hω, ↓reduceIte]; exact continuous_const
  · intro ω s
    by_cases hω : ω ∈ G
    · simpa only [gapStopR, hω, ↓reduceIte] using
        (hpos ω hω (min s (σ ω)) (min_le_right _ _)).ne'
    · simp only [gapStopR, hω, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]

omit mΩ in
/-- The stopped-gap alpha and beta coefficients agree with the originals through the stop. -/
theorem stopped_coefficients_eq {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0} (hs : s ≤ σ ω) :
    let g := gapStopR (0 : Fin 1) G W (fun _ => V) σ
    alphaK a g s ω = alpha a (W · ω) (V · ω) s ∧
      betaK a g s ω = beta a (W · ω) (V · ω) s := by
  dsimp only
  have hg : ∀ {t : ℝ≥0}, t ≤ σ ω → ∀ u ∈ uIcc (0 : ℝ) t,
      gapStopR (0 : Fin 1) G W (fun _ => V) σ u.toNNReal ω = gap (W · ω) (V · ω) u := by
    intro t ht u hu
    rw [uIcc_of_le t.coe_nonneg] at hu
    simp only [gapStopR, hω, ↓reduceIte, gap]
    rw [min_eq_left ((Sec2.toNNReal_le_of_mem_Icc hu).trans ht)]
  have hα : ∀ t : ℝ≥0, t ≤ σ ω →
      alphaK a (gapStopR (0 : Fin 1) G W (fun _ => V) σ) t ω = alpha a (W · ω) (V · ω) t := by
    intro t ht
    unfold alphaK alpha
    congr 3
    exact intervalIntegral.integral_congr fun u hu => by rw [hg ht u hu]
  refine ⟨hα s hs, ?_⟩
  unfold betaK beta
  congr 2
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu' := hu
  rw [uIcc_of_le s.coe_nonneg] at hu'
  rw [hg hs u hu, hα _ ((Sec2.toNNReal_le_of_mem_Icc hu').trans hs),
    Real.coe_toNNReal _ hu'.1]

end InteractingSLE.Sec5.TwoMark.Adapt8
