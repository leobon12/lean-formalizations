/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkVersion6Clock
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianMart

/-!
# Measurability of the capacity clock stopped before target separation

The existing stopped-gap and running-integral arguments are adapted to local
paths. No maximal lifetime or positive target-index restriction is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Clock7

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {a : ℝ} {W V : ℝ≥0 → Ω → ℝ} {G : Set Ω} {σ : Ω → ℝ≥0}

/-- The clock of an adapted continuous nonzero gap is adapted. -/
theorem measurable_clkK {g : ℝ≥0 → Ω → ℝ}
    (hm : ∀ s, Measurable[𝓕 s] (g s)) (hc : ∀ ω, Continuous (g · ω))
    (h0 : ∀ ω s, g s ω ≠ 0) (s : ℝ≥0) : Measurable[𝓕 s] (clkK a g s) := by
  have hg : IsStronglyProgressive 𝓕 g :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun s => (hm s).stronglyMeasurable) hc
  have hα : ∀ s, Measurable[𝓕 s] (alphaK a g s) := fun s => by
    have hi := (Girsanov.stronglyMeasurable_integral_comp hg
      (g := fun x : ℝ => (x ^ 2)⁻¹) (by fun_prop) s).measurable
    exact (Real.measurable_exp.comp (hi.const_mul (-2))).const_mul _
  have hαp : IsStronglyProgressive 𝓕 (alphaK a g) :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun s => (hα s).stronglyMeasurable)
      fun ω => continuous_alphaK (hc ω) (h0 ω)
  exact (stronglyMeasurable_integral_comp₂ hαp hg
    (g := fun p : ℝ × ℝ => p.1 ^ 2 / p.2 ^ 4) (by fun_prop) s).measurable

omit mΩ in
/-- Before the stop, the clock computed from the stopped gap is the original clock. -/
theorem clkK_gapStop_eq {ω : Ω} (hω : ω ∈ G) {s : ℝ≥0} (hs : s ≤ σ ω) :
    clkK a (gapStopR (0 : Fin 1) G W (fun _ => V) σ) s ω =
      clk (rate a (W · ω) (V · ω)) s := by
  have hgap : ∀ {t : ℝ≥0}, t ≤ σ ω → ∀ u ∈ uIcc (0 : ℝ) t,
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
    exact intervalIntegral.integral_congr fun u hu => by rw [hgap ht u hu]
  unfold clkK clk
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu' := hu
  rw [uIcc_of_le s.coe_nonneg] at hu'
  simp only [rate]
  rw [hgap hs u hu, hα _ ((Sec2.toNNReal_le_of_mem_Icc hu').trans hs),
    Real.coe_toNNReal _ hu'.1]

/-- The original capacity clock stopped before a separated local horizon is measurable. -/
theorem measurable_stopped_clock {e : Ω → ℝ≥0∞}
    (hW : AdaptedBefore 𝓕 e W) (hV : AdaptedBefore 𝓕 e V)
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    (hG : MeasurableSet[𝓕 0] G) (hσe : ∀ ω ∈ G, (σ ω : ℝ≥0∞) < e ω)
    (hc : ∀ ω ∈ G, ContinuousOn (fun s => V s ω - W s ω) (Iic (σ ω)))
    (hpos : ∀ ω ∈ G, ∀ s ≤ σ ω, 0 < V s ω - W s ω) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => if ω ∈ G then
      clk (rate a (W · ω) (V · ω)) (min t (σ ω)) else 0 := by
  classical
  let g := gapStopR (0 : Fin 1) G W (fun _ => V) σ
  have hgm : ∀ s, Measurable[𝓕 s] (g s) := fun s => by
    have hk : ∀ r, Measurable[𝓕 r] fun ω =>
        (if (r : ℝ≥0∞) < e ω then V r ω else 0) -
          (if (r : ℝ≥0∞) < e ω then W r ω else 0) :=
      fun r => (Sec2.TwoSeed.measurable_killed hV r).sub (Sec2.TwoSeed.measurable_killed hW r)
    exact Ito.measurable_stopped_of_agree hσ hk hG 1 (fun ω hω r hr => by
      have he := (ENNReal.coe_le_coe.2 hr).trans_lt (hσe ω hω)
      simp only [he, ↓reduceIte]) hc s
  have hgc : ∀ ω, Continuous (g · ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [g, gapStopR, hω, ↓reduceIte]
      exact (hc ω hω).comp_continuous (continuous_id.min continuous_const)
        fun s => mem_Iic.2 (min_le_right _ _)
    · simp only [g, gapStopR, hω, ↓reduceIte]; exact continuous_const
  have hg0 : ∀ ω s, g s ω ≠ 0 := by
    intro ω s
    by_cases hω : ω ∈ G
    · simpa only [g, gapStopR, hω, ↓reduceIte] using
        (hpos ω hω (min s (σ ω)) (min_le_right _ _)).ne'
    · simp only [g, gapStopR, hω, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
  have hm := Ito.measurable_stopped_of_agree (X := clkK a g) hσ
    (fun s => measurable_clkK hgm hgc hg0 s) hG 0 (fun _ _ _ _ => rfl)
    (fun ω _ => (continuous_clkK (hgc ω) (hg0 ω)).continuousOn) t
  convert hm using 1
  funext ω
  split_ifs with hω
  · exact (clkK_gapStop_eq hω (min_le_right t (σ ω))).symm
  · rfl

end InteractingSLE.Sec5.TwoMark.Clock7
