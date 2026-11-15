/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndIntegral

/-!
# Measurable original-clock band fields

Packet PROVE-ZHAN-GT4-A22. Export the measurable stopped field and the
coefficient facts from the actual alive values, so original-clock band
integration requires no separate measurability assumption about a remainder.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {ρ K : ℝ}

/-- The stopped compensated field is measurable from the alive field and
generator values. Only continuity on the actual moving tube is needed. -/
theorem SeedRegularBand.measurable_stopped
    (h : SeedRegularBand B S Φ Φ₁ Φ₂ Φ₃ Ψ ρ K) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm₀ : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Φ u ω (B u ω)))
    (hmG : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Ito.fieldGen Φ₂ Ψ B u ω)) (t : ℝ≥0) :
    Measurable[𝓕 t] (Ito.fieldStopped Φ Φ₂ Ψ B S 0 t) := by
  have hm (ω : Ω) : MapsTo (fun u => (u, B u.toNNReal ω)) (Icc 0 (S ω : ℝ))
      (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ)) := fun u hu =>
    ⟨hu, by simp only [sub_self, abs_zero]; linarith only [h.radius_pos]⟩
  have hc (ω : Ω) : ContinuousOn (fun u => (u, B u.toNNReal ω)) (Icc 0 (S ω : ℝ)) :=
    continuousOn_id.prodMk ((hBc ω).comp continuous_real_toNNReal).continuousOn
  have hc₀ (ω : Ω) : ContinuousOn (fun u => Φ u ω (B u.toNNReal ω)) (Icc 0 (S ω : ℝ)) :=
    (h.cont ω).comp (hc ω) (hm ω)
  have hcG (ω : Ω) : ContinuousOn (fun u => Ito.fieldGen Φ₂ Ψ B u ω) (Icc 0 (S ω : ℝ)) :=
    ((h.contT ω).comp (hc ω) (hm ω)).add
      (continuousOn_const.mul ((h.contXX ω).comp (hc ω) (hm ω)))
  have hcI (ω : Ω) : ContinuousOn
      (fun u => ∫ r in (0 : ℝ)..u, Ito.fieldGen Φ₂ Ψ B r ω) (Icc 0 (S ω : ℝ)) := by
    have hh := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (a := 0) (b := (S ω : ℝ)) (f := fun r => Ito.fieldGen Φ₂ Ψ B r ω) (by
        rw [uIcc_of_le (S ω).coe_nonneg]
        exact (hcG ω).integrableOn_Icc)
    simpa only [uIcc_of_le (S ω).coe_nonneg] using hh
  have hmI (u : ℝ≥0) : Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω =>
      ∫ r in (0 : ℝ)..u, Ito.fieldGen Φ₂ Ψ B r ω) := by
    have hs : MeasurableSet[𝓕 u] {ω | u ≤ S ω} := by
      simpa only [WithTop.coe_le_coe] using hS.measurableSet_ge u
    convert (measurable_cutInt hcG hS hmG u).indicator hs using 1
    funext ω
    by_cases hu : u ≤ S ω
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hu)]
      exact (cutInt_eq (g := fun ω r => Ito.fieldGen Φ₂ Ψ B r ω) ω ⟨u.coe_nonneg, hu⟩).symm
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω} from hu)]
  have h0 := measurable_stopped_of_indicator hS (by
    intro u
    simpa only [Real.toNNReal_coe] using hm₀ u) hc₀ t
  have hI := measurable_stopped_of_indicator hS hmI hcI t
  convert h0.sub hI using 1
  funext ω
  simp only [Ito.fieldStopped, Pi.sub_apply, Real.toNNReal_coe]

/-- Alive first derivative values give both adaptedness and the exact
Riemann regularity used by the original-clock stochastic integral. -/
theorem SeedRegularBand.coef_facts
    (h : SeedRegularBand B S Φ Φ₁ Φ₂ Φ₃ Ψ ρ K) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm₁ : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Φ₁ u ω (B u ω))) :
    StronglyAdapted 𝓕 (Ito.stopCoef Φ₁ B S) ∧ IsRiemannRegular P (Ito.stopCoef Φ₁ B S) := by
  have he : cutRate S (fun ω r => Φ₁ r ω (B r.toNNReal ω)) = Ito.stopCoef Φ₁ B S := by
    funext u ω
    simp only [cutRate, Ito.stopCoef, Real.toNNReal_coe]
  have ha : StronglyAdapted 𝓕 (Ito.stopCoef Φ₁ B S) := fun u => by
    rw [← he]
    exact (measurable_cutRate hS (by
      intro v
      simpa only [Real.toNNReal_coe] using hm₁ v) u).stronglyMeasurable
  refine ⟨ha, ?_⟩
  rw [← he]
  apply seed_isRiemannRegular_cutRate
  intro ω
  apply (h.contX ω).comp (continuousOn_id.prodMk
    ((hBc ω).comp continuous_real_toNNReal).continuousOn)
  intro u hu
  exact ⟨hu, by simp only [Function.comp_apply, id_eq, sub_self, abs_zero]; linarith only [h.radius_pos]⟩

end InteractingSLE.ZhanGT4
