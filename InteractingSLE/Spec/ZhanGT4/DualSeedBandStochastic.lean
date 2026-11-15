/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandDrift
import InteractingSLE.Spec.ZhanGT4.DualD10
import InteractingSLE.Spec.ZhanGT4.DualSeedLimitVersions

/-!
# Adapted band fields satisfy the stochastic integral formula

Packet PROVE-ZHAN-GT4-A22. Derive the required coefficient regularity and
measurability from the actual alive field values and the stopping time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {S : Ω → ℝ≥0} {g : Ω → ℝ → ℝ}

/-- A rate cut strictly at its horizon is left-continuous at almost every
time. The single endpoint exception is harmless for the Riemann integral. -/
theorem seed_isRiemannRegular_cutRate
    (hc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ))) :
    IsRiemannRegular P (cutRate S g) := by
  apply Eventually.of_forall
  intro ω
  filter_upwards [ae_ne_real (S ω)] with r hr
  rcases le_or_gt r 0 with h0 | h0
  · have he : Iic r.toNNReal = {r.toNNReal} := by
      simp only [Real.toNNReal_of_nonpos h0]
      ext u
      simp only [mem_Iic, nonpos_iff_eq_zero, mem_singleton_iff]
    rw [he]
    exact continuousWithinAt_singleton
  · let u := r.toNNReal
    have hu : (u : ℝ) = r := Real.coe_toNNReal _ h0.le
    have hne : u ≠ S ω := fun hh => hr (hu.symm.trans (congrArg NNReal.toReal hh))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hg : ContinuousWithinAt (fun v : ℝ≥0 => g ω v) (Iic u) u :=
        ((hc ω) u ⟨u.coe_nonneg, hlt.le⟩).comp
          NNReal.continuous_coe.continuousWithinAt (fun v hv => ⟨v.coe_nonneg, hv.trans hlt.le⟩)
      apply hg.congr_of_eventuallyEq
      · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with v hv
        simp only [cutRate, mem_Iio.1 hv, ite_true]
      · simp only [cutRate, hlt, ite_true]
    · apply (continuousAt_const (y := (0 : ℝ))).continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt)] with v hv
        simp only [cutRate, not_lt_of_ge (mem_Ioi.1 hv).le, ite_false]
      · change (if u < S ω then g ω u else 0) = 0
        exact ite_eq_right (not_lt_of_ge hgt.le)

variable {B : ℝ≥0 → Ω → ℝ} {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {ρ K : ℝ}

/-- Measurability of the stopped value and its compensated generator gives
the actual stochastic integral formula for a regular band. -/
theorem SeedRegularBand.stochIntegral
    (h : SeedRegularBand B S Φ Φ₁ Φ₂ Φ₃ Ψ ρ K)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm₀ : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Φ u ω (B u ω)))
    (hm₁ : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Φ₁ u ω (B u ω)))
    (hm₂ : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Φ₂ u ω (B u ω)))
    (hmG : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Ito.fieldGen Φ₂ Ψ B u ω)) (t : ℝ≥0) :
    (fun ω => Ito.fieldStopped Φ Φ₂ Ψ B S 0 t ω -
      Ito.fieldStopped Φ Φ₂ Ψ B S 0 0 ω) =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B (Ito.stopCoef Φ₁ B S) t ω -
        stochIntegral P 𝓕 B (Ito.stopCoef Φ₁ B S) 0 ω := by
  let β : Ω → ℝ → ℝ := fun ω u => B u.toNNReal ω
  have hm (ω : Ω) : MapsTo (fun u => (u, β ω u)) (Icc 0 (S ω : ℝ))
      (seedPathTube (β ω) 0 (S ω) (3 * ρ)) := fun u hu =>
    ⟨hu, by simp only [sub_self, abs_zero]; linarith only [h.radius_pos]⟩
  have hc (ω : Ω) : ContinuousOn (fun u => (u, β ω u)) (Icc 0 (S ω : ℝ)) :=
    continuousOn_id.prodMk ((hBc ω).comp continuous_real_toNNReal).continuousOn
  have hc₀ (ω : Ω) : ContinuousOn (fun u => Φ u ω (B u.toNNReal ω)) (Icc 0 (S ω : ℝ)) :=
    (h.cont ω).comp (hc ω) (hm ω)
  have hc₁ (ω : Ω) : ContinuousOn (fun u => Φ₁ u ω (B u.toNNReal ω)) (Icc 0 (S ω : ℝ)) :=
    (h.contX ω).comp (hc ω) (hm ω)
  have hcG (ω : Ω) : ContinuousOn (fun u => Ito.fieldGen Φ₂ Ψ B u ω) (Icc 0 (S ω : ℝ)) :=
    ((h.contT ω).comp (hc ω) (hm ω)).add
      (continuousOn_const.mul ((h.contXX ω).comp (hc ω) (hm ω)))
  have hgm : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => Ito.fieldGen Φ₂ Ψ B u ω) := hmG
  have hi (u : ℝ≥0) : Measurable[𝓕 u] fun ω =>
      cutInt S (fun ω r => Ito.fieldGen Φ₂ Ψ B r ω) ω u := measurable_cutInt hcG hS hgm u
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
    convert (hi u).indicator hs using 1
    funext ω
    by_cases hu : u ≤ S ω
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hu)]
      exact (cutInt_eq (g := fun ω r => Ito.fieldGen Φ₂ Ψ B r ω) ω ⟨u.coe_nonneg, hu⟩).symm
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω} from hu)]
  have hXm (u : ℝ≥0) : Measurable (Ito.fieldStopped Φ Φ₂ Ψ B S 0 u) := by
    have h0 := measurable_stopped_of_indicator hS (by
      intro v
      simpa only [Real.toNNReal_coe] using hm₀ v) hc₀ u
    have hI := measurable_stopped_of_indicator hS hmI hcI u
    convert (h0.sub hI).mono (𝓕.le u) le_rfl using 1
    funext ω
    simp only [Ito.fieldStopped, Pi.sub_apply, Real.toNNReal_coe]
  have heCut (F : ℝ → Ω → ℝ → ℝ) :
      cutRate S (fun ω r => F r ω (B r.toNNReal ω)) = Ito.stopCoef F B S := by
    funext u ω
    simp only [cutRate, Ito.stopCoef, Real.toNNReal_coe]
  have ha₁ : StronglyAdapted 𝓕 (Ito.stopCoef Φ₁ B S) := fun u => by
    rw [← heCut Φ₁]
    exact (measurable_cutRate (g := fun ω r => Φ₁ r ω (B r.toNNReal ω)) hS (by
      intro v
      simpa only [Real.toNNReal_coe] using hm₁ v) u).stronglyMeasurable
  have ha₂ : StronglyAdapted 𝓕 (Ito.stopCoef Φ₂ B S) := fun u => by
    rw [← heCut Φ₂]
    exact (measurable_cutRate (g := fun ω r => Φ₂ r ω (B r.toNNReal ω)) hS (by
      intro v
      simpa only [Real.toNNReal_coe] using hm₂ v) u).stronglyMeasurable
  have hr : IsRiemannRegular P (Ito.stopCoef Φ₁ B S) := by
    rw [← heCut Φ₁]
    exact seed_isRiemannRegular_cutRate (P := P) hc₁
  exact seed_stochIntegral_eq_of_band_field hB hBc hXm (h.continuous_stopped hBc) ha₁ ha₂
    (fun u ω => (h.coef_bound ω u).1) hr
    (fun ω => ⟨ρ, K, h.radius_pos, h.bound_nonneg, h.local_field ω, h.contT ω, h.contXX ω,
      fun u => (h.coef_bound ω u).1, fun u => (h.coef_bound ω u).2⟩) t

end InteractingSLE.ZhanGT4
