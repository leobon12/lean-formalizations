/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfStepGeom

/-!
# A continuous adapted version of an infinite-lifetime driving process

Packet PROVE-CFCHART2. Reuse the existing measurable good set and the
adapted killed driver; freeze the original driver to zero outside that set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfStep

open CfConv

/-- A conull good event makes the original driver continuous and zero-starting
everywhere after freezing, and adapted in the event-enlarged retained filtration. -/
theorem exists_regular_driver_event {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {nL nR : ℕ} {α : ℝ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {𝓕 𝓐 : Filtration ℝ≥0 mΩ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution α xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (h𝓐 : ∀ t, drivingFiltration P hX t ≤ 𝓐 t) :
    ∃ (A : Set Ω) (hA : MeasurableSet A), (∀ᵐ ω ∂P, ω ∈ A) ∧
      (∀ ω ∈ A, ζ ω = ⊤) ∧ (∀ ω, eventDriver A W 0 ω = 0) ∧
      (∀ ω, Continuous fun t => eventDriver A W t ω) ∧
      StronglyAdapted (eventFiltration 𝓐 A hA) (eventDriver A W) := by
  classical
  obtain ⟨A, hA, hA0, hg⟩ := Aux50Hit.exists_goodSet hE hζ
  have hAe : ∀ᵐ ω ∂P, ω ∈ A := ae_iff.2 hA0
  have hW := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (Coupling.adaptedBefore_killedDriving_W hX)
  have hkill : StronglyAdapted 𝓐 (Girsanov.killed ζ W) := fun t =>
    ((Girsanov.measurable_killed hW t).mono (h𝓐 t) le_rfl).stronglyMeasurable
  have he : eventDriver A W = eventDriver A (Girsanov.killed ζ W) := by
    funext t ω
    by_cases hω : ω ∈ A
    · rw [eventDriver_eq hω, eventDriver_eq hω]
      have ht : (t : ℝ≥0∞) < ζ ω := by rw [(hg ω hω).1]; exact ENNReal.coe_lt_top
      simp only [Girsanov.killed, ht, ite_eq_left]
    · simp only [eventDriver, ite_eq_right hω]
  refine ⟨A, hA, hAe, fun ω hω => (hg ω hω).1,
    eventDriver_zero (fun ω hω => (hg ω hω).2.1),
    continuous_eventDriver (fun ω hω => (hg ω hω).continuous), ?_⟩
  rw [he]
  exact stronglyAdapted_eventDriver 𝓐 hA hkill

end InteractingSLE.Sec5.CfStep
