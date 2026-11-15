/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepLaw
import InteractingSLE.Spec.Sec7.PocketStopSideLimR6

/-!
# R.5 transports exact heights with the actual inherited lift

PROVE-POCKET-SIDEIN. The global increment law gives the physical mean germ.
The current corrected height is the old height plus the actual difference
of the inherited lifts. Heights and the field coefficient are unrestricted,
so the statement applies at arbitrary R.7 margins, including nested pockets.
This does not construct a collar or an initial height anchor.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.PocketStopSide

/-- On one event, every incident germ transports the exact old height with
its inherited lift difference. In particular, a zero lift difference preserves
the height exactly. There is no separate integer choice on either side. -/
theorem ae_corrected_height_of_old_chart_increment_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : Set Ω} {old current : Ω → Chart}
    {gOld gNow : Ω → DistOn upperHalfPlaneOpens}
    (hOld : ∀ ω ∈ M, (old ω).IsConformal)
    (hCurrent : ∀ ω ∈ M, (current ω).IsConformal)
    (hInclusion : ∀ ω ∈ M, ((current ω).dom : Set ℂ) ⊆ (old ω).dom)
    (hLaw : HasOldChartIncrementLaw P M old current gOld gNow) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ vOld vNow : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vOld (old ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old ω).dom →
        gOld ω φ = ∫ z, vOld z * φ z) →
      InnerProductSpace.HarmonicOnNhd vNow (current ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (current ω).dom →
        gNow ω φ = ∫ z, vNow z * φ z) → ∀ ξ x r : ℝ,
      0 < r → (old ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (current ω).dom →
      Tendsto (fun z => (old ω).1 ((current ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) → ∀ (κ b ℓ : ℝ) (u : ℂ → ℝ),
      Tendsto (sideMean κ (old ω) u vOld) (𝓝[H] (x : ℂ)) (𝓝 b) →
      Tendsto (fun z => (current ω).2.2 ((current ω).2.1 z) -
        (old ω).2.2 ((current ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 ℓ) →
      Tendsto (sideMean κ (current ω) u vNow) (𝓝[H] (ξ : ℂ)) (𝓝 (b + chiC κ * ℓ)) := by
  filter_upwards [ae_physical_germ_of_old_chart_increment_law hOld hCurrent hInclusion hLaw]
    with ω hGerm hω vOld vNow hvOld hRepOld hvNow hRepNow ξ x r hr hCollar
      hTransition κ b ℓ u hHeight hLift
  have hWithin : Tendsto (fun z => (old ω).1 ((current ω).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hTransition, ?_⟩
    exact eventually_nhdsWithin_of_forall fun z hz =>
      (hOld ω hω).fwd_mem (hInclusion ω hω ((hCurrent ω hω).inv_mem_dom hz))
  have hPhysical := hGerm hω vOld vNow hvOld hRepOld hvNow hRepNow
    ξ x r hr hCollar hTransition
  have hSum := (hPhysical.add (hHeight.comp hWithin)).add (hLift.const_mul (chiC κ))
  rw [zero_add] at hSum
  refine hSum.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  dsimp only [sideMean, Function.comp_def]
  rw [(hOld ω hω).inv_fwd (hInclusion ω hω ((hCurrent ω hω).inv_mem_dom hz))]
  ring

end InteractingSLE.Sec7.PocketStopSide
