/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8Height
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepHeight

/-!
# Incoming own heights from the initial height and a named increment law

PROVE-SIDE-COLLAR2. The initial-to-reference increment law remains a named
input, as assigned to R5-ENLARGED. On surviving incoming real trajectories,
the collar, transition and zero lift are derived, so that law transports
the initial own height to the actual later own chart without extra
geometric or boundary-height assumptions.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The base chart itself is an incident reference at every surviving
incoming real trajectory, with the actual inherited lift difference zero. -/
theorem exists_base_collar_of_surviving_real {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T x : ℝ} (hT : 0 ≤ T)
    {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol W x T a) :
    ∃ ε : ℝ, 0 < ε ∧ c.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ ((c.loewner W T).dom : Set ℂ) ∧
      Tendsto (fun z => c.1 ((c.loewner W T).2.1 z))
        (𝓝[H] ((a T).re : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (fun z => (c.loewner W T).2.2 ((c.loewner W T).2.1 z) -
        c.2.2 ((c.loewner W T).2.1 z)) (𝓝[H] ((a T).re : ℂ)) (𝓝 0) := by
  obtain ⟨ε, hε, hCollar, hTransition, hLift⟩ :=
    exists_own_collar_of_surviving_real hc hW hW0 le_rfl hT ha
  have h0 : (a 0).re = x := by
    have hz := QuantumZipper.FwdHolo.sol_zero ha hT
    simpa only [hW0, Complex.ofReal_zero, sub_zero, Complex.ofReal_re] using
      congrArg Complex.re hz
  rw [h0] at hCollar hTransition
  rw [Theorem14.GW2aCont.loewner_zero_fwd hW0] at hTransition
  rw [Theorem14.GW2aCont.loewner_zero_lift] at hLift
  refine ⟨ε, hε, ?_, hTransition, hLift⟩
  rintro _ ⟨z, hz, rfl⟩
  have hInv := Theorem14.GW2aCont.loewner_zero_inv (c := c) hW hW0 hz.1
  exact hInv ▸ hCollar ⟨z, hz, rfl⟩

/-- A named reference increment law transports every initial own height
at a surviving incoming real point. All collar and lift premises of the
general R.5 height theorem are discharged here. -/
theorem ae_incoming_height_of_increment_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : Set Ω} {base current : Ω → Chart} {g₀ g : Ω → DistOn upperHalfPlaneOpens}
    (hBase : ∀ ω ∈ M, (base ω).IsConformal)
    (hCurrent : ∀ ω ∈ M, (current ω).IsConformal)
    (hInclusion : ∀ ω ∈ M, ((current ω).dom : Set ℂ) ⊆ (base ω).dom)
    (hLaw : HasOldChartIncrementLaw P M base current g₀ g) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ (v₀ v : ℂ → ℝ),
      InnerProductSpace.HarmonicOnNhd v₀ (base ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (base ω).dom →
        g₀ ω φ = ∫ z, v₀ z * φ z) →
      InnerProductSpace.HarmonicOnNhd v (current ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (current ω).dom →
        g ω φ = ∫ z, v z * φ z) →
      ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 → ∀ T : ℝ, 0 ≤ T →
      current ω = (base ω).loewner W T → ∀ (x : ℝ) (a : ℝ → ℂ),
      QuantumZipper.IsForwardSol W x T a → ∀ (κ b : ℝ) (u : ℂ → ℝ),
      Tendsto (sideMean κ (base ω) u v₀) (𝓝[H] (x : ℂ)) (𝓝 b) →
      Tendsto (sideMean κ (current ω) u v) (𝓝[H] ((a T).re : ℂ)) (𝓝 b) := by
  filter_upwards [ae_corrected_height_of_old_chart_increment_law
    hBase hCurrent hInclusion hLaw] with ω hHeight hM v₀ v hv₀ hrep₀ hv hrep
      W hW hW0 T hT hChart x a ha κ b u hInitial
  obtain ⟨ε, hε, hCollar, hTransition, hLift⟩ :=
    exists_base_collar_of_surviving_real (hBase ω hM) hW hW0 hT ha
  rw [← hChart] at hCollar hTransition hLift
  have h := hHeight hM v₀ v hv₀ hrep₀ hv hrep (a T).re x ε hε hCollar
    hTransition κ b 0 u hInitial hLift
  simpa only [mul_zero, add_zero] using h

end InteractingSLE.Sec7.PocketStopSide
