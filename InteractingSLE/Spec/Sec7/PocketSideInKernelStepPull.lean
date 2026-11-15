/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.MarkovChart

/-!
# The full conditional residual law in an old random chart

PROVE-POCKET-SIDEIN. Transport the complete Gaussian law, for every test,
through a chart retained by the conditioning record. The physical domain
may be a later subdomain of that chart. This is independent of the boundary
heights and hence of the margins of an R.7 configuration.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A random retained chart pulls a measurable distribution to a measurable
distribution. Only the forward chart and its domain events are needed. -/
theorem measurable_pullField_of_retained_chart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X) :
    Measurable fun ω => Chart.pullField (hc ω) (X ω) := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  exact RandomTest.measurable_apply_of_forall_measurable hX
    (fun z => Chart.measurable_pushTest_apply hc hdom hfwd φ z)

/-- The full, extended-by-zero conditional field law transports to the
old chart's preimage domain. No support restriction is imposed on the test. -/
theorem isCondZeroBoundaryGFF_pullField_subdomain
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hℋ : ℋ ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H)
    (hUD : ∀ ω, IsOpen (U ω \ (c ω).dom))
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hLaw : IsCondZeroBoundaryGFF P ℋ U X) :
    IsCondZeroBoundaryGFF P ℋ (fun ω => Restart.MarkovChart.chartPre (c ω) (U ω))
      (fun ω => Chart.pullField (hc ω) (X ω)) := by
  intro φ
  have hTest : ∀ z, Measurable[ℋ] fun ω => Chart.pushTest (hc ω) φ z := fun z =>
    @Chart.measurable_pushTest_apply Ω ℋ c hc hdom hfwd φ z
  have h := RandomTest.condExp_cexp_apply_ae_eq hℋ hX
    (Ψ := fun ω ψ => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) ψ ψ) : ℝ) : ℂ))
    (fun ω => RandomTest.exists_zbExtLaw (U := ⟨U ω, hUo ω⟩) (hUH ω)) hLaw hTest
  simp only [Chart.pullField_apply]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [Restart.MarkovChart.zeroGFFTestCov_pushTest_chartPre (hc ω) (hUo ω) (hUD ω) φ φ]

end InteractingSLE.Sec7.PocketStopSide
