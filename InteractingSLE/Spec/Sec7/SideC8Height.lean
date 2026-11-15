/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC8Reference

/-!
# An actual positive-reference cover witness on a surviving incoming side

PROVE-SIDE-COLLAR2. The old own height is the only analytic height input.
The incident half-disc, transition, inherited zero lift, exact word transport
and live reference event are derived. This covers the surviving-incoming
case; newly exposed sides still require their source own heights and access
selection. No increment law is proved or assumed in this pathwise step.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C
  Sec7.PocketStopWallsFin

variable {Ω : Type} [MeasurableSpace Ω]

/-- Exact native cover data at a surviving incoming access, from its
earlier reference's own height. No current mean or current boundary height
appears in the hypotheses. -/
theorem reference_incoming_cover_witness_of_own_height
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) (e : Late.SideData Ω) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) (s q : ℝ≥0)
    (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω))
    (hVisit : d.curve ω s ∈ (j.target i d).domain ω)
    (hHull : regHull d.driver d.lifetime s ω =
      QuantumZipper.fwdHull (fun r : ℝ => d.driver r.toNNReal ω) s)
    (hOrder : (j.visitCapacity d ω s).toNNReal ≤ q)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q' : ℝ} (hqq' : (q : ℝ) < q')
    (hEq : EqOn (fun r : ℝ => segDriver ((j.target i d).curve ω) r.toNNReal) W (Icc 0 q'))
    {x : ℝ} {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol W x q a)
    (hx : x ∉ forceJumpSet ((j.target i d).marksL ω) ((j.target i d).marksR ω))
    (hOldJump : (a (j.visitCapacity d ω s).toNNReal).re ∉
      (j.target i d).jumps (j.visitCapacity d ω s).toNNReal ω)
    (hNowJump : (a q).re ∉ (j.target i d).jumps q ω) (vB : ℂ → ℝ)
    (hOwn : Tendsto (sideMean (j.target i d).kappa (j.referenceVisitChart i d ω s)
        (j.target i d).harmonic vB)
      (𝓝[H] ((a (j.visitCapacity d ω s).toNNReal).re : ℂ))
      (𝓝 (j.nativeSideWord i d e (j.visitCapacity d ω s).toNNReal ω
        (a (j.visitCapacity d ω s).toNNReal).re))) :
    let p := (j.visitCapacity d ω s).toNNReal
    let old := j.referenceVisitChart i d ω s
    let current := relChart (j.target i d).baseChart (j.target i d).curve q ω
    ∃ ε : ℝ, 0 < ε ∧ ω ∈ j.referenceVisitEvent i d s q ∧
      old.2.1 '' (H ∩ ball ((a p).re : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
      Tendsto (fun z => old.1 (current.2.1 z))
        (𝓝[H] ((a q).re : ℂ)) (𝓝 ((a p).re : ℂ)) ∧
      Tendsto (fun z => vB (current.2.1 z) + (j.target i d).harmonic (current.2.1 z) +
        chiC (j.target i d).kappa * old.2.2 (current.2.1 z))
        (𝓝[H] ((a q).re : ℂ)) (𝓝 (j.nativeSideWord i d e q ω (a q).re)) ∧
      Tendsto (fun z => current.2.2 (current.2.1 z) - old.2.2 (current.2.1 z))
        (𝓝[H] ((a q).re : ℂ)) (𝓝 0) := by
  intro p old current
  obtain ⟨ε, hε, hCollar, hTransition, hLift, hWord⟩ :=
    reference_incoming_geometry_and_word hj hRc hLc e hω s q hOrder hW hW0 hqq' hEq
      ha hx hOldJump hNowJump
  have hp : (p : ℝ≥0∞) < capLife ((j.target i d).curve ω) :=
    (ENNReal.coe_le_coe.2 hOrder).trans_lt hq
  have hOld := isDomainChart_relChart_of_ready hj hRc hLc hω hp
  have hCurrent := isDomainChart_relChart_of_ready hj hRc hLc hω hq
  have hInclusion := relChart_dom_antitone (isDomainChart_baseChart hj hRc hLc hω).1
    (isDrivenCurve_target hj ω hω) hq hOrder
  have hHeight := tendsto_reference_height_at_incident_access hOld.1 hCurrent.1
    hInclusion hTransition hOwn
  rw [hWord] at hHeight
  exact ⟨ε, hε, ⟨hω, hq, hVisit, hOrder, hHull⟩, hCollar, hTransition, hHeight, hLift⟩

end InteractingSLE.Wire.Current.SideTest
