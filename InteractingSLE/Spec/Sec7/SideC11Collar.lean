/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC11Normalize
import InteractingSLE.Spec.Sec7.SideC10Original

/-!
# The installed-reference collar with the flow boundary proved

PROVE-SIDE-COLLAR2. The initial flow mean is explicit and its full
boundary input is a theorem. The physical conditional-mean frame is
still a separate premise; wall cover and conditioned increment laws
retain their existing named interfaces and owners.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current

/-- The actual installed-reference collar needs no initial flow-boundary
or cumulative-weight hypothesis. Those hold for the explicit canonical
family. This does not assert the remaining physical frame identification. -/
theorem lateSideCollarExc_originalReferences_of_canonicalFrameOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hZero : ∀ j, ∃ r, s j r = 0)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLawsOn i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : VisitReferenceHeightCoverPosExc i d side s X)
    (hFrame : InitialPocketFlowFrame i d side G (fun j => j.canonicalInitialFlowMean i d)) :
    LateSideCollarExc i d
      (fun j => ((side j).withVisitLifts i j d (s j)).withOriginalReferences j d hKilled (s j))
      X := by
  exact lateSideCollarExc_originalReferences_of_flowWord_frameOn i d side G
    (fun j => j.canonicalInitialFlowMean i d) (fun j => j.initialFlowAngle₁ i d)
    (fun j => j.initialFlowAngle₂ i d) hKilled s X hZero hRc hLc hRm hLm hCoupling hLife
    hLaw hCover
    (initialPocketFlowWord_of_boundary i d _ (initialPocketFlowBoundary_canonical i d)) hFrame

end InteractingSLE.Wire
