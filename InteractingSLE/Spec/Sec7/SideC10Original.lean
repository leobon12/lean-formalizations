/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC10Mean
import InteractingSLE.Spec.Sec7.SideC10CollarOn
import InteractingSLE.Spec.Sec7.SideLCLattice

/-!
# Initial normalization and the installed original-time references

PROVE-SIDE-COLLAR2. The original-reference installer preserves the supplied
lifts. Choosing the visit lifts before installation gives exactly the
family used in the checked collar theorem; the integer phase operation
commutes with this installation. This is the constructor interface needed
by `T12Asm2.refSide`, whose raw-reference facts remain applicable.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide

/-- Supply the actual visit lifts before installing the original hulls
and records. All other side fields, including the common offset, are inherited. -/
def Late.SideData.withVisitLifts {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (i : BothLow) (j : SideTest Ω) (d : WordObjects Ω)
    (s : ℕ → ℝ≥0) : Late.SideData Ω :=
  { e with lift := fun r ω => (j.referenceVisitChart i d ω (s r)).2.2 }

/-- Installing original references after choosing their visit lifts is
exactly the existing family, with identical records, phase and offset. -/
theorem Late.SideData.withVisitLifts_originalReferences {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (i : BothLow) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : ℕ → ℝ≥0) :
    (e.withVisitLifts i j d s).withOriginalReferences j d hKilled s =
      e.withVisitReferences i j d hKilled s := rfl

/-- The integer phase used by the assembly commutes with the actual
reference installation. It does not alter the supplied visit lifts. -/
theorem Late.SideData.intPhase_originalReferences_withVisitLifts
    {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (i : BothLow) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : ℕ → ℝ≥0) (κ : ℝ) (m : ℝ≥0 → Ω → ℤ) :
    ((e.withVisitLifts i j d s).withOriginalReferences j d hKilled s).intPhase κ m =
      (e.intPhase κ m).withVisitReferences i j d hKilled s := rfl

/-- The initial collar and the positive collar combine for the installed
original-time references. Finite-word inversion is proved; the flow mean's
physical frame, the positive height cover and R85's laws remain named inputs. -/
theorem lateSideCollarExc_originalReferences_of_flowWord_frameOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (θ₁ θ₂ : SideTest Ω → Ω → ℝ → ℝ)
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
    (hWord : InitialPocketFlowWord i d M θ₁ θ₂)
    (hFrame : InitialPocketFlowFrame i d side G M) :
    LateSideCollarExc i d
      (fun j => ((side j).withVisitLifts i j d (s j)).withOriginalReferences j d hKilled (s j))
      X := by
  have hFormula := initialPocketMeanFormula_of_flowWord_frame i d side G M θ₁ θ₂
    hRc hLc hWord hFrame
  exact lateSideCollarExc_visitReferences_of_initialHeightsOn i d side hKilled s X hZero
    hRc hLc hRm hLm hCoupling hLife hLaw hCover
    (initialReferenceHeightsExc_of_meanFormula i d side G hKilled hRc hLc hRm hLm hCoupling
      hFormula X)

end InteractingSLE.Wire
