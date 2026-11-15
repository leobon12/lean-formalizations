/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Frame
import InteractingSLE.Spec.Sec7.SideC11Collar

/-!
# The installed collar from original-coordinate initial mean data

PROVE-SIDE-COLLAR2. The physical frame and the flow boundary are supplied
by proved reductions. The original filled-pocket mean and its branch
compatibility remain explicit source inputs. The positive cover and
conditioned increment laws retain their existing owners and interfaces.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire

open Current

/-- The literal installed-reference collar, with the initial frame
transport proved and the remaining original source input named exactly. -/
theorem lateSideCollarExc_originalReferences_of_conjugateMeanOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (n : SideTest Ω → Ω → ℤ) (b : SideTest Ω → ℝ)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd d.coupledMean H)
    (hHarm : EqOn d.harmonic d.coupledMean H)
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
    (hSource : InitialPocketConjugateFlowMean i d G₀
      (fun j => j.canonicalInitialFlowMean i d) n b)
    (hBranch : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure,
      ω ∈ (j.target i d).event →
        (side j).offset = b j + 2 * π * chiC (16 / i.kappa) * (1 - (n j ω : ℝ))) :
    LateSideCollarExc i d
      (fun j => ((side j).withVisitLifts i j d (s j)).withOriginalReferences j d hKilled (s j))
      X := by
  apply lateSideCollarExc_originalReferences_of_canonicalFrameOn i d side
    (initialTransportedMeans i d G₀) hKilled s X hZero hRc hLc hRm hLm hCoupling hLife hLaw hCover
  exact initialPocketFlowFrame_of_conjugateMean i d side G₀
    (fun j => j.canonicalInitialFlowMean i d) n b hT hTr hu₀ hu₁ hHarm hRc hLc hSource hBranch

end InteractingSLE.Wire
