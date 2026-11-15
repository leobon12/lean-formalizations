/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Collar
import InteractingSLE.Spec.Sec7.R5EnlLateInst

/-!
# The literal installed collar with the increment laws discharged

PROVE-SIDE-COLLAR2. Use PROVE-R5-ENLARGED's landed visit-reference
producer. Only the initial source mean and branch normalization remain
in the C12 initial route; the positive cover retains its existing owner.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire

open Current WholeField

/-- The original-reference collar with `hLaw` supplied by the landed
late increment-law theorem. The numerical field normalizations are the
literal ones in `wordSafeObjects`. -/
theorem lateSideCollarExc_originalReferences_of_conjugateMean_walls
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (n : SideTest Ω → Ω → ℤ) (b : SideTest Ω → ℝ)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hScale : d.scale = -(π * chiC (16 / i.kappa)))
    (hCoeff : d.chartConstant = chiC i.kappa) (hShift : d.translateConstant = 0)
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hu₁ : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hZero : ∀ j, ∃ r, s j r = 0)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hR0 : ∀ ω, d.rightWall ω 0 = 0) (hL0 : ∀ seed ω, d.leftWall seed ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ seed t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall seed ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
    (hlocL : ∀ seed, Sec6.IsEntranceHistoryLocal (d.leftWall seed)
      (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCover : VisitReferenceHeightCoverPosExc i d side s X)
    (hSource : InitialPocketConjugateFlowMean i d G₀
      (fun j => j.canonicalInitialFlowMean i d) n b)
    (hBranch : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure,
      ω ∈ (j.target i d).event →
        (side j).offset = b j + 2 * π * chiC (16 / i.kappa) * (1 - (n j ω : ℝ))) :
    LateSideCollarExc i d
      (fun j => ((side j).withVisitLifts i j d (s j)).withOriginalReferences j d hKilled (s j))
      X := by
  have hLaw := lateSideIncrementLawsOn_visitReferences i d side hKilled s hT hTr hu₀ hh hCoupling
    hu₁ hLife hRm hLm hRc hLc hR0 hL0 hηm hdetR hdetL hlocR hlocL
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω) := by
    simpa only [hScale, hCoeff] using hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω) := by
    simpa only [hShift] using hTr
  exact lateSideCollarExc_originalReferences_of_conjugateMeanOn i d side G₀ n b hT' hTr'
    hu₀ hu₁.1 hHarm hKilled s X hZero hRc hLc hRm hLm hCoupling hLife hLaw hCover hSource hBranch

end InteractingSLE.Wire
