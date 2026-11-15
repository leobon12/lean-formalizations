/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14Offset

/-!
# The initial physical frame with its installed source offset

PROVE-SIDE-COLLAR2. R90 removes the branch-compatibility input. The
original flow formula supplies the frame; the offset is its source
value, with the branch chosen for the test by the word construction.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Wire

open Current LocalSets WholeField Sec7 Sec7.SideC12 Sec7.Aux119Heights

/-- The normalized frame, without a branch-compatibility hypothesis. -/
theorem initialPocketFlowFrame_normalized_of_conjugateMean
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (M : SideTest Ω → Ω → ℂ → ℝ) (n : SideTest Ω → ℤ)
    (b : SideTest Ω → ℝ)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd d.coupledMean H)
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hSource : InitialPocketConjugateFlowMean i d G₀ M (fun j _ => n j) b) :
    InitialPocketFlowFrame i d
      (normalizeInitialOffset side (fun j => sourceFrameOffset (16 / i.kappa) (b j) (n j)))
      (initialTransportedMeans i d G₀) M := by
  exact initialPocketFlowFrame_of_conjugateMean i d _ G₀ M (fun j _ => n j) b
    hT hTr hu₀ hu₁ hHarm hRc hLc hSource (normalizeInitialOffset_branch i d side b n)

end InteractingSLE.Wire
