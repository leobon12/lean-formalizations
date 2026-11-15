/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14Frame
import InteractingSLE.Spec.Sec7.SideC14Install
import InteractingSLE.Spec.Wire.T12CtxInitial
import InteractingSLE.Spec.Sec7.SideC11Normalize

/-!
# The word context installs its source frame's offset and initial collar

PROVE-SIDE-COLLAR2. Use the actual counterflow witness of the two-angle
strip system for the field transports. R90's normalized installer removes
the branch-compatibility premise. The named source input below is the
remaining identification of the source extension with the native word.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.SideC12 Sec7.PocketWordIn

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)

/-- The literal normalized installed side has the source initial frame.
Transport coefficients and both fields come from the strip's own witness;
branch compatibility is a conclusion of the normalization. -/
theorem installedFrameSide_initialFrame_of_source
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (n : SideTest Ω → ℤ) (b : SideTest Ω → ℝ)
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hHarm : EqOn x.harmonic (counterflowObjects hS.counterflow).mean H)
    (hRc : ∀ ω, Continuous (x.rightWall ω))
    (hLc : ∀ seed ω, Continuous (x.leftWall seed ω))
    (hSource : InitialPocketConjugateFlowMean i (wordSafeObjects i x hS) G₀
      (fun j => j.canonicalInitialFlowMean i (wordSafeObjects i x hS)) (fun j _ => n j) b) :
    InitialPocketFlowFrame i (wordSafeObjects i x hS)
      (installedFrameSide i x hS side idx (fun j => sourceFrameOffset (16 / i.kappa) (b j) (n j)))
      (initialTransportedMeans i (wordSafeObjects i x hS) G₀)
      (fun j => j.canonicalInitialFlowMean i (wordSafeObjects i x hS)) := by
  let d := wordSafeObjects i x hS
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, -, hu₁⟩ := counterflowObjects_spec hS.counterflow
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω) := by
    simpa only [d, wordSafeObjects, hdual] using hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω) := by
    simpa only [d, wordSafeObjects, hdual, zero_mul] using hTr
  have hFrame := initialPocketFlowFrame_normalized_of_conjugateMean i d side G₀
    (fun j => j.canonicalInitialFlowMean i d) n b hT' hTr' hu₀.1 hu₁.1 hHarm hRc hLc hSource
  exact installedFrameSide_initialFrame i x hS hFrame side idx

/-- The normalized initial frame supplies the actual zero-time collar,
with empty exception set, for the literal installed references. -/
theorem installedFrameSide_collarAtZero_of_source
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (n : SideTest Ω → ℤ) (b : SideTest Ω → ℝ)
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hHarm : EqOn x.harmonic (counterflowObjects hS.counterflow).mean H)
    (hRc : ∀ ω, Continuous (x.rightWall ω))
    (hLc : ∀ seed ω, Continuous (x.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => x.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => x.leftWall seed ω t)
    (hSource : InitialPocketConjugateFlowMean i (wordSafeObjects i x hS) G₀
      (fun j => j.canonicalInitialFlowMean i (wordSafeObjects i x hS)) (fun j _ => n j) b) :
    LateSideCollarAtExc i (wordSafeObjects i x hS)
      (installedFrameSide i x hS side idx (fun j => sourceFrameOffset (16 / i.kappa) (b j) (n j)))
      (fun _ _ _ => ∅) 0 := by
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hFrame := installedFrameSide_initialFrame_of_source i x hS side idx G₀ n b hu₀ hHarm hRc hLc hSource
  have hFormula : InitialPocketMeanFormula i d
      (normalizeInitialOffset side (fun j => sourceFrameOffset (16 / i.kappa) (b j) (n j)))
      (initialTransportedMeans i d G₀) :=
    (initialPocketFlowFrame_canonical_iff_meanFormula i d _ _ hRc hLc).1 hFrame
  rw [installedFrameSide_eq]
  exact installedSide_collarAtZero_of_meanFormula i x hS _ idx
    (initialTransportedMeans i d G₀) hRc hLc hRm hLm hFormula

end InteractingSLE.Wire.T12Ctx
