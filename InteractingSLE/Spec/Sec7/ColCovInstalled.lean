/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovAssembly
import InteractingSLE.Spec.Wire.T12CtxLifts
import InteractingSLE.Spec.Supplement.GW3Word
import InteractingSLE.Spec.Sec7.SideC14Offset
import InteractingSLE.Spec.Sec7.SideC14Install

/-!
# The late collar for the literal installed side data of the Theorem 1.2–1.3 tops

Packet PROVE-COLLAR-COVER. The tops' collar input `Wire.T12Asm3.SideCollarInputExc` asks, in every word context, for
pre-side data, an integer phase `wordIdx` and finite exceptional sets `X` with `LateSideCollarExc` for
`T12Ctx.installedSide`. Here, for one word (`d = wordSafeObjects i x hS`):

* **`installedSide_lateSideCollarExc_colCov`**: with a lattice offset `(pre j).offset = m_j · phaseStep` (as in
  WORDCTX's `T12Ctx.exists_installedHullCover_of_liftGeom`), the integer phase `wordIdx := m_j − lateCurPhaseInt` and
  `X := colCovExc d` (finite, `colCovExc_finite`), the installed side data satisfy `LateSideCollarExc`, from
  SIDE-COLLAR2's `hSource`/`hBranch`, the two shared inputs `LateSeedLand`, `LateOuterRefl`, and the physical facts
  of the word context. The coupling, its harmonic extension, the killed driving, the field transports and the
  numerical normalizations of `wordSafeObjects` and the signs of the ambient marks are discharged here;
* `sourceFrameOffset_zero_eq`: with the source boundary constant `b = 0`, R90's normalized offset
  `sourceFrameOffset (16/κ) 0 n = b + 2πχ(16/κ)(1 − n)` is the lattice value `(1 − n) · phaseStep`;
* **`installedSide_lateSideCollarExc_colCov_source`**: the same collar for pre-side data carrying R90's normalized
  offset with `b = 0` and a per-test branch `n j` (R90a's refined tests): `hOffset` and `hBranch` are then discharged,
  and the integer phase is `1 − n j − lateCurPhaseInt`;
* **`installedFrameSide_lateSideCollarExc_colCov`**: the same for SIDE-COLLAR2's R90 installer
  `T12Ctx.installedFrameSide` (definitionally the installed side of the normalized pre-side data).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField PocketWordIn PhaseSel
open Wire.Current.SideTest (rationalOriginalTime)

/-- **The late collar for the installed side data of one word** (`X = colCovExc`, finite): see the module
docstring. -/
theorem installedSide_lateSideCollarExc_colCov {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (pre : SideTest Ω → Late.SideData Ω) (offsetIndex : SideTest Ω → ℤ)
    (hOffset : ∀ j, (pre j).offset = (offsetIndex j : ℝ) * phaseStep (16 / (16 / i.kappa)))
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens) (n : SideTest Ω → Ω → ℤ) (b : SideTest Ω → ℝ)
    (hu₀ : InnerProductSpace.HarmonicOnNhd (wordSafeObjects i x hS).originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hHarm : EqOn (wordSafeObjects i x hS).harmonic (wordSafeObjects i x hS).coupledMean H)
    (hRc : ∀ ω, Continuous ((wordSafeObjects i x hS).rightWall ω))
    (hLc : ∀ seed ω, Continuous ((wordSafeObjects i x hS).leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => (wordSafeObjects i x hS).rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => (wordSafeObjects i x hS).leftWall seed ω t)
    (hR0 : ∀ ω, (wordSafeObjects i x hS).rightWall ω 0 = 0)
    (hL0 : ∀ seed ω, (wordSafeObjects i x hS).leftWall seed ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => (wordSafeObjects i x hS).curve ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (wordSafeObjects i x hS).rightWall ω t) =ᵐ[(wordSafeObjects i x hS).measure]
        fun ω => f (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean ω))
    (hdetL : ∀ seed t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (wordSafeObjects i x hS).leftWall seed ω t) =ᵐ[(wordSafeObjects i x hS).measure]
        fun ω => f (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal (wordSafeObjects i x hS).rightWall
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hlocL : ∀ seed, Sec6.IsEntranceHistoryLocal ((wordSafeObjects i x hS).leftWall seed)
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hLife : ∀ᵐ ω ∂(wordSafeObjects i x hS).measure, (wordSafeObjects i x hS).lifetime ω = ⊤)
    (hSeed : LateSeedLand i (wordSafeObjects i x hS))
    (hRefl : LateOuterRefl i (wordSafeObjects i x hS) (colCovExc (wordSafeObjects i x hS)))
    (hSource : InitialPocketConjugateFlowMean i (wordSafeObjects i x hS) G₀
      (fun j => j.canonicalInitialFlowMean i (wordSafeObjects i x hS)) n b)
    (hBranch : ∀ j : SideTest Ω, j.Ready (wordSafeObjects i x hS) → ∀ᵐ ω ∂(wordSafeObjects i x hS).measure,
      ω ∈ (j.target i (wordSafeObjects i x hS)).event →
        (pre j).offset = b j + 2 * π * chiC (16 / i.kappa) * (1 - (n j ω : ℝ))) :
    LateSideCollarExc i (wordSafeObjects i x hS)
      (T12Ctx.installedSide i x hS pre
        (fun j q ω => offsetIndex j - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω))
      (colCovExc (wordSafeObjects i x hS)) := by
  have : IsProbabilityMeasure (wordSafeObjects i x hS).measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hk : i.kappa ≠ 0 := (lt_trans (by norm_num) i.kappa_gt_four).ne'
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hCoupling : IsOptionalHullCoupling i.kappa (wordSafeObjects i x hS).xL (wordSafeObjects i x hS).xR
      (wordSafeObjects i x hS).rhoL (wordSafeObjects i x hS).rhoR (wordSafeObjects i x hS).measure
      (wordSafeObjects i x hS).filtration (wordSafeObjects i x hS).driver (wordSafeObjects i x hS).forceL
      (wordSafeObjects i x hS).forceR (wordSafeObjects i x hS).brownian (wordSafeObjects i x hS).lifetime
      (wordSafeObjects i x hS).translatedField := by
    simpa only [wordSafeObjects, hdual] using hC
  have hMean : IsBoundedHarmonicExtension
      (forceBoundaryData i.kappa (wordSafeObjects i x hS).rhoL (wordSafeObjects i x hS).rhoR
        (wordSafeObjects i x hS).xL (wordSafeObjects i x hS).xR)
      (forceJumpSet (wordSafeObjects i x hS).xL (wordSafeObjects i x hS).xR)
      (wordSafeObjects i x hS).coupledMean := by
    simpa only [wordSafeObjects, hdual] using hu'
  have hKilled : IsMeasurableKilledDriving (wordSafeObjects i x hS).driver (wordSafeObjects i x hS).forceL
      (wordSafeObjects i x hS).forceR (wordSafeObjects i x hS).lifetime :=
    counterflowObjects_measurable hS.counterflow
  have hside : ∀ j q ω, ((pre j).intPhase (16 / (16 / i.kappa))
      (fun q ω => offsetIndex j - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω)).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i (wordSafeObjects i x hS) j q ω) +
        ((pre j).intPhase (16 / (16 / i.kappa))
          (fun q ω => offsetIndex j - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω)).offset := by
    intro j q ω
    change ((offsetIndex j - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω : ℤ) : ℝ) *
        phaseStep (16 / (16 / i.kappa)) =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i (wordSafeObjects i x hS) j q ω) + (pre j).offset
    rw [hOffset j, hdual]
    simp only [Int.cast_sub, phaseStep]
    ring
  have hCoeff : (wordSafeObjects i x hS).chartConstant = chiC i.kappa := by
    simp only [wordSafeObjects, hdual]
  have hShift : (wordSafeObjects i x hS).translateConstant = 0 := by
    simp only [wordSafeObjects, zero_mul]
  exact lateSideCollarExc_colCov i (wordSafeObjects i x hS)
    (fun j => (pre j).intPhase (16 / (16 / i.kappa))
      (fun q ω => offsetIndex j - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω))
    G₀ n b hT hTr rfl hCoeff hShift hu₀ hh hMean hHarm hKilled hRc hLc hRm hLm hR0 hL0 hηm hdetR hdetL hlocR hlocL
    hCoupling hLife (fun a => Theorem14.GW3Word.flowLineXL_nonpos _ _ a)
    (fun b => Theorem14.GW3Word.flowLineXR_nonneg _ _ b) hSeed hRefl hside hSource hBranch

/-- **R90's normalized offset with `b = 0` is a lattice value**: `sourceFrameOffset (16/κ) 0 n = (1 − n) · phaseStep`
(`χ(16/κ) = −χ(κ)`, `phaseStep κ = −2πχ(κ)`). -/
theorem sourceFrameOffset_zero_eq (i : BothLow) (n : ℤ) :
    sourceFrameOffset (16 / i.kappa) 0 n = ((1 - n : ℤ) : ℝ) * phaseStep (16 / (16 / i.kappa)) := by
  have hk : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  rw [sourceFrameOffset, hdual, Sec4.chiC_sixteen_div hk, phaseStep]
  push_cast
  ring

/-- **The late collar for installed side data with R90's normalized offset** (`b = 0`, per-test branch `n j`;
`X = colCovExc`, finite): the integer phase is `1 − n j − lateCurPhaseInt`; the remaining inputs are SIDE-COLLAR2's
source formula `hSource` (with `b = 0` and the constant branch), the two shared inputs and the physical facts. -/
theorem installedSide_lateSideCollarExc_colCov_source {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (pre : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → ℤ)
    (hpre : ∀ j, (pre j).offset = sourceFrameOffset (16 / i.kappa) 0 (n j))
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hu₀ : InnerProductSpace.HarmonicOnNhd (wordSafeObjects i x hS).originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hHarm : EqOn (wordSafeObjects i x hS).harmonic (wordSafeObjects i x hS).coupledMean H)
    (hRc : ∀ ω, Continuous ((wordSafeObjects i x hS).rightWall ω))
    (hLc : ∀ seed ω, Continuous ((wordSafeObjects i x hS).leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => (wordSafeObjects i x hS).rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => (wordSafeObjects i x hS).leftWall seed ω t)
    (hR0 : ∀ ω, (wordSafeObjects i x hS).rightWall ω 0 = 0)
    (hL0 : ∀ seed ω, (wordSafeObjects i x hS).leftWall seed ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => (wordSafeObjects i x hS).curve ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (wordSafeObjects i x hS).rightWall ω t) =ᵐ[(wordSafeObjects i x hS).measure]
        fun ω => f (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean ω))
    (hdetL : ∀ seed t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (wordSafeObjects i x hS).leftWall seed ω t) =ᵐ[(wordSafeObjects i x hS).measure]
        fun ω => f (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal (wordSafeObjects i x hS).rightWall
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hlocL : ∀ seed, Sec6.IsEntranceHistoryLocal ((wordSafeObjects i x hS).leftWall seed)
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hLife : ∀ᵐ ω ∂(wordSafeObjects i x hS).measure, (wordSafeObjects i x hS).lifetime ω = ⊤)
    (hSeed : LateSeedLand i (wordSafeObjects i x hS))
    (hRefl : LateOuterRefl i (wordSafeObjects i x hS) (colCovExc (wordSafeObjects i x hS)))
    (hSource : InitialPocketConjugateFlowMean i (wordSafeObjects i x hS) G₀
      (fun j => j.canonicalInitialFlowMean i (wordSafeObjects i x hS)) (fun j _ => n j) (fun _ => 0)) :
    LateSideCollarExc i (wordSafeObjects i x hS)
      (T12Ctx.installedSide i x hS pre
        (fun j q ω => (1 - n j) - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω))
      (colCovExc (wordSafeObjects i x hS)) :=
  installedSide_lateSideCollarExc_colCov i x hS pre (fun j => 1 - n j)
    (fun j => by rw [hpre j, sourceFrameOffset_zero_eq]) G₀ (fun j _ => n j) (fun _ => 0) hu₀ hh hHarm hRc hLc
    hRm hLm hR0 hL0 hηm hdetR hdetL hlocR hlocL hLife hSeed hRefl hSource
    (fun j _ => Eventually.of_forall fun _ _ => by rw [hpre j, sourceFrameOffset])

/-- **The late collar for SIDE-COLLAR2's R90 installer** `T12Ctx.installedFrameSide` with the source offset
`sourceFrameOffset (16/κ) 0 (n j)` (`b = 0`, per-test branch; `X = colCovExc`, finite): the integer phase is
`1 − n j − lateCurPhaseInt`. -/
theorem installedFrameSide_lateSideCollarExc_colCov {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → ℤ)
    (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hu₀ : InnerProductSpace.HarmonicOnNhd (wordSafeObjects i x hS).originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hHarm : EqOn (wordSafeObjects i x hS).harmonic (wordSafeObjects i x hS).coupledMean H)
    (hRc : ∀ ω, Continuous ((wordSafeObjects i x hS).rightWall ω))
    (hLc : ∀ seed ω, Continuous ((wordSafeObjects i x hS).leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => (wordSafeObjects i x hS).rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => (wordSafeObjects i x hS).leftWall seed ω t)
    (hR0 : ∀ ω, (wordSafeObjects i x hS).rightWall ω 0 = 0)
    (hL0 : ∀ seed ω, (wordSafeObjects i x hS).leftWall seed ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => (wordSafeObjects i x hS).curve ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (wordSafeObjects i x hS).rightWall ω t) =ᵐ[(wordSafeObjects i x hS).measure]
        fun ω => f (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean ω))
    (hdetL : ∀ seed t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (wordSafeObjects i x hS).leftWall seed ω t) =ᵐ[(wordSafeObjects i x hS).measure]
        fun ω => f (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal (wordSafeObjects i x hS).rightWall
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hlocL : ∀ seed, Sec6.IsEntranceHistoryLocal ((wordSafeObjects i x hS).leftWall seed)
      (centredField (wordSafeObjects i x hS).field (wordSafeObjects i x hS).originalMean)
      (wordSafeObjects i x hS).measure)
    (hLife : ∀ᵐ ω ∂(wordSafeObjects i x hS).measure, (wordSafeObjects i x hS).lifetime ω = ⊤)
    (hSeed : LateSeedLand i (wordSafeObjects i x hS))
    (hRefl : LateOuterRefl i (wordSafeObjects i x hS) (colCovExc (wordSafeObjects i x hS)))
    (hSource : InitialPocketConjugateFlowMean i (wordSafeObjects i x hS) G₀
      (fun j => j.canonicalInitialFlowMean i (wordSafeObjects i x hS)) (fun j _ => n j) (fun _ => 0)) :
    LateSideCollarExc i (wordSafeObjects i x hS)
      (T12Ctx.installedFrameSide i x hS side
        (fun j q ω => (1 - n j) - lateCurPhaseInt i (wordSafeObjects i x hS) j q ω)
        (fun j => sourceFrameOffset (16 / i.kappa) 0 (n j)))
      (colCovExc (wordSafeObjects i x hS)) :=
  installedSide_lateSideCollarExc_colCov_source i x hS
    (normalizeInitialOffset side fun j => sourceFrameOffset (16 / i.kappa) 0 (n j)) n (fun _ => rfl) G₀ hu₀ hh
    hHarm hRc hLc hRm hLm hR0 hL0 hηm hdetR hdetL hlocR hlocL hLife hSeed hRefl hSource

end InteractingSLE.Sec7.ColCov
