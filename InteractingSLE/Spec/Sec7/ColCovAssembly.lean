/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovFresh
import InteractingSLE.Spec.Sec7.ColCovIncoming
import InteractingSLE.Spec.Sec7.SideC13Collar
import InteractingSLE.Spec.Sec7.SideC11Normalize

/-!
# Theorem 1.2's collar: the late positive cover `VisitReferenceHeightCoverPosExc … X`, with `X` finite

Packet PROVE-COLLAR-COVER. The late reference-height cover (SIDE-COLLAR2's `hCover`) assembled from R5-WALL's
three-piece split (`Wire.visitReferenceHeightCoverPosExc_of_wall_split`, rulings R86, R86a):

* `colCovExc` (def): the exceptional physical set `X = lateExc ∪ lateOuterExc` — the current tip `η(T⁰(q))` and the
  opening point of a bounded pocket (`refExc`) or the tip alone (`refExcInf`), and the first- or last-visit attachments
  at `T⁰(q)` and `0` (`outerExc` / `outerExcInf`); **finite** (`colCovExc_finite`);
* `visitReferenceAmbientCoverPosExc_of_hull`: the hull-landing cover (R5-REFCHART's corrected form) gives the split's
  `hExposed` piece;
* **`visitReferenceHeightCoverPosExc_of_liftGeom`**: the cover from the initial mean formula, R5-LIFT2's late current
  geometry `R5Lift.LateLiftCurGeom` and the outer collars' geometry `LateOuterLiftGeom`, for every side data whose
  phase is `χ·2π lateCurPhaseInt + offset` (the incoming wall piece is PROVED, `ColCovIncoming`);
* **`visitReferenceHeightCoverPosExc_colCov`**: the same from the two shared named inputs `LateSeedLand`
  (PROVE-R5-FRESHTIP) and `LateOuterRefl` (PROVE-WALL-ORDER);
* **`lateSideCollarExc_colCov`**: SIDE-COLLAR2's collar `LateSideCollarExc` for the original-reference side data with
  `X = colCovExc`, from its source inputs `hSource`/`hBranch` and the two shared inputs (the cover's initial formula is
  derived from `hSource`/`hBranch`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketStopWallsFin
  R5Ref R5Lift
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The exceptional physical set of the late cover**: R5-REFCHART's `lateExc` (current tip, bounded pocket's
opening point) and R5-WALL's `lateOuterExc` (the attachments at the left stop and `0`). -/
def colCovExc (d : WordObjects Ω) : SideTest Ω → ℝ≥0 → Ω → Set ℂ :=
  fun j q ω => lateExc j d q ω ∪ lateOuterExc j d q ω

/-- **The exceptional set is finite** (at most five points). -/
theorem colCovExc_finite (d : WordObjects Ω) (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) : (colCovExc d j q ω).Finite :=
  (lateExc_finite j d q ω).union (lateOuterExc_finite j d q ω)

/-- **The split's `hExposed` piece from the hull-landing cover**: R5-REFCHART's `VisitReferenceAmbientCoverPosExcHull`
with exceptional set `E ⊆ X` gives SAMETIME's `VisitReferenceAmbientCoverPosExc` with exceptional set `X ∪ Cᶜ`. -/
theorem visitReferenceAmbientCoverPosExc_of_hull (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (s : SideTest Ω → ℕ → ℝ≥0) {E X : SideTest Ω → ℝ≥0 → Ω → Set ℂ}
    (hEX : ∀ j q ω, E j q ω ⊆ X j q ω) (h : VisitReferenceAmbientCoverPosExcHull i d side s E) :
    VisitReferenceAmbientCoverPosExc i d side s (fun j q ω => X j q ω ∪ ((j.target i d).domain ω)ᶜ) := by
  intro j hj target e zL zR q hq
  filter_upwards [h j hj q hq] with ω hω hE hlive current ξ hξ hXξ
  have hC : extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω := not_not.1 fun hC => hXξ (Or.inr hC)
  exact hω hE hlive ξ hξ (fun h' => hXξ (Or.inl (hEX j q ω h'))) hC

/-- **The pair-wall facts from the walls' facts** (`pairWallFamily j j d = ![R, L_seed, L_seed]`). -/
theorem pairWallFamily_facts (d : WordObjects Ω) (P : Measure Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hR0 : ∀ ω, d.rightWall ω 0 = 0) (hL0 : ∀ seed ω, d.leftWall seed ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[P] fun ω => f (h₀ ω))
    (hdetL : ∀ seed t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall seed ω t) =ᵐ[P] fun ω => f (h₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall h₀ P)
    (hlocL : ∀ seed, Sec6.IsEntranceHistoryLocal (d.leftWall seed) h₀ P) (j : SideTest Ω) :
    (∀ k ω, Continuous (pairWallFamily j j d k ω)) ∧ (∀ k ω, pairWallFamily j j d k ω 0 = 0) ∧
      (∀ k t, Measurable fun ω => pairWallFamily j j d k ω t) ∧
      (∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => pairWallFamily j j d k ω t) =ᵐ[P] fun ω => f (h₀ ω)) ∧
      ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k) h₀ P := by
  refine ⟨fun k ω => ?_, fun k ω => ?_, fun k t => ?_, fun k t => ?_, fun k => ?_⟩ <;> fin_cases k
  · exact hRc ω
  · exact hLc _ ω
  · exact hLc _ ω
  · exact hR0 ω
  · exact hL0 _ ω
  · exact hL0 _ ω
  · exact hRm t
  · exact hLm _ t
  · exact hLm _ t
  · exact hdetR t
  · exact hdetL _ t
  · exact hdetL _ t
  · exact hlocR
  · exact hlocL _
  · exact hlocL _

/-- **The late cover from the lift geometry** (references at the rational original times, `X = colCovExc`): R5-WALL's
three-piece split with the incoming wall piece PROVED (`visitReferenceIncomingWallCoverPosExc_rational`), the exposed
wall piece from `LateOuterLiftGeom` and the hull piece from `R5Lift.LateLiftCurGeom`, for every side data whose phase
is `χ·2π lateCurPhaseInt + offset`. -/
theorem visitReferenceHeightCoverPosExc_of_liftGeom (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ j : SideTest Ω, j.Ready d → ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ j : SideTest Ω, j.Ready d → ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j : SideTest Ω, j.Ready d → ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hHarm : EqOn d.harmonic d.coupledMean H) (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b)
    (hFormula : InitialPocketMeanFormula i d side G)
    (hGeom : LateLiftCurGeom i d) (hOuterGeom : LateOuterLiftGeom i d (colCovExc d))
    (hside : ∀ j q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side j).offset) :
    VisitReferenceHeightCoverPosExc i d side (fun _ => rationalOriginalTime) (colCovExc d) := by
  have hpath := hCoupling.1.2.2.2.2
  have hOuter := visitReferenceHeightCoverOuterPosExc_of_liftWord i d side (colCovExc d) hTransport hTranslate hu
    hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal hRc hLc hHarm (fun _ _ _ => subset_rfl)
    (lateOuterLiftWord_of_curInt i d _ hRc hLc hpath hxL₀ hxR₀ hGeom hOuterGeom side hside)
  have hHull := visitReferenceAmbientCoverPosExcHull_of_liftWord i d side (colCovExc d) hRc hLc hCoupling
    (lateAmbientLiftWord_of_curInt i d _ hRc hLc hpath hxL₀ hxR₀ hGeom side hside)
  have hExposed := visitReferenceAmbientCoverPosExc_of_hull i d side (fun _ => rationalOriginalTime)
    (X := colCovExc d) (fun j q ω => union_subset subset_union_left subset_rfl) hHull
  exact visitReferenceHeightCoverPosExc_of_wall_split i d side G _ (colCovExc d) hTransport hTranslate hu hh
    hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal hRc hLc hRm hLm hHarm hFormula
    (visitReferenceIncomingWallCoverPosExc_rational i d _) hOuter hExposed

/-- **The late cover from the two shared named inputs** (`X = colCovExc`, finite): the seed-interval landings at the
late pockets (`LateSeedLand`, PROVE-R5-FRESHTIP) and the outer collars' `K_s`-landing (`LateOuterRefl`,
PROVE-WALL-ORDER), for every side data whose phase is `χ·2π lateCurPhaseInt + offset`. -/
theorem visitReferenceHeightCoverPosExc_colCov (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ j : SideTest Ω, j.Ready d → ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ j : SideTest Ω, j.Ready d → ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j : SideTest Ω, j.Ready d → ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hHarm : EqOn d.harmonic d.coupledMean H) (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b)
    (hFormula : InitialPocketMeanFormula i d side G)
    (hSeed : LateSeedLand i d) (hRefl : LateOuterRefl i d (colCovExc d))
    (hside : ∀ j q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side j).offset) :
    VisitReferenceHeightCoverPosExc i d side (fun _ => rationalOriginalTime) (colCovExc d) :=
  visitReferenceHeightCoverPosExc_of_liftGeom i d side G hTransport hTranslate hu hh hCoupling hu' hKilled hLife
    hCont hStart hMeas hDetermined hLocal hRc hLc hRm hLm hHarm hxL₀ hxR₀ hFormula
    (lateLiftCurGeom_of_seedLand hRc hLc hSeed) (lateOuterLiftGeom_of_seedLand _ hRc hLc hCoupling hLife hSeed hRefl)
    hside

/-- **SIDE-COLLAR2's collar with the cover supplied** (`X = colCovExc`, finite): the late-side collar
`LateSideCollarExc` for the original-reference side data at the rational original times, from SIDE-COLLAR2's source
inputs `hSource`/`hBranch` (which also give the cover's initial mean formula) and the two shared named inputs, for
every side data whose phase is `χ·2π lateCurPhaseInt + offset`. -/
theorem lateSideCollarExc_colCov (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (side : SideTest Ω → Late.SideData Ω) (G₀ : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
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
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤) (hxL₀ : ∀ a, d.xL a ≤ 0) (hxR₀ : ∀ b, 0 ≤ d.xR b)
    (hSeed : LateSeedLand i d) (hRefl : LateOuterRefl i d (colCovExc d))
    (hside : ∀ j q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side j).offset)
    (hSource : InitialPocketConjugateFlowMean i d G₀
      (fun j => j.canonicalInitialFlowMean i d) n b)
    (hBranch : ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂d.measure,
      ω ∈ (j.target i d).event →
        (side j).offset = b j + 2 * π * chiC (16 / i.kappa) * (1 - (n j ω : ℝ))) :
    LateSideCollarExc i d
      (fun j => ((side j).withVisitLifts i j d rationalOriginalTime).withOriginalReferences j d hKilled
        rationalOriginalTime)
      (colCovExc d) := by
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω) := by
    simpa only [hScale, hCoeff] using hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω) := by
    simpa only [hShift] using hTr
  have hFrame := initialPocketFlowFrame_of_conjugateMean i d side G₀ (fun j => j.canonicalInitialFlowMean i d) n b
    hT' hTr' hu₀ hu₁.1 hHarm hRc hLc hSource hBranch
  have hFormula := (initialPocketFlowFrame_canonical_iff_meanFormula i d side (initialTransportedMeans i d G₀)
    hRc hLc).1 hFrame
  have hpw := pairWallFamily_facts d d.measure (centredField d.field d.originalMean) hRc hLc hR0 hL0 hRm hLm hdetR
    hdetL hlocR hlocL
  have hCover := visitReferenceHeightCoverPosExc_colCov i d side (initialTransportedMeans i d G₀) hT hTr hu₀ hh
    hCoupling hu₁ hKilled hLife (fun j _ => (hpw j).1) (fun j _ => (hpw j).2.1) (fun j _ => (hpw j).2.2.1)
    (fun j _ => (hpw j).2.2.2.1) (fun j _ => (hpw j).2.2.2.2) hRc hLc hRm hLm hHarm hxL₀ hxR₀ hFormula hSeed hRefl
    hside
  exact lateSideCollarExc_originalReferences_of_conjugateMean_walls i d side G₀ n b hT hTr hScale hCoeff hShift hu₀
    hh hu₁ hHarm hKilled (fun _ => rationalOriginalTime) (colCovExc d)
    (fun _ => ⟨Denumerable.eqv ℚ 0, rationalOriginalTime_eqv_zero⟩) hRc hLc hRm hLm hR0 hL0 hηm hdetR hdetL
    hlocR hlocL hCoupling hLife hCover hSource hBranch

end InteractingSLE.Sec7.ColCov
