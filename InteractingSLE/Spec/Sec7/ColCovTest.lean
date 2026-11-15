/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovRefl
import InteractingSLE.Spec.Sec7.SideC7Mean

/-!
# The late positive cover one test at a time (for R90a's refined branch tests)

Packet PROVE-COLLAR-COVER (second round). R90a's refined binder (SIDE-COLLAR2) asks the positive cover for one
(refined) ready test `j` at a time, with that test's own offset, the other tests being made vacuous by an exceptional
set `univ`. Here the cover is proved testwise, from the initial mean formula of the single test and the phase condition
at that test only; no hypothesis is needed at the other tests:

* `testExc j X` (def): the exceptional sets `X` at `j`, `univ` at every other test;
* **`ae_initialHeights_of_meanFormula_test`**: SIDE-COLLAR2's initial heights
  (`initialReferenceHeightsExc_of_meanFormula`) for one test, from one local mean of the capacity-`0` reference with
  the canonical interior formula;
* **`visitReferenceHeightCoverPosExc_test_of_wall_split`**: R5-WALL's three-piece split for one test, with the
  three pieces read for any side data agreeing with the given one at `j`;
* **`visitReferenceHeightCoverPosExc_test`**: the cover `VisitReferenceHeightCoverPosExc … (testExc j (colCovExc d j))`
  from the single test's mean formula, the seed-interval landings `LateSeedLand` and the phase condition at `j`
  (`LateOuterRefl` is PROVED, `lateOuterRefl_of_subset`);
* **`physCtx_cover_test`**: the same for a word of the tops' physical context (`T12Asm3.PhysCtx`), every physical
  premise discharged (as in `sideCollarInputExc_of_colCov`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketStopWallsFin
  R5Ref R5Lift Aux119Heights
open Wire.Current.SideTest (rationalOriginalTime)

/-- **One test's exceptional sets**: `X` at `j`, `univ` (a vacuous requirement) at every other test. -/
def testExc {Ω : Type} (j : SideTest Ω) (X : ℝ≥0 → Ω → Set ℂ) : SideTest Ω → ℝ≥0 → Ω → Set ℂ := by
  classical
  exact fun j' q ω => if j' = j then X q ω else Set.univ

theorem testExc_self {Ω : Type} (j : SideTest Ω) (X : ℝ≥0 → Ω → Set ℂ) : testExc j X j = X := by
  funext q ω
  simp only [testExc, ↓reduceIte]

theorem testExc_of_ne {Ω : Type} {j j' : SideTest Ω} (X : ℝ≥0 → Ω → Set ℂ) (h : j' ≠ j) (q : ℝ≥0) (ω : Ω) :
    testExc j X j' q ω = Set.univ := by
  simp only [testExc, h, ↓reduceIte]

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The initial heights of one test from its mean formula** (SIDE-COLLAR2's
`initialReferenceHeightsExc_of_meanFormula` for a single test): one local mean `G` of the capacity-`0` reference
with the canonical interior formula (offset of `e`) gives, almost surely on the test, the native word at capacity `0`
as the limit of the base-chart reading. -/
theorem ae_initialHeights_of_meanFormula_test {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d) (e : Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    {G : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G)
    (hGform : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
        chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z =
        j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) - e.offset) :
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ, x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω) (j.target i d).harmonic
        (harmRep (G ω) (H \ j.capacityReference i d 0 ω))) (𝓝[H] (x : ℂ)) (𝓝 (j.nativeSideWord i d e 0 ω x)) := by
  have hSet := j.activeCompl_zero_eq_capacityReference (i := i) hj hRc hLc
  have hgCur := hG
  rw [← hSet] at hgCur
  have hEq := j.ae_initial_reference_eq hj hRc hLc hRm hLm hKilled hCoupling hG hgCur
  filter_upwards [hEq, hG.2.1, hGform] with ω hEq hH hFormulaω hA ξ hξ
  obtain ⟨hv₀, hrep₀⟩ := harmRep_spec hH
  have hEqv := hEq _ hv₀ hrep₀
  have hDriven := SideTest.isDrivenCurve_target hj ω hA
  have hBase := j.isDomainChart_baseChart hj hRc hLc hA
  have hCurrent := j.isDomainChart_relChart_of_ready hj hRc hLc hA (PocketPhaseMeans.capLife_pos hDriven)
  have hPhase := j.initial_phase_window_eq_zero hj hA (e.phase 0 ω) ξ
  show Tendsto _ _ (𝓝 (forceBoundaryData (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR
      (fun a => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL a 0 ω -
        segDriver ((j.target i d).curve ω) 0)
      (fun a => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR a 0 ω -
        segDriver ((j.target i d).curve ω) 0) ξ +
      e.phase 0 ω * (Ioo
        (geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL (Late.leftZero i d j) 0 ω -
          segDriver ((j.target i d).curve ω) 0)
        (geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR (Late.rightZero i d j) 0 ω -
          segDriver ((j.target i d).curve ω) 0)).indicator 1 ξ - e.offset))
  rw [hPhase, add_zero]
  have hlim := ((j.isBoundedHarmonicExtension_initialWordExtension i d ω).2.2 ξ hξ).sub_const e.offset
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hInv := relChart_zero_inv_of_driven (c := (j.target i d).baseChart) hDriven hz
  have hDom : ((j.target i d).baseChart ω).2.1 z ∈ (j.target i d).domain ω := by
    rw [← hBase.2.1]
    exact mem_image_of_mem _ hz
  have hComp : ((j.target i d).baseChart ω).2.1 z ∈ H \ j.capacityReference i d 0 ω := by
    rw [← hSet, ← hCurrent.2.1, ← hInv]
    exact mem_image_of_mem _ hz
  dsimp only [sideMean]
  rw [hEqv hComp, hFormulaω hA _ hDom, hBase.fwd_inv hz]

/-- **R5-WALL's three-piece split for one test** (`Wire.visitReferenceHeightCoverPosExc_of_wall_split` at the test
`j` only, exceptional sets `testExc j X`): the initial heights of `j`, the incoming wall selection, and the exposed
covers (outer and hull) read for any side data `side'` agreeing with `side` at `j`. -/
theorem visitReferenceHeightCoverPosExc_test_of_wall_split (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side side' : SideTest Ω → Late.SideData Ω) (j : SideTest Ω) (hj : j.Ready d)
    (hsj : side' j = side j) (s : SideTest Ω → ℕ → ℝ≥0) (X : ℝ≥0 → Ω → Set ℂ)
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
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hHarm : EqOn d.harmonic d.coupledMean H) {G : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G)
    (hInitial : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ x : ℝ, x ∉ (j.target i d).jumps 0 ω →
      Tendsto (sideMean (j.target i d).kappa ((j.target i d).baseChart ω) (j.target i d).harmonic
        (harmRep (G ω) (H \ j.capacityReference i d 0 ω))) (𝓝[H] (x : ℂ))
        (𝓝 (j.nativeSideWord i d (side j) 0 ω x)))
    (hIncoming : VisitReferenceIncomingWallCoverPosExc i d s (testExc j X))
    (hOuter : VisitReferenceHeightCoverOuterPosExc i d side' s (testExc j X))
    (hExposed : VisitReferenceHeightCoverPosExc i d side' s
      (fun j' q ω => testExc j X j' q ω ∪ ((j'.target i d).domain ω)ᶜ)) :
    VisitReferenceHeightCoverPosExc i d side s (testExc j X) := by
  intro j' hj' target e zL zR q hq gB hgB
  by_cases hjj : j' = j
  · subst hjj
    have hOwn := ae_reference_incoming_own_heights_of_initial hj' hTransport hTranslate hu hh hCoupling hu' hKilled
      hLife hCont hStart hMeas hDetermined hLocal (side j') hHarm (s j') hG hgB hInitial
    have hE := hExposed j' hj' q hq gB hgB
    have hO := hOuter j' hj' q hq gB hgB
    rw [hsj] at hE hO
    filter_upwards [hOwn, hIncoming j' hj' q hq, hE, hO]
      with ω hOwnω hIncomingω hExposedω hOuterω hω hLive current ξ hξ hX
    by_cases hInside : extendFrom H current.2.1 (ξ : ℂ) ∈ target.domain ω
    · exact hExposedω hω hLive ξ hξ (fun h => h.elim hX (fun h => h hInside))
    · by_cases hSeed : ξ ∈ Ioo (geomLW (fun t ω => segDriver ((j'.target i d).curve ω) t) (j'.target i d).marksL
                    (Late.leftZero i d j') q ω - segDriver ((j'.target i d).curve ω) q)
              (geomRW (fun t ω => segDriver ((j'.target i d).curve ω) t) (j'.target i d).marksR
                    (Late.rightZero i d j') q ω - segDriver ((j'.target i d).curve ω) q)
      · exact hOuterω hω hLive ξ hξ hX hSeed hInside
      obtain ⟨r, W, q', x, a, hVisit, hOrder, hW, hW0, hqq', hEq, ha, haξ, hx, hx₀, hxB⟩ :=
        hIncomingω hω hLive ξ hξ hX hSeed
      have hOwnHeight := hOwnω hω r hVisit q hOrder W hW hW0 q' hqq' hEq x a ha hx hx₀ hxB
      obtain ⟨ε, hε, hCollar, hTransition, -, hWord⟩ :=
        reference_incoming_geometry_and_word hj' hRc hLc (side j') hω (s j' r) q hOrder
          hW hW0 hqq' hEq ha hx hxB (by simpa only [haξ, SideTarget.jumps] using hξ)
      rw [haξ] at hTransition hWord
      exact ⟨r, _, ε, _, hVisit, hOrder, hε, hCollar, hTransition, hOwnHeight, hWord⟩
  · refine Eventually.of_forall fun ω _ _ ξ _ hX => absurd ?_ hX
    rw [testExc_of_ne X hjj]
    exact Set.mem_univ _

/-- **The late positive cover for one test** (`X = testExc j (colCovExc d j)`): from the test's initial mean formula
(one local mean `G` of the capacity-`0` reference with the canonical interior formula and the offset of `side j`), the
seed-interval landings `LateSeedLand` and the phase condition `phase = χ·2π lateCurPhaseInt + offset` at `j` only.
The other tests carry no hypothesis (their exceptional sets are `univ`). -/
theorem visitReferenceHeightCoverPosExc_test (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (side : SideTest Ω → Late.SideData Ω) (j : SideTest Ω) (hj : j.Ready d)
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
    {G : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G)
    (hGform : ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
        chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z =
        j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) - (side j).offset)
    (hSeed : LateSeedLand i d)
    (hside : ∀ q ω, (side j).phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j q ω) + (side j).offset) :
    VisitReferenceHeightCoverPosExc i d side (fun _ => rationalOriginalTime) (testExc j (colCovExc d j)) := by
  classical
  let side' : SideTest Ω → Late.SideData Ω := fun j' =>
    if j' = j then side j else withLiftPhase (side j') i.kappa (lateCurPhaseInt i d j')
  have hsj : side' j = side j := by simp only [side', ↓reduceIte]
  have hside' : ∀ j' q ω, (side' j').phase q ω =
      chiC i.kappa * (2 * Real.pi * lateCurPhaseInt i d j' q ω) + (side' j').offset := by
    intro j' q ω
    by_cases h : j' = j
    · subst h
      rw [hsj]
      exact hside q ω
    · have e : side' j' = withLiftPhase (side j') i.kappa (lateCurPhaseInt i d j') := by
        simp only [side', h, ↓reduceIte]
      rw [e]
      rfl
  have hXsub : ∀ j' q ω, lateExc j' d q ω ∪ lateOuterExc j' d q ω ⊆ testExc j (colCovExc d j) j' q ω := by
    intro j' q ω
    by_cases h : j' = j
    · subst h
      rw [testExc_self]
      exact subset_rfl
    · rw [testExc_of_ne _ h]
      exact subset_univ _
  have hRefl := lateOuterRefl_of_subset (i := i) hRc hLc fun j' q ω => subset_union_right.trans (hXsub j' q ω)
  have hGeom := lateLiftCurGeom_of_seedLand hRc hLc hSeed
  have hOuterGeom := lateOuterLiftGeom_of_seedLand _ hRc hLc hCoupling hLife hSeed hRefl
  have hpath := hCoupling.1.2.2.2.2
  have hOuter := visitReferenceHeightCoverOuterPosExc_of_liftWord i d side' _ hTransport hTranslate hu hh hCoupling
    hu' hKilled hLife hCont hStart hMeas hDetermined hLocal hRc hLc hHarm hXsub
    (lateOuterLiftWord_of_curInt i d _ hRc hLc hpath hxL₀ hxR₀ hGeom hOuterGeom side' hside')
  have hHull := visitReferenceAmbientCoverPosExcHull_of_liftWord i d side' (testExc j (colCovExc d j)) hRc hLc
    hCoupling (lateAmbientLiftWord_of_curInt i d _ hRc hLc hpath hxL₀ hxR₀ hGeom side' hside')
  have hExp := visitReferenceAmbientCoverPosExc_of_hull i d side' (fun _ => rationalOriginalTime)
    (X := testExc j (colCovExc d j))
    (fun j' q ω => union_subset (subset_union_left.trans (hXsub j' q ω)) subset_rfl) hHull
  have hExposed := visitReferenceHeightCoverPosExc_of_ambient i d side' _ _ hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal hHarm hExp
  have hInitial := ae_initialHeights_of_meanFormula_test hj (side j) hKilled hRc (hLc j.seed) hRm (hLm j.seed)
    hCoupling hG hGform
  exact visitReferenceHeightCoverPosExc_test_of_wall_split i d side side' j hj hsj _ (colCovExc d j) hTransport
    hTranslate hu hh hCoupling hu' hKilled hLife (hCont j hj) (hStart j hj) (hMeas j hj) (hDetermined j hj)
    (hLocal j hj) hRc (hLc j.seed) hHarm hG hInitial (visitReferenceIncomingWallCoverPosExc_rational i d _) hOuter
    hExposed

/-- **The late positive cover for one test of a word of the tops' physical context** (`X = testExc j (colCovExc d j)`,
`d = wordSafeObjects …`): every physical premise is read from `T12Asm3.PhysCtx` and the word's strip system; the
inputs are the test's initial mean formula, `LateSeedLand` and the phase condition at `j`. -/
theorem physCtx_cover_test {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow)
    (side : SideTest (Ωw index) → Late.SideData (Ωw index)) (j : SideTest (Ωw index))
    (hj : j.Ready (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)))
    {G : Ωw index → DistOn upperHalfPlaneOpens}
    (hG : IsLocalSetMean (j.capacityReference index
        (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) 0)
      (j.target index
        (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))).zeroField
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)).measure G)
    (hGform : let d := wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)
      ∀ᵐ ω ∂d.measure, ω ∈ (j.target index d).event → ∀ z ∈ (j.target index d).domain ω,
        harmRep (G ω) (H \ j.capacityReference index d 0 ω) z + (j.target index d).harmonic z +
          chiC (j.target index d).kappa * ((j.target index d).baseChart ω).2.2 z =
          j.initialWordExtension index d ω (((j.target index d).baseChart ω).1 z) - (side j).offset)
    (hSeed : LateSeedLand index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)))
    (hside : ∀ q ω, (side j).phase q ω = chiC index.kappa * (2 * Real.pi * lateCurPhaseInt index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) j q ω) +
        (side j).offset) :
    VisitReferenceHeightCoverPosExc index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) side
      (fun _ => rationalOriginalTime)
      (testExc j (colCovExc
        (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) j)) := by
  have hS := hC.wordT index
  have : IsProbabilityMeasure
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).measure :=
    inferInstanceAs (IsProbabilityMeasure (Relay.words T12Asm2.cond44Holds baseWord hWordb index).measure)
  have hdual : 16 / (16 / index.kappa) = index.kappa := by
    have hk : index.kappa ≠ 0 := (lt_trans (by norm_num) index.kappa_gt_four).ne'
    field_simp
  obtain ⟨hT, hTr, hCc, hu'⟩ := PocketWordIn.counterflowObjects_spec hS.counterflow
  have hu₀ := hC.hWordu₀ index
  have hvα := hC.hWordvα index
  have hvL := hC.hWordvL index
  have hleft := hC.hWordleft index
  have hright := hC.hWordright index
  have hθ₁ := hC.hWordθ₁ index
  have hθ₂ := hC.hWordθ₂ index
  have hreg := Sec7.WordSafe.isTwoAngle_regTwo hS hleft hright
  have hw := fun q => Sec7.WordSafe.wall_inputs T12Asm2.cond44Holds hreg hleft hright
    (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) (PocketWordIn.positiveSeed_pos q)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) hu₀
    (Sec7.WordSafe.isWallVersion_regTwo hS hleft hright
      StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self hθ₁) hvα)
    (Sec7.WordSafe.isWallVersion_regTwo hS hleft hright
      StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθ₂) (hvL q))
  have hHarm : EqOn (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).harmonic
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).coupledMean H := by
    intro z _
    show (Relay.words T12Asm2.cond44Holds baseWord hWordb index).harmonic z =
      (PocketWordIn.counterflowObjects hS.counterflow).mean z
    rw [hC.harmonic_eq index hS.counterflow]
  have hpw := pairWallFamily_facts
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS)
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).measure
    (centredField (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).field
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).originalMean)
    hvα.continuous (fun q => (hvL q).continuous) hvα.zero (fun q => (hvL q).zero) hvα.measurable
    (fun q => (hvL q).measurable) (hw 1).1 (fun q => (hw q).2.2.1) (hw 1).2.1 (fun q => (hw q).2.2.2)
  exact visitReferenceHeightCoverPosExc_test index _ side j hj hT hTr hu₀.1
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀)
    (by simpa only [wordSafeObjects, hdual] using hCc) (by simpa only [wordSafeObjects, hdual] using hu')
    (PocketWordIn.counterflowObjects_measurable hS.counterflow) hS.lifetime (fun j _ => (hpw j).1)
    (fun j _ => (hpw j).2.1) (fun j _ => (hpw j).2.2.1) (fun j _ => (hpw j).2.2.2.1) (fun j _ => (hpw j).2.2.2.2)
    hvα.continuous (fun q => (hvL q).continuous) hvα.measurable (fun q => (hvL q).measurable) hHarm
    (fun a => Theorem14.GW3Word.flowLineXL_nonpos _ _ a) (fun b => Theorem14.GW3Word.flowLineXR_nonneg _ _ b)
    hG hGform hSeed hside

end InteractingSLE.Sec7.ColCov
