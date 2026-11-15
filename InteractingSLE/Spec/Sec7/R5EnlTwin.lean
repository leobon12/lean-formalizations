/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC7Collar
import InteractingSLE.Spec.Sec7.R5SameClause
import InteractingSLE.Spec.Sec7.R5EnlLate

/-!
# One-line `On` twins of the committed consumers of R.5's clause 4 (ruling R85)

Packet PROVE-R5-ENLARGED (continued). Ruling R85 makes the conditioned increment laws `HasOldChartIncrementLawOn` /
`Wire.LateSideIncrementLawsOn` the targets. The committed consumers that take the old law only pass it to
`PocketStopSide.collar_of_oldChartIncrementLaws`; their twins below are the same proofs with
`R5Enl.collar_of_oldChartIncrementLawsOn` (and the same conclusions):

* PROVE-SIDE-COLLAR2's late collar chain: `Wire.lateSideCollarAtExc_of_incrementLawsOn` (`SideC5Slices`),
  `Wire.lateSideCollarPosExc_visitReferencesOn`, `Wire.lateSideCollarExc_visitReferences_of_initialOn` (`SideC5Collar`),
  `Wire.lateSideCollarExc_visitReferences_of_initialHeightsOn` (`SideC6Collar`),
  **`Wire.lateSideCollarExc_visitReferences_of_initialMeanFormulaOn`** (`SideC7Collar`);
* PROVE-R5-SAMETIME's **`R5Same.r5ClausesOn_of_ambient`** (`R5SameClause`): `R5ClausesOn` with the ambient lifts.

R5-REFCHART's `r5Clauses_of_refHeights(Inf)` is not committed (not importable here); its twin is the same one-lemma
substitution. Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal
  Sec7.PocketAdapt Sec7.Lemma71C Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PhaseSel Sec7.R5Enl

/-- `lateSideCollarAtExc_of_incrementLaws` with the conditioned laws (R85). -/
theorem lateSideCollarAtExc_of_incrementLawsOn {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (old : SideTest Ω → ℕ → Ω → Chart) (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRef : LateSideReferenceCharts i d side old M) (hLaw : LateSideIncrementLawsOn i d side old M)
    (q : ℝ≥0) (hCov : LateSideCoverAtExc i d side old M X q) :
    LateSideCollarAtExc i d side X q := by
  intro j hj _ _ _ _ gB hgB g hg
  refine (collar_of_oldChartIncrementLawsOn (M := M j q) (old := old j)
    (J := fun ω => forceJumpSet
      (fun l => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL l q ω -
        segDriver ((j.target i d).curve ω) q)
      (fun k => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR k q ω -
        segDriver ((j.target i d).curve ω) q) ∪
      {ξ : ℝ | extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∈ X j q ω})
    (SideTest.isDrivenCurve_target hj) (fun ω _ => SideTest.isConformal_baseChart_of_ready hj ω)
    (hRef j hj q) (hLaw j hj q) (fun gB hgB => ?_) gB hgB g hg).mono
    fun ω hω hA hq v hv hvr ξ hξ hξX => hω hA hq v hv hvr ξ fun h => h.elim hξ hξX
  filter_upwards [hCov j hj gB hgB] with ω hω hA hq ξ hξ
  exact hω hA hq ξ (fun h => hξ (Or.inl h)) (fun h => hξ (Or.inr h))

/-- `lateSideCollarPosExc_visitReferences` with the conditioned laws (R85). -/
theorem lateSideCollarPosExc_visitReferencesOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLawsOn i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : VisitReferenceHeightCoverPosExc i d side s X) :
    ∀ q : ℝ≥0, 0 < q → LateSideCollarAtExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X q := by
  intro q hq
  exact lateSideCollarAtExc_of_incrementLawsOn i d
    (fun j => (side j).withVisitReferences i j d hKilled (s j))
    (fun j r ω => j.referenceVisitChart i d ω (s j r))
    (fun j q r => j.referenceVisitEvent i d (s j r) q) X
    (visit_reference_charts i d side hKilled s hRc hLc) hLaw q
    (lateSideCoverAtExc_visitReferences i d side hKilled s X hRc hLc hCoupling hLife
      hCover q hq)

/-- `lateSideCollarExc_visitReferences_of_initial` with the conditioned laws (R85). -/
theorem lateSideCollarExc_visitReferences_of_initialOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLawsOn i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : VisitReferenceHeightCoverPosExc i d side s X)
    (hInitial : LateSideCollarAtExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X 0) :
    LateSideCollarExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X := by
  exact lateSideCollarExc_of_pos_and_zero i d
    (fun j => (side j).withVisitReferences i j d hKilled (s j)) X
    (lateSideCollarPosExc_visitReferencesOn i d side hKilled s X hRc hLc hCoupling hLife
      hLaw hCover) hInitial

/-- `lateSideCollarExc_visitReferences_of_initialHeights` with the conditioned laws (R85). -/
theorem lateSideCollarExc_visitReferences_of_initialHeightsOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
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
    (hHeight : InitialReferenceHeightsExc i d side X) :
    LateSideCollarExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X := by
  exact lateSideCollarExc_visitReferences_of_initialOn i d side hKilled s X hRc hLc hCoupling
    hLife hLaw hCover (lateSideCollarAtZeroExc_of_initialReferenceHeights i d side hKilled
      s X hZero hRc hLc hRm hLm hCoupling hHeight)

/-- **PROVE-SIDE-COLLAR2's full late collar with the conditioned laws** (R85):
`lateSideCollarExc_visitReferences_of_initialMeanFormula` with `hLaw : LateSideIncrementLawsOn …`. -/
theorem lateSideCollarExc_visitReferences_of_initialMeanFormulaOn
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
    (hFormula : InitialPocketMeanFormula i d side G) :
    LateSideCollarExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X := by
  exact lateSideCollarExc_visitReferences_of_initialHeightsOn i d side hKilled s X hZero
    hRc hLc hRm hLm hCoupling hLife hLaw hCover
    (initialReferenceHeightsExc_of_meanFormula i d side G hKilled hRc hLc hRm hLm hCoupling
      hFormula X)

end InteractingSLE.Wire

namespace InteractingSLE.Sec7.R5Same

open LocalSets WholeField Aux119Heights PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop
  PocketWordPerQ PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C R5Phase PocketUnionPt PhaseSel R5Enl

variable {Ω : Type*}

/-- **`R5ClausesOn` on an R.7 test with the ambient lifts** (`r5Clauses_of_ambient` with the conditioned clause 4,
ruling R85). -/
theorem r5ClausesOn_of_ambient {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ}
    {ρR' : Fin mR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
    {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {M : ℕ → Set Ω}
    {old : ℕ → Ω → Chart} {q : ℝ≥0}
    (hXf : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hOld : ∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
      ((old i ω).dom : Set ℂ) = H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω)
    (hLaw : ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
        (centredField h'' u₀') P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) (centredField h'' u₀') P g →
      ∀ i, HasOldChartIncrementLawOn P (M i) (old i) (relChart c γ q) (gB i) g)
    (hCov : R7AmbientCover κ ρL ρR ρL' ρR' P A γ xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ' VL VR δ X M
      old q) :
    R5ClausesOn κ ρL ρR P A γ xL xR c a (centredField h'' u₀') u₀' (fun ω => cfPocket (R ω) (L ω) r)
      (refHull W' ζ') δ X (ambLift W') M old q := by
  refine ⟨hXf, hLattice, hOld, hLaw, fun gB hgB => ?_⟩
  have hH := ae_tendsto_harmRep_refHull hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hCov] with ω hHω hcovω hωA hlive ξ hξ hXξ
  obtain ⟨i, x, r', x', d, z₀, hM, hr, hcol, htr, hz₀, hinv, hev, hx', hfx, hd, hword⟩ :=
    hcovω hωA hlive ξ hξ hXξ
  exact ⟨i, x, r', _, d, hM, hr, hcol, htr, hHω hωA i z₀ hz₀ _ (ξ : ℂ) x' hx' hinv hev hfx, hd, hword⟩

end InteractingSLE.Sec7.R5Same
