/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlLate
import InteractingSLE.Spec.Sec7.SideC6Collar

/-!
# The initial/positive collar split with conditioned increment laws

PROVE-SIDE-COLLAR2. R85's conditioned laws suffice at each positive
capacity. The zero reference and initial heights supply the initial
slice independently, as in the landed unconditioned assembly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal
  Sec7.PocketAdapt Sec7.Lemma71C Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PhaseSel Sec7.R5Enl

/-- The fixed-capacity collar uses only the law conditioned on the actual
reference event, including when the reference complement is empty off it. -/
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


/-- The initial own heights and positive cover give the native collar
with the R85 increment laws. No unconditioned law is an input. -/
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
  apply lateSideCollarExc_of_pos_and_zero i d
    (fun j => (side j).withVisitReferences i j d hKilled (s j)) X
  · intro q hq
    exact lateSideCollarAtExc_of_incrementLawsOn i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q) X
      (visit_reference_charts i d side hKilled s hRc hLc) hLaw q
      (lateSideCoverAtExc_visitReferences i d side hKilled s X hRc hLc hCoupling hLife
        hCover q hq)
  · exact lateSideCollarAtZeroExc_of_initialReferenceHeights i d side hKilled
      s X hZero hRc hLc hRm hLm hCoupling hHeight

end InteractingSLE.Wire
