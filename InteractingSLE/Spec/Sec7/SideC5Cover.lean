/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Data
import InteractingSLE.Spec.Sec7.SideC4Lift
import InteractingSLE.Spec.Sec7.SideC5Slices

/-!
# The positive-capacity reference-height cover off exceptional physical fibres

PROVE-SIDE-COLLAR2 continuation. Only a surviving incident old half-disc is
required. The actual original reference chart and its lift are installed,
and the inherited lift difference is zero by Aux. 57. There is no whole-ball
filled-set equality, reflected map, boundary logarithm or selected integer
in the remaining cover. The exact old heights and force-word identification
are still explicit mathematics, as is selection at fixed relative capacity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopSide Sec7.PocketStopWallsFin
  Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C Sec7.Aux119Heights

/-- Remaining pathwise original-reference selection, own-chart height and
force-word equality, only off exceptional physical fibres. No current-height
limit or inherited lift limit is a premise. This sufficient cover is not
asserted for the source configuration. -/
def VisitReferenceHeightCoverPosExc {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q → ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ r, IsLocalSetMean (j.capacityReference i d (s j r))
      target.zeroField d.measure (gB r)) →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        ∃ (r : ℕ) (x ε b : ℝ), let old := j.referenceVisitChart i d ω (s j r);
          d.curve ω (s j r) ∈ target.domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧ 0 < ε ∧
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
          Tendsto (fun z => old.1 (current.2.1 z))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (sideMean target.kappa old target.harmonic
            (harmRep (gB r ω) (H \ j.capacityReference i d (s j r) ω)))
            (𝓝[H] (x : ℂ)) (𝓝 b) ∧
          b = forceBoundaryData target.kappa target.rhoL target.rhoR
            (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
              target.marksL a q ω - segDriver (target.curve ω) q)
            (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
              target.marksR a q ω - segDriver (target.curve ω) q)
            ξ + e.phase q ω * (Ioo
              (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                segDriver (target.curve ω) q)
              (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                segDriver (target.curve ω) q)).indicator 1 ξ - e.offset

/-- The source-shaped incident half-disc cover supplies the native cover
off exceptional fibres. The two charts, reference-domain identification,
current reference-height limit and ZERO inherited lift difference are proved. -/
theorem lateSideCoverAtExc_visitReferences
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCover : VisitReferenceHeightCoverPosExc i d side s X) (q : ℝ≥0) (hqPos : 0 < q) :
    LateSideCoverAtExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q) X q := by
  intro j hj target refs zL zR gB hgB
  have hSet := visit_references_liveExt (i := i) hj hKilled (side j) (s j)
  have hgB' : ∀ r, IsLocalSetMean (j.capacityReference i d (s j r))
      (j.target i d).zeroField d.measure (gB r) := by
    intro r
    have h := hgB r
    rw [SideTest.target_measure, hSet r] at h
    exact h
  rw [SideTest.target_measure]
  filter_upwards [ae_regHull_eq hCoupling hLife, hCover j hj q hqPos gB hgB']
    with ω hHull hAccess hA hq ξ hξ hξX
  obtain ⟨r, x, ε, b, hVisit, hOrder, hε, hCollar, hTransition, hHeight, hWord⟩ :=
    hAccess hA hq ξ hξ hξX
  have hOld := Current.SideTest.isDomainChart_capacityReference_at_visit
    hj hRc (hLc j.seed) hA (s j r) hVisit (hHull (s j r))
  have hCurrent := Current.SideTest.isDomainChart_relChart_of_ready
    hj hRc (hLc j.seed) hA hq
  have hIncl := relChart_dom_antitone (Current.SideTest.isDomainChart_baseChart
    hj hRc (hLc j.seed) hA).1 (Current.SideTest.isDrivenCurve_target hj ω hA) hq hOrder
  have hRef := tendsto_reference_height_at_incident_access hOld.1 hCurrent.1
    hIncl hTransition hHeight
  have hZero := Current.SideTest.tendsto_referenceVisit_lift_sub_zero
    hj hRc (hLc j.seed) hA hq hOrder hε hCollar hTransition
  refine ⟨r, x, ε, b, 0, ⟨hA, hq, hVisit, hOrder, hHull (s j r)⟩,
    hε, hCollar, hTransition, ?_, hZero, ?_⟩
  · rw [← hSet r] at hRef
    exact hRef
  · simpa only [target, refs, zL, zR, Late.SideData.withVisitReferences,
      Late.SideData.withOriginalReferences, mul_zero, add_zero] using hWord

end InteractingSLE.Wire
