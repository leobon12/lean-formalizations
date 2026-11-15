/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideCol2Max
import InteractingSLE.Spec.Sec7.PocketSideInRetainTopology
import InteractingSLE.Spec.Sec7.PhaseContMeas

/-!
# Retained set records for the comparison at a fixed relative capacity

PROVE-SIDE-COLLAR2 continuation. Original-time references use the existing
`eventFilled` normalization on the initial pocket event. The current set is
measurable for the relative prefix; the old reference is measurable for the
walls and its ordinary stopped history. These records can mark their union
before an incident collar is selected. Landed files are unchanged.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 LocalSets PocketStopField PocketCoupling PocketCoord PocketJordan
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketTraversal
  PocketAdapt PocketStopSide PocketWordPerQ PocketStopWallsFin PocketMarks

variable {Ω : Type} [mΩ : MeasurableSpace Ω]
  {i : BothLow} {d : WordObjects Ω} {j : SideTest Ω}

/-- The actual old hull reference, filled outside the pocket selected by its
initial labels. Its normalization does not depend on a later collar event. -/
def capacityReference (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (s : ℝ≥0) : Ω → Set ℂ :=
  eventFilled j.event (j.target i d).domain
    (fun ω => regHull d.driver d.lifetime s ω)

/-- Ready gives measurability of the Jordan coordinate at fixed interior points. -/
theorem measurable_chart_on_domain_of_ready (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) (z : ℂ) :
    Measurable[(j.target i d).walls]
      ({ω | ω ∈ (j.target i d).event ∧ z ∈ (j.target i d).domain ω}.indicator
        fun ω => (j.target i d).chart ω z) := by
  have hCm := measurableSet_domain (i := i) hj hRc hLc z
  rcases hj with ⟨-, -, -, hG, -, -, -, -, hAG, -, -, hJm, -⟩
  rw [target_walls, target_event, target_domain] at hCm
  rw [target_walls, target_event, target_domain, target_chart]
  cases hI : j.infinite
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJm
    exact hJm _ hCm (fun ω hω => hAG hω.1) (fun _ => z) measurable_const
      (fun ω hω => ⟨subset_closure hω.2, fun h =>
        (hG ω (hAG hω.1).1).1.cfPt_openPt_notMem (h ▸ hω.2)⟩)
  · simp only [hI, ↓reduceIte] at hAG hJm
    exact hJm _ hCm (fun ω hω => hAG hω.1) (fun _ => z) measurable_const
      (fun _ hω => subset_closure hω.2)

/-- The current physical filled set is measured by the native relative prefix.
The only path measurability premise is for evaluations of the actual traversal. -/
theorem measurable_activeCompl_prefix_of_ready (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t)
    (hγm : ∀ u, 0 ≤ u → Measurable fun ω : (j.target i d).event =>
      (j.target i d).curve ω u) (q : ℝ≥0) :
    Measurable[locPrefixSigma (j.target i d).walls (j.target i d).event
      (j.target i d).curve q, hittingSigma]
      (activeCompl (j.target i d).event (j.target i d).curve
        (j.target i d).baseChart q) := by
  have hc := isPocketChartOn (i := i) hj hRc hLc
  have h𝓦 : (j.target i d).walls ≤ mΩ := by
    rw [target_walls]
    exact wallsSigma_le (P := d.measure) hRm hLm
  have hA : MeasurableSet[(j.target i d).walls] (j.target i d).event := by
    rw [target_walls, target_event]
    obtain ⟨-, -, -, -, -, -, -, hA, -⟩ := hj
    exact hA
  have hψ : ∀ ω ∈ (j.target i d).event,
      SupercriticalConformalCovariance.IsConformalBijection
        ((j.target i d).chart ω) ((j.target i d).domain ω) H := by
    rw [target_event, target_chart, target_domain]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hJ, -⟩ := hj
    cases hI : j.infinite <;>
      simp only [hI, Bool.false_eq_true, ↓reduceIte] at hJ <;>
      exact fun ω hω => (hJ ω hω).2.2.2.1
  exact PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA
    (isDrivenCurve_target hj) hγm (isOpen_domain hj)
    (fun ω hω => by
      rw [← (hc.1 ω hω).2.1]
      exact (hc.1 ω hω).1.dom_subset)
    hψ (measurableSet_domain hj hRc hLc)
    (measurable_chart_on_domain_of_ready hj hRc hLc)
    (measurableSet_domainIn hj hRc hLc)
    (fun ω hω => ⟨(hc.1 ω hω).1, (hc.1 ω hω).2.1, (hc.1 ω hω).2.2.1⟩) q

/-- The old original-time reference is measured by the walls and the stopped
ordinary history. This remains true even when the relative capacity stop
occurs before the reference time. -/
theorem measurable_capacityReference_stopped [IsProbabilityMeasure d.measure]
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hζ : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤) (s : ℝ≥0) :
    let hs := isStoppingTime_const (drivingFiltration d.measure hX) s
    Measurable[(j.target i d).walls ⊔ hs.measurableSpace, hittingSigma]
      (j.capacityReference i d s) := by
  let hs := isStoppingTime_const (drivingFiltration d.measure hX) s
  have hF : Measurable[hs.measurableSpace, hittingSigma]
      (fun ω => regHull d.driver d.lifetime s ω) := by
    simpa only [WithTop.untopD_coe] using measurable_regHull_stopping hC
      (lt_trans (by norm_num) i.kappa_gt_four) hX hζ hs (fun _ => WithTop.coe_ne_top)
  have hW : (j.target i d).walls ≤ (j.target i d).walls ⊔ hs.measurableSpace :=
    le_sup_left
  have hA : MeasurableSet[(j.target i d).walls] j.event := by
    rw [target_walls]
    obtain ⟨-, -, -, -, -, -, -, hA, -⟩ := hj
    exact hA
  exact measurable_eventFilled_of_ready hj hRc hLc hW (hW _ hA)
    (by rw [target_event]) (hF.mono le_sup_right le_rfl)

end InteractingSLE.Wire.Current.SideTest
