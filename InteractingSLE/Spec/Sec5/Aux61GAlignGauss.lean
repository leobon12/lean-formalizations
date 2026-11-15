/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GAlignZero
import InteractingSLE.Spec.Sec5.Aux61GWordGauss

/-! # The initial Gaussian law for the concrete source construction

Only hitting measurability of the initial marked set and its containment
of the physical union remain inputs. All field, locality, record, raw-code
and chart facts are supplied by the source coupling and restart facts.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting Aux61Marks Aux61ChLoc
open Aux61ULoc LawUnique GlueCond WholeField
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
include hR

/-- Initial locality on the actual theta-glued source space follows from
UNIONLOC and containment; no later MARKS facts or initial data are used. -/
theorem source_initial_locality (i : F.ι)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hcontains : ∀ᵐ p ∂S.μ, unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
      (fun p => capacityRule (F.chart i) (F.start i) 0
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
        (S.marksData F).baseSets i 0 p) :
    IsHistoryAvoidanceLocal ((S.marksData F).baseMarks i 0)
      ((S.marksData F).baseSets i 0) (S.marksData F).cfield S.μ := by
  have hraw := isHistoryAvoidanceLocal_unionAt_rule_cfGlueT S.own.coupling S.κ_pos
    S.own_infinite S.theta_bounds S.counterflow S.theta_field_law S.kernel_law
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
    (rationalTime S.s) (measurable_capacityRule (hR.chart_measurable i) (F.start i) 0)
    (isGalmarinoRule_capacityRule (F.chart i) (F.start i) 0)
  rw [← S.theta_measure] at hraw
  exact Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hraw.nullMarks hsets hcontains

/-- The actual source coupling constructs an initial Gaussian mean before
any initial boundary or cutoff data have been supplied. -/
theorem exists_source_initialGauss (i : F.ι)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hcontains : ∀ᵐ p ∂S.μ, unionAt (fun p => cfHullQ (rationalTime S.s) p.2)
      (fun t p => Sec7.PocketStopWallsFin.regHull S.own.W S.life t p.1)
      (fun p => capacityRule (F.chart i) (F.start i) 0
        (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) p ⊆
        (S.marksData F).baseSets i 0 p) :
    ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      @IsChartGaussAt (S.Ω × HistorySpace 0 0) _
        ((S.marksData F).β i) ((S.marksData F).mβ i)
        S.μ ((S.marksData F).Z i) ((S.marksData F).B i)
        ((S.marksData F).code i) 0 ((S.marksData F).sigma i 0) g := by
  let D := S.marksData F
  have hX := S.own.coupling.2.2.2.1
  apply Aux61GWord.exists_initialGauss_of_physical_marks D i
    (measurable_down (hR.selected_measurable i)) (hR.spec i) (hR.open_window i)
    (hR.zero_window i) (hR.landing i) (hR.injective_path i) (hR.continuous_lift i)
    (hR.harmonic_lift i) (S.own.coupling.2.1.comp measurable_fst)
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR).1
    (source_zero_field S F) nullMarks_le
    (sourceHistory_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR hX i 0).comap_le
    (source_zero_code_marks S F hR i)
    (sourceEvent_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR i 0)
    (sourceChart_marks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR hX i 0)
    (hsets.mono nullMarks_le le_rfl)
    (sourceSets_closed F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life S.κ S.ownField hR.spec i 0)
    (source_initial_locality S F hR i hsets hcontains)
  exact Eventually.of_forall fun p hp hq => sourceSets_geometry F (rationalTime S.s)
    S.own.W S.own.VL S.own.VR S.life S.κ S.ownField hR.spec i 0 p ⟨hp, hq⟩

end InteractingSLE.Sec5.Aux61GAlign
