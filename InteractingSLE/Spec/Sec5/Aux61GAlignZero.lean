/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceFlow
import InteractingSLE.Spec.Sec5.Aux61GWordZero

/-! # Initial aliveness for the actual retained source record

The selected record event and the physical restart event agree only almost
surely. This suffices to record the zero-time code, without extending the
physical stop hypothesis beyond its stated selected event.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GAlign
open Aux61SlitW Aux61SlitW.SourceSetting
open Aux61Marks Aux61FibData Aux61GInst LawUnique GlueCond
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    (μ := S.μ) S.κ)
include hR

/-- Aliveness at zero is exactly the selected retained-record event, up to
the source null set. Neither event is identified pointwise with the other. -/
theorem source_zero_alive_iff (i : F.ι) : ∀ᵐ p ∂S.μ,
    (0 : ℝ≥0∞) < ((S.marksData F).code i p).life ↔
      sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := by
  filter_upwards [hR.event_version i, hR.physical_stop i] with p he hs
  constructor
  · intro hp
    have hx := mem_exitEv_of_lt_accessLife (Er := F.event i)
      (c := sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      (ρ := F.path i) (T := F.contact i) (V := (F.data i).V)
      (a := 0) (k := QuantumZipper.chiC S.κ) (h := fun p => S.ownField p.1)
      (q := 0) hp
    exact he ▸ hx.1.1
  · intro hp
    exact Aux61GHist.accessExitCode_life_pos (hR.spec i) (hR.open_window i)
      (hR.zero_window i) (hR.landing i) (hR.injective_path i)
      (Aux61GCont.mem_exitEv_of_contact_or_exit (hs hp).1 (hs hp).2.1 (hs hp).2.2)

/-- The source zero-time raw code is measurable for its completed physical
marks, even before the positive-time record reconstruction is supplied. -/
theorem source_zero_code_marks (i : F.ι) :
    (Aux61FibK.codeFiltration.{u} 0).comap
      (fun p => ULift.up.{u} ((S.marksData F).code i p)) ≤ (S.marksData F).baseMarks i 0 := by
  have hY := measurable_accessExitCode (a := 0) (k := QuantumZipper.chiC S.κ)
    (hR.spec i) (hR.open_window i) (hR.zero_window i) (hR.landing i)
    (hR.injective_path i) (hR.continuous_lift i) (S.own.coupling.2.1.comp measurable_fst)
  apply Aux61GWord.codeFiltration_zero_le_nullMarks
    (Aux61Fib.FibCode.measurable_life.comp hY)
    ((sourceRecord_ruleMarks F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i 0)
      (hR.selected_measurable i))
  exact source_zero_alive_iff S F hR i

omit hR in
/-- The original centered source field is a zero-boundary GFF on the
actual theta-glued probability space. -/
theorem source_zero_field : IsZeroBoundaryGFF upperHalfPlaneOpens
    (S.marksData F).cfield S.μ := by
  change IsZeroBoundaryGFF upperHalfPlaneOpens
    (fun p : S.Ω × HistorySpace 0 0 => WholeField.centredField S.ownField
      (Impl.forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR) p.1) S.μ
  rw [S.theta_measure]
  exact isZeroBoundaryGFF_glued S.own.coupling
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
    S.kernel ((CrossCond.Theta.measurable_cfFieldT S.κ S.θ).comp S.own.coupling.2.1)

end InteractingSLE.Sec5.Aux61GAlign
