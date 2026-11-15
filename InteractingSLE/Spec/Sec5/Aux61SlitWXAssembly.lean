/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXLanding
import InteractingSLE.Spec.Sec5.Aux61SlitWXSelection

/-!
# The normalized R1 source assembled from the remaining named inputs

All chart and basic restart geometry is proved from the selected record
model and the named forward-tip theorem. The remaining window, exit,
comparison and capture inputs retain their exact physical quantifiers.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61Marks Aux61ULoc LawUnique
open WangWu (histLine)
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart)

/-- The reference window and its retained free seed buffer. These are the
window-construction inputs; no restart specification is stored here. -/
structure WindowData where
  open_window : ∀ i, IsOpen (D.data i).V
  zero_window : ∀ i, (0 : ℂ) ∈ (D.data i).V
  clearance : ∀ i, (D.data i).ℓ = clr (D.data i).V
  kappa : ∀ i, (D.data i).κ = S.κ
  reference : ∀ i, Aux61Cov.RefWin (D.data i).κ (D.data i).bR (D.data i).JR (Ioo (D.left i) (D.right i))
  buffer : D.ι → Set ℂ
  gap : D.ι → ℝ
  bounded : ∀ i, Bornology.IsBounded (buffer i)
  window_subset : ∀ i, (D.data i).V ⊆ seedExitWindow (buffer i) (gap i)
  seed : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → ∀ a : ℝ, |a| < gap i →
    boundedInverse (sourceChart (source D h)
      (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉
      oldModelBoundary (counterflowRecord (histLine p.2) (rationalTime S.s))

/-- A finite physical contact or a witnessed window exit. Event membership
and positive contact are proved separately, not included as hypotheses. -/
def PhysicalExit : Prop :=
  ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → D.contact i p < ⊤ ∨
    ∃ v : ℝ≥0, (v : ℝ≥0∞) < D.contact i p ∧
      inPath (D.event i)
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (D.q i))) (D.contact i) p v ∉ (D.data i).V

/-- The retained physical mean comparisons required by the existing
assembly, for this exact normalized chart and its actual marked unions. -/
def ComparisonFacts : Prop :=
  ∀ i, Nonempty (Aux61GAlign.ZeroComparisons
    (S.marksData (cutSource S (withRecordPath S (source D h)))) i)

/-- The two remaining capture inputs. In particular completion is still
required for every selected index; pointwise existence is not substituted. -/
structure CaptureFacts : Prop where
  history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
    sourceRecord (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i
  completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i →
    S.windowEvent p → D.contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < D.contact i p →
      inPath (D.event i)
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (D.q i))) (D.contact i) p v ∈ (D.data i).V) ∧
    ∃ y ∈ Ioo (D.left i) (D.right i), Tendsto
      (inPath (D.event i)
        (sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (D.q i))) (D.contact i) p)
      (𝓝[<] (D.contact i p).toNNReal) (𝓝 (y : ℂ))

variable {D h} (R : ReaderFacts D)
include R

/-- Restart facts independent of either physical comparison interface. -/
theorem ReaderFacts.recordRestartFacts (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h) : RecordRestartFacts S (source D h) where
  selected_measurable := R.selected_measurable
  chart_measurable := fun i => (chart_spec D h i).measurable
  event_measurable := (eventFacts_of_eq_preimage S (source D h) R.selected_measurable fun _ => rfl).1
  contact_measurable := D.measurable_contact
  open_window := V.open_window
  zero_window := V.zero_window
  clearance := V.clearance
  kappa := V.kappa
  reference := V.reference
  event_version := (eventFacts_of_eq_preimage S (source D h) R.selected_measurable fun _ => rfl).2
  physical_stop := fun i => by
    filter_upwards [hExit i, r1_contact_fields_of_tipOff D h R.tipOff i] with p hx ht he
    exact ⟨he, (ht he).2.1, hx he⟩
  geometric := fun i => by
    filter_upwards [R.ae_restartPoint h hTip i, R.ae_geometry h i,
      R.ae_landing h hTip V.buffer V.gap V.bounded V.window_subset V.seed i] with p hB hg hl he
    exact ⟨(hB he).conformal, (hB he).start_mem, (hB he).start_lim, (hB he).inside,
      (fun _ => hl he), (chart_spec D h i).continuous_lift _, (hg he).harmonic_lift⟩

/-- The full existing R1 input record, with chart geometry, contact,
initial closure, pre-contact membership and selected landing proved. -/
theorem ReaderFacts.r1Inputs (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h) (hCompare : ComparisonFacts D h) (hCapture : CaptureFacts D h) :
    R1Inputs S (source D h) (fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) where
  selected_measurable := R.selected_measurable
  chart_measurable := fun i => (chart_spec D h i).measurable
  chart_conformal := fun i y _ => (chart_spec D h i).conformal y
  chart_lift := fun i y _ => (chart_spec D h i).continuous_lift y
  chart_domain := R.record_domain h
  event_measurable := (eventFacts_of_eq_preimage S (source D h) R.selected_measurable fun _ => rfl).1
  contact_measurable := D.measurable_contact
  contact_hit := r1_contact_hit_of_tipOff D h R.tipOff
  open_window := V.open_window
  zero_window := V.zero_window
  clearance := V.clearance
  kappa := V.kappa
  reference := V.reference
  event_version := (eventFacts_of_eq_preimage S (source D h) R.selected_measurable fun _ => rfl).2
  physical_stop := fun i => by
    filter_upwards [hExit i, r1_contact_fields_of_tipOff D h R.tipOff i] with p hx ht he
    exact ⟨he, (ht he).2.1, hx he⟩
  geometric := fun i => by
    filter_upwards [R.ae_restartPoint h hTip i, R.ae_geometry h i,
      R.ae_landing h hTip V.buffer V.gap V.bounded V.window_subset V.seed i] with p hB hg hl he
    exact ⟨(hB he).start_mem, (hB he).start_lim, (hB he).inside, fun _ => hl he, (hg he).harmonic_lift⟩
  chart_geometry := R.ae_geometry h
  comparisons := hCompare
  history_cover := hCapture.history_cover
  completed_window := hCapture.completed_window

/-- Explicit remaining data per source setting. The genuinely new analytic
input is named `tip`; no chart geometry or restart-specification input remains. -/
structure AssemblyData (S : SourceSetting.{u}) where
  restart : R1Restart S
  hasChart : restart.HasChart
  readers : ReaderFacts restart
  tip : OwnTipForwardLimit S
  windows : WindowData restart hasChart
  exit : PhysicalExit restart hasChart
  comparisons : ComparisonFacts restart hasChart
  capture : CaptureFacts restart hasChart

omit R in
/-- The fibre cover with every remaining input given its precise type. -/
theorem dyCover_of_assembly (A : ∀ S : SourceSetting.{u}, AssemblyData S) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_r1 (fun S => source (A S).restart (A S).hasChart)
    (fun S _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (fun S => obstacleFacts_retObs S _) fun S =>
      (A S).readers.r1Inputs (A S).tip (A S).windows (A S).exit (A S).comparisons (A S).capture

omit R in
/-- The same cover at both universes used by the consuming assembly. -/
theorem dyCover_of_assembly_both (A : ∀ S : SourceSetting.{u}, AssemblyData S)
    (A₀ : ∀ S : SourceSetting.{0}, AssemblyData S) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  ⟨dyCover_of_assembly A, dyCover_of_assembly A₀⟩

end InteractingSLE.Sec5.Aux61SlitWX
