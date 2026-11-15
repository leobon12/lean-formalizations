/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafSurvEClock

/-!
# WFS from a continuous closed survival reader

All strict gaps, terminal limits, clocks and announcing rules are derived.
The remaining input constructs a continuous history-coded version of the
closed martingale of the bounded lifetime discount, with optional sampling.
It is stated explicitly and is not proved in this file.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.FlowStopIdentG LQGMetric

/-- Remaining stochastic version construction. A single Borel non-anticipating
reader must represent the closed survival martingale at bounded stopping times.
Continuity in an arbitrary ambient filtration is not asserted here. -/
def ContinuousSurvivalReaderStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h),
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      (∀ᵐ ω ∂P, 0 < V ω) →
      ∃ M : HistorySpace nL nR → ℝ≥0 → ℝ,
        (∀ p, Measurable fun γ => M γ (dyadicTime p)) ∧ IsNonAnticipating M ∧
        (∀ᵐ ω ∂P, Continuous (M (killedHistory W VL VR V ω))) ∧
        IsOptionalSurvivalReader P (drivingFiltration P hC.2.2.2.2.choose)
          V (killedHistory W VL VR V) M

/-- Construction of the former clock input from the closed survival reader. -/
theorem historyBlowupClockStatement_of_continuousSurvivalReader
    {κ : ℝ} (hreader : ContinuousSurvivalReaderStatement.{u} κ) :
    HistoryBlowupClockStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hm hgal Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  obtain ⟨M, hMm, hMn, hMc, hMr⟩ :=
    hreader xL xR ρL ρR hF R hm hgal P 𝓕 W VL VR B ζ V h hC hself hpos
  have hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact (continuousOn_state_of_isSLEPathUpTo hp).mono (fun t ht => ht.trans_le (hC.2.1 ω))
  exact hasHistoryBlowupClock_of_optionalSurvivalReader hC.2.2.2.2.choose hc hpos hMm hMn hMc hMr

/-- The unchanged WFS target, conditional on the precise stochastic reader
construction and the permitted Theorem 1.2/1.3 inputs. -/
theorem throughKernelStatement_of_continuousSurvivalReader
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hreader : ContinuousSurvivalReaderStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_historyBlowupClock h12 h13 hκ
    (historyBlowupClockStatement_of_continuousSurvivalReader hreader)

end InteractingSLE.WFS
