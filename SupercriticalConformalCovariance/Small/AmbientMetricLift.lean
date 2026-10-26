import SupercriticalConformalCovariance.Small.RegularAdapters
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2MetricBorel
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import SupercriticalLQGUniqueness.B2.LscTop.Compact
import LQGMetric.Field.StandardBorelRange

set_option autoImplicit false
noncomputable section
open MeasureTheory Classical
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.PfeAxioms

/-- Total Borel lift of the metric locus in the Polish epigraph space. -/
def ambientMetricLift (F : LSCFun) : LSCMetric :=
  if h : IsMetricLSCFun F then metricOfLSCFun F h
  else SupercriticalLQGUniqueness.B2.LscTop.euclideanLSCMetric

theorem ambientMetricLift_toLSCFun (F : LSCFun) (h : IsMetricLSCFun F) :
    (ambientMetricLift F).toLSCFun = F := by
  simp only [ambientMetricLift, dif_pos h]
  exact toLSCFun_metricOfLSCFun F h

theorem ambientMetricLift_measurable [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    Measurable ambientMetricLift := by
  rw [SupercriticalLQGUniqueness.B2.LscTop.measurable_iff_toLSCFun]
  have heq : (fun F : LSCFun => (ambientMetricLift F).toLSCFun) =
      ({F : LSCFun | IsMetricLSCFun F}).piecewise id
        (fun _ => SupercriticalLQGUniqueness.B2.LscTop.euclideanLSCMetric.toLSCFun) := by
    funext F
    by_cases h : IsMetricLSCFun F
    · simp only [Set.piecewise, Set.mem_setOf_eq, if_pos h, id_eq]
      exact ambientMetricLift_toLSCFun F h
    · simp only [Set.piecewise, Set.mem_setOf_eq, if_neg h,
        ambientMetricLift, dif_neg h]
  rw [heq]
  exact measurable_id.piecewise measurableSet_isMetricLSCFun measurable_const

theorem ambientMetricLift_eq (D : LSCMetric) :
    ambientMetricLift D.toLSCFun = D := by
  apply SupercriticalLQGUniqueness.B2.LscTop.toLSCFun_injective
  rw [ambientMetricLift_toLSCFun _ (isMetricLSCFun_toLSCFun D)]

/-- Select compact witnesses from the field plus both ambient epigraph coordinates. -/
local instance : MeasurableSpace LSCFun := borel LSCFun
local instance : BorelSpace LSCFun := ⟨rfl⟩
theorem selected_compact_endpoints_of_ambient_joint
    {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Z : Ω → X × (LSCFun × LSCFun))
    (hZ : Measurable Z)
    (α θ m M η : ℝ) (hα : α ≤ 1) :
    ∃ V : Ω → ℂ × ℂ, Measurable V ∧
      (∀ ω, (V ω).1 ∈ Metric.closedBall 0 1 ∧
        (V ω).2 ∈ Metric.closedBall 0 1) ∧
      (∀ᵐ ω ∂P, (∃ u v : ℂ,
          SupercriticalConformalCovariance.Regular.SourceFailure
            (ambientMetricLift (Z ω).2.1) (ambientMetricLift (Z ω).2.2)
            0 u v 1 α θ m M (1 - α) η) →
        SupercriticalConformalCovariance.Regular.SourceFailure
          (ambientMetricLift (Z ω).2.1) (ambientMetricLift (Z ω).2.2)
          0 (V ω).1 (V ω).2 1 α θ m M (1 - α) η) := by
  let J := X × (LSCFun × LSCFun)
  let D : J → LSCMetric := fun p => ambientMetricLift p.2.1
  let E : J → LSCMetric := fun p => ambientMetricLift p.2.2
  have hD : Measurable D :=
    ambientMetricLift_measurable.comp (measurable_fst.comp measurable_snd)
  have hE : Measurable E :=
    ambientMetricLift_measurable.comp (measurable_snd.comp measurable_snd)
  exact selected_compact_endpoints_of_source_failure P Z hZ D E hD hE
    0 α θ m M η hα

end SupercriticalConformalCovariance.Small
