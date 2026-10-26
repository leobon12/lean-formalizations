import SupercriticalConformalCovariance.Small.ConfinedMeasurable
import SupercriticalConformalCovariance.Small.ConfinedRegularity
import SupercriticalConformalCovariance.Small.AmbientMetricLift
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointCompactPort
import LQGMetric.Meas.UM

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

local instance clgMeasurableSpaceLSCFun : MeasurableSpace LSCFun := borel LSCFun
local instance clgBorelSpaceLSCFun : BorelSpace LSCFun := ⟨rfl⟩

/-- The image of diagonal-corrected confinement is universally measurable
in the Polish epigraph carrier. -/
theorem um_confined_image (c : ℂ) (R : ℝ) :
    LQGMetric.UMeasurableSet
      (Set.range (fun F : LSCFun =>
        (conf (ambientMetricLift F) c R).toLSCFun)) := by
  have hf : Measurable (fun F : LSCFun =>
      (conf (ambientMetricLift F) c R).toLSCFun) :=
    (measurable_conf c R).comp ambientMetricLift_measurable
  have hu := LQGMetric.UMeasurableSet.image hf
    (s := (Set.univ : Set LSCFun)) MeasurableSet.univ
  simpa only [Set.image_univ] using hu

theorem conf_mem_um_image (D : LSCMetric) (c : ℂ) (R : ℝ) :
    (conf D c R).toLSCFun ∈
      Set.range (fun F : LSCFun =>
        (conf (ambientMetricLift F) c R).toLSCFun) := by
  refine ⟨D.toLSCFun, ?_⟩
  simp only [ambientMetricLift_eq]

theorem conf_image_geometry (c : ℂ) (R : ℝ) (F : LSCFun)
    (hF : F ∈ Set.range (fun G : LSCFun =>
      (conf (ambientMetricLift G) c R).toLSCFun)) :
    (ambientMetricLift F).IsLengthSpace ∧
      (∀ (P : ℝ → ℂ) (a b : ℝ), (ambientMetricLift F).IsCurve P a b →
        (ambientMetricLift F).len P a b < ⊤ → ContinuousOn P (Icc a b)) := by
  obtain ⟨G, rfl⟩ := hF
  rw [ambientMetricLift_eq]
  exact ⟨conf_isLengthSpace (ambientMetricLift G) c R,
    fun P a b hP _ => conf_euclidean_regular_any (ambientMetricLift G) c R P a b hP⟩

/-- Universal measurability of the two-sided global comparison relation
on ambient epigraph coordinates. -/
theorem um_two_sided_comparison (C : NNReal) :
    LQGMetric.UMeasurableSet
      {p : LSCFun × LSCFun |
        ∀ x y : ℂ,
          ambientMetricLift p.1 (x,y) ≤ (C : ℝ≥0∞) * ambientMetricLift p.2 (x,y) ∧
          ambientMetricLift p.2 (x,y) ≤ (C : ℝ≥0∞) * ambientMetricLift p.1 (x,y)} := by
  let ev₁ : (LSCFun × LSCFun) × (ℂ × ℂ) → ℝ≥0∞ :=
    fun p => ambientMetricLift p.1.1 p.2
  let ev₂ : (LSCFun × LSCFun) × (ℂ × ℂ) → ℝ≥0∞ :=
    fun p => ambientMetricLift p.1.2 p.2
  have hm₁ : Measurable ev₁ :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.jointEval_lsc.measurable.comp
      ((ambientMetricLift_measurable.comp (measurable_fst.comp measurable_fst)).prodMk
        measurable_snd)
  have hm₂ : Measurable ev₂ :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.jointEval_lsc.measurable.comp
      ((ambientMetricLift_measurable.comp (measurable_snd.comp measurable_fst)).prodMk
        measurable_snd)
  have hB : MeasurableSet
      {p : (LSCFun × LSCFun) × (ℂ × ℂ) |
        ev₁ p ≤ (C : ℝ≥0∞) * ev₂ p ∧ ev₂ p ≤ (C : ℝ≥0∞) * ev₁ p} :=
    (measurableSet_le hm₁ (measurable_const.mul hm₂)).inter
      (measurableSet_le hm₂ (measurable_const.mul hm₁))
  convert LQGMetric.UMeasurableSet.setOf_forall hB using 1
  ext p
  simp only [Set.mem_setOf_eq, ev₁, ev₂]
  constructor
  · intro h q
    exact h q.1 q.2
  · intro h x y
    exact h (x,y)

/-- The selected endpoint failure is universally measurable in the ambient
Polish coordinates. The path witness is projected out only after proving a
Borel relation with the path included. -/
theorem um_source_failure_endpoints
    (z : ℂ) (r α θ m M b η : ℝ) :
    LQGMetric.UMeasurableSet
      {p : (LSCFun × LSCFun) × (ℂ × ℂ) |
        SupercriticalConformalCovariance.Regular.SourceFailure
          (ambientMetricLift p.1.1) (ambientMetricLift p.1.2)
          z p.2.1 p.2.2 r α θ m M b η} := by
  let A : Set (((LSCFun × LSCFun) × (ℂ × ℂ)) × SupercriticalConformalCovariance.Regular.Path) :=
    {p | SupercriticalConformalCovariance.Regular.FailureWitness z r α θ m M b η
      ((ambientMetricLift p.1.1.1, ambientMetricLift p.1.1.2),
        (p.2, p.1.2))}
  have hmap : Measurable (fun p : ((LSCFun × LSCFun) × (ℂ × ℂ)) × SupercriticalConformalCovariance.Regular.Path =>
      ((ambientMetricLift p.1.1.1, ambientMetricLift p.1.1.2),
        (p.2, p.1.2))) := by
    exact ((ambientMetricLift_measurable.comp
      (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (ambientMetricLift_measurable.comp
        (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hA : MeasurableSet A :=
    (SupercriticalConformalCovariance.Regular.failureWitness_borel z r α θ m M b η).preimage hmap
  have hu := LQGMetric.UMeasurableSet.setOf_exists hA
  convert hu using 1
  ext p
  simp only [A, Set.mem_setOf_eq]
  simpa only [Prod.mk.eta] using
    (SupercriticalConformalCovariance.Regular.sourceFailure_iff_witness
      (ambientMetricLift p.1.1) (ambientMetricLift p.1.2)
      z p.2.1 p.2.2 r α θ m M b η)

end SupercriticalConformalCovariance.Small
