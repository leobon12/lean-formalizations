import SupercriticalConformalCovariance.Small.ConfinedLSC
import SupercriticalConformalCovariance.Lemma31.LscMeas
import SupercriticalConformalCovariance.Lemma31.InMeasure

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

/-- Diagonal correction preserves joint lower semicontinuity in a metric
parameter and two endpoints. -/
theorem joint_lsc_zero_diagonal
    {F : LSCMetric × (ℂ × ℂ) → ℝ≥0∞}
    (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) =>
      if p.2.1 = p.2.2 then (0 : ℝ≥0∞) else F p) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hF ⊢
  intro a
  let O : Set (LSCMetric × (ℂ × ℂ)) := {p | p.2.1 ≠ p.2.2}
  have hO : IsOpen O :=
    (isClosed_eq (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).isOpen_compl
  have hset : (fun p : LSCMetric × (ℂ × ℂ) =>
      if p.2.1 = p.2.2 then (0 : ℝ≥0∞) else F p) ⁻¹' Ioi a =
      F ⁻¹' Ioi a ∩ O := by
    ext p
    by_cases hp : p.2.1 = p.2.2 <;> simp [hp, O]
  rw [hset]
  exact (hF a).inter hO

def confSection (c : ℂ) (R : ℝ) (D : LSCMetric) : LSCFun :=
  SupercriticalConformalCovariance.Lemma31.lscSection
    (fun D q => ((confKernel D c R q : ℝ≥0∞) : EReal))
    (by
      have h := joint_lsc_zero_diagonal
        (F := fun p : LSCMetric × (ℂ × ℂ) =>
          SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
            p.1 c R p.2.1 p.2.2)
        (by
          have hc : Continuous fun p : LSCMetric × (ℂ × ℂ) =>
              (p.1, (c, (R, p.2))) :=
            continuous_fst.prodMk
              (continuous_const.prodMk (continuous_const.prodMk continuous_snd))
          change LowerSemicontinuous
            ((fun p : LSCMetric × (ℂ × (ℝ × (ℂ × ℂ))) =>
              SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
                p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
              fun p : LSCMetric × (ℂ × ℂ) => (p.1, (c, (R, p.2))))
          exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf_joint_lsc.comp hc)
      exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous h
        EReal.coe_ennreal_strictMono.monotone)
    D

theorem confSection_eq (D : LSCMetric) (c : ℂ) (R : ℝ) :
    confSection c R D = (conf D c R).toLSCFun := by
  apply Subtype.ext
  funext p
  change ((confKernel D c R p : ℝ≥0∞) : EReal) =
    ((confKernel D c R p : ℝ≥0∞) : EReal)
  rfl

theorem measurable_conf [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (c : ℂ) (R : ℝ) :
    Measurable fun D : LSCMetric => (conf D c R).toLSCFun := by
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  have hm : Measurable (confSection c R) := by
    unfold confSection
    exact SupercriticalConformalCovariance.Lemma31.measurable_lscSection _ _
  have heq : (fun D : LSCMetric => (conf D c R).toLSCFun) = confSection c R := by
    funext D
    exact (confSection_eq D c R).symm
  rw [heq]
  exact hm

end SupercriticalConformalCovariance.Small
