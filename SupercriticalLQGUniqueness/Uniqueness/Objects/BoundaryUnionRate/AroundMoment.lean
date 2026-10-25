import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AroundTail
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.TailMoment




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem normalizedAroundCost_moment
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (m : ℝ) (hm : 0 < m) :
    ∃ M : ENNReal, M < ∞ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (s : Set.Ioi (0 : ℝ)) (y : ℂ),
          (∫⁻ ω, normalizedAroundCost ξ Q D (h ω) s y ^ m ∂P) ≤ M := by
  have hq : 0 < m + 1 := by linarith
  obtain ⟨R₀, C, hR₀, hC, htail⟩ :=
    normalizedAroundCost_upper_tail ξ Q hQ D hD (m + 1) hq
  let M : ENNReal := ENNReal.ofReal m *
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tailDom m (m + 1) R₀ C t)
  have hMfin : M < ∞ := by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (tailDom_lintegral_ne_top hm (by linarith : m < m + 1)
        (lt_of_lt_of_le zero_lt_one hR₀) hC.le).lt_top
  refine ⟨M, hMfin, ?_⟩
  intro Ω _ P _ h hh s y
  have hmeas : AEMeasurable
      (fun ω => normalizedAroundCost ξ Q D (h ω) s y) P :=
    ((measurable_normalizedAroundCost ξ Q D hD.1 s y).comp hh.1.measurable).aemeasurable
  exact lintegral_rpow_le_of_power_tail P
    (fun ω => normalizedAroundCost ξ Q D (h ω) s y)
    hmeas (ae_normalizedAroundCost_lt_top ξ Q hQ D hD P h hh s y)
    hm hC (fun R hR => htail P h hh R hR s y)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
