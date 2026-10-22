import HigherDimLQGMetric.Locality.SecondGraph
import HigherDimLQGMetric.Metric.WeylCompose

/-! Metric-valued versions of the two limits read from a marked full metric
coordinate. The first is a measurable constant multiple of the full metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l7a_normalizedMarkedMetric {d : ℕ} (ξ : ℝ)
    (q : L7aMarkedBase d) : ContMetric d :=
  (l7a_metricLift q.2).smul (Real.exp (ξ * (-q.1.2.1)))
    (Real.exp_pos _)

def l7a_perturbedMarkedMetric {d : ℕ} (ξ : ℝ)
    (q : L7aMarkedBase d) : ContMetric d := by
  classical
  let D := l7a_metricLift q.2
  exact if hD : D.IsLength then
    weylMetric ξ (ContinuousMap.const (Rd d) (-q.1.2.1) - q.1.2.2) D hD
  else fieldLfppMetric 0 (0 : C(Rd d, ℝ))

theorem l7a_measurable_normalizedMarkedMetric {d : ℕ} (ξ : ℝ) :
    Measurable (l7a_normalizedMarkedMetric (d := d) ξ) := by
  have hEmb : MeasurableEmbedding
      ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  apply (hEmb.measurable_comp_iff).mp
  have hs : Measurable (fun q : L7aMarkedBase d =>
      Real.exp (ξ * (-q.1.2.1))) :=
    (((measurable_fst.comp measurable_snd).comp measurable_fst).neg.const_mul ξ).exp
  have hD : Measurable (fun q : L7aMarkedBase d =>
      (l7a_metricLift q.2).1) :=
    measurable_subtype_coe.comp
      (l7a_measurable_metricLift.comp measurable_snd)
  exact hs.smul hD

theorem l7a_normalizedMarkedMetric_eq_weyl {d : ℕ} (ξ : ℝ)
    (q : L7aMarkedBase d)
    (hD : (l7a_metricLift q.2).IsLength) :
    l7a_normalizedMarkedMetric ξ q =
      weylMetric ξ (ContinuousMap.const (Rd d) (-q.1.2.1))
        (l7a_metricLift q.2) hD := by
  apply Subtype.ext
  apply ContinuousMap.ext
  rintro ⟨u, v⟩
  change Real.exp (ξ * (-q.1.2.1)) *
      (l7a_metricLift q.2).1 (u,v) =
      (weylScale ξ (ContinuousMap.const (Rd d) (-q.1.2.1))
        (l7a_metricLift q.2) u v).toReal
  rw [weylScale_const_of_isLength hD]
  exact (ENNReal.toReal_ofReal
    (mul_nonneg (Real.exp_pos _).le ((l7a_metricLift q.2).nonneg u v))).symm

theorem l7a_perturbedMarkedMetric_eq_weyl {d : ℕ} (ξ : ℝ)
    (q : L7aMarkedBase d)
    (hD : (l7a_metricLift q.2).IsLength) :
    l7a_perturbedMarkedMetric ξ q =
      weylMetric ξ (ContinuousMap.const (Rd d) (-q.1.2.1) - q.1.2.2)
        (l7a_metricLift q.2) hD := by
  classical
  simp [l7a_perturbedMarkedMetric, hD]

theorem l7a_markedWeyl_relation {d : ℕ} (ξ : ℝ)
    (q : L7aMarkedBase d)
    (hD : (l7a_metricLift q.2).IsLength)
    (u v : Rd d) :
    ENNReal.ofReal ((l7a_normalizedMarkedMetric ξ q).1 (u,v)) =
      weylScale ξ q.1.2.2 (l7a_perturbedMarkedMetric ξ q) u v := by
  rw [l7a_normalizedMarkedMetric_eq_weyl ξ q hD,
    l7a_perturbedMarkedMetric_eq_weyl ξ q hD,
    weylMetric_spec hD,
    weylScale_weylMetric hD]
  have hsum : q.1.2.2 +
      (ContinuousMap.const (Rd d) (-q.1.2.1) - q.1.2.2) =
      ContinuousMap.const (Rd d) (-q.1.2.1) := by
    abel
  rw [hsum]

end HigherDimLQGMetric
