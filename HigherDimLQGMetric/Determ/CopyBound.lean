import HigherDimLQGMetric.Select.MetricBorel
import LQGMetric.Papers.LM.T1_7E5

/-!
# The conditional metric-copy sandwich in `Rd d`

This is the dimension-generic class argument of MA5 A19(0), using the generic
one-measure lemma `LQGMetric.LM.t17e_condBded_measure`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private lemma determ_measurable_eval {d : ℕ} (p : Rd d × Rd d) :
    Measurable fun D : ContMetric d => D.1 p :=
  (continuous_eval_const p).measurable.comp measurable_subtype_coe

/-- If two independent draws from a metric law are comparable, any coupling of
that law is comparable with the squared constant. -/
theorem determ_bilip_any_coupling {d : ℕ} {ν : Measure (ContMetric d)}
    [IsProbabilityMeasure ν] {c : ℝ} (hc : 0 ≤ c)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd d,
      p.2.1 (z, w) ≤ c * p.1.1 (z, w))
    {π : Measure (ContMetric d × ContMetric d)}
    (h1 : π.map Prod.fst = ν) (h2 : π.map Prod.snd = ν) :
    ∀ᵐ p ∂π, ∀ x y : Rd d, p.2.1 (x, y) ≤ c ^ 2 * p.1.1 (x, y) := by
  have hpair : ∀ q : Rd d × Rd d, ∀ᵐ p ∂π,
      p.2.1 q ≤ c ^ 2 * p.1.1 q := by
    intro q
    let f : ContMetric d → ℝ≥0∞ := fun D => ENNReal.ofReal (D.1 q)
    have hf : Measurable f := ENNReal.measurable_ofReal.comp (determ_measurable_eval q)
    have hle : ∀ᵐ p ∂ν.prod ν, f p.2 ≤ ENNReal.ofReal c * f p.1 := by
      filter_upwards [hcopy] with p hp
      rw [show f p.2 = ENNReal.ofReal (p.2.1 q) from rfl,
        show f p.1 = ENNReal.ofReal (p.1.1 q) from rfl,
        ← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal (hp q.1 q.2)
    have hb := LQGMetric.LM.t17e_condBded_measure hf _ hle
    let I : ℝ≥0∞ := ∫⁻ D, f D ∂ν
    have hS1 : MeasurableSet {D : ContMetric d | I ≤ ENNReal.ofReal c * f D} :=
      measurableSet_le measurable_const (measurable_const.mul hf)
    have hS2 : MeasurableSet {D : ContMetric d | f D ≤ ENNReal.ofReal c * I} :=
      measurableSet_le hf measurable_const
    have hb1 : ∀ᵐ p ∂π, I ≤ ENNReal.ofReal c * f p.1 := by
      have h : ∀ᵐ D ∂π.map Prod.fst, I ≤ ENNReal.ofReal c * f D := by
        rw [h1]
        filter_upwards [hb] with D hD using hD.1
      exact (ae_map_iff measurable_fst.aemeasurable hS1).1 h
    have hb2 : ∀ᵐ p ∂π, f p.2 ≤ ENNReal.ofReal c * I := by
      have h : ∀ᵐ D ∂π.map Prod.snd, f D ≤ ENNReal.ofReal c * I := by
        rw [h2]
        filter_upwards [hb] with D hD using hD.2
      exact (ae_map_iff measurable_snd.aemeasurable hS2).1 h
    filter_upwards [hb1, hb2] with p hp1 hp2
    have key : f p.2 ≤ ENNReal.ofReal (c ^ 2 * p.1.1 q) := by
      rw [pow_two, ENNReal.ofReal_mul (mul_nonneg hc hc), ENNReal.ofReal_mul hc, mul_assoc]
      exact hp2.trans (by gcongr)
    have hd0 : 0 ≤ p.1.1 q :=
      (dist_nonneg : 0 ≤ dist (p.1.pt q.1) (p.1.pt q.2))
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_two_nonneg _) hd0)).1 key
  have hall : ∀ᵐ p ∂π, ∀ n : ℕ,
      p.2.1 (TopologicalSpace.denseSeq (Rd d × Rd d) n) ≤
        c ^ 2 * p.1.1 (TopologicalSpace.denseSeq (Rd d × Rd d) n) :=
    ae_all_iff.2 fun n => hpair _
  filter_upwards [hall] with p hp x y
  exact (TopologicalSpace.denseRange_denseSeq (Rd d × Rd d)).induction_on (x, y)
    (isClosed_le p.2.1.continuous (continuous_const.mul p.1.1.continuous)) hp

end HigherDimLQGMetric
