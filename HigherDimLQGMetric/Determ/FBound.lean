import HigherDimLQGMetric.Determ.PerD2
import LQGMetric.Papers.LM.T1_7E5

/-! Almost-sure boundedness of the internal ball distance under a comparable metric law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_F_bdd (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 < C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {z w : Rd dim} (hz : ‖z‖ < m) (hw : ‖w‖ < m) :
    ∃ B : ℝ, ∀ᵐ d ∂ν, determF m z w d ≤ ENNReal.ofReal B ∧ determF m z w d ≠ ⊤ := by
  set f := determF m z w
  have hf : Measurable f := determ_measurableF m z w
  have hle : ∀ᵐ p ∂ν.prod ν, f p.2 ≤ ENNReal.ofReal C * f p.1 := by
    have hl := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hL
    filter_upwards [hcopy, hl] with p hp hpl
    exact determ_chainInf_le_of_le hpl hC hp Metric.isOpen_ball z w
  have hb := LQGMetric.LM.t17e_condBded_measure hf (ENNReal.ofReal C) hle
  have hfin : ∀ᵐ d ∂ν, f d ≠ ⊤ := by
    filter_upwards [hL] with d hd
    rw [show f d = d.internal (Metric.ball 0 (m : ℝ)) z w from
      (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm]
    exact d.internal_ne_top_of_isPreconnected hd Metric.isOpen_ball (convex_ball _ _).isPreconnected
      (mem_ball_zero_iff.2 hz) (mem_ball_zero_iff.2 hw)
  obtain ⟨y₀, hy₀b, hy₀f⟩ := (hb.and hfin).exists
  have hI : ∫⁻ y, f y ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy₀f) hy₀b.1
  refine ⟨(ENNReal.ofReal C * ∫⁻ y, f y ∂ν).toReal, ?_⟩
  filter_upwards [hb, hfin] with d hd hdf
  refine ⟨?_, hdf⟩
  rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)]
  exact hd.2

/-- `F_m ∈ L²(ν)` -/
theorem determ_memLp_F (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 < C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {z w : Rd dim} (hz : ‖z‖ < m) (hw : ‖w‖ < m) :
    MemLp (fun d => (determF m z w d).toReal) 2 ν := by
  obtain ⟨B, hB⟩ := determ_F_bdd ν hL hC hcopy hz hw
  refine MemLp.of_bound (determ_measurableF m z w).ennreal_toReal.aestronglyMeasurable
    (ENNReal.ofReal B).toReal ?_
  filter_upwards [hB] with d hd
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hd.1


end HigherDimLQGMetric
