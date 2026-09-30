import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, node FM-ADM: the first-mode measures are admissible

Task N2Z-FMVAR-A. `fmAdmStmt_holds : FMAdmStmt`.

Route: the arc measure `fmArc w v` (`cos⁺ φ dφ` on `(0, 2π]` pushed to the circle
`∂B(w, ‖v‖)`) has density `≤ 1` in the angle, so a ball of radius `t` gets mass at most the
Lebesgue measure of an arc of the unit circle inside a ball of radius `t / ‖v‖`, i.e.
`≤ 6π t / ‖v‖` (`TwoPoint.volume_arc_le`), and at most the total mass. This gives a
`1/3`-Frostman bound, and `RegCont.isAdmissibleH_bindFc` concludes (the folded circles keep the
measure in `Hbar` and the support is bounded by `‖w‖ + ‖v‖ + s`). Own elementary bookkeeping on
top of the existing repository lemmas.
-/

noncomputable section

open MeasureTheory Set
open scoped Real ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Density `≤ 1`: the base measure of a set is at most its Lebesgue measure in `(0, 2π]`. -/
theorem fmBase_le_volume {S : Set ℝ} (hS : MeasurableSet S) :
    fmBase S ≤ volume (S ∩ Ioc 0 (2 * π)) := by
  unfold fmBase
  rw [withDensity_apply _ hS, ← Measure.restrict_apply hS, ← setLIntegral_one]
  exact lintegral_mono fun a => ENNReal.ofReal_le_one.2 (Real.cos_le_one a)

/-- A ball of radius `t` gets `fmArc w v`-mass at most `6π t / ‖v‖`. -/
theorem fmArc_closedBall_le (w v p : ℂ) (hv : 0 < ‖v‖) (t : ℝ) :
    fmArc w v (Metric.closedBall p t) ≤ ENNReal.ofReal (6 * π * (t / ‖v‖) / 1) := by
  unfold fmArc
  rw [Measure.map_apply (measurable_fmArcMap w v) Metric.isClosed_closedBall.measurableSet]
  refine (fmBase_le_volume ((measurable_fmArcMap w v)
    Metric.isClosed_closedBall.measurableSet)).trans ?_
  have hv0 : v ≠ 0 := norm_pos_iff.1 hv
  set q : ℂ := (p - w) / v
  have hsub : (fun φ : ℝ => w + v * Complex.exp ((φ : ℂ) * Complex.I)) ⁻¹'
      Metric.closedBall p t ∩ Ioc 0 (2 * π) ⊆
      {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap 0 1 θ - q‖ ≤ t / ‖v‖} ∪ {2 * π} := by
    rintro θ ⟨h1, h2⟩
    rcases eq_or_ne θ (2 * π) with h | h
    · exact Or.inr h
    refine Or.inl ⟨⟨h2.1.le, lt_of_le_of_ne h2.2 h⟩, ?_⟩
    rw [mem_preimage, Metric.mem_closedBall, dist_eq_norm] at h1
    have e : v * (circleMap 0 1 θ - q) = w + v * Complex.exp ((θ : ℂ) * Complex.I) - p := by
      simp only [circleMap, Complex.ofReal_one, one_mul, zero_add, q]
      rw [mul_sub, mul_div_cancel₀ _ hv0]; ring
    rw [le_div_iff₀ hv, mul_comm, ← norm_mul, e]
    exact h1
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, add_zero]
  exact TwoPoint.volume_arc_le 0 q one_pos (t / ‖v‖)

/-- `fmArc w v` is `1/3`-Frostman for `v ≠ 0`. -/
theorem isFrostman_fmArc (w v : ℂ) (hv : 0 < ‖v‖) :
    TwoPoint.IsFrostman (fmArc w v) (1 / 3)
      ((6 * π + (fmBase univ).toReal) / ‖v‖ ^ (1 / 3 : ℝ)) := by
  intro p t ht
  set M := (fmBase univ).toReal with hM_def
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  set x := t / ‖v‖ with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 : (fmArc w v (Metric.closedBall p t)).toReal ≤ 6 * π * x := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (fmArc_closedBall_le w v p hv t)
    rwa [ENNReal.toReal_ofReal (by positivity), div_one] at this
  have h2 : (fmArc w v (Metric.closedBall p t)).toReal ≤ M := by
    rw [hM_def, ← fmArc_univ w v]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have e : (6 * π + M) / ‖v‖ ^ (1 / 3 : ℝ) * t ^ (1 / 3 : ℝ) = (6 * π + M) * x ^ (1 / 3 : ℝ) := by
    rw [hx, Real.div_rpow ht.le hv.le]; ring
  rw [e]
  have hπ := Real.pi_pos
  rcases le_total x 1 with hx1 | hx1
  · have := Real.self_le_rpow_of_le_one hx0 hx1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have hr : 0 ≤ x ^ (1 / 3 : ℝ) := Real.rpow_nonneg hx0 _
    nlinarith
  · have := Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    nlinarith

/-- The arc lies in the closed ball of radius `‖w‖ + ‖v‖`. -/
theorem ae_norm_fmArc_le (w v : ℂ) : ∀ᵐ y ∂fmArc w v, ‖y‖ ≤ ‖w‖ + ‖v‖ := by
  unfold fmArc
  refine (ae_map_iff (measurable_fmArcMap w v).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).2 (ae_of_all _ fun φ => ?_)
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Node FM-ADM holds.** -/
theorem fmAdmStmt_holds : FMAdmStmt := by
  intro w v s hs hv _
  exact RegCont.isAdmissibleH_bindFc (isFrostman_fmArc w v hv) (ae_norm_fmArc_le w v) hs

end D3Plus
end QuantumZipper
