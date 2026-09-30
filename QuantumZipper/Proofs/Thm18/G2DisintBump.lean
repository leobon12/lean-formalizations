import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration: the length is a smooth increasing function of the bump coefficient

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66): "once we condition on `h₀`, each
`ν_h(∂U_i ∩ ℝ)` is a.s. given by an increasing smooth function of `α_i`. Here the smoothness can
be verified by differentiating with respect to `α`". With `ν_h = e^{(γ/2) α φ} ν_{h₀}` on the bump,
the length is `c + ∫ e^{a g} dν` with `g = γφ/2` bounded; this file proves differentiability
(`g2bump_hasDerivAt`, differentiation under the integral) and positivity of the derivative when
`g ≥ 0` and `ν{g > 0} > 0` (`g2bump_deriv_pos`), which is what `g2clip_frozen` needs.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

theorem g2bump_integrable {ν : Measure ℝ} [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, |g t| ≤ B) (a : ℝ) :
    Integrable (fun t => g t * Real.exp (a * g t)) ν ∧ Integrable (fun t => Real.exp (a * g t)) ν := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have he : ∀ t, Real.exp (a * g t) ≤ Real.exp (|a| * B) := fun t => by
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB t) (abs_nonneg a)
  have hm : Measurable fun t => Real.exp (a * g t) := (hg.const_mul a).exp
  refine ⟨(integrable_const (B * Real.exp (|a| * B))).mono' (hg.mul hm).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_), (integrable_const (Real.exp (|a| * B))).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)⟩
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hB t) (he t) (Real.exp_pos _).le hB0
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact he t

/-- **Differentiation under the integral** of `a ↦ ∫ e^{a g} dν`, `g` bounded, `ν` finite. -/
theorem g2bump_hasDerivAt {ν : Measure ℝ} [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, |g t| ≤ B) (a : ℝ) :
    HasDerivAt (fun b => ∫ t, Real.exp (b * g t) ∂ν) (∫ t, g t * Real.exp (a * g t) ∂ν) a := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball a 1)
    (F := fun b t => Real.exp (b * g t)) (F' := fun b t => g t * Real.exp (b * g t))
    (bound := fun _ => B * Real.exp ((|a| + 1) * B))
    (Metric.ball_mem_nhds a one_pos)
    (Eventually.of_forall fun b => ((hg.const_mul b).exp).aestronglyMeasurable)
    (g2bump_integrable hg hB a).2 (hg.mul (hg.const_mul a).exp).aestronglyMeasurable
    (Eventually.of_forall fun t b hb => ?_) (integrable_const _)
    (Eventually.of_forall fun t b _ => ?_)).2
  · have hb' : |b| ≤ |a| + 1 := by
      have := Metric.mem_ball.1 hb
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub b a
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hB t) (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)) (Real.exp_pos _).le hB0
    rw [abs_mul]; exact mul_le_mul hb' (hB t) (abs_nonneg _) (by positivity)
  · have := ((hasDerivAt_id b).mul_const (g t)).exp
    simpa [mul_comm] using this

/-- **The derivative is positive** when `g ≥ 0` charges a set of positive `ν`-measure. -/
theorem g2bump_deriv_pos {ν : Measure ℝ} [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ t, |g t| ≤ B) (hg0 : ∀ t, 0 ≤ g t) (hpos : 0 < ν {t | 0 < g t}) (a : ℝ) :
    0 < ∫ t, g t * Real.exp (a * g t) ∂ν := by
  rw [integral_pos_iff_support_of_nonneg (fun t => mul_nonneg (hg0 t) (Real.exp_pos _).le)
    (g2bump_integrable hg hB a).1]
  refine hpos.trans_le (measure_mono fun t ht => ?_)
  simp only [Function.mem_support, ne_eq, mul_eq_zero, Real.exp_ne_zero, or_false]
  exact (ne_of_gt ht)

end Thm18Asm
end QuantumZipper
