import GaussianLQG.Field.Frame.LogInt
import LQGMetric.Field.ExistHeatCov
import LQGMetric.Field.ExistKernel

/-!
# Heat kernels and the signed Frullani identity (blueprint Appendix B, `lem:heat`)

* `heatAvg β t y = ∫ p_{t/2}(u, y) β(du)`, the heat average of `β` at time `t/2`.
* `integral_heatAvg_mul`: `∫ heatAvg α t y · heatAvg β t y dy = ∬ p_t(u, v) α(du) β(dv)`
  (Chapman–Kolmogorov `p_{t/2} * p_{t/2} = p_t` and Fubini).
* `integrableOn_Ioi_subst`: integrability is preserved by the substitution `t = 2τ²`.
* `frullani_comb`: for a finite family of finite measures `m_i` on `ℂ × ℂ` that do not charge the
  diagonal, with `log|u − v| ∈ L¹(m_i)` and balanced masses `∑ c_i m_i(ℂ²) = 0`,
  `t ↦ π ∑ c_i ∬ p_t dm_i` is integrable on `(0, ∞)` with integral `−∑ c_i ∬ log|u − v| dm_i`
  (Frullani: `LQGDimension.HeatKernel.heatRep_of_integrable_log`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG
namespace WNFrame

open LQGMetric

/-! ## Heat averages of finite measures -/

/-- `A_β(t, y) = ∫ p_{t/2}(u, y) β(du)`. -/
def heatAvg (β : Measure ℂ) (t : ℝ) (y : ℂ) : ℝ := ∫ u, heatKernel (t / 2) u y ∂β

lemma integrable_heatKernel_left (β : Measure ℂ) [IsFiniteMeasure β] {s : ℝ} (hs : 0 < s)
    (y : ℂ) : Integrable (fun u => heatKernel s u y) β := by
  refine Integrable.of_bound (by unfold heatKernel; fun_prop) (2 * Real.pi * s)⁻¹
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (heatKernel_nonneg s hs.le u y)]
  exact LQGMetric.GFFExist.heatKernel_le s hs u y

/-- **Chapman–Kolmogorov against finite measures.**
`∫ A_α(t, y) A_β(t, y) dy = ∬ p_t(u, v) α(du) β(dv)`. -/
theorem integral_heatAvg_mul (α β : Measure ℂ) [IsFiniteMeasure α] [IsFiniteMeasure β] {t : ℝ}
    (ht : 0 < t) :
    Integrable (fun y => heatAvg α t y * heatAvg β t y) ∧
      ∫ y, heatAvg α t y * heatAvg β t y = ∫ p, heatKernel t p.1 p.2 ∂(α.prod β) := by
  have hs : 0 < t / 2 := by linarith
  have h2s : 2 * (t / 2) = t := by ring
  set F : (ℂ × ℂ) × ℂ → ℝ := fun z =>
    heatKernel (t / 2) z.1.1 z.2 * heatKernel (t / 2) z.1.2 z.2 with hF
  have hFm : Measurable F := by simp only [hF]; unfold heatKernel; fun_prop
  have hslice : ∀ x : ℂ × ℂ, ∫ y, F (x, y) = heatKernel t x.1 x.2 := fun x => by
    simp only [hF]
    rw [WhiteNoise.integral_heatKernel_mul_heatKernel _ hs, h2s]
  have hFi : Integrable F ((α.prod β).prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact WhiteNoise.integrable_heatKernel_mul_heatKernel _ hs x.1 x.2
    · have e : (fun x : ℂ × ℂ => ∫ y, ‖F (x, y)‖) = fun x => heatKernel t x.1 x.2 := by
        funext x
        rw [← hslice x]
        congr 1; funext y
        exact Real.norm_of_nonneg (mul_nonneg (heatKernel_nonneg _ hs.le _ _)
          (heatKernel_nonneg _ hs.le _ _))
      rw [e]
      refine Integrable.of_bound (by unfold heatKernel; fun_prop) (2 * Real.pi * t)⁻¹
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (heatKernel_nonneg t ht.le _ _)]
      exact LQGMetric.GFFExist.heatKernel_le t ht _ _
  have hA : ∀ y, heatAvg α t y * heatAvg β t y = ∫ x, F (x, y) ∂(α.prod β) := fun y => by
    unfold heatAvg
    rw [← integral_prod_mul (μ := α) (ν := β) (fun u => heatKernel (t / 2) u y)
      (fun v => heatKernel (t / 2) v y)]
  refine ⟨?_, ?_⟩
  · simp_rw [hA]
    exact hFi.integral_prod_right
  · simp_rw [hA]
    rw [← integral_integral_swap (f := fun x y => F (x, y)) hFi]
    simp_rw [hslice]

/-! ## The substitution `t = 2τ²` for integrability -/

/-- If `τ ↦ G(2τ²)/τ` is integrable on `(0, ∞)`, so is `t ↦ G(t)/(2t)`. -/
lemma integrableOn_Ioi_subst {G : ℝ → ℝ}
    (h : IntegrableOn (fun τ => G (2 * τ ^ 2) / τ) (Ioi 0)) :
    IntegrableOn (fun t => G t / (2 * t)) (Ioi 0) := by
  set f : ℝ → ℝ := fun x => G (x ^ 2) / x with hf
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have h1 : IntegrableOn f (Ioi 0) := by
    have h' : IntegrableOn (fun x => f (Real.sqrt 2 * x)) (Ioi 0) := by
      refine IntegrableOn.congr_fun (h.const_mul (Real.sqrt 2)⁻¹) (fun x hx => ?_) measurableSet_Ioi
      have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
      simp only [hf]
      rw [mul_pow, Real.sq_sqrt zero_le_two]
      field_simp
    have := (integrableOn_Ioi_comp_mul_left_iff f 0 hs2).mp h'
    rwa [mul_zero] at this
  rw [← integrableOn_Ioi_comp_rpow_iff (fun t => G t / (2 * t)) two_ne_zero]
  refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
  simp only [hf, smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two]
  field_simp

/-! ## The signed Frullani identity -/

/-- `∬ p_t dm = (2πt)⁻¹ ∬ e^{−|u−v|²/(2t)} dm`. -/
lemma integral_heatKernel_eq (m : Measure (ℂ × ℂ)) (t : ℝ) :
    ∫ p, heatKernel t p.1 p.2 ∂m =
      (2 * Real.pi * t)⁻¹ * ∫ p, Real.exp (-‖p.1 - p.2‖ ^ 2 / (2 * t)) ∂m := by
  unfold heatKernel
  rw [integral_const_mul]

/-- **Signed Frullani identity for heat kernels.** -/
theorem frullani_comb {ι : Type*} (s : Finset ι) (m : ι → Measure (ℂ × ℂ))
    (hfin : ∀ i, IsFiniteMeasure (m i)) (c : ι → ℝ)
    (hpos : ∀ i ∈ s, ∀ᵐ p ∂(m i), 0 < ‖p.1 - p.2‖)
    (hlog : ∀ i ∈ s, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (m i))
    (hmass : ∑ i ∈ s, c i * (m i).real univ = 0) :
    IntegrableOn (fun t => Real.pi * ∑ i ∈ s, c i * ∫ p, heatKernel t p.1 p.2 ∂(m i)) (Ioi 0) ∧
      ∫ t in Ioi 0, Real.pi * ∑ i ∈ s, c i * ∫ p, heatKernel t p.1 p.2 ∂(m i) =
        -∑ i ∈ s, c i * ∫ p, Real.log ‖p.1 - p.2‖ ∂(m i) := by
  have hD : Measurable LQGMetric.GFFExist.dist2 := by
    unfold LQGMetric.GFFExist.dist2; fun_prop
  -- the regularized Frullani functions
  set R : ι → ℝ → ℝ := fun i τ => (∫ p, Real.exp (-LQGMetric.GFFExist.dist2 p ^ 2 / (4 * τ ^ 2))
    ∂(m i) - (m i).real univ * Real.exp (-1 / (4 * τ ^ 2))) / τ with hR
  have hrep : ∀ i ∈ s, IntegrableOn (R i) (Ioi 0) ∧
      ∫ τ in Ioi 0, R i τ = -∫ p, Real.log ‖p.1 - p.2‖ ∂(m i) := fun i hi => by
    have := hfin i
    exact LQGDimension.HeatKernel.heatRep_of_integrable_log (m i) _ hD (hpos i hi) (hlog i hi)
  set G : ℝ → ℝ := fun t => ∑ i ∈ s, c i * ∫ p, Real.exp (-‖p.1 - p.2‖ ^ 2 / (2 * t)) ∂(m i)
    with hG
  -- `G(2τ²)/τ = ∑ c_i R_i(τ)`
  have hGR : ∀ τ, G (2 * τ ^ 2) / τ = ∑ i ∈ s, c i * R i τ := fun τ => by
    simp only [hG, hR]
    have e1 : ∀ i, c i * ((∫ p, Real.exp (-LQGMetric.GFFExist.dist2 p ^ 2 / (4 * τ ^ 2)) ∂(m i) -
        (m i).real univ * Real.exp (-1 / (4 * τ ^ 2))) / τ) =
        c i * (∫ p, Real.exp (-‖p.1 - p.2‖ ^ 2 / (2 * (2 * τ ^ 2))) ∂(m i)) / τ -
          (c i * (m i).real univ) * (Real.exp (-1 / (4 * τ ^ 2)) / τ) := fun i => by
      have : ∀ p : ℂ × ℂ, -LQGMetric.GFFExist.dist2 p ^ 2 / (4 * τ ^ 2) =
          -‖p.1 - p.2‖ ^ 2 / (2 * (2 * τ ^ 2)) := fun p => by
        unfold LQGMetric.GFFExist.dist2; ring
      simp_rw [this]
      ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, zero_mul, sub_zero, Finset.sum_div]
  have hint : IntegrableOn (fun τ => G (2 * τ ^ 2) / τ) (Ioi 0) := by
    simp_rw [hGR]
    exact integrable_finsetSum s fun i hi => (hrep i hi).1.const_mul (c i)
  have hval : ∫ τ in Ioi 0, G (2 * τ ^ 2) / τ =
      -∑ i ∈ s, c i * ∫ p, Real.log ‖p.1 - p.2‖ ∂(m i) := by
    simp_rw [hGR]
    rw [integral_finsetSum s fun i hi => (hrep i hi).1.const_mul (c i), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, (hrep i hi).2, mul_neg]
  -- back to `t`
  have heq : EqOn (fun t => Real.pi * ∑ i ∈ s, c i * ∫ p, heatKernel t p.1 p.2 ∂(m i))
      (fun t => G t / (2 * t)) (Ioi 0) := fun t ht => by
    have ht0 : t ≠ 0 := (mem_Ioi.mp ht).ne'
    simp only [hG, integral_heatKernel_eq]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  refine ⟨(integrableOn_Ioi_subst hint).congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, LQGMetric.GFFExist.integral_Ioi_subst G, hval]

end WNFrame
end GaussianLQG
