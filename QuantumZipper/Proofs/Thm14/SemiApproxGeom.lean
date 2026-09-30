import QuantumZipper.Proofs.Thm14.SemiApproxPolar
import QuantumZipper.Proofs.Thm14.FcRPairEnergy
import QuantumZipper.Proofs.Zipper.RegContEnergy

/-!
# SEMI-APPROX, part 3: geometry of `Γ_e` and integrability of the dominating functions

For `p, q` in the box `(-1,1) × (0,π)` and `|e|, |e'| ≤ s/4`:

* `saGam_mem_H`, `norm_saGam_le`, `im_saGam_bounds`: `Γ_e p ∈ ℍ`, `‖Γ_e p‖ ≤ |c| + 2s`,
  `(3s/4) sin θ ≤ Im Γ_e p ≤ 5s/4`;
* `dist_saGam_bounds`: `(3s/4) ‖u θ − u θ'‖ ≤ ‖Γ_e p − Γ_{e'} q‖ ≤ 5s/2` (`u = circleMap 0 1`);
* `integrable_logSin_saM`, `integrable_logChord_saM`: `|log sin θ|` is integrable on `saM`, and
  `|log ‖u θ − u θ'‖|` is integrable on `saM ⊗ saM` (Frostman bound of the semicircle and
  `TwoPoint.integrable_logRatio`).

Own elementary arguments.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

/-- The unit semicircle parametrization. -/
def saU (θ : ℝ) : ℂ := circleMap 0 1 θ

theorem sa_abs_log_le {a b x y : ℝ} (ha : 0 < a) (hx : 0 < x) (h1 : a * x ≤ y) (h2 : y ≤ b) :
    |Real.log y| ≤ |Real.log a| + |Real.log b| + |Real.log x| := by
  have hy : 0 < y := lt_of_lt_of_le (mul_pos ha hx) h1
  have l1 : Real.log a + Real.log x ≤ Real.log y := by
    rw [← Real.log_mul ha.ne' hx.ne']; exact Real.log_le_log (mul_pos ha hx) h1
  have l2 : Real.log y ≤ Real.log b := Real.log_le_log hy h2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b), le_abs_self (Real.log x),
    neg_abs_le (Real.log x)]

theorem sa_sq_ineq {ρ ρ' m a b a' b' : ℝ} (hm : 0 ≤ m) (h1 : m ≤ ρ) (h2 : m ≤ ρ')
    (ha : a ^ 2 + b ^ 2 = 1) (ha' : a' ^ 2 + b' ^ 2 = 1) :
    m ^ 2 * ((a - a') ^ 2 + (b - b') ^ 2) ≤ (ρ * a - ρ' * a') ^ 2 + (ρ * b - ρ' * b') ^ 2 := by
  have hS : 0 ≤ (a - a') ^ 2 + (b - b') ^ 2 := by positivity
  have hρρ : m ^ 2 ≤ ρ * ρ' := by nlinarith
  have key : (ρ * a - ρ' * a') ^ 2 + (ρ * b - ρ' * b') ^ 2 - m ^ 2 * ((a - a') ^ 2 + (b - b') ^ 2)
      = (ρ - ρ') ^ 2 + (ρ * ρ' - m ^ 2) * ((a - a') ^ 2 + (b - b') ^ 2) := by
    linear_combination (ρ ^ 2 - ρ * ρ') * ha + (ρ' ^ 2 - ρ * ρ') * ha'
  nlinarith [sq_nonneg (ρ - ρ'), mul_nonneg (sub_nonneg.2 hρρ) hS]

theorem sq_norm_circleMap_sub (c : ℂ) (ρ ρ' θ θ' : ℝ) :
    ‖circleMap c ρ θ - circleMap c ρ' θ'‖ ^ 2 =
      (ρ * Real.cos θ - ρ' * Real.cos θ') ^ 2 + (ρ * Real.sin θ - ρ' * Real.sin θ') ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [circleMap, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem norm_circleMap_sub_ge (c : ℂ) {ρ ρ' m : ℝ} (hm : 0 ≤ m) (h1 : m ≤ ρ) (h2 : m ≤ ρ')
    (θ θ' : ℝ) : m * ‖saU θ - saU θ'‖ ≤ ‖circleMap c ρ θ - circleMap c ρ' θ'‖ := by
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rw [mul_pow, saU, saU, sq_norm_circleMap_sub, sq_norm_circleMap_sub]
  simp only [one_mul]
  exact sa_sq_ineq hm h1 h2 (Real.cos_sq_add_sin_sq θ) (Real.cos_sq_add_sin_sq θ')

theorem saU_ne {θ θ' : ℝ} (hθ : θ ∈ Ioo 0 π) (hθ' : θ' ∈ Ioo 0 π) (h : θ ≠ θ') :
    saU θ ≠ saU θ' := by
  intro he
  have : Real.cos θ = Real.cos θ' := by
    have := congrArg Complex.re he
    simpa [saU, circleMap, Complex.exp_ofReal_mul_I_re] using this
  exact h (Real.injOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨hθ'.1.le, hθ'.2.le⟩ this)

/-- The box `(-1,1) × (0,π)`. -/
def saBox : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 π

theorem saRad_bounds {s e : ℝ} {p : ℝ × ℝ} (he : |e| ≤ s / 4) (hp : p ∈ saBox) :
    3 * s / 4 ≤ s + e * p.1 ∧ s + e * p.1 ≤ 5 * s / 4 := by
  have h1 : |e * p.1| ≤ s / 4 := by
    rw [abs_mul]
    have : |p.1| ≤ 1 := abs_le.2 ⟨hp.1.1.le, hp.1.2.le⟩
    nlinarith [abs_nonneg e, abs_nonneg p.1]
  rw [abs_le] at h1
  constructor <;> linarith [h1.1, h1.2]

theorem im_saGam (c s e : ℝ) (p : ℝ × ℝ) :
    (saGam c s e p).im = (s + e * p.1) * Real.sin p.2 := im_circleMap_real _ _ _

theorem im_saGam_bounds {c s e : ℝ} (hs : 0 < s) {p : ℝ × ℝ} (he : |e| ≤ s / 4)
    (hp : p ∈ saBox) : 3 * s / 4 * Real.sin p.2 ≤ (saGam c s e p).im ∧
      (saGam c s e p).im ≤ 5 * s / 4 := by
  obtain ⟨h1, h2⟩ := saRad_bounds he hp
  have hsin := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
  have hsin1 := Real.sin_le_one p.2
  rw [im_saGam]
  constructor <;> nlinarith

theorem saGam_mem_H {c s e : ℝ} (hs : 0 < s) {p : ℝ × ℝ} (he : |e| ≤ s / 4) (hp : p ∈ saBox) :
    saGam c s e p ∈ H := by
  have := (im_saGam_bounds (c := c) hs he hp).1
  have hsin := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
  show 0 < (saGam c s e p).im
  nlinarith

theorem norm_saGam_le {c s e : ℝ} (hs : 0 < s) {p : ℝ × ℝ} (he : |e| ≤ s / 4) (hp : p ∈ saBox) :
    ‖saGam c s e p‖ ≤ |c| + 2 * s := by
  obtain ⟨h1, h2⟩ := saRad_bounds he hp
  unfold saGam circleMap
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < s + e * p.1 by linarith)]
  linarith

theorem dist_saGam_bounds {c s e e' : ℝ} (hs : 0 < s) {p q : ℝ × ℝ} (he : |e| ≤ s / 4)
    (he' : |e'| ≤ s / 4) (hp : p ∈ saBox) (hq : q ∈ saBox) :
    3 * s / 4 * ‖saU p.2 - saU q.2‖ ≤ ‖saGam c s e p - saGam c s e' q‖ ∧
      ‖saGam c s e p - saGam c s e' q‖ ≤ 5 * s / 2 := by
  obtain ⟨h1, h2⟩ := saRad_bounds he hp
  obtain ⟨h1', h2'⟩ := saRad_bounds he' hq
  refine ⟨norm_circleMap_sub_ge _ (by positivity) h1 h1' _ _, ?_⟩
  have e1 : saGam c s e p - saGam c s e' q = circleMap 0 (s + e * p.1) p.2 -
      circleMap 0 (s + e' * q.1) q.2 := by
    simp only [saGam, circleMap]; ring
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  simp only [circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (show (0:ℝ) < s + e * p.1 by linarith),
    abs_of_pos (show (0:ℝ) < s + e' * q.1 by linarith)]
  linarith

/-! ## Integrability of the dominating functions -/

theorem ae_saM_mem : ∀ᵐ p ∂saM, p ∈ saBox := by
  unfold saM saBox
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

theorem integrable_logSin_saM : Integrable (fun p : ℝ × ℝ => |Real.log (Real.sin p.2)|) saM := by
  have h : IntegrableOn (fun θ => Real.log (Real.sin θ)) (Ioo 0 π) := by
    have := (intervalIntegrable_log_sin (a := 0) (b := π))
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le] at this
    exact this
  unfold saM
  exact (Integrable.comp_snd_iff (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (by simp)).2 h.abs

/-- The semicircle measure in parameter form is Frostman of exponent `1`. -/
theorem isFrostman_saU :
    TwoPoint.IsFrostman (saM.map fun p => saU p.2) 1 (12 * π) := by
  have hm : Measurable fun p : ℝ × ℝ => saU p.2 :=
    (continuous_circleMap 0 1).measurable.comp measurable_snd
  have hfc := foldedCircle_real_eq 0 zero_le_one
  simp only [Complex.ofReal_zero] at hfc
  intro w r hr
  have hS : MeasurableSet (Metric.closedBall w r) := Metric.isClosed_closedBall.measurableSet
  have e1 : (saM.map fun p => saU p.2) (Metric.closedBall w r) =
      ENNReal.ofReal 2 * ENNReal.ofReal π * foldedCircle 0 1 (Metric.closedBall w r) := by
    rw [Measure.map_apply hm hS, hfc, Measure.smul_apply,
      Measure.map_apply (continuous_circleMap 0 1).measurable hS, smul_eq_mul, ← mul_assoc,
      mul_assoc (ENNReal.ofReal 2), ENNReal.mul_inv_cancel (by simp [Real.pi_pos])
        ENNReal.ofReal_ne_top, mul_one]
    have : (fun p : ℝ × ℝ => saU p.2) ⁻¹' Metric.closedBall w r =
        univ ×ˢ (circleMap 0 1 ⁻¹' Metric.closedBall w r) := by ext p; simp [saU]
    rw [this]
    unfold saM
    rw [Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num
  have h2 := RegCont.foldedCircle_closedBall_le_arc 0 w one_pos hr.le
  rw [e1, Real.rpow_one]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal Real.pi_pos.le]
  have h3 := ENNReal.toReal_le_of_le_ofReal (by positivity) h2
  rw [div_one] at h3
  nlinarith [Real.pi_pos]

theorem integrable_logChord_saM :
    Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => |Real.log ‖saU x.1.2 - saU x.2.2‖|)
      (saM.prod saM) := by
  set ν := saM.map fun p => saU p.2 with hν
  have hm : Measurable fun p : ℝ × ℝ => saU p.2 :=
    (continuous_circleMap 0 1).measurable.comp measurable_snd
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hF := isFrostman_saU
  have hC : (0 : ℝ) ≤ 12 * π := by positivity
  have hB : ∀ᵐ y ∂ν, ‖y‖ ≤ 1 := by
    rw [hν, ae_map_iff hm.aemeasurable (measurableSet_le measurable_norm measurable_const)]
    exact ae_of_all _ fun p => by simp [saU]
  have hLm : Measurable fun x : ℂ × ℂ => |Real.log ‖x.1 - x.2‖| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm)
  have hLz : ∀ z : ℂ, Measurable fun y : ℂ => |Real.log ‖z - y‖| := fun z =>
    continuous_abs.measurable.comp (Real.measurable_log.comp (measurable_const.sub measurable_id).norm)
  have hGm : Measurable fun x : (ℝ × ℝ) × (ℝ × ℝ) => |Real.log ‖saU x.1.2 - saU x.2.2‖| :=
    hLm.comp ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd))
  have hint : ∀ z : ℂ, Integrable (fun q : ℝ × ℝ => |Real.log ‖z - saU q.2‖|) saM := fun z => by
    have := (TwoPoint.frostman_integrable_log hF one_pos hC zero_le_one hB z).abs
    rw [integrable_map_measure (hLz z).aestronglyMeasurable hm.aemeasurable] at this
    exact this
  have hbd : ∀ z : ℂ, ‖z‖ = 1 → ∫ q, |Real.log ‖z - saU q.2‖| ∂saM ≤
      12 * π + |Real.log 3| * ν.real univ := fun z hz => by
    have e : ∫ q, |Real.log ‖z - saU q.2‖| ∂saM = ∫ y, |Real.log ‖z - y‖| ∂ν := by
      rw [hν, integral_map hm.aemeasurable (hLz z).aestronglyMeasurable]
    rw [e]
    have hi := TwoPoint.integrable_logRatio hF one_pos hC z one_pos
    calc ∫ y, |Real.log ‖z - y‖| ∂ν ≤ ∫ y, (TwoPoint.logRatio 1 z y + |Real.log 3|) ∂ν := by
          refine integral_mono_ae (TwoPoint.frostman_integrable_log hF one_pos hC zero_le_one
            hB z).abs (hi.add (integrable_const _)) ?_
          filter_upwards [hB] with y hy
          have := TwoPoint.abs_log_norm_sub_le zero_le_one hy (x := z)
          rw [hz] at this; norm_num at this; exact this
      _ = (∫ y, TwoPoint.logRatio 1 z y ∂ν) + |Real.log 3| * ν.real univ := by
          rw [integral_add hi (integrable_const _), integral_const, smul_eq_mul, mul_comm]
      _ ≤ 12 * π + |Real.log 3| * ν.real univ := by
          have := TwoPoint.integral_logRatio_le hF one_pos hC z one_pos
          rw [Real.one_rpow, mul_one, div_one] at this
          linarith
  rw [integrable_prod_iff hGm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun p => hint (saU p.2), ?_⟩
  refine Integrable.of_bound (hGm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    (12 * π + |Real.log 3| * ν.real univ) (ae_of_all _ fun p => ?_)
  simp only [Real.norm_eq_abs, abs_abs]
  rw [abs_of_nonneg (integral_nonneg fun q => abs_nonneg _)]
  exact hbd _ (by simp [saU])

end Thm14WDG
end QuantumZipper
