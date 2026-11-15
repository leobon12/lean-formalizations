import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import QuantumZipper.Proofs.Probability.BMMoments
import InteractingSLE.Foundations.Brownian.Exit

/-!
# Planar Brownian motion

Packet GEO-BM of the geometry foundation (`planning/INFRA-GEO.md` §3 "SLE", §4). Infrastructure
(textbook material: [Law05] Lawler, *Conformally Invariant Processes in the Plane*, Ch. 2;
[RY] Revuz–Yor, *Continuous Martingales and Brownian Motion*, Ch. I, IV), not a frozen
source-facing file.

* `planarGaussian v` is the centred Gaussian law on `ℂ ≅ ℝ²` with covariance `v • I` (real and
  imaginary parts independent `N(0, v)`).
* `IsPlanarBrownian 𝓕 Z P`: `Z : ℝ≥0 → Ω → ℂ` is a planar Brownian motion with respect to the
  filtration `𝓕` ("`(𝓕_t)`-Brownian motion", [RY] Def. IV.1.1 in dimension two): adapted, with
  continuous paths, each increment `Z t − Z s` (`s ≤ t`) independent of `𝓕 s` and of law
  `planarGaussian (t − s)`. The starting point is `Z 0` (a planar Brownian motion "started at
  `z`" is one with `Z 0 = z`).
* Gaussian moments of `planarGaussian` and the weak Markov property in integrated form
  (`IsPlanarBrownian.integral_mul_comp_sub`): for `𝓕 a`-measurable `G`,
  `E[G φ(Z (a+h) − Z a)] = E[G] ∫ φ d(planarGaussian h)`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

/-- The centred planar Gaussian law of variance `v` in each coordinate: the image of
`N(0, v) ⊗ N(0, v)` under `(x, y) ↦ x + y i`. -/
def planarGaussian (v : ℝ≥0) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map Complex.measurableEquivRealProd.symm

instance (v : ℝ≥0) : IsProbabilityMeasure (planarGaussian v) := by
  unfold planarGaussian
  exact (Measure.isProbabilityMeasure_map_iff
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable).2 inferInstance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `Z` is a **planar Brownian motion** with respect to the filtration `𝓕` under `P`: it is
adapted, has continuous paths, and each increment `Z t − Z s` (`s ≤ t`) is independent of `𝓕 s`
with law `planarGaussian (t − s)`. Its starting point is `Z 0`. -/
structure IsPlanarBrownian (𝓕 : Filtration ℝ≥0 mΩ) (Z : ℝ≥0 → Ω → ℂ) (P : Measure Ω) : Prop where
  measurable : ∀ t, Measurable[𝓕 t] (Z t)
  continuous : ∀ ω, Continuous (Z · ω)
  indep : ∀ s t, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => Z t ω - Z s ω) inferInstance) (𝓕 s) P
  map_sub : ∀ s t, s ≤ t → P.map (fun ω => Z t ω - Z s ω) = planarGaussian (t - s)

namespace PlanarBM

/-! ### Moments of the planar Gaussian -/

lemma integral_planarGaussian (v : ℝ≥0) (φ : ℂ → ℝ) :
    ∫ w, φ w ∂(planarGaussian v) =
      ∫ p, φ (Complex.measurableEquivRealProd.symm p) ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) :=
  integral_map_equiv _ _

lemma integrable_planarGaussian_iff (v : ℝ≥0) {φ : ℂ → ℝ} :
    Integrable φ (planarGaussian v) ↔
      Integrable (fun p => φ (Complex.measurableEquivRealProd.symm p))
        ((gaussianReal 0 v).prod (gaussianReal 0 v)) :=
  integrable_map_equiv _ _

lemma integral_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    ∫ x, |x| ^ n ∂(gaussianReal 0 v) = (v : ℝ) ^ ((n : ℝ) / 2) * QuantumZipper.gaussianAbsMoment n := by
  have hv0 : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hsqrt : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hcsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv0
  have hmap : gaussianReal (0 : ℝ) v = (gaussianReal (0 : ℝ) 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      push_cast
      rw [hcsq]
      ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ n = (v : ℝ) ^ ((n : ℝ) / 2) * |x| ^ n := by
    intro x
    rw [abs_mul, abs_of_nonneg hsqrt, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (Real.sqrt v) n, Real.sqrt_eq_rpow, ← Real.rpow_mul hv0]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) (n : ℝ≥0) (gaussianReal 0 v) := memLp_id_gaussianReal n
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

lemma integrable_id_gaussianReal (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

lemma integrable_sq_gaussianReal (v : ℝ≥0) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  have := integrable_abs_pow_gaussianReal v 2
  simpa [sq_abs] using this

lemma integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at h
  have h0 : ∫ x, id x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [h0] at h
  simpa using h

/-- Real part of a planar Gaussian sample through the product coordinates. -/
lemma re_symm (p : ℝ × ℝ) : (Complex.measurableEquivRealProd.symm p).re = p.1 := rfl

lemma im_symm (p : ℝ × ℝ) : (Complex.measurableEquivRealProd.symm p).im = p.2 := rfl

lemma integral_re_planarGaussian (v : ℝ≥0) : ∫ w, w.re ∂(planarGaussian v) = 0 := by
  rw [integral_planarGaussian]
  simp only [re_symm]
  rw [integral_fun_fst (fun x : ℝ => x), integral_id_gaussianReal]
  simp

lemma integral_im_planarGaussian (v : ℝ≥0) : ∫ w, w.im ∂(planarGaussian v) = 0 := by
  rw [integral_planarGaussian]
  simp only [im_symm]
  rw [integral_fun_snd (fun x : ℝ => x), integral_id_gaussianReal]
  simp

lemma integral_re_sq_planarGaussian (v : ℝ≥0) :
    ∫ w, w.re ^ 2 ∂(planarGaussian v) = v := by
  rw [integral_planarGaussian]
  simp only [re_symm]
  rw [integral_fun_fst (fun x : ℝ => x ^ 2), integral_sq_gaussianReal]
  simp

lemma integral_im_sq_planarGaussian (v : ℝ≥0) :
    ∫ w, w.im ^ 2 ∂(planarGaussian v) = v := by
  rw [integral_planarGaussian]
  simp only [im_symm]
  rw [integral_fun_snd (fun x : ℝ => x ^ 2), integral_sq_gaussianReal]
  simp

lemma integral_re_mul_im_planarGaussian (v : ℝ≥0) :
    ∫ w, w.re * w.im ∂(planarGaussian v) = 0 := by
  rw [integral_planarGaussian]
  simp only [re_symm, im_symm]
  rw [integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x), integral_id_gaussianReal]
  simp

lemma integrable_re_planarGaussian (v : ℝ≥0) : Integrable (fun w : ℂ => w.re) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_id_gaussianReal v).comp_fst _

lemma integrable_im_planarGaussian (v : ℝ≥0) : Integrable (fun w : ℂ => w.im) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_id_gaussianReal v).comp_snd _

lemma integrable_re_sq_planarGaussian (v : ℝ≥0) :
    Integrable (fun w : ℂ => w.re ^ 2) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_sq_gaussianReal v).comp_fst _

lemma integrable_im_sq_planarGaussian (v : ℝ≥0) :
    Integrable (fun w : ℂ => w.im ^ 2) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_sq_gaussianReal v).comp_snd _

lemma integrable_re_mul_im_planarGaussian (v : ℝ≥0) :
    Integrable (fun w : ℂ => w.re * w.im) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_id_gaussianReal v).mul_prod (integrable_id_gaussianReal v)

lemma integrable_abs_re_pow_planarGaussian (v : ℝ≥0) (n : ℕ) :
    Integrable (fun w : ℂ => |w.re| ^ n) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_abs_pow_gaussianReal v n).comp_fst _

lemma integrable_abs_im_pow_planarGaussian (v : ℝ≥0) (n : ℕ) :
    Integrable (fun w : ℂ => |w.im| ^ n) (planarGaussian v) := by
  rw [integrable_planarGaussian_iff]
  exact (integrable_abs_pow_gaussianReal v n).comp_snd _

lemma integral_abs_re_pow_planarGaussian (v : ℝ≥0) (n : ℕ) :
    ∫ w, |w.re| ^ n ∂(planarGaussian v) = (v : ℝ) ^ ((n : ℝ) / 2) * QuantumZipper.gaussianAbsMoment n := by
  rw [integral_planarGaussian]
  simp only [re_symm]
  rw [integral_fun_fst (fun x : ℝ => |x| ^ n), integral_abs_pow_gaussianReal]
  simp

lemma integral_abs_im_pow_planarGaussian (v : ℝ≥0) (n : ℕ) :
    ∫ w, |w.im| ^ n ∂(planarGaussian v) = (v : ℝ) ^ ((n : ℝ) / 2) * QuantumZipper.gaussianAbsMoment n := by
  rw [integral_planarGaussian]
  simp only [im_symm]
  rw [integral_fun_snd (fun x : ℝ => |x| ^ n), integral_abs_pow_gaussianReal]
  simp

lemma rpow_three_halves_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (((3 : ℕ) : ℝ) / 2) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (((3 : ℕ) : ℝ) / 2) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

lemma rpow_one_half_eq (x : ℝ) : x ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]; norm_num

lemma norm_pow_three_le (w : ℂ) : ‖w‖ ^ 3 ≤ 4 * (|w.re| ^ 3 + |w.im| ^ 3) := by
  have h := Complex.norm_le_abs_re_add_abs_im w
  have ha := abs_nonneg w.re
  have hb := abs_nonneg w.im
  calc ‖w‖ ^ 3 ≤ (|w.re| + |w.im|) ^ 3 := pow_le_pow_left₀ (norm_nonneg w) h 3
    _ ≤ 4 * (|w.re| ^ 3 + |w.im| ^ 3) := by
      nlinarith [sq_nonneg (|w.re| - |w.im|), mul_nonneg ha hb,
        mul_nonneg (mul_nonneg ha hb) (add_nonneg ha hb)]

lemma integrable_norm_pow_three_planarGaussian (v : ℝ≥0) :
    Integrable (fun w : ℂ => ‖w‖ ^ 3) (planarGaussian v) := by
  refine Integrable.mono' (((integrable_abs_re_pow_planarGaussian v 3).add
    (integrable_abs_im_pow_planarGaussian v 3)).const_mul 4)
    (by fun_prop) (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_pow_three_le w

lemma integrable_norm_planarGaussian (v : ℝ≥0) :
    Integrable (fun w : ℂ => ‖w‖) (planarGaussian v) := by
  refine Integrable.mono' ((integrable_abs_re_pow_planarGaussian v 1).add
    (integrable_abs_im_pow_planarGaussian v 1)) (by fun_prop)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa using Complex.norm_le_abs_re_add_abs_im w

lemma integral_norm_pow_three_planarGaussian_le (v : ℝ≥0) :
    ∫ w, ‖w‖ ^ 3 ∂(planarGaussian v) ≤ 8 * QuantumZipper.gaussianAbsMoment 3 * ((v : ℝ) * Real.sqrt v) := by
  have h1 : ∫ w, ‖w‖ ^ 3 ∂(planarGaussian v) ≤ ∫ w, 4 * (|w.re| ^ 3 + |w.im| ^ 3) ∂(planarGaussian v) :=
    integral_mono (integrable_norm_pow_three_planarGaussian v)
      (((integrable_abs_re_pow_planarGaussian v 3).add
        (integrable_abs_im_pow_planarGaussian v 3)).const_mul 4) norm_pow_three_le
  rw [integral_const_mul, integral_add (integrable_abs_re_pow_planarGaussian v 3)
    (integrable_abs_im_pow_planarGaussian v 3), integral_abs_re_pow_planarGaussian,
    integral_abs_im_pow_planarGaussian, rpow_three_halves_eq v.coe_nonneg] at h1
  linarith

lemma integral_norm_planarGaussian_le (v : ℝ≥0) :
    ∫ w, ‖w‖ ∂(planarGaussian v) ≤ 2 * QuantumZipper.gaussianAbsMoment 1 * Real.sqrt v := by
  have h1 : ∫ w, ‖w‖ ∂(planarGaussian v) ≤ ∫ w, (|w.re| ^ 1 + |w.im| ^ 1) ∂(planarGaussian v) :=
    integral_mono (integrable_norm_planarGaussian v)
      ((integrable_abs_re_pow_planarGaussian v 1).add (integrable_abs_im_pow_planarGaussian v 1))
      (fun w => by simpa using Complex.norm_le_abs_re_add_abs_im w)
  rw [integral_add (integrable_abs_re_pow_planarGaussian v 1)
    (integrable_abs_im_pow_planarGaussian v 1), integral_abs_re_pow_planarGaussian,
    integral_abs_im_pow_planarGaussian, rpow_one_half_eq] at h1
  linarith

end PlanarBM

/-! ### Basic properties of planar Brownian motion -/

namespace IsPlanarBrownian

variable {𝓕 : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ} {P : Measure Ω}

lemma measurable' (hZ : IsPlanarBrownian 𝓕 Z P) (t : ℝ≥0) : Measurable (Z t) :=
  (hZ.measurable t).mono (𝓕.le t) le_rfl

lemma measurable_sub (hZ : IsPlanarBrownian 𝓕 Z P) (s t : ℝ≥0) :
    Measurable (fun ω => Z t ω - Z s ω) :=
  (hZ.measurable' t).sub (hZ.measurable' s)

lemma isProbabilityMeasure (hZ : IsPlanarBrownian 𝓕 Z P) : IsProbabilityMeasure P := by
  have h := hZ.map_sub 0 0 le_rfl
  constructor
  have h1 : (P.map (fun ω => Z 0 ω - Z 0 ω)) univ = P univ :=
    Measure.map_apply (hZ.measurable_sub 0 0) MeasurableSet.univ
  rw [h, measure_univ] at h1
  exact h1.symm

/-- Weak Markov property, integrated form: an `𝓕 a`-measurable factor and a function of the
increment after `a` integrate independently. -/
lemma integral_mul_comp_sub (hZ : IsPlanarBrownian 𝓕 Z P) {a h : ℝ≥0} {G : Ω → ℝ}
    (hG : Measurable[𝓕 a] G) {φ : ℂ → ℝ} (hφ : Measurable φ) :
    ∫ ω, G ω * φ (Z (a + h) ω - Z a ω) ∂P
      = (∫ ω, G ω ∂P) * ∫ w, φ w ∂(planarGaussian h) := by
  have hind : IndepFun G (fun ω => φ (Z (a + h) ω - Z a ω)) P := by
    rw [IndepFun_iff_Indep]
    have h1 := hZ.indep a (a + h) le_self_add
    have hY : MeasurableSpace.comap (fun ω => φ (Z (a + h) ω - Z a ω)) inferInstance ≤
        MeasurableSpace.comap (fun ω => Z (a + h) ω - Z a ω) inferInstance :=
      (hφ.comp (Measurable.of_comap_le le_rfl)).comap_le
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_left h1 hY).symm hG.comap_le
  have hGm : Measurable G := hG.mono (𝓕.le a) le_rfl
  have hYm : Measurable (fun ω => φ (Z (a + h) ω - Z a ω)) := hφ.comp (hZ.measurable_sub a (a + h))
  have h2 := hind.integral_mul_eq_mul_integral hGm.aestronglyMeasurable hYm.aestronglyMeasurable
  simp only [Pi.mul_apply] at h2
  rw [h2]
  congr 1
  have hlaw := hZ.map_sub a (a + h) le_self_add
  rw [add_tsub_cancel_left] at hlaw
  rw [← hlaw, integral_map (hZ.measurable_sub a (a + h)).aemeasurable hφ.aestronglyMeasurable]

/-- The law of an increment, in integrated form. -/
lemma integral_comp_sub (hZ : IsPlanarBrownian 𝓕 Z P) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : ℂ → ℝ} (hφ : Measurable φ) :
    ∫ ω, φ (Z t ω - Z s ω) ∂P = ∫ w, φ w ∂(planarGaussian (t - s)) := by
  rw [← hZ.map_sub s t hst, integral_map (hZ.measurable_sub s t).aemeasurable hφ.aestronglyMeasurable]

lemma integrable_comp_sub (hZ : IsPlanarBrownian 𝓕 Z P) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : ℂ → ℝ} (hφ : Integrable φ (planarGaussian (t - s))) :
    Integrable (fun ω => φ (Z t ω - Z s ω)) P := by
  rw [← hZ.map_sub s t hst] at hφ
  exact hφ.comp_measurable (hZ.measurable_sub s t)

lemma integrable_norm_sub (hZ : IsPlanarBrownian 𝓕 Z P) {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun ω => ‖Z t ω - Z s ω‖) P :=
  hZ.integrable_comp_sub hst (PlanarBM.integrable_norm_planarGaussian _)

lemma integral_norm_sub_le (hZ : IsPlanarBrownian 𝓕 Z P) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, ‖Z t ω - Z s ω‖ ∂P ≤ 2 * QuantumZipper.gaussianAbsMoment 1 * Real.sqrt ((t : ℝ) - s) := by
  rw [hZ.integral_comp_sub hst continuous_norm.measurable]
  have := PlanarBM.integral_norm_planarGaussian_le (t - s)
  rwa [NNReal.coe_sub hst] at this

end IsPlanarBrownian

end InteractingSLE
