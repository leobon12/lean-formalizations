import GaussianLQG.Energy.Coupling

/-!
# Segment energies, part 1 (blueprint Lemma `lem:segments` (a), (b))

* `energy_segMeasure_eq_intervalIntegral`: `ℰ(λ_{a,b}, λ_{c,d}) = ∫₀¹∫₀¹ G(φ(u), ψ(v)) dv du`
  for the affine parametrizations `φ, ψ`; `energy_segMeasure_eq_integral_prod` is the same on
  `[0,1]²` with integrability, for nondegenerate segments.
* `integral_mul_log_zero_one`: `∫₀¹ x log x dx = -1/4`.
* (a) `energy_segMeasure_zero_one`: `ℰ(λ_{0,1}, λ_{0,1}) = ∫₀¹∫₀¹ -log|u-v| = 3/2`.
* (b) `three_halves_le_energy_segMeasure_I`: `ℰ(λ_{i,1+i}, λ_{i,1+i}) ≥ 3/2`;
  `abs_energy_segMeasure_zero_one_I_le`: `|ℰ(λ_{0,1}, λ_{i,1+i})| ≤ (log 2)/2`; and the Gram
  determinant bound `segMeasure_gram_det_pos`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Complex
open scoped ENNReal Real

namespace GaussianLQG

/-! ## Energies of segment measures as integrals over `[0,1]²` -/

/-- `ℰ(λ_{a,b}, λ_{c,d}) = ∫₀¹ ∫₀¹ G((1-u)a + ub, (1-v)c + vd) dv du` (no integrability needed). -/
theorem energy_segMeasure_eq_intervalIntegral (a b c d : ℂ) :
    energy (segMeasure a b) (segMeasure c d) =
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, kernelG (segPath a b u) (segPath c d v) := by
  unfold energy
  rw [integral_segMeasure a b
    (measurable_kernelG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only
  rw [integral_segMeasure c d (by fun_prop : Measurable fun w => kernelG _ w).aestronglyMeasurable]
  rfl

/-- For nondegenerate segments, `G ∘ (φ × ψ)` is integrable on `[0,1]²` and its integral is
`ℰ(λ_{a,b}, λ_{c,d})`. -/
theorem energy_segMeasure_eq_integral_prod {a b c d : ℂ} (hab : a ≠ b) (hcd : c ≠ d) :
    Integrable (fun q : ℝ × ℝ => kernelG (segPath a b q.1) (segPath c d q.2))
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) ∧
      energy (segMeasure a b) (segMeasure c d) =
        ∫ q : ℝ × ℝ, kernelG (segPath a b q.1) (segPath c d q.2)
          ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  set L : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hL
  have hm : Measurable (Prod.map (segPath a b) (segPath c d)) :=
    (measurable_segPath a b).prodMap (measurable_segPath c d)
  have hmap : (segMeasure a b).prod (segMeasure c d) =
      (L.prod L).map (Prod.map (segPath a b) (segPath c d)) := by
    rw [segMeasure_eq_map, segMeasure_eq_map,
      Measure.map_prod_map L L (measurable_segPath a b) (measurable_segPath c d)]
  have hint := (isRegular_segMeasure hab).integrable_kernelG (isRegular_segMeasure hcd)
  rw [hmap] at hint
  refine ⟨(integrable_map_measure measurable_kernelG.aestronglyMeasurable
    hm.aemeasurable).1 hint, ?_⟩
  rw [energy_eq_integral_prod (isRegular_segMeasure hab) (isRegular_segMeasure hcd), hmap,
    integral_map hm.aemeasurable measurable_kernelG.aestronglyMeasurable]
  rfl

/-- Lebesgue-a.e. point of `[0,1]²` (for the restricted product measure) lies in `[0,1]²`. -/
theorem ae_mem_Icc_prod :
    ∀ᵐ q ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))),
      q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ Icc (0 : ℝ) 1 := by
  have h0 : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)), u ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ν := volume.restrict (Icc (0 : ℝ) 1))).ae h0
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ν := volume.restrict (Icc (0 : ℝ) 1))).ae h0
  filter_upwards [h1, h2] with q hq1 hq2 using ⟨hq1, hq2⟩

/-! ## One-dimensional integrals -/

/-- `∫₀¹ x log x dx = -1/4`. -/
theorem integral_mul_log_zero_one : ∫ x in (0 : ℝ)..1, x * Real.log x = -1 / 4 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x => x * (x * Real.log x) / 2 - x ^ 2 / 4) (x * Real.log x) x := by
    intro x hx
    have h1 := ((hasDerivAt_id' x).mul (Real.hasDerivAt_mul_log hx.1.ne')).div_const 2
    have h2 := h1.sub ((hasDerivAt_pow 2 x).div_const 4)
    refine h2.congr_deriv ?_
    norm_num
    ring
  have hcont : ContinuousOn (fun x : ℝ => x * (x * Real.log x) / 2 - x ^ 2 / 4) (Icc 0 1) :=
    (((continuous_id.mul Real.continuous_mul_log).div_const 2).sub
      ((continuous_pow 2).div_const 4)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    (Real.continuous_mul_log.intervalIntegrable 0 1)]
  simp only [Real.log_one, mul_zero, zero_mul]
  norm_num

/-- `∫_{-1}^0 x log x dx = 1/4`. -/
theorem integral_mul_log_neg_one_zero : ∫ x in (-1 : ℝ)..0, x * Real.log x = 1 / 4 := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun x : ℝ => x * Real.log x)
  simp only [neg_zero, Real.log_neg_eq_log] at h
  rw [← h]
  simp only [neg_mul, intervalIntegral.integral_neg, integral_mul_log_zero_one]
  norm_num

/-- `∫₀¹ log(u - v) dv = u log u + (1-u) log(1-u) - 1` (with `log 0 = 0`). -/
theorem integral_log_sub (u : ℝ) :
    ∫ v in (0 : ℝ)..1, Real.log (u - v) = u * Real.log u - (u - 1) * Real.log (u - 1) - 1 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x => Real.log x) u, sub_zero, integral_log]
  ring

/-- `∫₀¹ ∫₀¹ -log|u - v| dv du = 3/2`. -/
theorem integral_integral_neg_log_abs_sub :
    ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, -Real.log |u - v| = 3 / 2 := by
  have hinner : ∀ u : ℝ, ∫ v in (0 : ℝ)..1, -Real.log |u - v| =
      1 - u * Real.log u + (u - 1) * Real.log (u - 1) := by
    intro u
    simp only [Real.log_abs]
    rw [intervalIntegral.integral_neg, integral_log_sub]
    ring
  simp only [hinner]
  have i1 : IntervalIntegrable (fun u : ℝ => u * Real.log u) volume 0 1 :=
    Real.continuous_mul_log.intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun u : ℝ => (u - 1) * Real.log (u - 1)) volume 0 1 :=
    (Real.continuous_mul_log.comp (continuous_sub_right 1)).intervalIntegrable 0 1
  have i0 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  rw [intervalIntegral.integral_add (i0.sub i1) i2, intervalIntegral.integral_sub i0 i1,
    integral_mul_log_zero_one,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x * Real.log x) 1]
  norm_num [integral_mul_log_neg_one_zero]

/-! ## (a) The unit segment -/

theorem segPath_zero_one (u : ℝ) : segPath 0 1 u = (u : ℂ) := by
  simp [segPath]

theorem norm_ofReal_sub_ofReal (u v : ℝ) : ‖(u : ℂ) - (v : ℂ)‖ = |u - v| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- On `[0,1]²`, `G(u, v) = -log|u - v|`. -/
theorem kernelG_ofReal_of_mem_Icc {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    kernelG (u : ℂ) (v : ℂ) = -Real.log |u - v| := by
  rw [kernelG, norm_ofReal_sub_ofReal, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hu.1, abs_of_nonneg hv.1, max_eq_left hu.2,
    max_eq_left hv.2, Real.log_one]
  ring

/-- Blueprint Lemma `lem:segments` (a): `ℰ(λ_{0,1}, λ_{0,1}) = 3/2`. -/
theorem energy_segMeasure_zero_one : energy (segMeasure 0 1) (segMeasure 0 1) = 3 / 2 := by
  rw [energy_segMeasure_eq_intervalIntegral, ← integral_integral_neg_log_abs_sub]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le zero_le_one] at hu
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  simp only [segPath_zero_one]
  exact kernelG_ofReal_of_mem_Icc hu hv

/-! ## (b) The segments `[0,1]` and `[i, 1+i]` -/

theorem segPath_I (u : ℝ) : segPath I (1 + I) u = (u : ℂ) + I := by
  simp only [segPath, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem zero_ne_one_complex : (0 : ℂ) ≠ 1 := zero_ne_one

theorem I_ne_one_add_I : I ≠ 1 + I := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- Blueprint Lemma `lem:segments` (b), first part: `ℰ(λ_{i,1+i}, λ_{i,1+i}) ≥ 3/2`. -/
theorem three_halves_le_energy_segMeasure_I :
    3 / 2 ≤ energy (segMeasure I (1 + I)) (segMeasure I (1 + I)) := by
  obtain ⟨i0, e0⟩ := energy_segMeasure_eq_integral_prod zero_ne_one_complex zero_ne_one_complex
  obtain ⟨i1, e1⟩ := energy_segMeasure_eq_integral_prod I_ne_one_add_I I_ne_one_add_I
  rw [← energy_segMeasure_zero_one, e0, e1]
  refine integral_mono i0 i1 fun q => ?_
  simp only [segPath_zero_one, segPath_I, kernelG]
  have hre : ∀ u : ℝ, ‖(u : ℂ)‖ ≤ ‖(u : ℂ) + I‖ := by
    intro u
    have := Complex.abs_re_le_norm ((u : ℂ) + I)
    simpa using this
  have hmono : ∀ u : ℝ, Real.log (max 1 ‖(u : ℂ)‖) ≤ Real.log (max 1 ‖(u : ℂ) + I‖) :=
    fun u => Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _))
      (max_le_max le_rfl (hre u))
  have e : (q.1 : ℂ) + I - ((q.2 : ℂ) + I) = (q.1 : ℂ) - (q.2 : ℂ) := by ring
  rw [e]
  linarith [hmono q.1, hmono q.2]

/-- `‖z‖ ≤ √2` when `|Re z| ≤ 1` and `|Im z| ≤ 1`. -/
theorem norm_le_sqrt_two {z : ℂ} (h1 : |z.re| ≤ 1) (h2 : |z.im| ≤ 1) : ‖z‖ ≤ √2 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  refine Real.sqrt_le_sqrt ?_
  have a1 : z.re ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg z.re]
  have a2 : z.im ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg z.im]
  linarith

/-- `log √2 = (log 2)/2`. -/
theorem log_sqrt_two : Real.log √2 = Real.log 2 / 2 := Real.log_sqrt (by norm_num)

/-- For `u, v ∈ [0,1]`, `|G(u, v + i)| ≤ (log 2)/2`. -/
theorem abs_kernelG_ofReal_add_I_le {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) : |kernelG (u : ℂ) ((v : ℂ) + I)| ≤ Real.log 2 / 2 := by
  have hu1 : max 1 ‖(u : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1, max_eq_left hu.2]
  -- `A = |u - v - i|` and `B = |v + i|` both lie in `[1, √2]`.
  set A := ‖(u : ℂ) - ((v : ℂ) + I)‖ with hA
  set B := ‖(v : ℂ) + I‖ with hB
  have hA1 : 1 ≤ A := by
    have := Complex.abs_im_le_norm ((u : ℂ) - ((v : ℂ) + I))
    simpa using this
  have hB1 : 1 ≤ B := by
    have := Complex.abs_im_le_norm ((v : ℂ) + I)
    simpa using this
  have hA2 : A ≤ √2 := by
    refine norm_le_sqrt_two ?_ ?_
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.I_re, add_zero]
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    · simp
  have hB2 : B ≤ √2 := by
    refine norm_le_sqrt_two ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      rw [abs_le]
      constructor <;> linarith [hv.1, hv.2]
    · simp
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hlogA : Real.log A ≤ Real.log 2 / 2 := by
    rw [← log_sqrt_two]
    exact Real.log_le_log (by linarith) hA2
  have hlogB : Real.log B ≤ Real.log 2 / 2 := by
    rw [← log_sqrt_two]
    exact Real.log_le_log (by linarith) hB2
  rw [kernelG, ← hA, hu1, Real.log_one, max_eq_right hB1, abs_le]
  constructor <;> linarith

/-- Blueprint Lemma `lem:segments` (b), second part: `|ℰ(λ_{0,1}, λ_{i,1+i})| ≤ (log 2)/2`. -/
theorem abs_energy_segMeasure_zero_one_I_le :
    |energy (segMeasure 0 1) (segMeasure I (1 + I))| ≤ Real.log 2 / 2 := by
  obtain ⟨-, e⟩ := energy_segMeasure_eq_integral_prod zero_ne_one_complex I_ne_one_add_I
  rw [e, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := (volume.restrict (Icc (0 : ℝ) 1)).prod
    (volume.restrict (Icc (0 : ℝ) 1)))
    (f := fun q : ℝ × ℝ => kernelG (segPath 0 1 q.1) (segPath I (1 + I) q.2))
    (C := Real.log 2 / 2) (by
      filter_upwards [ae_mem_Icc_prod] with q hq
      simp only [segPath_zero_one, segPath_I, Real.norm_eq_abs]
      exact abs_kernelG_ofReal_add_I_le hq.1 hq.2)
  rwa [probReal_univ, mul_one] at h

/-- Blueprint Lemma `lem:segments` (b), consequence: the Gram determinant of `λ_{0,1}` and
`λ_{i,1+i}` is at least `9/4 - (log 2)²/4 > 0`. -/
theorem segMeasure_gram_det_pos :
    9 / 4 - Real.log 2 ^ 2 / 4 ≤
        energy (segMeasure 0 1) (segMeasure 0 1) *
            energy (segMeasure I (1 + I)) (segMeasure I (1 + I)) -
          energy (segMeasure 0 1) (segMeasure I (1 + I)) ^ 2 ∧
      0 < 9 / 4 - Real.log 2 ^ 2 / 4 := by
  have h11 := three_halves_le_energy_segMeasure_I
  have h01 := abs_energy_segMeasure_zero_one_I_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [energy_segMeasure_zero_one]
  constructor
  · have hsq : energy (segMeasure 0 1) (segMeasure I (1 + I)) ^ 2 ≤ (Real.log 2 / 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h01 2
    nlinarith
  · nlinarith

end GaussianLQG
