import GaussianLQG.Energy.SegmentsBasic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Segment energies, part 2 (blueprint Lemma `lem:segments` (c), (d), (e))

Horizontal-ish segments `λ_{is, 1+it}` from `is` to `1 + it`, `s, t ∈ [0, 1]`:

* (c) `energy_segMeasure_sub_le`: with `a = |s-s'| ∨ |t-t'|`,
  `ℰ(λ,λ) - 2ℰ(λ,λ') + ℰ(λ',λ') ≤ 6 a^{1/2}` for `λ = λ_{is,1+it}`, `λ' = λ_{is',1+it'}`
  (coupling estimate with `α = 1`, `B = 2`, `ρ = a^{1/2}`);
* (d) `energy_segMeasure_sI_le`: `ℰ(λ_{is,1+it}, λ_{is,1+it}) ≤ 3/2 + log 2`;
* (e) `muZero`, the uniform probability measure on `B_{1/4}((1+i)/2)`: `isRegular_muZero` and
  `neg_log_le_energy_muZero_segMeasure`: `ℰ(μ₀, λ_{iy,1+iy}) ≥ c_* = -log(1/4 + √2/2)` for
  `y ∈ [0, 1]`, with `c_* > 0` (`cStar_pos`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Complex
open scoped ENNReal Real

namespace GaussianLQG

/-! ## The segments `[is, 1 + it]` -/

theorem sI_ne_one_add_tI (s t : ℝ) : (s : ℂ) * I ≠ 1 + (t : ℂ) * I := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_le_norm_sI_sub (s t : ℝ) : 1 ≤ ‖(s : ℂ) * I - (1 + (t : ℂ) * I)‖ := by
  have := Complex.abs_re_le_norm ((s : ℂ) * I - (1 + (t : ℂ) * I))
  simpa using this

theorem segPath_sI_re (s t u : ℝ) : (segPath ((s : ℂ) * I) (1 + (t : ℂ) * I) u).re = u := by
  simp [segPath]

theorem segPath_sI_im (s t u : ℝ) :
    (segPath ((s : ℂ) * I) (1 + (t : ℂ) * I) u).im = (1 - u) * s + u * t := by
  simp [segPath]

/-- `λ_{is,1+it}(B_r(u)) ≤ 2r`, since the segment has length at least `1`. -/
theorem segMeasure_sI_ball_toReal_le (s t : ℝ) (u : ℂ) {r : ℝ} (hr : 0 < r) :
    (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I) (ball u r)).toReal ≤ 2 * r ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have h := segMeasure_ball_le (sI_ne_one_add_tI s t) u r
  have hn := one_le_norm_sI_sub s t
  calc (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I) (ball u r)).toReal
      ≤ (ENNReal.ofReal (2 * r / ‖(s : ℂ) * I - (1 + (t : ℂ) * I)‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = 2 * r / ‖(s : ℂ) * I - (1 + (t : ℂ) * I)‖ := ENNReal.toReal_ofReal (by positivity)
    _ ≤ 2 * r := div_le_self (by positivity) hn

/-- The displacement of the coupling `u ↦ (φ(u), φ'(u))` is at most `|s-s'| ∨ |t-t'|`. -/
theorem norm_segPath_sI_sub_le (s t s' t' : ℝ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖segPath ((s : ℂ) * I) (1 + (t : ℂ) * I) u - segPath ((s' : ℂ) * I) (1 + (t' : ℂ) * I) u‖ ≤
      max |s - s'| |t - t'| := by
  have e : segPath ((s : ℂ) * I) (1 + (t : ℂ) * I) u -
      segPath ((s' : ℂ) * I) (1 + (t' : ℂ) * I) u =
        (((1 - u) * (s - s') + u * (t - t') : ℝ) : ℂ) * I := by
    simp only [segPath]
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h1u : 0 ≤ 1 - u := by linarith [hu.2]
  calc |(1 - u) * (s - s') + u * (t - t')| ≤ |(1 - u) * (s - s')| + |u * (t - t')| :=
        abs_add_le _ _
    _ = (1 - u) * |s - s'| + u * |t - t'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1u, abs_of_nonneg hu.1]
    _ ≤ (1 - u) * max |s - s'| |t - t'| + u * max |s - s'| |t - t'| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1u)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hu.1)
    _ = max |s - s'| |t - t'| := by ring

/-- Blueprint Lemma `lem:segments` (c): for `s, t, s', t' ∈ [0,1]` and `a = |s-s'| ∨ |t-t'|`,
`‖λ_{is,1+it} - λ_{is',1+it'}‖_*² ≤ 6 a^{1/2}`. -/
theorem energy_segMeasure_sub_le {s t s' t' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) :
    energy (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I))
          (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I)) -
        2 * energy (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I))
          (segMeasure ((s' : ℂ) * I) (1 + (t' : ℂ) * I)) +
        energy (segMeasure ((s' : ℂ) * I) (1 + (t' : ℂ) * I))
          (segMeasure ((s' : ℂ) * I) (1 + (t' : ℂ) * I)) ≤
      6 * (max |s - s'| |t - t'|) ^ (1 / 2 : ℝ) := by
  have ha0 : 0 ≤ max |s - s'| |t - t'| := le_max_of_le_left (abs_nonneg _)
  rcases ha0.lt_or_eq with hapos | hazero
  · -- the coupling estimate with `α = 1`, `B = B' = 2`, `η = a`, `ρ = √a`
    set a := max |s - s'| |t - t'| with ha_def
    have ha1 : a ≤ 1 := by
      refine max_le ?_ ?_
      · rw [abs_le]
        constructor <;> linarith [hs.1, hs.2, hs'.1, hs'.2]
      · rw [abs_le]
        constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    set φ := segPath ((s : ℂ) * I) (1 + (t : ℂ) * I) with hφ
    set φ' := segPath ((s' : ℂ) * I) (1 + (t' : ℂ) * I) with hφ'
    set P : Measure (ℂ × ℂ) := (volume.restrict (Icc (0 : ℝ) 1)).map fun u => (φ u, φ' u)
      with hP
    have hm : Measurable fun u : ℝ => (φ u, φ' u) :=
      (measurable_segPath _ _).prodMk (measurable_segPath _ _)
    have hP1 : P.map Prod.fst = segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I) := by
      rw [hP, Measure.map_map measurable_fst hm, segMeasure_eq_map]
      rfl
    have hP2 : P.map Prod.snd = segMeasure ((s' : ℂ) * I) (1 + (t' : ℂ) * I) := by
      rw [hP, Measure.map_map measurable_snd hm, segMeasure_eq_map]
      rfl
    have hPη : P {p | a < ‖p.1 - p.2‖} = 0 := by
      rw [hP, Measure.map_apply hm (measurableSet_lt measurable_const (by fun_prop)),
        Measure.restrict_apply' measurableSet_Icc]
      refine measure_mono_null (fun u hu => ?_) measure_empty
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq] at hu
      exact absurd (norm_segPath_sI_sub_le s t s' t' hu.2) (not_le.2 hu.1)
    have hρ : 0 < √a := Real.sqrt_pos.2 hapos
    have hρ1 : √a ≤ 1 := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt ha1
    have h := energy_sub_le_of_coupling (isRegular_segMeasure (sI_ne_one_add_tI s t))
      (isRegular_segMeasure (sI_ne_one_add_tI s' t')) one_pos zero_le_two zero_le_two
      (fun u r hr _ => segMeasure_sI_ball_toReal_le s t u hr)
      (fun u r hr _ => segMeasure_sI_ball_toReal_le s' t' u hr) hP1 hP2 hPη hρ hρ1
    have e : 2 * a / √a + (2 + 2) * √a ^ (1 : ℝ) / 1 = 6 * a ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_one, div_one, mul_div_assoc, Real.div_sqrt, ← Real.sqrt_eq_rpow]
      ring
    rw [e] at h
    exact h
  · -- `a = 0`: the two segments coincide
    have h1 : s' = s := by
      have : |s - s'| ≤ 0 := hazero ▸ le_max_left _ _
      linarith [abs_nonpos_iff.1 this]
    have h2 : t' = t := by
      have : |t - t'| ≤ 0 := hazero ▸ le_max_right _ _
      linarith [abs_nonpos_iff.1 this]
    subst h1 h2
    rw [← hazero, Real.zero_rpow (by norm_num)]
    linarith

/-- Blueprint Lemma `lem:segments` (d): `ℰ(λ_{is,1+it}, λ_{is,1+it}) ≤ 3/2 + log 2` for
`s, t ∈ [0,1]`. -/
theorem energy_segMeasure_sI_le {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    energy (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I))
        (segMeasure ((s : ℂ) * I) (1 + (t : ℂ) * I)) ≤ 3 / 2 + Real.log 2 := by
  obtain ⟨i0, e0⟩ := energy_segMeasure_eq_integral_prod zero_ne_one_complex zero_ne_one_complex
  obtain ⟨i1, e1⟩ := energy_segMeasure_eq_integral_prod (sI_ne_one_add_tI s t)
    (sI_ne_one_add_tI s t)
  set L : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hL
  have hrhs : 3 / 2 + Real.log 2 =
      ∫ q : ℝ × ℝ, (kernelG (segPath 0 1 q.1) (segPath 0 1 q.2) + Real.log 2) ∂(L.prod L) := by
    rw [integral_add i0 (integrable_const _), ← e0, energy_segMeasure_zero_one, integral_const,
      probReal_univ, one_smul]
  rw [e1, hrhs]
  refine integral_mono_ae i1 (i0.add (integrable_const _)) ?_
  filter_upwards [ae_mem_Icc_prod] with q hq
  set φ := segPath ((s : ℂ) * I) (1 + (t : ℂ) * I) with hφ
  -- the one-variable terms are at most `log √2 = (log 2)/2`
  have hlog : ∀ u ∈ Icc (0 : ℝ) 1, Real.log (max 1 ‖φ u‖) ≤ Real.log 2 / 2 := by
    intro u hu
    have hn : ‖φ u‖ ≤ √2 := by
      refine norm_le_sqrt_two ?_ ?_
      · rw [hφ, segPath_sI_re, abs_le]
        constructor <;> linarith [hu.1, hu.2]
      · rw [hφ, segPath_sI_im, abs_le]
        have h1 : 0 ≤ (1 - u) * s := mul_nonneg (by linarith [hu.2]) hs.1
        have h2 : 0 ≤ u * t := mul_nonneg hu.1 ht.1
        have h3 : (1 - u) * s ≤ 1 - u := mul_le_of_le_one_right (by linarith [hu.2]) hs.2
        have h4 : u * t ≤ u := mul_le_of_le_one_right hu.1 ht.2
        constructor <;> linarith
    have h1 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [← log_sqrt_two]
    exact Real.log_le_log (by positivity) (max_le h1 hn)
  -- the logarithmic singularity only improves, since the segment has length at least `1`
  have hsing : -Real.log ‖φ q.1 - φ q.2‖ ≤ -Real.log |q.1 - q.2| := by
    rcases eq_or_ne q.1 q.2 with h | h
    · rw [h, sub_self, sub_self, norm_zero, abs_zero]
    · have hpos : 0 < |q.1 - q.2| := abs_pos.2 (sub_ne_zero.2 h)
      have hle : |q.1 - q.2| ≤ ‖φ q.1 - φ q.2‖ := by
        rw [hφ, segPath_sub_segPath, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          norm_sub_rev]
        exact le_mul_of_one_le_right (abs_nonneg _) (one_le_norm_sI_sub s t)
      exact neg_le_neg (Real.log_le_log hpos hle)
  rw [segPath_zero_one, segPath_zero_one, kernelG_ofReal_of_mem_Icc hq.1 hq.2]
  have k : kernelG (φ q.1) (φ q.2) = -Real.log ‖φ q.1 - φ q.2‖ + Real.log (max 1 ‖φ q.1‖) +
      Real.log (max 1 ‖φ q.2‖) := rfl
  rw [k]
  linarith [hlog q.1 hq.1, hlog q.2 hq.2]

/-! ## The disc measure `μ₀` -/

/-- The uniform probability measure on the disc `B_r(c)` (normalized Lebesgue measure). -/
def discMeasure (c : ℂ) (r : ℝ) : Measure ℂ := (volume (ball c r))⁻¹ • volume.restrict (ball c r)

/-- `μ₀`: the uniform probability measure on `B_{1/4}((1+i)/2)` (blueprint Lemma
`lem:segments` (e)). -/
def muZero : Measure ℂ := discMeasure ((1 + I) / 2) (1 / 4)

theorem isProbabilityMeasure_discMeasure (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (discMeasure c r) := by
  constructor
  rw [discMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne

instance isProbabilityMeasure_muZero : IsProbabilityMeasure muZero :=
  isProbabilityMeasure_discMeasure _ (by norm_num)

theorem ae_mem_discMeasure (c : ℂ) (r : ℝ) : ∀ᵐ x ∂(discMeasure c r), x ∈ ball c r :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_ball) _

theorem volume_ball_toReal (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball a r)).toReal = r ^ 2 * Real.pi := by
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.coe_toReal, NNReal.coe_real_pi]

/-- `μ_{B_r(c)}(B_s(u)) ≤ s²/r²`. -/
theorem discMeasure_ball_toReal_le (c : ℂ) {r : ℝ} (hr : 0 < r) (u : ℂ) {s : ℝ} (hs : 0 < s) :
    (discMeasure c r (ball u s)).toReal ≤ (r ^ 2)⁻¹ * s ^ (2 : ℝ) := by
  have hB0 : volume (ball c r) ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hle : discMeasure c r (ball u s) ≤ (volume (ball c r))⁻¹ * volume (ball u s) := by
    rw [discMeasure, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_ball]
    gcongr
    exact inter_subset_left
  calc (discMeasure c r (ball u s)).toReal
      ≤ ((volume (ball c r))⁻¹ * volume (ball u s)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hB0)
          measure_ball_lt_top.ne) hle
    _ = (r ^ 2 * Real.pi)⁻¹ * (s ^ 2 * Real.pi) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, volume_ball_toReal c hr.le,
          volume_ball_toReal u hs.le]
    _ = (r ^ 2)⁻¹ * s ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        field_simp

/-- The uniform probability measure on a disc is regular (ball-mass exponent `2`). -/
theorem isRegular_discMeasure (c : ℂ) {r : ℝ} (hr : 0 < r) : IsRegular (discMeasure c r) := by
  have := isProbabilityMeasure_discMeasure c hr
  refine ⟨inferInstance, ⟨‖c‖ + r, compl_closedBall_eq_zero_of_ae_norm_le ?_⟩, (r ^ 2)⁻¹, 2,
    two_pos, fun u s hs _ => discMeasure_ball_toReal_le c hr u hs⟩
  filter_upwards [ae_mem_discMeasure c r] with x hx
  rw [mem_ball, dist_eq_norm] at hx
  calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + r := by linarith

/-- Blueprint Lemma `lem:segments` (e), first part: `μ₀` is regular. -/
theorem isRegular_muZero : IsRegular muZero := isRegular_discMeasure _ (by norm_num)

/-- `c_* = -log(1/4 + √2/2) > 0`. -/
theorem cStar_pos : 0 < -Real.log (1 / 4 + √2 / 2) := by
  have h1 : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have h2 : 0 < 1 / 4 + √2 / 2 := by positivity
  have h3 : 1 / 4 + √2 / 2 < 1 := by linarith
  have := Real.log_neg h2 h3
  linarith

/-- Points of the segment `[iy, 1+iy]`, `y ∈ [0,1]`, lie within `√2/2` of `(1+i)/2`. -/
theorem norm_segPath_sub_center_le {y u : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖segPath ((y : ℂ) * I) (1 + (y : ℂ) * I) u - (1 + I) / 2‖ ≤ √2 / 2 := by
  have hre : (segPath ((y : ℂ) * I) (1 + (y : ℂ) * I) u - (1 + I) / 2).re = u - 1 / 2 := by
    rw [Complex.sub_re, segPath_sI_re]
    simp
  have him : (segPath ((y : ℂ) * I) (1 + (y : ℂ) * I) u - (1 + I) / 2).im = y - 1 / 2 := by
    rw [Complex.sub_im, segPath_sI_im]
    simp
    ring
  rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him]
  have hsq : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hb : (u - 1 / 2) ^ 2 + (y - 1 / 2) ^ 2 ≤ (√2 / 2) ^ 2 := by
    rw [hsq]
    nlinarith [hu.1, hu.2, hy.1, hy.2]
  calc √((u - 1 / 2) ^ 2 + (y - 1 / 2) ^ 2) ≤ √((√2 / 2) ^ 2) := Real.sqrt_le_sqrt hb
    _ = √2 / 2 := Real.sqrt_sq (by positivity)

/-- Blueprint Lemma `lem:segments` (e): `ℰ(μ₀, λ_{iy,1+iy}) ≥ c_* = -log(1/4 + √2/2)` for
`y ∈ [0,1]`. -/
theorem neg_log_le_energy_muZero_segMeasure {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    -Real.log (1 / 4 + √2 / 2) ≤
      energy muZero (segMeasure ((y : ℂ) * I) (1 + (y : ℂ) * I)) := by
  have hμ := isRegular_muZero
  have hlam' := isRegular_segMeasure (sI_ne_one_add_tI y y)
  set c : ℂ := (1 + I) / 2 with hc
  set lam := segMeasure ((y : ℂ) * I) (1 + (y : ℂ) * I) with hlam
  rw [energy_eq_integral_prod hμ hlam']
  have hae1 : ∀ᵐ z ∂muZero, z ∈ ball c (1 / 4) := ae_mem_discMeasure c (1 / 4)
  have hae2 : ∀ᵐ w ∂lam, ‖w - c‖ ≤ √2 / 2 := by
    rw [hlam, segMeasure_eq_map, ae_map_iff (measurable_segPath _ _).aemeasurable
      (measurableSet_le (by fun_prop) measurable_const), ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun u hu => norm_segPath_sub_center_le hy hu
  have hprod : ∀ᵐ p ∂(muZero.prod lam), p.1 ∈ ball c (1 / 4) ∧ ‖p.2 - c‖ ≤ √2 / 2 ∧
      p.1 ≠ p.2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := muZero) (ν := lam)).ae hae1,
      (Measure.quasiMeasurePreserving_snd (μ := muZero) (ν := lam)).ae hae2,
      hlam'.ae_prod_ne (μ := muZero)] with p h1 h2 h3 using ⟨h1, h2, h3⟩
  calc -Real.log (1 / 4 + √2 / 2) = ∫ _p, -Real.log (1 / 4 + √2 / 2) ∂(muZero.prod lam) := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ ∫ p, kernelG p.1 p.2 ∂(muZero.prod lam) := by
        refine integral_mono_ae (integrable_const _) (hμ.integrable_kernelG hlam') ?_
        filter_upwards [hprod] with p hp
        obtain ⟨h1, h2, h3⟩ := hp
        rw [mem_ball, dist_eq_norm] at h1
        have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 h3)
        have hle : ‖p.1 - p.2‖ ≤ 1 / 4 + √2 / 2 := by
          calc ‖p.1 - p.2‖ ≤ ‖p.1 - c‖ + ‖c - p.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ = ‖p.1 - c‖ + ‖p.2 - c‖ := by rw [norm_sub_rev c]
            _ ≤ 1 / 4 + √2 / 2 := by linarith
        have hlog := Real.log_le_log hpos hle
        have k : kernelG p.1 p.2 = -Real.log ‖p.1 - p.2‖ + Real.log (max 1 ‖p.1‖) +
            Real.log (max 1 ‖p.2‖) := rfl
        rw [k]
        linarith [log_max_one_nonneg ‖p.1‖, log_max_one_nonneg ‖p.2‖]

end GaussianLQG
