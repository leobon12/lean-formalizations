import InteractingSLE.Spec.Sobolev.Duality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Gagliardo seminorm controls the Fourier `H^ε` norm: (SR4)

Source: `source/spec/p049-096.md`, proof of Aux. lemma 12, (SR4) (`#id-SR4`, p. 84): for
`0 < ε < 1`, `‖v‖²_{H^ε}` is comparable to `‖v‖²_{L²} + ∬ |v(x) - v(y)|² |x - y|^{-2-2ε} dx dy`
("for smooth compactly supported `v`, this follows directly by Fourier transform and Fubini:
integrating `|e^{iξ·z} - 1|² |z|^{-2-2ε}` in `z` gives a finite positive constant times `|ξ|^{2ε}`").

The cutoff argument of Aux. lemma 12 uses one direction: `‖v‖²_{H^ε} ≤ ‖v‖²₂ + c_ε⁻¹ [v]²_ε`
(`sobolevSq_le_l2Sq_add_gagSq`). We prove the needed lower bound
`∫ |e^{2πi⟪z,ξ⟫} - 1|² |z|^{-2-2ε} dz ≥ c_ε |ξ|^{2ε}` on an explicit ball of `z`, which avoids
the rotation and scaling invariances.

## Main definitions

* `gagKer ε z = |z|^{-2-2ε}`; `gagSq ε f = ∬ |f(x) - f(y)|² |x - y|^{-2-2ε}`; `l2Sq f = ∫ f²`.

## Main results

* `lintegral_sq_translate_sub` : `∫ |f(x+z) - f(x)|² dx = ∫ |𝓕f(ξ)|² |e^{2πi⟪z,ξ⟫} - 1|² dξ`;
* `gagSq_eq_lintegral_fourier` : `[f]²_ε = ∫ |𝓕f(ξ)|² m_ε(ξ) dξ`;
* `gagConst_mul_le_gagMult` : `m_ε(ξ) ≥ c_ε |ξ|^{2ε}`;
* `sobolevSq_le_l2Sq_add_gagSq` : (SR4), the direction used.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real FourierTransform Metric
open scoped Distributions ContDiff ENNReal RealInnerProductSpace SchwartzMap

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### Definitions -/

/-- The Gagliardo kernel `|z|^{-2-2ε}` (equal to `0` at `z = 0`). -/
def gagKer (ε : ℝ) (z : ℂ) : ℝ := ‖z‖ ^ (-(2 + 2 * ε))

theorem gagKer_nonneg (ε : ℝ) (z : ℂ) : 0 ≤ gagKer ε z := Real.rpow_nonneg (norm_nonneg _) _

theorem gagKer_neg (ε : ℝ) (z : ℂ) : gagKer ε (-z) = gagKer ε z := by simp [gagKer]

theorem measurable_gagKer (ε : ℝ) : Measurable (gagKer ε) :=
  measurable_norm.pow_const _

/-- The Gagliardo seminorm `[f]²_ε = ∬ |f(x) - f(y)|² |x - y|^{-2-2ε} dx dy`. -/
def gagSq (ε : ℝ) (f : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2 * gagKer ε (x - y))

/-- `‖f‖²_{L²}`. -/
def l2Sq (f : ℂ → ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (f x ^ 2)

/-- The Fourier multiplier of the Gagliardo seminorm, `m_ε(ξ) = ∫ |e^{2πi⟪z,ξ⟫} - 1|² |z|^{-2-2ε}`. -/
def gagMult (ε : ℝ) (ξ : ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (gagKer ε z * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2)

/-! ### Plancherel for translated differences -/

section Plancherel

variable {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
include hf hfc

omit hfc in
theorem contDiff_translate (z : ℂ) : ContDiff ℝ ∞ (fun x => f (x + z)) :=
  hf.comp (contDiff_id.add contDiff_const)

omit hf in
theorem hasCompactSupport_translate (z : ℂ) : HasCompactSupport (fun x => f (x + z)) :=
  hfc.comp_homeomorph (Homeomorph.addRight z)

omit hf hfc in
theorem fourier_cplx_translate (z : ℂ) :
    𝓕 (cplx (fun x => f (x + z))) = fun ξ => (𝐞 ⟪z, ξ⟫ : Circle) • 𝓕 (cplx f) ξ := by
  have h := VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℂ) (cplx f) z
  have e : cplx (fun x => f (x + z)) = cplx f ∘ fun v => v + z := rfl
  rw [e]
  exact h

/-- `∫ |f(x+z) - f(x)|² dx = ∫ |𝓕f(ξ)|² |e^{2πi⟪z,ξ⟫} - 1|² dξ`. -/
theorem lintegral_sq_translate_sub (z : ℂ) :
    ∫⁻ x, ENNReal.ofReal ((f (x + z) - f x) ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal (‖𝓕 (cplx f) ξ‖ ^ 2 * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2) := by
  set S := schwartzCplx hf hfc
  set Sz := schwartzCplx (contDiff_translate hf z) (hasCompactSupport_translate hfc z)
  set D : 𝓢(ℂ, ℂ) := Sz - S
  have hD : ∀ x, D x = ((f (x + z) - f x : ℝ) : ℂ) := fun x => by
    simp [D, Sz, S, coe_schwartzCplx, cplx]
  have hFD : ∀ ξ, (𝓕 D : 𝓢(ℂ, ℂ)) ξ = (((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1) * 𝓕 (cplx f) ξ := by
    intro ξ
    have h1 : (𝓕 D : 𝓢(ℂ, ℂ)) = 𝓕 Sz - 𝓕 S := by
      rw [← SchwartzMap.fourierTransformCLM_apply ℂ, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        ← SchwartzMap.fourierTransformCLM_apply ℂ, map_sub]
    rw [h1, sub_apply, ← fourier_cplx_eq, ← fourier_cplx_eq,
      fourier_cplx_translate z]
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  have hP := SchwartzMap.integral_norm_sq_fourier D
  have hcont1 : Continuous (fun x => (f (x + z) - f x) ^ 2) :=
    ((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous).pow 2
  have hsupp1 : support (fun x => (f (x + z) - f x) ^ 2) ⊆
      support (fun x => f (x + z)) ∪ support f := by
    intro x hx
    by_contra h
    simp only [mem_union, mem_support, not_or, not_not] at h
    exact hx (by simp [h.1, h.2])
  have hcs1 : HasCompactSupport (fun x => (f (x + z) - f x) ^ 2) := by
    refine IsCompact.of_isClosed_subset ((hasCompactSupport_translate hfc z).union hfc)
      (isClosed_tsupport _) ?_
    exact (closure_mono hsupp1).trans closure_union.subset
  have hint1 : Integrable (fun x => (f (x + z) - f x) ^ 2) :=
    hcont1.integrable_of_hasCompactSupport hcs1
  have hint2 : Integrable (fun ξ => ‖(𝓕 D : 𝓢(ℂ, ℂ)) ξ‖ ^ 2) :=
    (SchwartzMap.memLp (𝓕 D : 𝓢(ℂ, ℂ)) (2 : ℕ)).integrable_norm_pow two_ne_zero
  rw [← ofReal_integral_eq_lintegral_ofReal hint1 (Eventually.of_forall fun _ => sq_nonneg _)]
  have e2 : ∀ ξ, ‖𝓕 (cplx f) ξ‖ ^ 2 * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2 =
      ‖(𝓕 D : 𝓢(ℂ, ℂ)) ξ‖ ^ 2 := fun ξ => by
    rw [hFD, norm_mul, mul_pow, mul_comm]
  simp_rw [e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun _ => sq_nonneg _), hP]
  congr 1
  congr 1
  funext x
  rw [hD, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Plancherel** in `ℝ≥0∞` form: `∫ |𝓕f|² = ∫ f²`. -/
theorem lintegral_sq_fourier_eq_l2Sq :
    ∫⁻ ξ, ENNReal.ofReal (‖𝓕 (cplx f) ξ‖ ^ 2) = l2Sq f := by
  set S := schwartzCplx hf hfc
  have hP := SchwartzMap.integral_norm_sq_fourier S
  have hint1 : Integrable (fun ξ => ‖(𝓕 S : 𝓢(ℂ, ℂ)) ξ‖ ^ 2) :=
    (SchwartzMap.memLp (𝓕 S : 𝓢(ℂ, ℂ)) (2 : ℕ)).integrable_norm_pow two_ne_zero
  have hc2 : Continuous (fun x => f x ^ 2) := hf.continuous.pow 2
  have hcs2 : HasCompactSupport (fun x => f x ^ 2) := by
    refine hfc.mono fun x hx => ?_
    simp only [mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true]
      at hx ⊢
    exact hx
  have hint2 : Integrable (fun x => f x ^ 2) := hc2.integrable_of_hasCompactSupport hcs2
  rw [fourier_cplx_eq hf hfc, ← ofReal_integral_eq_lintegral_ofReal hint1
    (Eventually.of_forall fun _ => sq_nonneg _), hP, l2Sq,
    ← ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall fun _ => sq_nonneg _)]
  congr 1
  congr 1
  funext x
  simp [S, coe_schwartzCplx, cplx, sq_abs]

omit hfc in
theorem measurable_gagIntegrand (ε : ℝ) :
    Measurable (uncurry fun (x z : ℂ) =>
      ENNReal.ofReal ((f (x + z) - f x) ^ 2 * gagKer ε z)) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ((measurable_gagKer ε).comp measurable_snd))
  exact (((hf.continuous.comp (continuous_fst.add continuous_snd)).sub
    (hf.continuous.comp continuous_fst)).pow 2).measurable

/-- **The Fourier form of the Gagliardo seminorm**: `[f]²_ε = ∫ |𝓕f(ξ)|² m_ε(ξ) dξ`. -/
theorem gagSq_eq_lintegral_fourier (ε : ℝ) :
    gagSq ε f = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 (cplx f) ξ‖ ^ 2) * gagMult ε ξ := by
  have h1 : ∀ x, ∫⁻ y, ENNReal.ofReal ((f x - f y) ^ 2 * gagKer ε (x - y)) =
      ∫⁻ z, ENNReal.ofReal ((f (x + z) - f x) ^ 2 * gagKer ε z) := by
    intro x
    rw [← lintegral_add_left_eq_self (fun y => ENNReal.ofReal ((f x - f y) ^ 2 * gagKer ε (x - y))) x]
    congr 1
    funext z
    rw [show x - (x + z) = -z by ring, gagKer_neg]
    congr 2
    ring
  have hFmeas : Measurable (fun ξ => ‖𝓕 (cplx f) ξ‖) := (continuous_fourier_cplx hf hfc).norm.measurable
  have hEmeas : Measurable (uncurry fun (z ξ : ℂ) => ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖) :=
    ((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_fst.inner continuous_snd))).sub continuous_const).norm.measurable
  have hmeas2 : Measurable (uncurry fun (z ξ : ℂ) => ENNReal.ofReal
      (gagKer ε z * (‖𝓕 (cplx f) ξ‖ ^ 2 * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2))) :=
    ENNReal.measurable_ofReal.comp (((measurable_gagKer ε).comp measurable_fst).mul
      (((hFmeas.comp measurable_snd).pow_const 2).mul (hEmeas.pow_const 2)))
  calc gagSq ε f
      = ∫⁻ x, ∫⁻ z, ENNReal.ofReal ((f (x + z) - f x) ^ 2 * gagKer ε z) := by
        simp_rw [gagSq, h1]
    _ = ∫⁻ z, ∫⁻ x, ENNReal.ofReal ((f (x + z) - f x) ^ 2 * gagKer ε z) :=
        lintegral_lintegral_swap (measurable_gagIntegrand hf ε).aemeasurable
    _ = ∫⁻ z, ENNReal.ofReal (gagKer ε z) * ∫⁻ x, ENNReal.ofReal ((f (x + z) - f x) ^ 2) := by
        congr 1
        funext z
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext x
        rw [← ENNReal.ofReal_mul (gagKer_nonneg _ _), mul_comm]
    _ = ∫⁻ z, ∫⁻ ξ, ENNReal.ofReal
          (gagKer ε z * (‖𝓕 (cplx f) ξ‖ ^ 2 * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2)) := by
        congr 1
        funext z
        rw [lintegral_sq_translate_sub hf hfc z, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext ξ
        rw [← ENNReal.ofReal_mul (gagKer_nonneg _ _)]
    _ = ∫⁻ ξ, ∫⁻ z, ENNReal.ofReal
          (gagKer ε z * (‖𝓕 (cplx f) ξ‖ ^ 2 * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2)) :=
        lintegral_lintegral_swap hmeas2.aemeasurable
    _ = ∫⁻ ξ, ENNReal.ofReal (‖𝓕 (cplx f) ξ‖ ^ 2) * gagMult ε ξ := by
        congr 1
        funext ξ
        rw [gagMult, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext z
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Plancherel

/-! ### The lower bound for the multiplier -/

/-- The constant `c_ε = (π / 4096) (32 / 7)^{2+2ε}` of the lower bound `m_ε(ξ) ≥ c_ε |ξ|^{2ε}`. -/
def gagConst (ε : ℝ) : ℝ := π / 4096 * (32 / 7) ^ (2 + 2 * ε)

theorem gagConst_pos (ε : ℝ) : 0 < gagConst ε := by
  unfold gagConst; positivity

theorem norm_fourierChar_sub_one_ge {s : ℝ} (hs1 : 5 / 32 ≤ s) (hs2 : s ≤ 7 / 32) :
    1 / 4 ≤ ‖((𝐞 s : Circle) : ℂ) - 1‖ ^ 2 := by
  rw [Real.fourierChar_apply, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show 2 * π * s / 2 = π * s by ring]
  have h0 : 0 ≤ π * s := by positivity
  have h1 : π * s ≤ π / 2 := by nlinarith [Real.pi_pos]
  have h2 := Real.mul_le_sin h0 h1
  have h3 : 2 / π * (π * s) = 2 * s := by field_simp
  rw [h3] at h2
  rw [abs_mul, abs_two, abs_of_nonneg (by linarith : 0 ≤ Real.sin (π * s))]
  nlinarith

/-- **The multiplier lower bound** `m_ε(ξ) ≥ c_ε |ξ|^{2ε}` (`ε > 0`), from the ball
`B((3/16) ξ/|ξ|², 1/(32|ξ|))`, on which `⟪z, ξ⟫ ∈ [5/32, 7/32]` and `|z| ≤ 7/(32|ξ|)`. -/
theorem gagConst_mul_le_gagMult {ε : ℝ} (hε : 0 < ε) (ξ : ℂ) :
    ENNReal.ofReal (gagConst ε * ‖ξ‖ ^ (2 * ε)) ≤ gagMult ε ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [norm_zero, Real.zero_rpow (by positivity), mul_zero, ENNReal.ofReal_zero]
    exact bot_le
  set r := ‖ξ‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hξ
  set z₀ : ℂ := ((3 / (16 * r ^ 2) : ℝ) : ℂ) * ξ
  set ρ : ℝ := 1 / (32 * r)
  have hz₀ : ‖z₀‖ = 3 / (16 * r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), ← hr]
    field_simp
  have hinner₀ : ⟪z₀, ξ⟫ = 3 / 16 := by
    rw [show z₀ = ((3 / (16 * r ^ 2) : ℝ) • ξ) by simp [z₀, Complex.real_smul], real_inner_smul_left,
      real_inner_self_eq_norm_sq, ← hr]
    field_simp
  set K₀ : ℝ := (32 * r / 7) ^ (2 + 2 * ε) * (1 / 4)
  have hpt : ∀ z ∈ ball z₀ ρ, K₀ ≤ gagKer ε z * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hin : |⟪z - z₀, ξ⟫| ≤ ‖z - z₀‖ * r := by
      rw [hr]; exact abs_real_inner_le_norm _ _
    have hzr : ‖z - z₀‖ * r < 1 / 32 := by
      calc ‖z - z₀‖ * r < ρ * r := mul_lt_mul_of_pos_right hz hr0
        _ = 1 / 32 := by simp only [ρ]; field_simp
    have hs : ⟪z, ξ⟫ = 3 / 16 + ⟪z - z₀, ξ⟫ := by
      rw [inner_sub_left, hinner₀]; ring
    have hs1 : 5 / 32 ≤ ⟪z, ξ⟫ := by rw [hs]; linarith [neg_abs_le ⟪z - z₀, ξ⟫]
    have hs2 : ⟪z, ξ⟫ ≤ 7 / 32 := by rw [hs]; linarith [le_abs_self ⟪z - z₀, ξ⟫]
    have hE := norm_fourierChar_sub_one_ge hs1 hs2
    have hz1 : ‖z‖ ≤ 7 / (32 * r) := by
      calc ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
            calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
              _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ 3 / (16 * r) + ρ := by rw [hz₀]; linarith
        _ = 7 / (32 * r) := by simp only [ρ]; field_simp; ring
    have hz2 : 0 < ‖z‖ := by
      have : 5 / (32 * r) ≤ ‖z‖ := by
        have h := norm_sub_norm_le z₀ (z₀ - z)
        rw [show z₀ - (z₀ - z) = z by ring, norm_sub_rev, hz₀] at h
        have : 3 / (16 * r) - ρ = 5 / (32 * r) := by simp only [ρ]; field_simp; ring
        linarith
      exact lt_of_lt_of_le (by positivity) this
    have hK : (32 * r / 7) ^ (2 + 2 * ε) ≤ gagKer ε z := by
      rw [gagKer, Real.rpow_neg (norm_nonneg _), ← Real.inv_rpow (norm_nonneg _)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      rw [le_inv_comm₀ (by positivity) hz2, inv_div]
      calc ‖z‖ ≤ 7 / (32 * r) := hz1
        _ = 7 / (32 * r) := rfl
    calc K₀ = (32 * r / 7) ^ (2 + 2 * ε) * (1 / 4) := rfl
      _ ≤ gagKer ε z * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2 :=
          mul_le_mul hK hE (by norm_num) (gagKer_nonneg _ _)
  calc ENNReal.ofReal (gagConst ε * r ^ (2 * ε))
      = ENNReal.ofReal K₀ * (ENNReal.ofReal ρ ^ 2 * NNReal.pi) := by
        rw [← ENNReal.ofReal_pow (by positivity), ENNReal.coe_nnreal_eq, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e1 : (32 * r / 7) ^ (2 + 2 * ε) = (32 / 7) ^ (2 + 2 * ε) * (r ^ 2 * r ^ (2 * ε)) := by
          rw [show 32 * r / 7 = 32 / 7 * r by ring, Real.mul_rpow (by norm_num) hr0.le,
            Real.rpow_add hr0, Real.rpow_two]
        simp only [K₀, ρ, gagConst]
        rw [e1]
        field_simp
        ring
    _ = ∫⁻ z in ball z₀ ρ, ENNReal.ofReal K₀ := by
        rw [setLIntegral_const, Complex.volume_ball]
    _ ≤ ∫⁻ z in ball z₀ ρ, ENNReal.ofReal
          (gagKer ε z * ‖((𝐞 ⟪z, ξ⟫ : Circle) : ℂ) - 1‖ ^ 2) :=
        setLIntegral_mono' measurableSet_ball fun z hz => ENNReal.ofReal_le_ofReal (hpt z hz)
    _ ≤ gagMult ε ξ := setLIntegral_le_lintegral _ _

/-! ### (SR4): the Fourier `H^ε` norm is bounded by the Gagliardo norm -/

theorem one_add_sq_rpow_le {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ξ : ℂ) :
    sobWeight ε ξ ≤ 1 + ‖ξ‖ ^ (2 * ε) := by
  have h : ((1 + (‖ξ‖ ^ 2).toNNReal) ^ ε : NNReal) ≤ 1 ^ ε + (‖ξ‖ ^ 2).toNNReal ^ ε :=
    NNReal.rpow_add_le_add_rpow _ _ hε hε1
  have h' := NNReal.coe_le_coe.2 h
  simp only [NNReal.coe_rpow, NNReal.coe_add, NNReal.coe_one,
    Real.coe_toNNReal _ (sq_nonneg _), Real.one_rpow] at h'
  rw [sobWeight, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  exact h'

/-- **(SR4)**, the direction used in Aux. lemma 12: for a smooth compactly supported `f` and
`0 < ε ≤ 1`, `‖f‖²_{H^ε} ≤ ‖f‖²₂ + c_ε⁻¹ [f]²_ε`. -/
theorem sobolevSq_le_l2Sq_add_gagSq {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    sobolevSq ε f ≤ l2Sq f + (ENNReal.ofReal (gagConst ε))⁻¹ * gagSq ε f := by
  have hc : ENNReal.ofReal (gagConst ε) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact gagConst_pos ε
  have hmeas : Measurable (fun ξ => ENNReal.ofReal (‖𝓕 (cplx f) ξ‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((continuous_fourier_cplx hf hfc).norm.pow 2).measurable
  rw [gagSq_eq_lintegral_fourier hf hfc, ← lintegral_sq_fourier_eq_l2Sq hf hfc,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc), ← lintegral_add_left hmeas]
  refine lintegral_mono fun ξ => ?_
  set a := ‖𝓕 (cplx f) ξ‖ ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  have h1 : ENNReal.ofReal (‖ξ‖ ^ (2 * ε)) ≤ (ENNReal.ofReal (gagConst ε))⁻¹ * gagMult ε ξ := by
    calc ENNReal.ofReal (‖ξ‖ ^ (2 * ε))
        = (ENNReal.ofReal (gagConst ε))⁻¹ * (ENNReal.ofReal (gagConst ε) *
            ENNReal.ofReal (‖ξ‖ ^ (2 * ε))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (gagConst ε))⁻¹ * gagMult ε ξ := by
          gcongr
          rw [← ENNReal.ofReal_mul (gagConst_pos ε).le]
          exact gagConst_mul_le_gagMult hε ξ
  calc ENNReal.ofReal (a * sobWeight ε ξ) ≤ ENNReal.ofReal (a * (1 + ‖ξ‖ ^ (2 * ε))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (one_add_sq_rpow_le hε.le hε1 ξ) ha)
    _ = ENNReal.ofReal a + ENNReal.ofReal a * ENNReal.ofReal (‖ξ‖ ^ (2 * ε)) := by
        rw [mul_add, mul_one, ENNReal.ofReal_add ha (by positivity), ENNReal.ofReal_mul ha]
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a * ((ENNReal.ofReal (gagConst ε))⁻¹ * gagMult ε ξ) := by
        gcongr
    _ = ENNReal.ofReal a + (ENNReal.ofReal (gagConst ε))⁻¹ * (ENNReal.ofReal a * gagMult ε ξ) := by
        rw [mul_left_comm]

end InteractingSLE.Sobolev
