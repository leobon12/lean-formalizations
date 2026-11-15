import InteractingSLE.Spec.Sobolev.Thin
import LQGMetric.Field.StandardBorelRange
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Aux. lemma 11, conditional means: a locally `H^{-ε}` version of `E[h | 𝓕]`

Source: `source/spec/p049-096.md`, Aux. lemma 11 (`#aux-11`, p. 83): "For any sigma-algebra `𝓕`,
the distributional conditional mean `M = E[h | 𝓕]` has a version with `ζM ∈ H^{-ε}(ℝ²)` almost
surely. All these assertions may be imposed simultaneously on a countable family of cutoffs and
exponents."

**Route.** The specification takes the Bochner conditional expectation of the `H^{-ε}`-valued
random variable `ζh` and patches the local versions. Here the distribution space `𝒟'(D)` (cylinder
σ-algebra) is standard Borel (`LQGMetric.standardBorelSpace_distOn`), so the field has a regular
conditional distribution `κ` given `𝓕` (Mathlib's `condDistrib` of `h` given `id : (Ω, mΩ) →
(Ω, 𝓕)`), and the version is the barycentre `M(ω)(φ) = ∫ T(φ) dκ_ω(T)`. It is a distribution
for almost every `ω`: by duality (`sq_apply_mulTest_le`) `|T(φ)| ≤ 2 ‖ζ_n T‖_{H^{-ε}} ‖φ‖_{H^ε}`
for `φ` supported where the cutoff `ζ_n` equals one, `∫ ‖ζ_n T‖²_{H^{-ε}} dκ_ω < ∞` a.s. by (SR1),
and `‖φ‖_{H^ε} ≤ C_K (sup |φ| + sup |∇φ|)` (`sobolevSq_le_of_sup`). Jensen's inequality and (SR1)
give `‖ζ M‖_{H^{-ε}} < ∞` a.s. for every cutoff `ζ`.

## Main results

* `gagSq_le_of_sq_le`, `sobolevSq_le_of_sup` : `‖f‖²_{H^ε} ≤ C (sup |f| + Lip f)²`;
* `ofReal_sq_integral_le_prob` : Jensen for probability measures;
* `measurable_negSobolevSq` : `T ↦ ‖ζT‖²_{H^{-ε}}` is measurable on `𝒟'(D)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real Metric ProbabilityTheory
open scoped Distributions ContDiff ENNReal NNReal

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### `‖f‖_{H^ε}` is controlled by `sup |f|` and the Lipschitz constant -/

/-- `[w]²_ε ≤ 2 A |B(c, R)| J_ε(M)` if `(w x - w y)² ≤ A min(1, M²|x - y|²)` and `w` vanishes off
`B(c, R)`. -/
theorem gagSq_le_of_sq_le {ε : ℝ} {w : ℂ → ℝ} {A M : ℝ} (hA : 0 ≤ A)
    (hw : ∀ x y, (w x - w y) ^ 2 ≤ A * min 1 (M ^ 2 * ‖x - y‖ ^ 2)) {c : ℂ} {R : ℝ}
    (hsupp : ∀ x, x ∉ ball c R → w x = 0) :
    gagSq ε w ≤ ENNReal.ofReal A * (2 * volume (ball c R) * gagJ ε M) := by
  set B := ball c R
  have hpt : ∀ x y, ENNReal.ofReal ((w x - w y) ^ 2 * gagKer ε (x - y)) ≤
      ENNReal.ofReal A * (B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) +
        B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y))) := by
    intro x y
    have h1 : ENNReal.ofReal ((w x - w y) ^ 2 * gagKer ε (x - y)) ≤
        ENNReal.ofReal A * ENNReal.ofReal (gagG ε M (x - y)) := by
      rw [← ENNReal.ofReal_mul hA]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [gagG, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hw x y) (gagKer_nonneg _ _)
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, Pi.one_apply, one_mul]
      exact h1.trans (by gcongr; exact le_self_add)
    · by_cases hy : y ∈ B
      · rw [indicator_of_mem hy, Pi.one_apply, one_mul]
        exact h1.trans (by gcongr; exact le_add_self)
      · rw [hsupp x hx, hsupp y hy]; simp
  have hmG : Measurable (uncurry fun (x y : ℂ) => ENNReal.ofReal (gagG ε M (x - y))) :=
    ENNReal.measurable_ofReal.comp ((measurable_gagG ε M).comp measurable_sub)
  have hind : Measurable (B.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator measurableSet_ball
  have hsum : ∫⁻ x, ∫⁻ y, (B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) +
      B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y))) = 2 * volume B * gagJ ε M := by
    have hA' : ∫⁻ x, ∫⁻ y, B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) =
        volume B * gagJ ε M := by
      have : ∀ x, ∫⁻ y, B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) =
          B.indicator 1 x * gagJ ε M := fun x => by
        rw [lintegral_const_mul' _ _ (by by_cases hx : x ∈ B <;> simp [hx]),
          lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (gagG ε M z)) x, gagJ]
      simp_rw [this]
      rw [lintegral_mul_const _ hind, lintegral_indicator_one measurableSet_ball]
    have hB' : ∫⁻ x, ∫⁻ y, B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) =
        volume B * gagJ ε M := by
      rw [lintegral_lintegral_swap ((hind.comp measurable_snd).mul hmG).aemeasurable]
      have : ∀ y, ∫⁻ x, B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) =
          B.indicator 1 y * gagJ ε M := fun y => by
        rw [lintegral_const_mul' _ _ (by by_cases hy : y ∈ B <;> simp [hy]),
          lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (gagG ε M z)) y, gagJ]
      simp_rw [this]
      rw [lintegral_mul_const _ hind, lintegral_indicator_one measurableSet_ball]
    calc ∫⁻ x, ∫⁻ y, (B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) +
          B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)))
        = (∫⁻ x, ∫⁻ y, B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y))) +
            ∫⁻ x, ∫⁻ y, B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y)) := by
          rw [← lintegral_add_left (f := fun x => ∫⁻ y, B.indicator 1 x *
            ENNReal.ofReal (gagG ε M (x - y))) ((hind.comp measurable_fst).mul hmG).lintegral_prod_right']
          congr 1; funext x
          exact lintegral_add_left
            (f := fun y => B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)))
            (measurable_const.mul (ENNReal.measurable_ofReal.comp
              ((measurable_gagG ε M).comp (measurable_const.sub measurable_id)))) _
      _ = 2 * volume B * gagJ ε M := by rw [hA', hB']; ring
  calc gagSq ε w ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal A * (B.indicator 1 x *
        ENNReal.ofReal (gagG ε M (x - y)) + B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y))) :=
        lintegral_mono fun x => lintegral_mono fun y => hpt x y
    _ = ENNReal.ofReal A * ∫⁻ x, ∫⁻ y, (B.indicator 1 x * ENNReal.ofReal (gagG ε M (x - y)) +
          B.indicator 1 y * ENNReal.ofReal (gagG ε M (x - y))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; funext x
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * (2 * volume B * gagJ ε M) := by rw [hsum]

/-- `(f x - f y)² ≤ 4 (M₀ + L)² min(1, |x - y|²)` for `|f| ≤ M₀`, `f` `L`-Lipschitz. -/
theorem sq_sub_le_of_sup {f : ℂ → ℝ} {M₀ L : ℝ} (hM : ∀ x, |f x| ≤ M₀)
    (hL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) (x y : ℂ) :
    (f x - f y) ^ 2 ≤ 4 * (M₀ + L) ^ 2 * min 1 (1 ^ 2 * ‖x - y‖ ^ 2) := by
  have hM0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM 0)
  have hL0 : 0 ≤ L := by
    by_contra h
    push Not at h
    have := hL 1 0
    have : L * ‖(1 : ℂ) - 0‖ < 0 := by simp; linarith
    linarith [abs_nonneg (f 1 - f 0)]
  rw [one_pow, one_mul]
  rcases le_total 1 (‖x - y‖ ^ 2) with h | h
  · rw [min_eq_left h, mul_one]
    have : |f x - f y| ≤ 2 * (M₀ + L) := (abs_sub _ _).trans (by linarith [hM x, hM y])
    nlinarith [abs_nonneg (f x - f y), sq_abs (f x - f y)]
  · rw [min_eq_right h]
    have h1 : |f x - f y| ≤ (M₀ + L) * ‖x - y‖ :=
      (hL x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow] at h2
    nlinarith [sq_nonneg (M₀ + L), sq_nonneg ‖x - y‖]

/-- `‖f‖²_{H^ε} ≤ C_{ε,R} (sup |f| + Lip f)²` for `f` smooth, supported in `B(c, R)`. -/
theorem sobolevSq_le_of_sup {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {M₀ L : ℝ} (hM : ∀ x, |f x| ≤ M₀) (hL : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) {c : ℂ} {R : ℝ}
    (hsupp : ∀ x, x ∉ ball c R → f x = 0) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    sobolevSq ε f ≤ ENNReal.ofReal ((M₀ + L) ^ 2) *
      (volume (ball c R) + (ENNReal.ofReal (gagConst ε))⁻¹ * (8 * volume (ball c R) * gagJ ε 1)) := by
  have hM0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM 0)
  have hl2 : l2Sq f ≤ ENNReal.ofReal ((M₀ + L) ^ 2) * volume (ball c R) := by
    rw [l2Sq, ← lintegral_indicator_one measurableSet_ball, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ ball c R
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hL0 : 0 ≤ L := by
        by_contra hneg; push Not at hneg
        have h' : |f 1 - f 0| ≤ L * ‖(1 : ℂ) - 0‖ := hL 1 0
        simp at h'; linarith [abs_nonneg (f 1 - f 0)]
      have : |f x| ≤ M₀ + L := (hM x).trans (by linarith)
      nlinarith [abs_nonneg (f x), sq_abs (f x)]
    · rw [hsupp x hx]; simp
  have hgag := gagSq_le_of_sq_le (ε := ε) (by positivity) (sq_sub_le_of_sup hM hL) hsupp
  refine (sobolevSq_le_l2Sq_add_gagSq hf hfc hε0 hε1).trans ?_
  calc l2Sq f + (ENNReal.ofReal (gagConst ε))⁻¹ * gagSq ε f
      ≤ ENNReal.ofReal ((M₀ + L) ^ 2) * volume (ball c R) + (ENNReal.ofReal (gagConst ε))⁻¹ *
          (ENNReal.ofReal (4 * (M₀ + L) ^ 2) * (2 * volume (ball c R) * gagJ ε 1)) := by
        gcongr
    _ = ENNReal.ofReal ((M₀ + L) ^ 2) * (volume (ball c R) + (ENNReal.ofReal (gagConst ε))⁻¹ *
          (8 * volume (ball c R) * gagJ ε 1)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

/-! ### Jensen for probability measures -/

theorem sq_lintegral_mul_le' {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e : ∀ y : ℝ≥0∞, y ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simp only [e, Pi.mul_apply] at h
  calc (∫⁻ x, f x * g x ∂μ) ^ 2
      ≤ ((∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- Jensen: `(∫ f dν)² ≤ ∫ f² dν` for a probability measure `ν`. -/
theorem ofReal_sq_integral_le_prob {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Measurable f) :
    ENNReal.ofReal ((∫ x, f x ∂ν) ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν := by
  have h1 : ENNReal.ofReal ((∫ x, f x ∂ν) ^ 2) = ‖∫ x, f x ∂ν‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h2 := sq_lintegral_mul_le' ν (f := fun x => ‖f x‖ₑ) (g := fun _ => 1)
    hf.enorm.aemeasurable aemeasurable_const
  simp only [mul_one, one_pow, lintegral_const, measure_univ] at h2
  rw [h1]
  calc ‖∫ x, f x ∂ν‖ₑ ^ 2 ≤ (∫⁻ x, ‖f x‖ₑ ∂ν) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2
    _ ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := h2
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν := by
        congr 1; funext x
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-! ### Measurability on `𝒟'(D)` -/

variable {D : Opens ℂ}

theorem measurable_distOn_apply (φ : TestOn D) : Measurable (fun T : DistOn D => T φ) :=
  (measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)

theorem measurable_uncurry_fourierSq_distOn (ζ : TestOn D) (s : ℝ) :
    Measurable (uncurry fun (T : DistOn D) (ξ : ℂ) =>
      ENNReal.ofReal (fourierSq T ζ ξ * sobWeight s ξ)) := by
  have hmeas : Measurable (uncurry fun (ξ : ℂ) (T : DistOn D) => fourierSq T ζ ξ * sobWeight s ξ) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun T => (continuous_fourierSq T ζ).mul (continuous_sobWeight _))
      (fun ξ => (((measurable_distOn_apply (cosTest ζ ξ)).pow_const 2).add
        ((measurable_distOn_apply (sinTest ζ ξ)).pow_const 2)).mul_const _)
  exact ENNReal.measurable_ofReal.comp (hmeas.comp measurable_swap)

theorem measurable_negSobolevSq (ε : ℝ) (ζ : TestOn D) :
    Measurable (fun T : DistOn D => negSobolevSq ε T ζ) :=
  (measurable_uncurry_fourierSq_distOn ζ (-ε)).lintegral_prod_right'

theorem measurable_distOn_iff {α : Type*} [MeasurableSpace α] {F : α → DistOn D} :
    Measurable F ↔ ∀ φ : TestOn D, Measurable (fun x => F x φ) := by
  refine ⟨fun hF φ => (measurable_distOn_apply φ).comp hF, fun hF => ?_⟩
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap F (MeasurableSpace.comap (fun (T : DistOn D) (φ : TestOn D) => T φ)
    MeasurableSpace.pi) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (measurable_pi_iff.2 hF).comap_le

/-! ### The sub-σ-algebra as a measurable space -/

/-- `Ω` equipped with the sub-σ-algebra `𝓕` (a type synonym). -/
def SubSigma (Ω : Type*) (_ : MeasurableSpace Ω) : Type _ := Ω

instance {Ω : Type*} (𝓕 : MeasurableSpace Ω) : MeasurableSpace (SubSigma Ω 𝓕) := 𝓕

/-- The identity `(Ω, mΩ) → (Ω, 𝓕)`. -/
def toSub {Ω : Type*} (𝓕 : MeasurableSpace Ω) (o : Ω) : SubSigma Ω 𝓕 := o

theorem measurable_toSub {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : MeasurableSpace Ω}
    (h𝓕 : 𝓕 ≤ mΩ) : Measurable[mΩ] (toSub 𝓕) := fun _ hs => h𝓕 _ hs

theorem measurable_toSub_sub {Ω : Type*} (𝓕 : MeasurableSpace Ω) :
    Measurable[𝓕] (toSub 𝓕) := fun _ hs => hs

theorem comap_toSub {Ω : Type*} (𝓕 : MeasurableSpace Ω) :
    MeasurableSpace.comap (toSub 𝓕) (inferInstance : MeasurableSpace (SubSigma Ω 𝓕)) = 𝓕 :=
  MeasurableSpace.comap_id

/-! ### The barycentre of the regular conditional distribution -/

section Bary

variable {Ω : Type*} {𝓕 mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn D} (hh : Measurable h) (h𝓕 : 𝓕 ≤ mΩ)
include h𝓕 hh

/-- The tower identity `E[∫ f dκ] = E[f(h)]` for the regular conditional distribution `κ` of `h`
given `𝓕`. -/
theorem lintegral_condDistrib_toSub {f : DistOn D → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ o, ∫⁻ T, f T ∂(condDistrib h (toSub 𝓕) P (toSub 𝓕 o)) ∂P = ∫⁻ o, f (h o) ∂P := by
  have hι := measurable_toSub h𝓕
  have hcp := compProd_map_condDistrib (μ := P) (Y := h) hι.aemeasurable hh.aemeasurable
  have h1 := congrArg (fun μ => ∫⁻ p, f p.2 ∂μ) hcp
  have hm2 : Measurable (fun p : SubSigma Ω 𝓕 × DistOn D => f p.2) := hf.comp measurable_snd
  rw [Measure.lintegral_compProd hm2, lintegral_map hm2 (hι.prodMk hh)] at h1
  have hm3 : Measurable (fun x : SubSigma Ω 𝓕 =>
      ∫⁻ T, f T ∂(condDistrib h (toSub 𝓕) P x)) := hf.lintegral_kernel
  rw [← h1, lintegral_map hm3 hι]

theorem ae_lintegral_condDistrib_lt_top {f : DistOn D → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ o, f (h o) ∂P < ⊤) :
    ∀ᵐ o ∂P, ∫⁻ T, f T ∂(condDistrib h (toSub 𝓕) P (toSub 𝓕 o)) < ⊤ :=
  ae_lt_top (hf.lintegral_kernel.comp (measurable_toSub h𝓕))
    (by rw [lintegral_condDistrib_toSub hh h𝓕 hf]; exact hfin.ne)

end Bary

/-! ### Pointwise bounds through a cutoff -/

theorem mulTest_eq_self (ζ φ : TestOn D) (h1 : EqOn ζ 1 (tsupport φ)) :
    mulTest ζ φ.contDiff = φ := by
  refine TestFunction.ext fun x => ?_
  rw [mulTest_apply]
  by_cases hx : x ∈ tsupport φ
  · rw [h1 hx, Pi.one_apply, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem ofReal_sq_apply_le (T : DistOn D) (ζ φ : TestOn D) (h1 : EqOn ζ 1 (tsupport φ)) (ε : ℝ) :
    ENNReal.ofReal (T φ ^ 2) ≤ 4 * negSobolevSq ε T ζ * sobolevSq ε φ := by
  have h := sq_apply_mulTest_le T ζ φ.contDiff φ.hasCompactSupport ε
  rwa [mulTest_eq_self ζ φ h1] at h

theorem enorm_apply_le (T : DistOn D) (ζ φ : TestOn D) (h1 : EqOn ζ 1 (tsupport φ)) (ε : ℝ) :
    ‖T φ‖ₑ ≤ negSobolevSq ε T ζ + sobolevSq ε φ := by
  have h := ofReal_sq_apply_le T ζ φ h1 ε
  set N := negSobolevSq ε T ζ
  set S := sobolevSq ε φ
  by_cases hN : N = ⊤
  · rw [hN, top_add]; exact le_top
  by_cases hS : S = ⊤
  · rw [hS, add_top]; exact le_top
  rw [← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_toReal hS, ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)] at h
  have h2 : T φ ^ 2 ≤ 4 * N.toReal * S.toReal :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_toReal hS,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hN0 : 0 ≤ N.toReal := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
  nlinarith [sq_abs (T φ), abs_nonneg (T φ), sq_nonneg (N.toReal - S.toReal)]

theorem exists_ball_superset (φ : TestOn D) : ∃ R : ℝ, ∀ x, x ∉ ball (0 : ℂ) R → φ x = 0 := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball 0
  exact ⟨R, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hR h)⟩

theorem sobolevSq_lt_top {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (φ : TestOn D) :
    sobolevSq ε φ < ⊤ := by
  obtain ⟨M₀, hM₀⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨L, hL⟩ := exists_lipschitz_of_contDiff φ.contDiff φ.hasCompactSupport
  obtain ⟨R, hR⟩ := exists_ball_superset φ
  have hc : ENNReal.ofReal (gagConst ε) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact gagConst_pos ε
  refine lt_of_le_of_lt (sobolevSq_le_of_sup φ.contDiff φ.hasCompactSupport
    (fun x => by rw [← Real.norm_eq_abs]; exact hM₀ x) hL hR hε0 hε1.le) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨measure_ball_lt_top, ?_⟩)
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hc))
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) measure_ball_lt_top) (gagJ_lt_top hε0 hε1 1))

/-- For `f ∈ 𝓓_K` with `K ⊆ B(0, R)`: `‖f‖²_{H^ε} ≤ C_{ε,R} (N₀ f + N₁ f)²`. -/
theorem sobolevSq_le_seminorm {K : Compacts ℂ} {R : ℝ} (hKR : (K : Set ℂ) ⊆ ball 0 R)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (f : 𝓓_{K}(ℂ, ℝ)) :
    sobolevSq ε f ≤ ENNReal.ofReal ((ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 0 f +
      ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 1 f) ^ 2) *
      (volume (ball (0 : ℂ) R) + (ENNReal.ofReal (gagConst ε))⁻¹ *
        (8 * volume (ball (0 : ℂ) R) * gagJ ε 1)) := by
  set N₀ := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 0 f
  set N₁ := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 1 f
  have hM : ∀ x, |f x| ≤ N₀ := fun x => by
    have := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ (i := 0) (by simp)
      (f := f) (x := x)
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hD : ∀ x, ‖fderiv ℝ f x‖₊ ≤ ⟨N₁, by positivity⟩ := fun x => by
    have := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ (i := 1) (by simp)
      (f := f) (x := x)
    rw [norm_iteratedFDeriv_one] at this
    exact this
  have hLip := lipschitzWith_of_nnnorm_fderiv_le (f.contDiff.differentiable (by simp)) hD
  have hL : ∀ x y, |f x - f y| ≤ N₁ * ‖x - y‖ := fun x y => by
    have := hLip.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at this
  exact sobolevSq_le_of_sup f.contDiff f.hasCompactSupport hM hL
    (fun x hx => f.zero_on_compl fun h => hx (hKR h)) hε0 hε1

/-! ### The version -/

/-- **Aux. lemma 11, conditional means.** Let `h` be a measurable random distribution on `D` whose
pairings are integrable and which satisfies (SR1) for every cutoff (`E‖ζh‖²_{H^{-ε}} < ∞`). For
every sub-σ-algebra `𝓕`, the distributional conditional mean `E[h | 𝓕]` has an `𝓕`-measurable
version `M : Ω → 𝒟'(D)` (`⟨M, φ⟩ = E[⟨h, φ⟩ | 𝓕]` a.s. for every `φ`) with `ζM ∈ H^{-ε}(ℝ²)` almost
surely for every cutoff `ζ` (hence simultaneously for any countable family of cutoffs). -/
theorem exists_condMean_version {Ω : Type*} {𝓕 mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn D} (hh : Measurable h) (h𝓕 : 𝓕 ≤ mΩ)
    (hint : ∀ φ : TestOn D, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn D, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤) :
    ∃ M : Ω → DistOn D, Measurable[𝓕] M ∧
      (∀ φ : TestOn D, (fun o => M o φ) =ᵐ[P] P[fun o => h o φ | 𝓕]) ∧
      ∀ ζ : TestOn D, ∀ᵐ o ∂P, negSobolevSq ε (M o) ζ < ⊤ := by
  classical
  set κ := condDistrib h (toSub 𝓕) P
  have hcut : ∀ n, ∃ ζ : TestOn D, EqOn ζ 1 (exhaustK D n) := fun n => by
    obtain ⟨ζ, -, h1⟩ := exists_cutoff_testOn (exhaustK D n).isCompact (exhaustK_subset D n)
    exact ⟨ζ, h1⟩
  choose ζ hζ using hcut
  set G : Set (SubSigma Ω 𝓕) := {x | ∀ n, ∫⁻ T, negSobolevSq ε T (ζ n) ∂(κ x) < ⊤}
  have hGm : MeasurableSet G := by
    have : G = ⋂ n, {x | ∫⁻ T, negSobolevSq ε T (ζ n) ∂(κ x) < ⊤} := by ext x; simp [G]
    rw [this]
    exact MeasurableSet.iInter fun n =>
      measurableSet_lt (measurable_negSobolevSq ε (ζ n)).lintegral_kernel measurable_const
  have hGae : ∀ᵐ o ∂P, toSub 𝓕 o ∈ G :=
    ae_all_iff.2 fun n => ae_lintegral_condDistrib_lt_top hh h𝓕
      (measurable_negSobolevSq ε (ζ n)) (hSR1 (ζ n))
  have hφn : ∀ φ : TestOn D, ∃ n, EqOn (ζ n) 1 (tsupport φ) := fun φ => by
    obtain ⟨n, hn⟩ := exists_exhaustK_superset D φ.hasCompactSupport.isCompact φ.tsupport_subset
    exact ⟨n, (hζ n).mono hn⟩
  have hintκ : ∀ x ∈ G, ∀ φ : TestOn D, Integrable (fun T : DistOn D => T φ) (κ x) := by
    intro x hx φ
    obtain ⟨n, hn⟩ := hφn φ
    refine ⟨(measurable_distOn_apply φ).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ T, ‖T φ‖ₑ ∂(κ x) ≤ ∫⁻ T, (negSobolevSq ε T (ζ n) + sobolevSq ε φ) ∂(κ x) :=
          lintegral_mono fun T => enorm_apply_le T (ζ n) φ hn ε
      _ = ∫⁻ T, negSobolevSq ε T (ζ n) ∂(κ x) + sobolevSq ε φ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hx n, sobolevSq_lt_top hε0 hε1 φ⟩
  -- the barycentre as a linear functional
  let Λ : (x : SubSigma Ω 𝓕) → x ∈ G → TestOn D →ₗ[ℝ] ℝ := fun x hx =>
    { toFun := fun φ => ∫ T, T φ ∂(κ x)
      map_add' := fun φ ψ => by
        simp only [map_add]
        exact integral_add (hintκ x hx φ) (hintκ x hx ψ)
      map_smul' := fun c φ => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hΛ : ∀ x (hx : x ∈ G) φ, Λ x hx φ = ∫ T, T φ ∂(κ x) := fun _ _ _ => rfl
  have hc0 : ENNReal.ofReal (gagConst ε) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact gagConst_pos ε
  have hcont : ∀ x (hx : x ∈ G), Continuous (Λ x hx) := by
    intro x hx
    rw [TestFunction.continuous_iff_continuous_comp]
    intro K hKD
    obtain ⟨n, hn⟩ := exists_exhaustK_superset D K.isCompact hKD
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_ball 0
    set I := ∫⁻ T, negSobolevSq ε T (ζ n) ∂(κ x)
    set Cst := volume (ball (0 : ℂ) R) + (ENNReal.ofReal (gagConst ε))⁻¹ *
      (8 * volume (ball (0 : ℂ) R) * gagJ ε 1)
    have hCst : Cst ≠ ⊤ := ENNReal.add_ne_top.2 ⟨measure_ball_lt_top.ne,
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne) (gagJ_lt_top hε0 hε1 1).ne)⟩
    have hfin : 4 * Cst * I ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hCst) (hx n).ne
    set Q := (4 * Cst * I).toReal
    have key : ∀ f : 𝓓_{K}(ℂ, ℝ), |Λ x hx (TestFunction.ofSupportedIn hKD f)| ≤
        √Q * (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 0 f +
          ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 1 f) := by
      intro f
      set g := TestFunction.ofSupportedIn hKD f
      set p := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 0 f +
        ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 1 f
      have hp : 0 ≤ p := by positivity
      have hg1 : EqOn (ζ n) 1 (tsupport g) := (hζ n).mono (f.tsupport_subset.trans hn)
      have hS : sobolevSq ε g ≤ ENNReal.ofReal (p ^ 2) * Cst :=
        sobolevSq_le_seminorm hR hε0 hε1.le f
      have h1 : ENNReal.ofReal ((Λ x hx g) ^ 2) ≤ ENNReal.ofReal (p ^ 2) * ENNReal.ofReal Q := by
        rw [hΛ x hx, ENNReal.ofReal_toReal hfin]
        calc ENNReal.ofReal ((∫ T, T g ∂(κ x)) ^ 2)
            ≤ ∫⁻ T, ENNReal.ofReal (T g ^ 2) ∂(κ x) :=
              ofReal_sq_integral_le_prob _ (measurable_distOn_apply g)
          _ ≤ ∫⁻ T, (4 * sobolevSq ε g) * negSobolevSq ε T (ζ n) ∂(κ x) := by
              refine lintegral_mono fun T => ?_
              have := ofReal_sq_apply_le T (ζ n) g hg1 ε
              calc ENNReal.ofReal (T g ^ 2) ≤ 4 * negSobolevSq ε T (ζ n) * sobolevSq ε g := this
                _ = (4 * sobolevSq ε g) * negSobolevSq ε T (ζ n) := by ring
          _ = (4 * sobolevSq ε g) * I := lintegral_const_mul _ (measurable_negSobolevSq ε (ζ n))
          _ ≤ (4 * (ENNReal.ofReal (p ^ 2) * Cst)) * I := by gcongr
          _ = ENNReal.ofReal (p ^ 2) * (4 * Cst * I) := by ring
      have h2 : (Λ x hx g) ^ 2 ≤ p ^ 2 * Q := by
        rw [← ENNReal.ofReal_mul (by positivity)] at h1
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
      have hQ : 0 ≤ Q := ENNReal.toReal_nonneg
      calc |Λ x hx g| = √((Λ x hx g) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(p ^ 2 * Q) := Real.sqrt_le_sqrt h2
        _ = √Q * p := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp, mul_comm]
    let ℓ : 𝓓_{K}(ℂ, ℝ) →ₗ[ℝ] ℝ := (Λ x hx).comp (TestFunction.ofSupportedInCLM ℝ hKD).toLinearMap
    have hℓ : Continuous ℓ := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ℝ ℂ ℝ ⊤ K)
        (norm_withSeminorms ℝ ℝ) ℓ fun _ => ⟨{0, 1}, ⟨2 * √Q, by positivity⟩, fun f => ?_⟩
      simp only [Seminorm.comp_apply, coe_normSeminorm]
      have h0 := Seminorm.le_finset_sup_apply (p := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)
        (x := f) (show (0 : ℕ) ∈ ({0, 1} : Finset ℕ) by simp)
      have h1 := Seminorm.le_finset_sup_apply (p := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)
        (x := f) (show (1 : ℕ) ∈ ({0, 1} : Finset ℕ) by simp)
      have hk := key f
      rw [Real.norm_eq_abs]
      calc |ℓ f| = |Λ x hx (TestFunction.ofSupportedIn hKD f)| := rfl
        _ ≤ √Q * (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 0 f +
            ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K 1 f) := hk
        _ ≤ √Q * (2 * ((({0, 1} : Finset ℕ).sup (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)) f)) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
        _ = 2 * √Q * ((({0, 1} : Finset ℕ).sup (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)) f) := by
            ring
    exact hℓ
  -- the version
  let Mx : SubSigma Ω 𝓕 → DistOn D := fun x =>
    if hx : x ∈ G then (⟨Λ x hx, hcont x hx⟩ : 𝓓(D, ℝ) →L[ℝ] ℝ) else 0
  have hMx : ∀ x ∈ G, ∀ φ, Mx x φ = ∫ T, T φ ∂(κ x) := by
    intro x hx φ
    have e : Mx x = (⟨Λ x hx, hcont x hx⟩ : 𝓓(D, ℝ) →L[ℝ] ℝ) := dite_eq_left hx
    rw [e]
    rfl
  have hMx0 : ∀ x ∉ G, ∀ φ, Mx x φ = 0 := by
    intro x hx φ
    have e : Mx x = 0 := dite_eq_right hx
    rw [e]
    rfl
  have hMxm : Measurable Mx := by
    refine measurable_distOn_iff.2 fun φ => ?_
    have : (fun x => Mx x φ) = G.piecewise (fun x => ∫ T, T φ ∂(κ x)) 0 := by
      funext x
      by_cases hx : x ∈ G
      · rw [piecewise_eq_of_mem _ _ _ hx, hMx x hx]
      · rw [piecewise_eq_of_notMem _ _ _ hx, hMx0 x hx]; rfl
    rw [this]
    exact Measurable.piecewise hGm
      ((measurable_distOn_apply φ).stronglyMeasurable.integral_kernel).measurable measurable_const
  refine ⟨fun o => Mx (toSub 𝓕 o), hMxm.comp (measurable_toSub_sub 𝓕), fun φ => ?_, fun ζ' => ?_⟩
  · have hce := condExp_ae_eq_integral_condDistrib (μ := P) (Y := h)
      (measurable_toSub h𝓕) hh.aemeasurable (measurable_distOn_apply φ).stronglyMeasurable (hint φ)
    rw [comap_toSub] at hce
    filter_upwards [hce, hGae] with o h1 h2
    rw [h1, hMx _ h2]
  · filter_upwards [hGae, ae_lintegral_condDistrib_lt_top hh h𝓕 (measurable_negSobolevSq ε ζ')
      (hSR1 ζ')] with o hx hfin
    refine lt_of_le_of_lt ?_ hfin
    change negSobolevSq ε (Mx (toSub 𝓕 o)) ζ' ≤ _
    set x := toSub 𝓕 o
    unfold negSobolevSq
    rw [lintegral_lintegral_swap (measurable_uncurry_fourierSq_distOn ζ' (-ε)).aemeasurable]
    refine lintegral_mono fun ξ => ?_
    have hw := (sobWeight_pos (-ε) ξ).le
    have hm1 : Measurable (fun T : DistOn D => ENNReal.ofReal (T (cosTest ζ' ξ) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((measurable_distOn_apply _).pow_const 2)
    have hm2 : Measurable (fun T : DistOn D => ENNReal.ofReal (T (sinTest ζ' ξ) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((measurable_distOn_apply _).pow_const 2)
    simp only [fourierSq, hMx x hx]
    calc ENNReal.ofReal (((∫ T, T (cosTest ζ' ξ) ∂(κ x)) ^ 2 +
          (∫ T, T (sinTest ζ' ξ) ∂(κ x)) ^ 2) * sobWeight (-ε) ξ)
        = ENNReal.ofReal ((∫ T, T (cosTest ζ' ξ) ∂(κ x)) ^ 2) * ENNReal.ofReal (sobWeight (-ε) ξ) +
            ENNReal.ofReal ((∫ T, T (sinTest ζ' ξ) ∂(κ x)) ^ 2) *
              ENNReal.ofReal (sobWeight (-ε) ξ) := by
          rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ ≤ (∫⁻ T, ENNReal.ofReal (T (cosTest ζ' ξ) ^ 2) ∂(κ x)) * ENNReal.ofReal (sobWeight (-ε) ξ) +
            (∫⁻ T, ENNReal.ofReal (T (sinTest ζ' ξ) ^ 2) ∂(κ x)) *
              ENNReal.ofReal (sobWeight (-ε) ξ) := by
          gcongr
          · exact ofReal_sq_integral_le_prob _ (measurable_distOn_apply _)
          · exact ofReal_sq_integral_le_prob _ (measurable_distOn_apply _)
      _ = ∫⁻ T, ENNReal.ofReal ((T (cosTest ζ' ξ) ^ 2 + T (sinTest ζ' ξ) ^ 2) *
            sobWeight (-ε) ξ) ∂(κ x) := by
          rw [← lintegral_mul_const _ hm1, ← lintegral_mul_const _ hm2,
            ← lintegral_add_left (hm1.mul_const _)]
          congr 1; funext T
          rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]
/-- **Aux. lemma 11, conditional-mean clause, for the GFF with a deterministic harmonic mean.**
For `h = h⁰ + u` (`h⁰` a zero-boundary GFF on `D` with finite Green covariance on compacts, `u`
harmonic on `D`), every `0 < ε < 1` and every sub-σ-algebra `𝓕`, the distributional conditional
mean `E[h | 𝓕]` has an `𝓕`-measurable version `M` with `ζM ∈ H^{-ε}(ℝ²)` a.s. for every cutoff. -/
theorem aux11_condMean {Ω : Type*} {𝓕 mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (hadm : ZBAdmissible D) {h : Ω → DistOn D}
    (hh : IsZeroBoundaryGFF D h P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u D)
    (h𝓕 : 𝓕 ≤ mΩ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Ω → DistOn D, Measurable[𝓕] M ∧
      (∀ φ : TestOn D, (fun o => M o φ) =ᵐ[P]
        P[fun o => (h o + Distribution.ofFun D u volume ⊤) φ | 𝓕]) ∧
      ∀ ζ : TestOn D, ∀ᵐ o ∂P, negSobolevSq ε (M o) ζ < ⊤ := by
  set m : DistOn D := Distribution.ofFun D u volume ⊤
  have hmeas : Measurable (fun o => h o + m) := by
    refine measurable_distOn_iff.2 fun φ => ?_
    simp only [add_apply]
    exact (hh.process.measurable φ).add_const _
  have hint : ∀ φ : TestOn D, Integrable (fun o => (h o + m) φ) P := by
    intro φ
    simp only [add_apply]
    exact ((hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two).add
      (integrable_const _)
  exact exists_condMean_version hmeas h𝓕 hint hε0 hε1
    (fun ζ => aux11_sr1 hadm hh hu hε0 ζ)

end InteractingSLE.Sobolev
