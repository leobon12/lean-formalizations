/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Complex.DerivLog
import QuantumZipper.Proofs.Complex.BasicsAutomorphisms

/-!
# The Möbius map of the unit disc onto `ℍ` sending two boundary points to `0` and `∞`

Packet PROVE-LEMMA71E (PROVE-LEMMA71D's "What remains" C (iv): "the real Möbius map `𝔻 → ℍ` sending them to `0, ∞`
(explicit, measurable in its parameters)"). For distinct points `p, q` of the unit circle,

  `M_{p,q}(w) = cayleyInv (q̄ w) − Re (cayleyInv (q̄ p))`,  `cayleyInv ζ = i (1 + ζ)/(1 − ζ)`,

is a conformal bijection of the unit disc onto `ℍ` (a rotation, the inverse Cayley map and a real translation) with
`M_{p,q}(w) → 0` as `w → p` and `|M_{p,q}(w)| → ∞` as `w → q` inside the disc. Its derivative is
`q̄ · 2i/(1 − q̄ w)²`, with the explicit holomorphic logarithm `log (2 i q̄) − 2 log (1 − q̄ w)` on the disc.

## Main results

* `bdryMob`, `bdryMobLog`; `bdryMob_mem_H`, **`isConformalBijection_bdryMob`**, **`isDerivLog_bdryMob`**;
* `tendsto_bdryMob_left` (`→ 0` at `p`), `tendsto_norm_bdryMob_right` (`→ ∞` at `q`);
* `measurable_bdryMob`, `measurable_bdryMobLog` (jointly in `(p, q, w)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped ComplexConjugate
open QuantumZipper (H)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.Lemma71E

/-- The Möbius map `M_{p,q}(w) = cayleyInv (q̄ w) − Re (cayleyInv (q̄ p))` of the unit disc onto `ℍ`. -/
def bdryMob (p q : ℂ) (w : ℂ) : ℂ := cayleyInv (conj q * w) - ((cayleyInv (conj q * p)).re : ℂ)

/-- The holomorphic logarithm `log (2 i q̄) − 2 log (1 − q̄ w)` of `M_{p,q}′` on the unit disc. -/
def bdryMobLog (q : ℂ) (w : ℂ) : ℂ := log (2 * I * conj q) - 2 * log (1 - conj q * w)

variable {p q : ℂ}

theorem norm_conj_mul_lt (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : ‖conj q * w‖ < 1 := by
  rw [norm_mul, Complex.norm_conj, hq, one_mul]
  exact mem_ball_zero_iff.1 hw

theorem conj_mul_mem_ball (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : conj q * w ∈ ball (0 : ℂ) 1 :=
  mem_ball_zero_iff.2 (norm_conj_mul_lt hq hw)

theorem conj_mul_ne_one (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : conj q * w ≠ 1 := fun h => by
  have := norm_conj_mul_lt hq hw
  rw [h, norm_one] at this
  exact lt_irrefl _ this

theorem conj_mul_self (hq : ‖q‖ = 1) : conj q * q = 1 := by
  rw [Complex.conj_mul', hq]
  simp

theorem conj_mul_ne_one_of_ne (hq : ‖q‖ = 1) (hpq : p ≠ q) : conj q * p ≠ 1 := fun h => by
  apply hpq
  have : q * (conj q * p) = q := by rw [h, mul_one]
  rw [← mul_assoc, mul_comm q, conj_mul_self hq, one_mul] at this
  exact this

theorem bdryMob_mem_H (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : bdryMob p q w ∈ H := by
  show 0 < (bdryMob p q w).im
  rw [bdryMob, sub_im, ofReal_im, sub_zero]
  exact QuantumZipper.CA.cayleyInv_mem_H (conj_mul_mem_ball hq hw)

theorem differentiableAt_bdryMob (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    DifferentiableAt ℂ (bdryMob p q) w :=
  ((QuantumZipper.CA.differentiableAt_cayleyInv (conj_mul_ne_one hq hw)).comp w
    (differentiableAt_id.const_mul _)).sub_const _

/-- **`M_{p,q}` is a conformal bijection of the unit disc onto `ℍ`.** -/
theorem isConformalBijection_bdryMob (hq : ‖q‖ = 1) : IsConformalBijection (bdryMob p q) (ball 0 1) H := by
  refine ⟨fun w hw => (differentiableAt_bdryMob hq hw).differentiableWithinAt,
    fun w hw => bdryMob_mem_H hq hw, fun w₁ h₁ w₂ h₂ h => ?_, fun z hz => ?_⟩
  · have h' : cayleyInv (conj q * w₁) = cayleyInv (conj q * w₂) := by
      simpa [bdryMob] using h
    have := congrArg cayley h'
    rw [QuantumZipper.CA.cayley_cayleyInv (conj_mul_ne_one hq h₁),
      QuantumZipper.CA.cayley_cayleyInv (conj_mul_ne_one hq h₂)] at this
    have hq0 : conj q ≠ 0 := by
      intro h0
      rw [map_eq_zero] at h0
      rw [h0, norm_zero] at hq
      exact zero_ne_one hq
    exact mul_left_cancel₀ hq0 this
  · set x : ℂ := ((cayleyInv (conj q * p)).re : ℂ)
    have hzx : z + x ∈ H := by
      have hz' : 0 < z.im := hz
      show 0 < (z + x).im
      simpa [x] using hz'
    have hc := QuantumZipper.CA.cayley_mem_ball hzx
    refine ⟨q * cayley (z + x), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_mul, hq, one_mul]
      exact mem_ball_zero_iff.1 hc
    · show cayleyInv (conj q * (q * cayley (z + x))) - x = z
      rw [← mul_assoc, conj_mul_self hq, one_mul,
        QuantumZipper.CA.cayleyInv_cayley (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hzx))]
      ring

theorem hasDerivAt_cayleyInv {ζ : ℂ} (hζ : ζ ≠ 1) : HasDerivAt cayleyInv (2 * I / (1 - ζ) ^ 2) ζ := by
  have h1 : (1 - ζ) ≠ 0 := sub_ne_zero.2 (Ne.symm hζ)
  have hn : HasDerivAt (fun ζ : ℂ => I * (1 + ζ)) (I * 1) ζ :=
    ((hasDerivAt_id ζ).const_add 1).const_mul I
  have hd : HasDerivAt (fun ζ : ℂ => 1 - ζ) (-1) ζ := by
    simpa using (hasDerivAt_id ζ).const_sub 1
  exact (hn.div hd h1).congr_deriv (by ring)

theorem hasDerivAt_bdryMob (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasDerivAt (bdryMob p q) (conj q * (2 * I / (1 - conj q * w) ^ 2)) w := by
  have h1 := (hasDerivAt_cayleyInv (conj_mul_ne_one hq hw)).comp w
    ((hasDerivAt_id w).const_mul (conj q))
  have h2 := h1.sub_const ((cayleyInv (conj q * p)).re : ℂ)
  exact h2.congr_deriv (by ring)

theorem one_sub_conj_mul_mem_slitPlane (hq : ‖q‖ = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    1 - conj q * w ∈ slitPlane := by
  left
  rw [sub_re, one_re]
  have := (Complex.re_le_norm (conj q * w)).trans_lt (norm_conj_mul_lt hq hw)
  linarith

theorem two_I_conj_ne_zero (hq : ‖q‖ = 1) : 2 * I * conj q ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) ?_
  intro h0
  rw [map_eq_zero] at h0
  rw [h0, norm_zero] at hq
  exact zero_ne_one hq

/-- **The explicit derivative lift of `M_{p,q}`** on the unit disc. -/
theorem isDerivLog_bdryMob (hq : ‖q‖ = 1) : IsDerivLog (bdryMob p q) (bdryMobLog q) (ball 0 1) := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have hs := one_sub_conj_mul_mem_slitPlane hq hw
    have : DifferentiableAt ℂ (fun w => log (1 - conj q * w)) w :=
      ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)).clog hs
    exact ((differentiableAt_const _).sub (this.const_mul 2)).differentiableWithinAt
  · rw [(hasDerivAt_bdryMob hq hw).deriv, bdryMobLog, exp_sub, exp_log (two_I_conj_ne_zero hq)]
    have hne : 1 - conj q * w ≠ 0 := slitPlane_ne_zero (one_sub_conj_mul_mem_slitPlane hq hw)
    have e2 : exp (2 * log (1 - conj q * w)) = (1 - conj q * w) ^ 2 := by
      rw [two_mul, exp_add, exp_log hne, sq]
    rw [e2]
    field_simp

theorem continuousOn_bdryMobLog (hq : ‖q‖ = 1) : ContinuousOn (bdryMobLog q) (ball 0 1) :=
  (isDerivLog_bdryMob (p := 0) hq).1.continuousOn

/-- `M_{p,q}(w) → 0` as `w → p`, for distinct `p, q` on the unit circle. -/
theorem tendsto_bdryMob_left (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    Tendsto (bdryMob p q) (𝓝 p) (𝓝 0) := by
  have hne := conj_mul_ne_one_of_ne hq hpq
  have hc : ContinuousAt (bdryMob p q) p :=
    (((QuantumZipper.CA.differentiableAt_cayleyInv hne).comp p
      (differentiableAt_id.const_mul _)).sub_const _).continuousAt
  have h0 : bdryMob p q p = 0 := by
    have him : (cayleyInv (conj q * p)).im = 0 := by
      rw [QuantumZipper.CA.im_cayleyInv, norm_mul, Complex.norm_conj, hq, hp]
      simp
    apply Complex.ext
    · simp [bdryMob]
    · simp [bdryMob, him]
  rw [← h0]
  exact hc.tendsto

/-- `|M_{p,q}(w)| → ∞` as `w → q` inside the unit disc, for `q` on the unit circle. -/
theorem tendsto_norm_bdryMob_right (hq : ‖q‖ = 1) :
    Tendsto (fun w => ‖bdryMob p q w‖) (𝓝[ball 0 1] q) atTop := by
  have h1 : Tendsto (fun w => conj q * w) (𝓝[ball 0 1] q) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => conj_mul_ne_one hq hw⟩
    have hc : Continuous fun w : ℂ => conj q * w := by fun_prop
    have := (hc.tendsto q).mono_left (nhdsWithin_le_nhds (s := ball 0 1))
    rwa [conj_mul_self hq] at this
  have h2 := QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp h1
  have h3 : Tendsto (fun w => bdryMob p q w) (𝓝[ball 0 1] q) (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded] at h2 ⊢
    refine tendsto_atTop_mono' _ (Eventually.of_forall fun w => ?_)
      (tendsto_atTop_add_const_right _ (-‖((cayleyInv (conj q * p)).re : ℂ)‖) h2)
    have := norm_sub_norm_le (cayleyInv (conj q * w)) ((cayleyInv (conj q * p)).re : ℂ)
    simp only [Function.comp_apply, bdryMob]
    linarith
  exact tendsto_norm_atTop_iff_cobounded.2 h3

/-! ### Measurability in the parameters -/

theorem measurable_cayleyInv : Measurable cayleyInv := by
  unfold cayleyInv
  fun_prop

theorem measurable_bdryMob : Measurable fun x : ℂ × ℂ × ℂ => bdryMob x.1 x.2.1 x.2.2 := by
  unfold bdryMob
  have hc : Measurable fun x : ℂ × ℂ × ℂ => conj x.2.1 := Complex.continuous_conj.measurable.comp (by fun_prop)
  refine (measurable_cayleyInv.comp (hc.mul (by fun_prop))).sub ?_
  exact Complex.measurable_ofReal.comp (Complex.measurable_re.comp
    (measurable_cayleyInv.comp (hc.mul (by fun_prop))))

theorem measurable_bdryMobLog : Measurable fun x : ℂ × ℂ => bdryMobLog x.1 x.2 := by
  unfold bdryMobLog
  have hc : Measurable fun x : ℂ × ℂ => conj x.1 := Complex.continuous_conj.measurable.comp (by fun_prop)
  exact (Complex.measurable_log.comp (measurable_const.mul hc)).sub
    (measurable_const.mul (Complex.measurable_log.comp (measurable_const.sub (hc.mul (by fun_prop)))))

end InteractingSLE.Sec7.Lemma71E
