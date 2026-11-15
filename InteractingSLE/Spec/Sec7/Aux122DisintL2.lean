/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux122DisintFilt
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

/-!
# §7.4, Aux. lemma 122: from rational to real times under one conditional law

Packet PROVE-AUX119-130. Specification §7.4.1, Aux. lemma 122, last paragraph of its proof
(`source/spec/p385-432.md` L111–L139, p. 391).

Under a fixed conditional law `ν` the Brownian identities are first obtained at countably many (rational) times.
This file passes to real times for a process `Y` with continuous paths and the rational-time `L²` isometry
`∫ |Y_{q'} − Y_q|² dν = |q' − q|` (`RatIsometry`):

* `lintegral_sq_sub_le`: `∫ |Y_q − Y_t|² dν ≤ |q − t|` for every real `t` (Fatou along rational approximants);
* `memLp_two_eval`: `Y_t ∈ L²(ν)`;
* `tendsto_setIntegral_eval`, `tendsto_setIntegral_sq_sub`: along rational times `r_n → t`, the set integrals of
  `Y_{r_n}` and of `Y_{r_n}² − r_n` over any event converge to those at `t`;
* `setIntegral_eq_of_rat`: an identity `∫_A F_{q'} = ∫_A F_q` at all rational `s ≤ q ≤ q'` passes to `∫_A F_t = ∫_A F_s`
  for real `s ≤ t`, for `F = Y` and `F = Y² − t` (`ratUp`: rational approximants from above).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux122Disint

/-! ### Rational approximants from above -/

/-- `ratApprox n t + 1/(n+1)`, a rational in `[t, t + 1/(n+1)]`. -/
def ratUp (n : ℕ) (t : ℝ≥0) : ℚ := ratApprox n t + 1 / (n + 1)

theorem ratUp_nonneg (n : ℕ) (t : ℝ≥0) : 0 ≤ ratUp n t := by
  unfold ratUp
  have := ratApprox_nonneg n t
  positivity

theorem coe_rt_ratUp (n : ℕ) (t : ℝ≥0) :
    ((rt (ratUp n t) : ℝ≥0) : ℝ) = ((rt (ratApprox n t) : ℝ≥0) : ℝ) + 1 / ((n : ℝ) + 1) := by
  rw [coe_rt (ratUp_nonneg n t), coe_rt (ratApprox_nonneg n t)]
  unfold ratUp
  push_cast
  rfl

theorem le_rt_ratUp (n : ℕ) (t : ℝ≥0) : t ≤ rt (ratUp n t) := by
  rw [← NNReal.coe_le_coe, coe_rt_ratUp, coe_rt_ratApprox]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfl : (t : ℝ) * ((n : ℝ) + 1) < (⌊t * (n + 1)⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (t * (n + 1))
    exact_mod_cast this
  rw [← add_div, le_div_iff₀ hn]
  linarith

theorem rt_ratUp_mono (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) : rt (ratUp n s) ≤ rt (ratUp n t) := by
  rw [← NNReal.coe_le_coe, coe_rt_ratUp, coe_rt_ratUp, coe_rt_ratApprox, coe_rt_ratApprox]
  gcongr

theorem tendsto_rt_ratUp (t : ℝ≥0) : Tendsto (fun n => rt (ratUp n t)) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  simp_rw [coe_rt_ratUp]
  have h := (NNReal.tendsto_coe.2 (tendsto_rt_ratApprox t)).add tendsto_one_div_add_atTop_nhds_zero_nat
  rwa [add_zero] at h

/-! ### The rational-time isometry and its consequences -/

section L2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} {Y : ℝ≥0 → Ω → ℝ}

/-- **The rational-time `L²` isometry**: `∫ |Y_{q'} − Y_q|² dν = |q' − q|` at rational times. -/
def RatIsometry (ν : Measure Ω) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ q q' : ℚ, ∫⁻ ω, ‖Y (rt q') ω - Y (rt q) ω‖ₑ ^ 2 ∂ν = (nndist (rt q) (rt q') : ℝ≥0∞)

/-- Cauchy–Schwarz for lower integrals, with square exponents. -/
theorem lintegral_mul_le_sqrt_mul_sqrt {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    ∫⁻ ω, f ω * g ω ∂ν ≤ (∫⁻ ω, f ω ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ ω, g ω ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg
  simp only [ENNReal.rpow_two, Pi.mul_apply] at h
  exact h

variable (hYc : ∀ ω, Continuous fun t => Y t ω) (hYm : ∀ t, Measurable (Y t))
include hYc hYm

/-- **Fatou at a real time**: `∫ |Y_q − Y_t|² dν ≤ |q − t|`. -/
theorem lintegral_sq_sub_le (hiso : RatIsometry ν Y) (q : ℚ) (t : ℝ≥0) :
    ∫⁻ ω, ‖Y (rt q) ω - Y t ω‖ₑ ^ 2 ∂ν ≤ (nndist (rt q) t : ℝ≥0∞) := by
  have hlim : ∀ ω, Tendsto (fun m => ‖Y (rt q) ω - Y (rt (ratApprox m t)) ω‖ₑ ^ 2) atTop
      (𝓝 (‖Y (rt q) ω - Y t ω‖ₑ ^ 2)) := fun ω =>
    ENNReal.Tendsto.pow ((continuous_enorm.tendsto _).comp
      (tendsto_const_nhds.sub (((hYc ω).tendsto t).comp (tendsto_rt_ratApprox t))))
  have hd : Tendsto (fun m => (nndist (rt (ratApprox m t)) (rt q) : ℝ≥0∞)) atTop
      (𝓝 (nndist t (rt q) : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto _).comp ((tendsto_rt_ratApprox t).nndist tendsto_const_nhds)
  calc ∫⁻ ω, ‖Y (rt q) ω - Y t ω‖ₑ ^ 2 ∂ν
      = ∫⁻ ω, liminf (fun m => ‖Y (rt q) ω - Y (rt (ratApprox m t)) ω‖ₑ ^ 2) atTop ∂ν :=
        lintegral_congr fun ω => ((hlim ω).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ ω, ‖Y (rt q) ω - Y (rt (ratApprox m t)) ω‖ₑ ^ 2 ∂ν) atTop :=
        lintegral_liminf_le fun m => (((hYm _).sub (hYm _)).enorm).pow_const 2
    _ = liminf (fun m => (nndist (rt (ratApprox m t)) (rt q) : ℝ≥0∞)) atTop := by
        congr 1
        funext m
        exact hiso _ _
    _ = (nndist (rt q) t : ℝ≥0∞) := by rw [hd.liminf_eq, nndist_comm]

/-- `∫ |Y_t|² dν ≤ t` when `Y_0 = 0`. -/
theorem lintegral_sq_le (hiso : RatIsometry ν Y) (hY0 : ∀ ω, Y 0 ω = 0) (t : ℝ≥0) :
    ∫⁻ ω, ‖Y t ω‖ₑ ^ 2 ∂ν ≤ t := by
  have h := lintegral_sq_sub_le hYc hYm hiso 0 t
  have hrt : rt 0 = 0 := by simp [rt]
  have hd : nndist (0 : ℝ≥0) t = t := by
    rw [← NNReal.coe_inj, coe_nndist, NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg]; exact abs_of_nonneg t.2
  simp only [hrt, hY0, zero_sub, enorm_neg, hd] at h
  exact h

/-- `Y_t ∈ L²(ν)`. -/
theorem memLp_two_eval_of_iso (hiso : RatIsometry ν Y) (hY0 : ∀ ω, Y 0 ω = 0) (t : ℝ≥0) : MemLp (Y t) 2 ν := by
  rw [memLp_two_iff_integrable_sq (hYm t).aestronglyMeasurable]
  refine ⟨((hYm t).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [enorm_pow]
  exact lt_of_le_of_lt (lintegral_sq_le hYc hYm hiso hY0 t) ENNReal.coe_lt_top

variable [IsProbabilityMeasure ν]

/-- `∫ |Y_q − Y_t| dν ≤ |q − t|^{1/2}`. -/
theorem lintegral_enorm_sub_le (hiso : RatIsometry ν Y) (q : ℚ) (t : ℝ≥0) :
    ∫⁻ ω, ‖Y (rt q) ω - Y t ω‖ₑ ∂ν ≤ (nndist (rt q) t : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
  have hm : Measurable fun ω => ‖Y (rt q) ω - Y t ω‖ₑ := ((hYm _).sub (hYm _)).enorm
  have h := lintegral_mul_le_sqrt_mul_sqrt (ν := ν) hm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [mul_one, one_pow, lintegral_const, measure_univ, ENNReal.one_rpow] at h
  exact h.trans (ENNReal.rpow_le_rpow (lintegral_sq_sub_le hYc hYm hiso q t) (by norm_num))

omit [IsProbabilityMeasure ν] in
/-- `∫ |Y_q² − Y_t²| dν ≤ |q − t| + 2 |q − t|^{1/2} t^{1/2}`. -/
theorem lintegral_enorm_sq_sub_le (hiso : RatIsometry ν Y) (hY0 : ∀ ω, Y 0 ω = 0) (q : ℚ) (t : ℝ≥0) :
    ∫⁻ ω, ‖Y (rt q) ω ^ 2 - Y t ω ^ 2‖ₑ ∂ν ≤
      (nndist (rt q) t : ℝ≥0∞) + 2 * ((nndist (rt q) t : ℝ≥0∞) ^ (1 / 2 : ℝ) * (t : ℝ≥0∞) ^ (1 / 2 : ℝ)) := by
  have hd : Measurable fun ω => ‖Y (rt q) ω - Y t ω‖ₑ := ((hYm _).sub (hYm _)).enorm
  have hb : Measurable fun ω => ‖Y t ω‖ₑ := (hYm t).enorm
  have hpt : ∀ ω, ‖Y (rt q) ω ^ 2 - Y t ω ^ 2‖ₑ ≤
      ‖Y (rt q) ω - Y t ω‖ₑ ^ 2 + 2 * (‖Y (rt q) ω - Y t ω‖ₑ * ‖Y t ω‖ₑ) := fun ω => by
    have e : Y (rt q) ω ^ 2 - Y t ω ^ 2 = (Y (rt q) ω - Y t ω) ^ 2 + 2 * Y t ω * (Y (rt q) ω - Y t ω) := by ring
    rw [e]
    refine (enorm_add_le _ _).trans (le_of_eq ?_)
    have h2 : ‖(2 : ℝ)‖ₑ = 2 := by rw [Real.enorm_eq_ofReal_abs]; norm_num
    rw [enorm_pow, enorm_mul, enorm_mul, h2]
    ring
  calc ∫⁻ ω, ‖Y (rt q) ω ^ 2 - Y t ω ^ 2‖ₑ ∂ν
      ≤ ∫⁻ ω, (‖Y (rt q) ω - Y t ω‖ₑ ^ 2 + 2 * (‖Y (rt q) ω - Y t ω‖ₑ * ‖Y t ω‖ₑ)) ∂ν := lintegral_mono hpt
    _ = ∫⁻ ω, ‖Y (rt q) ω - Y t ω‖ₑ ^ 2 ∂ν + 2 * ∫⁻ ω, ‖Y (rt q) ω - Y t ω‖ₑ * ‖Y t ω‖ₑ ∂ν := by
        rw [lintegral_add_left (hd.pow_const 2)]
        congr 1
        exact lintegral_const_mul _
          (show Measurable fun ω => ‖Y (rt q) ω - Y t ω‖ₑ * ‖Y t ω‖ₑ from hd.mul hb)
    _ ≤ (nndist (rt q) t : ℝ≥0∞) +
          2 * ((nndist (rt q) t : ℝ≥0∞) ^ (1 / 2 : ℝ) * (t : ℝ≥0∞) ^ (1 / 2 : ℝ)) := by
        gcongr
        · exact lintegral_sq_sub_le hYc hYm hiso q t
        · refine (lintegral_mul_le_sqrt_mul_sqrt hd.aemeasurable hb.aemeasurable).trans ?_
          gcongr
          · exact lintegral_sq_sub_le hYc hYm hiso q t
          · exact lintegral_sq_le hYc hYm hiso hY0 t

omit hYc hYm [IsProbabilityMeasure ν] in
theorem tendsto_nndist_rpow {r : ℕ → ℚ} {t : ℝ≥0} (hr : Tendsto (fun n => rt (r n)) atTop (𝓝 t)) :
    Tendsto (fun n => (nndist (rt (r n)) t : ℝ≥0∞) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => (nndist (rt (r n)) t : ℝ≥0∞)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_coe.tendsto _).comp (hr.nndist (tendsto_const_nhds (x := t)))
    rw [nndist_self, ENNReal.coe_zero] at this
    exact this
  have h2 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h1
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h2

/-- **Set integrals of `Y` converge along rational times.** -/
theorem tendsto_setIntegral_eval (hiso : RatIsometry ν Y) (hY0 : ∀ ω, Y 0 ω = 0) {r : ℕ → ℚ} {t : ℝ≥0}
    (hr : Tendsto (fun n => rt (r n)) atTop (𝓝 t)) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, Y (rt (r n)) ω ∂ν) atTop (𝓝 (∫ ω in A, Y t ω ∂ν)) := by
  refine tendsto_setIntegral_of_L1 (Y t) (hYm t).aestronglyMeasurable
    (Eventually.of_forall fun n => (memLp_two_eval_of_iso hYc hYm hiso hY0 _).integrable one_le_two) ?_ A
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_nndist_rpow hr)
    (fun _ => zero_le) (fun n => lintegral_enorm_sub_le hYc hYm hiso (r n) t)

/-- **Set integrals of `Y² − t` converge along rational times.** -/
theorem tendsto_setIntegral_sq_sub (hiso : RatIsometry ν Y) (hY0 : ∀ ω, Y 0 ω = 0) {r : ℕ → ℚ} {t : ℝ≥0}
    (hr : Tendsto (fun n => rt (r n)) atTop (𝓝 t)) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, (Y (rt (r n)) ω ^ 2 - (rt (r n) : ℝ)) ∂ν) atTop
      (𝓝 (∫ ω in A, (Y t ω ^ 2 - (t : ℝ)) ∂ν)) := by
  have hint : ∀ x : ℝ≥0, Integrable (fun ω => Y x ω ^ 2) ν := fun x =>
    (memLp_two_eval_of_iso hYc hYm hiso hY0 x).integrable_sq
  have hsq : Tendsto (fun n => ∫ ω in A, Y (rt (r n)) ω ^ 2 ∂ν) atTop (𝓝 (∫ ω in A, Y t ω ^ 2 ∂ν)) := by
    refine tendsto_setIntegral_of_L1 (fun ω => Y t ω ^ 2) (hint t).aestronglyMeasurable
      (Eventually.of_forall fun n => hint _) ?_ A
    have hb : Tendsto (fun n => (nndist (rt (r n)) t : ℝ≥0∞) +
        2 * ((nndist (rt (r n)) t : ℝ≥0∞) ^ (1 / 2 : ℝ) * (t : ℝ≥0∞) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (nndist (rt (r n)) t : ℝ≥0∞)) atTop (𝓝 0) := by
        have := (ENNReal.continuous_coe.tendsto _).comp (hr.nndist (tendsto_const_nhds (x := t)))
        rw [nndist_self, ENNReal.coe_zero] at this
        exact this
      have h2 := ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.mul_const (b := (t : ℝ≥0∞) ^ (1 / 2 : ℝ)) (tendsto_nndist_rpow hr)
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ENNReal.coe_ne_top))) (a := 2)
        (Or.inr ENNReal.ofNat_ne_top)
      simpa using h1.add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
      (fun n => lintegral_enorm_sq_sub_le hYc hYm hiso hY0 (r n) t)
  have e : ∀ x : ℝ≥0, ∫ ω in A, (Y x ω ^ 2 - (x : ℝ)) ∂ν = ∫ ω in A, Y x ω ^ 2 ∂ν - ν.real A * x := by
    intro x
    rw [integral_sub (hint x).integrableOn (integrable_const _).integrableOn, setIntegral_const, smul_eq_mul]
  simp_rw [e]
  refine hsq.sub (tendsto_const_nhds.mul ?_)
  exact NNReal.tendsto_coe.2 hr

omit hYc hYm [IsProbabilityMeasure ν] in
/-- **From rational to real times**: an identity `∫_A F_{q'} = ∫_A F_q` at rational times `s ≤ q ≤ q'` passes to
`∫_A F_t = ∫_A F_s`, when the set integrals of `F` converge along rational times. -/
theorem setIntegral_eq_of_rat {F : ℝ≥0 → Ω → ℝ} {A : Set Ω}
    (hconv : ∀ (x : ℝ≥0) (r : ℕ → ℚ), Tendsto (fun n => rt (r n)) atTop (𝓝 x) →
      Tendsto (fun n => ∫ ω in A, F (rt (r n)) ω ∂ν) atTop (𝓝 (∫ ω in A, F x ω ∂ν)))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hrat : ∀ q q' : ℚ, s ≤ rt q → rt q ≤ rt q' → ∫ ω in A, F (rt q') ω ∂ν = ∫ ω in A, F (rt q) ω ∂ν) :
    ∫ ω in A, F t ω ∂ν = ∫ ω in A, F s ω ∂ν := by
  refine tendsto_nhds_unique (hconv t (fun n => ratUp n t) (tendsto_rt_ratUp t)) ?_
  refine (hconv s (fun n => ratUp n s) (tendsto_rt_ratUp s)).congr fun n => ?_
  exact (hrat (ratUp n s) (ratUp n t) (le_rt_ratUp n s) (rt_ratUp_mono n hst)).symm

end L2

end Aux122Disint

end Sec7

end InteractingSLE
