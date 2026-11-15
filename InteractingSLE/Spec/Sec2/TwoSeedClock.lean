/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The clocks of the two-seed construction

Packet PROVE-SEC2-JAC. The deterministic part of the two-seed entrance construction in the proof
of Theorem 2.2 (Specification p. 23, `source/spec/p001-048.md` L516–L526): for a continuous path
`U : ℝ → [0, 1]` (the two-sided stationary Jacobi process in the source),

* `clock U u = t(u) = ½ ∫_{-∞}^u e^{2v} U_v (1 - U_v) dv`,
* `lowerL U u = L^-(u) = -∫_{-∞}^u e^v (1 - U_v) dv`, `upperL U u = L^+(u) = ∫_{-∞}^u e^v U_v dv`,
* `driver U u = w(u) = L^-(u) + e^u U_u`,

their finiteness, the identity `L^+(u) - L^-(u) = e^u`, the bounds `|L^±(u)|, |w(u)| ≤ e^u`
(the source states `≤ 2e^u`), `0 ≤ t(u) ≤ e^{2u}/8`, continuity, `t(u) ↓ 0` as `u → -∞`, strict
monotonicity of `t` when `{u : U_u ∈ {0, 1}}` is Lebesgue-null, and the inverse clock
`invClock U` (`u(t)` in the source) when moreover `t(u) → ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

/-- If `f` is continuous and integrable on every left half-line, then `x ↦ ∫_{(-∞, x]} f` has
derivative `f u` at every `u`. -/
theorem hasDerivAt_integral_Iic {f : ℝ → ℝ} (hf : Continuous f)
    (hfi : ∀ u, IntegrableOn f (Iic u)) (u : ℝ) :
    HasDerivAt (fun x => ∫ v in Iic x, f v) (f u) u := by
  have heq : (fun x => ∫ v in Iic x, f v) = fun x => (∫ v in Iic 0, f v) + ∫ v in (0 : ℝ)..x, f v := by
    funext x
    rw [← intervalIntegral.integral_Iic_sub_Iic (hfi 0) (hfi x)]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt).const_add _

/-- The density of the clock: `½ e^{2v} U_v (1 - U_v)`. -/
def clockDensity (U : ℝ → ℝ) (v : ℝ) : ℝ := exp (2 * v) * (U v * (1 - U v)) / 2

/-- The physical clock `t(u) = ½ ∫_{-∞}^u e^{2v} U_v (1 - U_v) dv` of the two-seed construction. -/
def clock (U : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v in Iic u, clockDensity U v

/-- The left force point in the logarithmic clock, `L^-(u) = -∫_{-∞}^u e^v (1 - U_v) dv`. -/
def lowerL (U : ℝ → ℝ) (u : ℝ) : ℝ := -∫ v in Iic u, exp v * (1 - U v)

/-- The right force point in the logarithmic clock, `L^+(u) = ∫_{-∞}^u e^v U_v dv`. -/
def upperL (U : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v in Iic u, exp v * U v

/-- The driving point in the logarithmic clock, `w(u) = L^-(u) + e^u U_u`. -/
def driver (U : ℝ → ℝ) (u : ℝ) : ℝ := lowerL U u + exp u * U u

/-- The inverse clock `u(t)`: the least `u` with `t ≤ t(u)`. -/
def invClock (U : ℝ → ℝ) (t : ℝ) : ℝ := sInf {u | t ≤ clock U u}

variable {U : ℝ → ℝ}

theorem mul_one_sub_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : x * (1 - x) ∈ Icc (0 : ℝ) (1 / 4) := by
  obtain ⟨h0, h1⟩ := hx
  constructor
  · exact mul_nonneg h0 (by linarith)
  · nlinarith [sq_nonneg (x - 1 / 2)]

section Basic

variable (hc : Continuous U) (h01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
include hc h01

theorem integrableOn_exp_mul (u : ℝ) : IntegrableOn (fun v => exp v * U v) (Iic u) := by
  refine (integrableOn_exp_Iic u).mono' (continuous_exp.mul hc).aestronglyMeasurable ?_
  refine ae_of_all _ fun v => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos v).le (h01 v).1)]
  exact mul_le_of_le_one_right (exp_pos v).le (h01 v).2

theorem integrableOn_exp_mul_one_sub (u : ℝ) :
    IntegrableOn (fun v => exp v * (1 - U v)) (Iic u) := by
  refine (integrableOn_exp_Iic u).mono'
    (continuous_exp.mul (continuous_const.sub hc)).aestronglyMeasurable ?_
  refine ae_of_all _ fun v => ?_
  have h0 : 0 ≤ 1 - U v := by linarith [(h01 v).2]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos v).le h0)]
  exact mul_le_of_le_one_right (exp_pos v).le (by linarith [(h01 v).1])

omit h01 in
theorem continuous_clockDensity : Continuous (clockDensity U) := by
  unfold clockDensity
  fun_prop

omit hc in
theorem clockDensity_nonneg (v : ℝ) : 0 ≤ clockDensity U v :=
  div_nonneg (mul_nonneg (exp_pos _).le (mul_one_sub_mem_Icc (h01 v)).1) zero_le_two

omit hc in
theorem clockDensity_le {u v : ℝ} (hv : v ≤ u) : clockDensity U v ≤ exp u * exp v / 8 := by
  unfold clockDensity
  have h1 : exp (2 * v) ≤ exp u * exp v := by
    rw [← exp_add]; exact exp_le_exp.2 (by linarith)
  have h2 := mul_one_sub_mem_Icc (h01 v)
  have h3 : exp (2 * v) * (U v * (1 - U v)) ≤ exp u * exp v * (1 / 4) :=
    mul_le_mul h1 h2.2 h2.1 (by positivity)
  linarith

theorem integrableOn_clockDensity (u : ℝ) : IntegrableOn (clockDensity U) (Iic u) := by
  refine ((integrableOn_exp_Iic u).const_mul (exp u / 8)).mono'
    (continuous_clockDensity hc).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun v hv => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (clockDensity_nonneg h01 v)]
  have := clockDensity_le h01 (U := U) (show v ≤ u from hv)
  linarith

/-- `L^+(u) - L^-(u) = e^u`. -/
theorem upperL_sub_lowerL (u : ℝ) : upperL U u - lowerL U u = exp u := by
  unfold upperL lowerL
  rw [sub_neg_eq_add, ← integral_add (integrableOn_exp_mul hc h01 u)
    (integrableOn_exp_mul_one_sub hc h01 u), ← integral_exp_Iic u]
  congr 1
  funext v
  ring

omit hc in
theorem lowerL_nonpos (u : ℝ) : lowerL U u ≤ 0 := by
  unfold lowerL
  rw [neg_nonpos]
  refine setIntegral_nonneg measurableSet_Iic fun v _ => ?_
  exact mul_nonneg (exp_pos v).le (by linarith [(h01 v).2])

omit hc in
theorem upperL_nonneg (u : ℝ) : 0 ≤ upperL U u :=
  setIntegral_nonneg measurableSet_Iic fun v _ => mul_nonneg (exp_pos v).le (h01 v).1

theorem neg_exp_le_lowerL (u : ℝ) : -exp u ≤ lowerL U u := by
  have := upperL_sub_lowerL hc h01 u
  have := upperL_nonneg h01 u
  linarith

theorem upperL_le_exp (u : ℝ) : upperL U u ≤ exp u := by
  have := upperL_sub_lowerL hc h01 u
  have := lowerL_nonpos h01 u
  linarith

omit hc h01 in
/-- `w(u) - L^-(u) = e^u U_u`. -/
theorem driver_sub_lowerL (u : ℝ) : driver U u - lowerL U u = exp u * U u := by
  unfold driver; ring

/-- `L^+(u) - w(u) = e^u (1 - U_u)`. -/
theorem upperL_sub_driver (u : ℝ) : upperL U u - driver U u = exp u * (1 - U u) := by
  have := upperL_sub_lowerL hc h01 u
  unfold driver
  linear_combination this

omit hc in
theorem lowerL_le_driver (u : ℝ) : lowerL U u ≤ driver U u := by
  have := driver_sub_lowerL (U := U) u
  have := mul_nonneg (exp_pos u).le (h01 u).1
  linarith

theorem driver_le_upperL (u : ℝ) : driver U u ≤ upperL U u := by
  have := upperL_sub_driver hc h01 u
  have := mul_nonneg (exp_pos u).le (show 0 ≤ 1 - U u by linarith [(h01 u).2])
  linarith

theorem abs_lowerL_le (u : ℝ) : |lowerL U u| ≤ exp u :=
  abs_le.2 ⟨neg_exp_le_lowerL hc h01 u, (lowerL_nonpos h01 u).trans (exp_pos u).le⟩

theorem abs_upperL_le (u : ℝ) : |upperL U u| ≤ exp u :=
  abs_le.2 ⟨(neg_nonpos.2 (exp_pos u).le).trans (upperL_nonneg h01 u), upperL_le_exp hc h01 u⟩

theorem abs_driver_le (u : ℝ) : |driver U u| ≤ exp u :=
  abs_le.2 ⟨(neg_exp_le_lowerL hc h01 u).trans (lowerL_le_driver h01 u),
    (driver_le_upperL hc h01 u).trans (upperL_le_exp hc h01 u)⟩

omit hc in
theorem clock_nonneg (u : ℝ) : 0 ≤ clock U u :=
  setIntegral_nonneg measurableSet_Iic fun v _ => clockDensity_nonneg h01 v

theorem clock_le (u : ℝ) : clock U u ≤ exp u * exp u / 8 := by
  unfold clock
  calc ∫ v in Iic u, clockDensity U v ≤ ∫ v in Iic u, exp u / 8 * exp v := by
        refine setIntegral_mono_on (integrableOn_clockDensity hc h01 u)
          ((integrableOn_exp_Iic u).const_mul _) measurableSet_Iic fun v hv => ?_
        have := clockDensity_le h01 (U := U) (show v ≤ u from hv)
        linarith
    _ = exp u * exp u / 8 := by
        rw [integral_const_mul, integral_exp_Iic]; ring

theorem hasDerivAt_clock (u : ℝ) : HasDerivAt (clock U) (clockDensity U u) u :=
  hasDerivAt_integral_Iic (continuous_clockDensity hc) (integrableOn_clockDensity hc h01) u

theorem hasDerivAt_lowerL (u : ℝ) : HasDerivAt (lowerL U) (-(exp u * (1 - U u))) u :=
  (hasDerivAt_integral_Iic (continuous_exp.mul (continuous_const.sub hc))
    (integrableOn_exp_mul_one_sub hc h01) u).neg

theorem hasDerivAt_upperL (u : ℝ) : HasDerivAt (upperL U) (exp u * U u) u :=
  hasDerivAt_integral_Iic (continuous_exp.mul hc) (integrableOn_exp_mul hc h01) u

theorem continuous_clock : Continuous (clock U) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_clock hc h01 u).continuousAt

theorem continuous_lowerL : Continuous (lowerL U) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_lowerL hc h01 u).continuousAt

theorem continuous_upperL : Continuous (upperL U) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_upperL hc h01 u).continuousAt

theorem continuous_driver : Continuous (driver U) :=
  (continuous_lowerL hc h01).add (continuous_exp.mul hc)

/-- `t(b) - t(a) = ∫_a^b ½ e^{2v} U_v (1 - U_v) dv`. -/
theorem clock_sub (a b : ℝ) : clock U b - clock U a = ∫ v in a..b, clockDensity U v :=
  intervalIntegral.integral_Iic_sub_Iic (integrableOn_clockDensity hc h01 a)
    (integrableOn_clockDensity hc h01 b)

theorem monotone_clock : Monotone (clock U) := fun a b hab => by
  have := clock_sub hc h01 a b
  have : 0 ≤ ∫ v in a..b, clockDensity U v :=
    intervalIntegral.integral_nonneg hab fun v _ => clockDensity_nonneg h01 v
  linarith

/-- `t(u) ↓ 0` as `u → -∞`. -/
theorem tendsto_clock_atBot : Tendsto (clock U) atBot (𝓝 0) := by
  have hlim : Tendsto (fun u => exp u * exp u / 8) atBot (𝓝 0) := by
    have := (tendsto_exp_atBot.mul tendsto_exp_atBot).div_const (8 : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (clock_nonneg h01) (clock_le hc h01)

theorem tendsto_lowerL_atBot : Tendsto (lowerL U) atBot (𝓝 0) := by
  refine squeeze_zero_norm (fun u => abs_lowerL_le hc h01 u) ?_
  simpa using tendsto_exp_atBot

theorem tendsto_upperL_atBot : Tendsto (upperL U) atBot (𝓝 0) := by
  refine squeeze_zero_norm (fun u => abs_upperL_le hc h01 u) ?_
  simpa using tendsto_exp_atBot

theorem tendsto_driver_atBot : Tendsto (driver U) atBot (𝓝 0) := by
  refine squeeze_zero_norm (fun u => abs_driver_le hc h01 u) ?_
  simpa using tendsto_exp_atBot

end Basic

section Inverse

variable (hc : Continuous U) (h01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
  (hnull : volume {v | U v = 0 ∨ U v = 1} = 0)
include hc h01

include hnull in
/-- If `{u : U_u ∈ {0, 1}}` is Lebesgue-null, the clock is strictly increasing. -/
theorem strictMono_clock : StrictMono (clock U) := by
  intro a b hab
  have hsub := clock_sub hc h01 a b
  have hpos : 0 < ∫ v in a..b, clockDensity U v := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (clockDensity_nonneg h01)) ((continuous_clockDensity hc).intervalIntegrable _ _)]
    refine ⟨hab, ?_⟩
    have hsub' : Ioc a b \ {v | U v = 0 ∨ U v = 1} ⊆
        Function.support (clockDensity U) ∩ Ioc a b := by
      rintro v ⟨hv, hv'⟩
      refine ⟨?_, hv⟩
      simp only [mem_ofPred_eq, not_or] at hv'
      have h1 : 1 - U v ≠ 0 := sub_ne_zero.2 (Ne.symm hv'.2)
      exact div_ne_zero (mul_ne_zero (exp_pos _).ne' (mul_ne_zero hv'.1 h1)) two_ne_zero
    calc (0 : ENNReal) < volume (Ioc a b \ {v | U v = 0 ∨ U v = 1}) := by
          rw [measure_sdiff_null hnull, Real.volume_Ioc]
          exact ENNReal.ofReal_pos.2 (sub_pos.2 hab)
      _ ≤ _ := measure_mono hsub'
  linarith

include hnull in
theorem clock_pos (u : ℝ) : 0 < clock U u :=
  (clock_nonneg h01 (u - 1)).trans_lt (strictMono_clock hc h01 hnull (by linarith))

theorem exists_clock_lt {t : ℝ} (ht : 0 < t) : ∃ u, clock U u < t :=
  ((tendsto_clock_atBot hc h01).eventually (gt_mem_nhds ht)).exists

variable (htop : Tendsto (clock U) atTop atTop)
include htop

/-- `t(u(t)) = t` for `t > 0`. -/
theorem clock_invClock {t : ℝ} (ht : 0 < t) : clock U (invClock U t) = t := by
  obtain ⟨u0, hu0⟩ := exists_clock_lt hc h01 ht
  obtain ⟨u1, hu1⟩ := (htop.eventually_ge_atTop t).exists
  have hne : {u | t ≤ clock U u}.Nonempty := ⟨u1, hu1⟩
  have hbdd : BddBelow {u | t ≤ clock U u} := by
    refine ⟨u0, fun u hu => le_of_lt (lt_of_not_ge fun h => ?_)⟩
    exact absurd ((show t ≤ clock U u from hu).trans (monotone_clock hc h01 h)) (not_le.2 hu0)
  have hclosed : IsClosed {u | t ≤ clock U u} := isClosed_le continuous_const (continuous_clock hc h01)
  have hmem : t ≤ clock U (invClock U t) := hclosed.csInf_mem hne hbdd
  have hlt : u0 ≤ invClock U t := by
    by_contra h
    exact absurd (hmem.trans (monotone_clock hc h01 (not_le.1 h).le)) (not_le.2 hu0)
  obtain ⟨c, hc', hct⟩ := intermediate_value_Icc hlt (continuous_clock hc h01).continuousOn
    ⟨hu0.le, hmem⟩
  have hle : invClock U t ≤ c := csInf_le hbdd (show t ≤ clock U c from hct.ge)
  rw [← le_antisymm hc'.2 hle]
  exact hct

include hnull in
/-- `u(t(u)) = u`. -/
theorem invClock_clock (u : ℝ) : invClock U (clock U u) = u :=
  (strictMono_clock hc h01 hnull).injective (clock_invClock hc h01 htop (clock_pos hc h01 hnull u))

include hnull in
theorem invClock_le_iff {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : invClock U s ≤ invClock U t ↔ s ≤ t := by
  rw [← (strictMono_clock hc h01 hnull).le_iff_le, clock_invClock hc h01 htop hs,
    clock_invClock hc h01 htop ht]

include hnull in
theorem invClock_lt_iff {u t : ℝ} (ht : 0 < t) : invClock U t < u ↔ t < clock U u := by
  rw [← (strictMono_clock hc h01 hnull).lt_iff_lt, clock_invClock hc h01 htop ht]

include hnull in
theorem lt_invClock_iff {u t : ℝ} (ht : 0 < t) : u < invClock U t ↔ clock U u < t := by
  rw [← (strictMono_clock hc h01 hnull).lt_iff_lt, clock_invClock hc h01 htop ht]

include hnull in
theorem continuousAt_invClock {t : ℝ} (ht : 0 < t) : ContinuousAt (invClock U) t := by
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := Ioi 0)
    (fun x hx y hy hxy => (invClock_le_iff hc h01 hnull htop hx hy).2 hxy) (Ioi_mem_nhds ht) ?_
  have : invClock U '' Ioi 0 = univ :=
    eq_univ_of_forall fun u => ⟨clock U u, clock_pos hc h01 hnull u, invClock_clock hc h01 hnull htop u⟩
  rw [this]
  exact univ_mem

include hnull in
/-- `u(t) → -∞` as `t ↓ 0`. -/
theorem tendsto_invClock_nhdsGT_zero : Tendsto (invClock U) (𝓝[>] 0) atBot := by
  refine tendsto_atBot.2 fun M => ?_
  have hM := clock_pos hc h01 hnull M
  filter_upwards [Ioo_mem_nhdsGT hM] with t ht
  exact ((invClock_lt_iff hc h01 hnull htop ht.1).2 ht.2).le

end Inverse

/-- The physical-clock version of a logarithmic-clock function `f`: `x ↦ f(u(x))` for `x > 0`, and
`0` for `x ≤ 0` (all coordinates of the two-seed construction start at `0`). -/
def phys (U : ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then f (invClock U x) else 0

theorem phys_of_pos {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) : phys U f x = f (invClock U x) := by
  simp [phys, hx]

theorem phys_of_nonpos {f : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) : phys U f x = 0 := by
  simp [phys, not_lt.2 hx]

/-- The physical-clock version of a continuous function with limit `0` at `-∞` is continuous. -/
theorem continuous_phys (hc : Continuous U) (h01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
    (hnull : volume {v | U v = 0 ∨ U v = 1} = 0) (htop : Tendsto (clock U) atTop atTop)
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : Tendsto f atBot (𝓝 0)) : Continuous (phys U f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact (phys_of_nonpos (le_of_lt hy)).symm
  · refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun y hy => phys_of_nonpos hy)
        (phys_of_nonpos le_rfl)
    · rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, phys_of_nonpos le_rfl]
      refine (hf0.comp (tendsto_invClock_nhdsGT_zero hc h01 hnull htop)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (phys_of_pos hy).symm
  · refine ((hf.continuousAt).comp (continuousAt_invClock hc h01 hnull htop hx)).congr ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (phys_of_pos hy).symm

end TwoSeed

end Sec2

end InteractingSLE
