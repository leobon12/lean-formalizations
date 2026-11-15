/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiSDE
import InteractingSLE.Spec.Sec2.TwoSeedLawPath
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Two seeds: the driving martingale on the logarithmic clock

Packet PROVE-SEC2-JAC3. Let `U` be a Jacobi diffusion (`Jacobi.IsJacobiDiffusion κ a b P 𝓗 U`,
`a = ρ_L + 2`, `b = ρ_R + 2`) on the logarithmic clock. The clock construction of
`TwoSeedClock.lean` gives `w(u) = L^-(u) + e^u U_u`, and the driving Brownian motion of the
two-seed evolution is `B_t = N(u(t))/√κ` with (Specification L530–L534)

  `N(u) = w(u) + ½ ρ_L L^-(u) + ½ ρ_R L^+(u)`  (`nProc`).

Here (without stochastic integrals):

* `nProc_sub`: pathwise, `N(v) - N(w) = e^v U_v - e^w U_w - ∫_w^v e^x (U_x + L(x¹)(U_x)) dx`, i.e.
  `N` is the martingale part of `e^u U_u` (`dN = e^u dM`);
* `setIntegral_nProc_eq`: `N` is an `𝓗`-martingale;
* `setIntegral_qProc_eq`: `N² - κ t(u)` is an `𝓗`-martingale (`t` the clock), from the quadratic
  compensator `HasCompensator.sq_sub` with `L(x²) - 2x L(x) = (κ/2) x (1 - x)`;
* `setIntegral_comp_eq_of_isStopping`: optional sampling at two bounded `𝓗`-stopping times, for
  continuous locally bounded martingales on the clock `ℝ` (by shifting the landed `ℝ≥0` theorem
  `setIntegral_stoppedValue_eq_of_rightContinuous`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

open Jacobi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Locality of the clock functionals -/

theorem lowerL_congr {f g : ℝ → ℝ} {u : ℝ} (h : ∀ v ≤ u, f v = g v) : lowerL f u = lowerL g u := by
  unfold lowerL
  rw [setIntegral_congr_fun measurableSet_Iic fun v hv => by rw [h v hv]]

theorem upperL_congr {f g : ℝ → ℝ} {u : ℝ} (h : ∀ v ≤ u, f v = g v) : upperL f u = upperL g u := by
  unfold upperL
  rw [setIntegral_congr_fun measurableSet_Iic fun v hv => by rw [h v hv]]

theorem clock_congr {f g : ℝ → ℝ} {u : ℝ} (h : ∀ v ≤ u, f v = g v) : clock f u = clock g u := by
  unfold clock clockDensity
  rw [setIntegral_congr_fun measurableSet_Iic fun v hv => by rw [h v hv]]

theorem driver_congr {f g : ℝ → ℝ} {u : ℝ} (h : ∀ v ≤ u, f v = g v) : driver f u = driver g u := by
  unfold driver
  rw [lowerL_congr h, h u le_rfl]

/-- A path functional that only sees the path up to time `u` is `𝓗_u`-measurable along an
adapted `[0, 1]`-valued continuous process. -/
theorem measurable_pathFun {𝓗 : Filtration ℝ mΩ} {U : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun u => U u ω) (hU : ∀ u, Measurable[𝓗 u] (U u))
    (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) {F : (ℝ → ℝ) → ℝ}
    (hF : Measurable fun f : CPathR => F (clampU f)) (u : ℝ)
    (hloc : ∀ f g : ℝ → ℝ, (∀ v ≤ u, f v = g v) → F f = F g) :
    Measurable[𝓗 u] fun ω => F (U · ω) := by
  have hcs : ∀ ω, Continuous fun v => U (min v u) ω := fun ω =>
    (hc ω).comp (continuous_id.min continuous_const)
  have hm : Measurable[𝓗 u] (toCPathR (fun v ω => U (min v u) ω) hcs) :=
    @measurable_toCPathR Ω (𝓗 u) _ (fun v => (hU (min v u)).mono (𝓗.mono (min_le_right _ _))
      le_rfl) hcs
  have e : (fun ω => F (U · ω)) = (fun f : CPathR => F (clampU f)) ∘
      toCPathR (fun v ω => U (min v u) ω) hcs := by
    funext ω
    simp only [Function.comp_apply]
    rw [clampU_eq fun v => h01 _ ω]
    exact hloc _ _ fun v hv => by simp [toCPathR, min_eq_left hv]
  rw [e]
  exact hF.comp hm

/-! ### The driving process on the logarithmic clock -/

/-- `N(u) = w(u) + ½ ρ_L L^-(u) + ½ ρ_R L^+(u)` along the path `U · ω`. -/
def nProc (ρL ρR : ℝ) (U : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  driver (U · ω) u + ρL / 2 * lowerL (U · ω) u + ρR / 2 * upperL (U · ω) u

/-- `Q(u) = N(u)² - κ t(u)`. -/
def qProc (κ ρL ρR : ℝ) (U : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  nProc ρL ρR U u ω ^ 2 - κ * clock (U · ω) u

/-- The pathwise identity `N(v) - N(w) = e^v f_v - e^w f_w - ∫_w^v e^x (f_x + L(x¹)(f_x)) dx`. -/
theorem nProc_sub_path {f : ℝ → ℝ} (hc : Continuous f) (h01 : ∀ v, f v ∈ Icc (0 : ℝ) 1)
    (κ ρL ρR w v : ℝ) :
    (driver f v + ρL / 2 * lowerL f v + ρR / 2 * upperL f v) -
      (driver f w + ρL / 2 * lowerL f w + ρR / 2 * upperL f w) =
      exp v * f v ^ 1 - exp w * f w ^ 1 - ∫ x in w..v, (exp x * f x ^ 1 +
        exp x * gen κ (ρL + 2) (ρR + 2) (fun y => y ^ 1) (f x)) := by
  have hl := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := w) (b := v)
    (fun x _ => hasDerivAt_lowerL hc h01 x)
    ((continuous_exp.mul (continuous_const.sub hc)).neg.intervalIntegrable _ _)
  have hu := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := w) (b := v)
    (fun x _ => hasDerivAt_upperL hc h01 x) ((continuous_exp.mul hc).intervalIntegrable _ _)
  have e : (fun x => exp x * f x ^ 1 + exp x * gen κ (ρL + 2) (ρR + 2) (fun y => y ^ 1) (f x)) =
      fun x => (1 + ρL / 2) * (exp x * (1 - f x)) + (-(ρR / 2)) * (exp x * f x) := by
    funext x
    rw [gen_pow]
    simp only [dcoef, ccoef, Nat.cast_one, sub_self, mul_zero, zero_add, pow_one]
    ring
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_neg] at *
  · have hl' : ∫ x in w..v, exp x * (1 - f x) = lowerL f w - lowerL f v := by linarith
    rw [hl', hu]
    unfold driver
    ring
  · exact ((continuous_const.mul (continuous_exp.mul (continuous_const.sub hc)))).intervalIntegrable
      _ _
  · exact ((continuous_const.mul (continuous_exp.mul hc))).intervalIntegrable _ _

section Diffusion

variable {κ ρL ρR : ℝ} {P : Measure Ω} {𝓗 : Filtration ℝ mΩ} {U : ℝ → Ω → ℝ}

theorem abs_nProc_le (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (u : ℝ) (ω : Ω) : |nProc ρL ρR U u ω| ≤ (1 + |ρL| / 2 + |ρR| / 2) * exp u := by
  have h1 := abs_driver_le (hc ω) (fun v => h01 v ω) u
  have h2 := abs_lowerL_le (hc ω) (fun v => h01 v ω) u
  have h3 := abs_upperL_le (hc ω) (fun v => h01 v ω) u
  unfold nProc
  calc |driver (U · ω) u + ρL / 2 * lowerL (U · ω) u + ρR / 2 * upperL (U · ω) u|
      ≤ |driver (U · ω) u| + |ρL| / 2 * |lowerL (U · ω) u| + |ρR| / 2 * |upperL (U · ω) u| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
          ?_) <;> rw [abs_mul, abs_div, abs_two]
    _ ≤ exp u + |ρL| / 2 * exp u + |ρR| / 2 * exp u := by gcongr
    _ = _ := by ring

theorem continuous_nProc (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (ω : Ω) : Continuous fun u => nProc ρL ρR U u ω :=
  ((continuous_driver (hc ω) (fun v => h01 v ω)).add
    (continuous_const.mul (continuous_lowerL (hc ω) (fun v => h01 v ω)))).add
    (continuous_const.mul (continuous_upperL (hc ω) (fun v => h01 v ω)))

theorem adapted_nProc (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (hU : ∀ u, Measurable[𝓗 u] (U u)) (u : ℝ) : Measurable[𝓗 u] (nProc ρL ρR U u) := by
  refine measurable_pathFun (F := fun f => driver f u + ρL / 2 * lowerL f u + ρR / 2 * upperL f u)
    hc hU h01 ?_ u fun f g h => by rw [driver_congr h, lowerL_congr h, upperL_congr h]
  exact ((measurable_driver u).add (measurable_const.mul (measurable_lowerL u))).add
    (measurable_const.mul (measurable_upperL u))

theorem adapted_clock (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (hU : ∀ u, Measurable[𝓗 u] (U u)) (u : ℝ) : Measurable[𝓗 u] fun ω => clock (U · ω) u :=
  measurable_pathFun (F := fun f => clock f u) hc hU h01 (measurable_clock u) u
    fun _ _ h => clock_congr h

theorem adapted_qProc (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (hU : ∀ u, Measurable[𝓗 u] (U u)) (u : ℝ) : Measurable[𝓗 u] (qProc κ ρL ρR U u) :=
  ((adapted_nProc h01 hc hU u).pow_const 2).sub
    (measurable_const.mul (adapted_clock h01 hc hU u))

theorem isRegProc_nProc (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (hU : ∀ u, Measurable[𝓗 u] (U u)) : IsRegProc (nProc ρL ρR U) := by
  refine ⟨continuous_nProc h01 hc, fun u => (adapted_nProc h01 hc hU u).mono (𝓗.le u) le_rfl,
    fun T => ⟨(1 + |ρL| / 2 + |ρR| / 2) * exp T, fun u ω hu => ?_⟩⟩
  refine (abs_nProc_le h01 hc u ω).trans ?_
  gcongr
  exact (le_abs_self u).trans hu

theorem isRegProc_clock (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (hU : ∀ u, Measurable[𝓗 u] (U u)) : IsRegProc fun u ω => clock (U · ω) u := by
  refine ⟨fun ω => continuous_clock (hc ω) (fun v => h01 v ω),
    fun u => (adapted_clock h01 hc hU u).mono (𝓗.le u) le_rfl,
    fun T => ⟨exp T * exp T / 8, fun u ω hu => ?_⟩⟩
  rw [abs_of_nonneg (clock_nonneg (fun v => h01 v ω) u)]
  refine (clock_le (hc ω) (fun v => h01 v ω) u).trans ?_
  have : exp u ≤ exp T := exp_le_exp.2 ((le_abs_self u).trans hu)
  gcongr

theorem isRegProc_qProc (h01 : ∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) (hc : ∀ ω, Continuous fun u => U u ω)
    (hU : ∀ u, Measurable[𝓗 u] (U u)) : IsRegProc (qProc κ ρL ρR U) := by
  have h := ((isRegProc_nProc (ρL := ρL) (ρR := ρR) h01 hc hU).mul
    (isRegProc_nProc (ρL := ρL) (ρR := ρR) h01 hc hU)).sub ((isRegProc_clock h01 hc hU).const_mul
      (g := fun _ => κ) continuous_const)
  refine ⟨fun ω => ?_, fun u => ?_, fun T => ?_⟩
  · simpa only [qProc, pow_two] using h.continuous ω
  · have e : qProc κ ρL ρR U u = fun ω =>
        nProc ρL ρR U u ω * nProc ρL ρR U u ω - κ * clock (fun x => U x ω) u := by
      funext ω; simp only [qProc, pow_two]
    rw [e]; exact h.measurable u
  · simpa only [qProc, pow_two] using h.exists_bound T

end Diffusion

/-! ### `N` and `N² - κ t` are martingales -/

theorem _root_.InteractingSLE.Sec2.Jacobi.HasCompensator.congr_left {P : Measure Ω}
    {𝓗 : Filtration ℝ mΩ} {X X' α : ℝ → Ω → ℝ} (h : HasCompensator P 𝓗 X α)
    (hX : ∀ u ω, X u ω = X' u ω) : HasCompensator P 𝓗 X' α := by
  have : X = X' := funext fun u => funext fun ω => hX u ω
  exact this ▸ h

theorem hasDerivAt_exp_two_mul (x : ℝ) :
    HasDerivAt (fun x => exp (2 * x)) (exp (2 * x) * 2) x := by
  have := ((hasDerivAt_id x).const_mul 2).exp
  simpa using this

theorem integral_indicator_mul_eq {P : Measure Ω} {A : Set Ω} (hA : MeasurableSet A) (f : Ω → ℝ) :
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * f ω ∂P = ∫ ω in A, f ω ∂P := by
  rw [← integral_indicator hA]
  congr 1; funext ω
  by_cases h : ω ∈ A <;> simp [h]

section Mart

variable {κ ρL ρR : ℝ} {P : Measure Ω} [IsFiniteMeasure P] {𝓗 : Filtration ℝ mΩ}
  {U : ℝ → Ω → ℝ}

theorem integral_mul_nProc_sub (hU : IsJacobiDiffusion κ (ρL + 2) (ρR + 2) P 𝓗 U) {w x : ℝ}
    (hwx : w ≤ x) {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓗 w] Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (nProc ρL ρR U x ω - nProc ρL ρR U w ω) ∂P = 0 := by
  have h := (hU.hasCompensator_pow 1).mul_left (hU.isRegProc_comp (continuous_pow 1))
    (hU.isRegProc_comp (continuous_gen_pow κ _ _ 1)) (fun x => hasDerivAt_exp x) continuous_exp
  have := h w x hwx Z hZ ⟨C, hZC⟩
  rw [← this]
  congr 1; funext ω; congr 1
  exact nProc_sub_path (hU.continuous ω) (fun v => hU.mem_Icc v ω) κ ρL ρR w x

theorem integral_mul_nProc_sq_sub (hU : IsJacobiDiffusion κ (ρL + 2) (ρR + 2) P 𝓗 U) {w x : ℝ}
    (hwx : w ≤ x) {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓗 w] Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * ((nProc ρL ρR U x ω - nProc ρL ρR U w ω) ^ 2 -
      κ * (clock (U · ω) x - clock (U · ω) w)) ∂P = 0 := by
  set a := ρL + 2
  set b := ρR + 2
  have hX1 := hU.isRegProc_comp (continuous_pow 1)
  have hX2 := hU.isRegProc_comp (continuous_pow 2)
  have hg1 := hU.isRegProc_comp (continuous_gen_pow κ a b 1)
  have hg2 := hU.isRegProc_comp (continuous_gen_pow κ a b 2)
  have h1 := (hU.hasCompensator_pow 1).mul_left hX1 hg1 (fun x => hasDerivAt_exp x) continuous_exp
  have h2 := (hU.hasCompensator_pow 2).mul_left hX2 hg2 hasDerivAt_exp_two_mul
    (continuous_exp.comp (continuous_const.mul continuous_id) |>.mul continuous_const)
  have h2' := h2.congr_left (X' := fun u ω => (exp u * U u ω ^ 1) ^ 2) fun u ω => by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring
  have hXr : IsRegProc fun u ω => exp u * U u ω ^ 1 := hX1.const_mul continuous_exp
  have hαr : IsRegProc fun u ω => exp u * U u ω ^ 1 + exp u * gen κ a b (fun y => y ^ 1) (U u ω) :=
    (hX1.const_mul continuous_exp).add (hg1.const_mul continuous_exp)
  have hγr : IsRegProc fun u ω => exp (2 * u) * 2 * U u ω ^ 2 +
      exp (2 * u) * gen κ a b (fun y => y ^ 2) (U u ω) :=
    (hX2.const_mul (continuous_exp.comp (continuous_const.mul continuous_id) |>.mul
      continuous_const)).add (hg2.const_mul (continuous_exp.comp (continuous_const.mul continuous_id)))
  have hXa : ∀ u, StronglyMeasurable[𝓗 u] fun ω => exp u * U u ω ^ 1 := fun u =>
    (measurable_const.mul ((hU.adapted u).pow_const 1)).stronglyMeasurable
  have hαa : ∀ u, StronglyMeasurable[𝓗 u] fun ω =>
      exp u * U u ω ^ 1 + exp u * gen κ a b (fun y => y ^ 1) (U u ω) := fun u =>
    ((measurable_const.mul ((hU.adapted u).pow_const 1)).add (measurable_const.mul
      ((continuous_gen_pow κ a b 1).measurable.comp (hU.adapted u)))).stronglyMeasurable
  have := h1.sq_sub h2' hXr hαr hγr hXa hαa hwx hZ hZC
  rw [← this]
  congr 1; funext ω; congr 1
  have hp := nProc_sub_path (hU.continuous ω) (fun v => hU.mem_Icc v ω) κ ρL ρR w x
  simp only [nProc] at hp ⊢
  rw [hp]
  congr 1
  rw [clock_sub (hU.continuous ω) (fun v => hU.mem_Icc v ω), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [gen_pow, dcoef, ccoef, clockDensity]
  rw [show exp (2 * s) = exp s * exp s by rw [← exp_add]; ring_nf]
  push_cast
  ring

/-- **`N` is an `𝓗`-martingale on the logarithmic clock.** -/
theorem setIntegral_nProc_eq (hU : IsJacobiDiffusion κ (ρL + 2) (ρR + 2) P 𝓗 U) {w x : ℝ}
    (hwx : w ≤ x) {A : Set Ω} (hA : MeasurableSet[𝓗 w] A) :
    ∫ ω in A, nProc ρL ρR U x ω ∂P = ∫ ω in A, nProc ρL ρR U w ω ∂P := by
  have hreg := isRegProc_nProc (ρL := ρL) (ρR := ρR) hU.mem_Icc hU.continuous hU.adapted
  have hAm : MeasurableSet A := 𝓗.le w A hA
  have h := integral_mul_nProc_sub hU hwx (Z := A.indicator fun _ => (1 : ℝ))
    (stronglyMeasurable_const.indicator hA) (C := 1) fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
  rw [integral_indicator_mul_eq hAm, integral_sub (hreg.integrable_mul (P := P) (Z := fun _ => 1)
    measurable_const (C := 1) (fun _ => by simp) x |>.congr (ae_of_all _ fun _ => one_mul _)
    |>.integrableOn) (hreg.integrable_mul (P := P) (Z := fun _ => 1) measurable_const (C := 1)
    (fun _ => by simp) w |>.congr (ae_of_all _ fun _ => one_mul _) |>.integrableOn),
    sub_eq_zero] at h
  exact h

/-- **`N² - κ t` is an `𝓗`-martingale on the logarithmic clock.** -/
theorem setIntegral_qProc_eq (hU : IsJacobiDiffusion κ (ρL + 2) (ρR + 2) P 𝓗 U) {w x : ℝ}
    (hwx : w ≤ x) {A : Set Ω} (hA : MeasurableSet[𝓗 w] A) :
    ∫ ω in A, qProc κ ρL ρR U x ω ∂P = ∫ ω in A, qProc κ ρL ρR U w ω ∂P := by
  have hreg := isRegProc_qProc (κ := κ) (ρL := ρL) (ρR := ρR) hU.mem_Icc hU.continuous hU.adapted
  have hN := isRegProc_nProc (ρL := ρL) (ρR := ρR) hU.mem_Icc hU.continuous hU.adapted
  have hAm : MeasurableSet A := 𝓗.le w A hA
  set Z : Ω → ℝ := A.indicator fun _ => (1 : ℝ) with hZ_def
  have hZ : StronglyMeasurable[𝓗 w] Z := stronglyMeasurable_const.indicator hA
  have hZC : ∀ ω, |Z ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A <;> simp [hZ_def, h]
  obtain ⟨D, hD⟩ := hN.exists_bound |w|
  have h1 := integral_mul_nProc_sq_sub hU hwx hZ hZC
  have h2 := integral_mul_nProc_sub hU hwx (Z := fun ω => Z ω * nProc ρL ρR U w ω)
    (hZ.mul (adapted_nProc hU.mem_Icc hU.continuous hU.adapted w).stronglyMeasurable) (C := 1 * D)
    fun ω => by rw [abs_mul]; exact mul_le_mul (hZC ω) (hD w ω le_rfl) (abs_nonneg _) zero_le_one
  have hZm : Measurable Z := hZ.measurable.mono (𝓗.le w) le_rfl
  have hZN : Measurable fun ω => Z ω * nProc ρL ρR U w ω := hZm.mul (hN.measurable w)
  have hZNC : ∀ ω, |Z ω * nProc ρL ρR U w ω| ≤ 1 * D := fun ω => by
    rw [abs_mul]; exact mul_le_mul (hZC ω) (hD w ω le_rfl) (abs_nonneg _) zero_le_one
  have i2 : Integrable (fun ω => (Z ω * nProc ρL ρR U w ω) *
      (nProc ρL ρR U x ω - nProc ρL ρR U w ω)) P :=
    ((hN.integrable_mul hZN hZNC x).sub (hN.integrable_mul hZN hZNC w)).congr
      (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  have iQ : Integrable (fun ω => Z ω * (qProc κ ρL ρR U x ω - qProc κ ρL ρR U w ω)) P :=
    ((hreg.integrable_mul hZm hZC x).sub (hreg.integrable_mul hZm hZC w)).congr
      (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
  have i1 : Integrable (fun ω => Z ω * ((nProc ρL ρR U x ω - nProc ρL ρR U w ω) ^ 2 -
      κ * (clock (U · ω) x - clock (U · ω) w))) P :=
    (iQ.sub (i2.const_mul 2)).congr (ae_of_all _ fun ω => by
      simp only [Pi.sub_apply, qProc]; ring)
  have hsum : ∫ ω, Z ω * (qProc κ ρL ρR U x ω - qProc κ ρL ρR U w ω) ∂P = 0 := by
    have e : (fun ω => Z ω * (qProc κ ρL ρR U x ω - qProc κ ρL ρR U w ω)) = fun ω =>
        Z ω * ((nProc ρL ρR U x ω - nProc ρL ρR U w ω) ^ 2 -
          κ * (clock (U · ω) x - clock (U · ω) w)) +
        2 * ((Z ω * nProc ρL ρR U w ω) * (nProc ρL ρR U x ω - nProc ρL ρR U w ω)) := by
      funext ω; simp only [qProc]; ring
    rw [e, integral_add i1 (i2.const_mul 2), integral_const_mul, h1, h2]
    simp
  have iQx := (hreg.integrable_mul (P := P) (Z := fun _ => 1) measurable_const (C := 1)
    (fun _ => by simp) x).congr (ae_of_all _ fun _ => one_mul _)
  have iQw := (hreg.integrable_mul (P := P) (Z := fun _ => 1) measurable_const (C := 1)
    (fun _ => by simp) w).congr (ae_of_all _ fun _ => one_mul _)
  have e2 : ∫ ω, Z ω * (qProc κ ρL ρR U x ω - qProc κ ρL ρR U w ω) ∂P =
      ∫ ω in A, qProc κ ρL ρR U x ω ∂P - ∫ ω in A, qProc κ ρL ρR U w ω ∂P := by
    rw [hZ_def, integral_indicator_mul_eq hAm, integral_sub iQx.integrableOn iQw.integrableOn]
  rw [e2, sub_eq_zero] at hsum
  exact hsum

end Mart

/-! ### Optional sampling on the logarithmic clock -/

/-- The filtration `r ↦ 𝓗 (r - K)` on `ℝ≥0`. -/
def shiftFiltration (𝓗 : Filtration ℝ mΩ) (K : ℝ) : Filtration ℝ≥0 mΩ where
  seq r := 𝓗 ((r : ℝ) - K)
  mono' _ _ hrs := 𝓗.mono (sub_le_sub_right (NNReal.coe_le_coe.2 hrs) K)
  le' _ := 𝓗.le _

theorem shiftFiltration_apply (𝓗 : Filtration ℝ mΩ) (K : ℝ) (r : ℝ≥0) :
    shiftFiltration 𝓗 K r = 𝓗 ((r : ℝ) - K) := rfl

section Sampling

variable {P : Measure Ω} [IsFiniteMeasure P] {𝓗 : Filtration ℝ mΩ}

/-- **Optional sampling on the clock `ℝ`** at two bounded stopping times `-K ≤ σ ≤ τ ≤ M`, for a
continuous locally bounded martingale `Y` (in set-integral form), over a set `A` of the
stopping σ-algebra of `σ`. -/
theorem setIntegral_comp_eq_of_isStopping {Y : ℝ → Ω → ℝ} (hY : IsRegProc Y)
    (hYa : ∀ u, Measurable[𝓗 u] (Y u))
    (hmart : ∀ w x, w ≤ x → ∀ A, MeasurableSet[𝓗 w] A →
      ∫ ω in A, Y x ω ∂P = ∫ ω in A, Y w ω ∂P)
    {σ τ : Ω → ℝ} (hσ : ∀ u, MeasurableSet[𝓗 u] {ω | σ ω ≤ u})
    (hτ : ∀ u, MeasurableSet[𝓗 u] {ω | τ ω ≤ u}) (hστ : ∀ ω, σ ω ≤ τ ω) {K M : ℝ}
    (hσK : ∀ ω, -K ≤ σ ω) (hτM : ∀ ω, τ ω ≤ M) {A : Set Ω}
    (hA : ∀ u, MeasurableSet[𝓗 u] (A ∩ {ω | σ ω ≤ u})) :
    ∫ ω in A, Y (σ ω) ω ∂P = ∫ ω in A, Y (τ ω) ω ∂P := by
  set 𝓕 := shiftFiltration 𝓗 K with h𝓕
  set Yr : ℝ≥0 → Ω → ℝ := fun r ω => Y ((r : ℝ) - K) ω with hYr
  have hint : ∀ r : ℝ≥0, Integrable (Yr r) P := fun r =>
    (hY.integrable_mul (P := P) (Z := fun _ => 1) measurable_const (C := 1) (fun _ => by simp)
      _).congr (ae_of_all _ fun _ => one_mul _)
  have hmartr : Martingale Yr 𝓕 P := by
    refine ⟨fun r => (hYa _).stronglyMeasurable, fun s t hst => ?_⟩
    refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hint t)
      (fun B _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
      ((hYa _).stronglyMeasurable.aestronglyMeasurable)).symm
    exact (hmart _ _ (sub_le_sub_right (NNReal.coe_le_coe.2 hst) K) B hB).symm
  have hrc : ∀ ω t, ContinuousWithinAt (Yr · ω) (Ici t) t := fun ω t =>
    ((hY.continuous ω).comp (NNReal.continuous_coe.sub continuous_const)).continuousWithinAt
  have hset : ∀ (ρ : Ω → ℝ) (r : ℝ≥0), {ω | ((ρ ω + K).toNNReal : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}
      = {ω | ρ ω ≤ (r : ℝ) - K} := by
    intro ρ r; ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
    constructor <;> intro h <;> linarith
  set σr : Ω → WithTop ℝ≥0 := fun ω => ((σ ω + K).toNNReal : WithTop ℝ≥0) with hσr_def
  set τr : Ω → WithTop ℝ≥0 := fun ω => ((τ ω + K).toNNReal : WithTop ℝ≥0) with hτr_def
  have hσr : IsStoppingTime 𝓕 σr := fun r => by
    show MeasurableSet[𝓗 _] _
    rw [hset]; exact hσ _
  have hτr : IsStoppingTime 𝓕 τr := fun r => by
    show MeasurableSet[𝓗 _] _
    rw [hset]; exact hτ _
  have hle : σr ≤ τr := fun ω =>
    WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal (by linarith [hστ ω]))
  have hτT : ∀ ω, τr ω ≤ ((M + K).toNNReal : WithTop ℝ≥0) := fun ω =>
    WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal (by linarith [hτM ω]))
  have hAr : MeasurableSet[hσr.measurableSpace] A := by
    refine ⟨?_, fun r => ?_⟩
    · have hAM : A = A ∩ {ω | σ ω ≤ ((M + K).toNNReal : ℝ) - K} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, iff_self_and]
        intro _
        have := Real.le_coe_toNNReal (M + K)
        linarith [hστ ω, hτM ω]
      rw [hAM]
      exact (le_iSup (fun r => 𝓕 r) (M + K).toNNReal) _ (hA _)
    · show MeasurableSet[𝓗 _] _
      rw [hset]; exact hA _
  have h := setIntegral_stoppedValue_eq_of_rightContinuous hmartr hrc hσr hτr hle hτT hAr
  have hv : ∀ ρ : Ω → ℝ, (∀ ω, -K ≤ ρ ω) →
      stoppedValue Yr (fun ω => ((ρ ω + K).toNNReal : WithTop ℝ≥0)) = fun ω => Y (ρ ω) ω := by
    intro ρ hρ; funext ω
    simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe, hYr,
      Real.coe_toNNReal _ (show 0 ≤ ρ ω + K by linarith [hρ ω]), add_sub_cancel_right]
  rw [hσr_def, hτr_def, hv σ hσK, hv τ fun ω => (hσK ω).trans (hστ ω)] at h
  exact h

theorem measurable_of_isStopping {σ : Ω → ℝ} (hσ : ∀ u, MeasurableSet[𝓗 u] {ω | σ ω ≤ u}) :
    Measurable σ :=
  measurable_of_Iic fun u => 𝓗.le u _ (hσ u)

theorem isStopping_clamp {σ : Ω → ℝ} (hσ : ∀ u, MeasurableSet[𝓗 u] {ω | σ ω ≤ u}) (K m : ℝ) :
    ∀ u, MeasurableSet[𝓗 u] {ω | max (-K) (min (σ ω) m) ≤ u} := by
  intro u
  have e : {ω | max (-K) (min (σ ω) m) ≤ u} = {_ω | -K ≤ u} ∩ ({ω | σ ω ≤ u} ∪ {_ω | m ≤ u}) := by
    ext ω; simp [min_le_iff]
  rw [e]
  exact (MeasurableSet.const _).inter ((hσ u).union (MeasurableSet.const _))

theorem measurable_comp_min {Y : ℝ → Ω → ℝ} (hY : IsRegProc Y) {σ : Ω → ℝ} (hσ : Measurable σ)
    (m : ℝ) : Measurable fun ω => Y (min (σ ω) m) ω :=
  hY.measurable_uncurry.comp ((hσ.min measurable_const).prodMk measurable_id)

/-- **Optional sampling at `σ ∧ m ≤ τ ∧ m`** for a continuous martingale on the clock `ℝ` that is
bounded on `(-∞, m]` (the stopping times may be unbounded below). -/
theorem setIntegral_min_eq {Y : ℝ → Ω → ℝ} (hY : IsRegProc Y)
    (hYa : ∀ u, Measurable[𝓗 u] (Y u))
    (hmart : ∀ w x, w ≤ x → ∀ A, MeasurableSet[𝓗 w] A →
      ∫ ω in A, Y x ω ∂P = ∫ ω in A, Y w ω ∂P)
    {σ τ : Ω → ℝ} (hσ : ∀ u, MeasurableSet[𝓗 u] {ω | σ ω ≤ u})
    (hτ : ∀ u, MeasurableSet[𝓗 u] {ω | τ ω ≤ u}) (hστ : ∀ ω, σ ω ≤ τ ω) (m : ℝ) {C : ℝ}
    (hYb : ∀ u ω, u ≤ m → |Y u ω| ≤ C) {A : Set Ω} (hAm : MeasurableSet A)
    (hA : ∀ u, MeasurableSet[𝓗 u] (A ∩ {ω | σ ω ≤ u})) :
    ∫ ω in A, Y (min (τ ω) m) ω ∂P = ∫ ω in A, Y (min (σ ω) m) ω ∂P := by
  have hσm := measurable_of_isStopping hσ
  have hτm := measurable_of_isStopping hτ
  have hint : ∀ ρ : Ω → ℝ, Measurable ρ → Integrable (fun ω => Y (min (ρ ω) m) ω) P := fun ρ hρ =>
    Integrable.of_bound (measurable_comp_min hY hρ m).aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hYb _ ω (min_le_right _ _))
  -- the part where `σ ≥ m`
  set A₁ := A ∩ {ω | m ≤ σ ω} with hA₁
  set A₂ := A ∩ {ω | σ ω < m} with hA₂
  have hA₁m : MeasurableSet A₁ := hAm.inter (measurableSet_le measurable_const hσm)
  have hA₂m : MeasurableSet A₂ := hAm.inter (measurableSet_lt hσm measurable_const)
  have hsplit : A = A₁ ∪ A₂ := by
    ext ω; simp only [hA₁, hA₂, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h; rcases le_or_gt m (σ ω) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint A₁ A₂ := by
    rw [Set.disjoint_left]; intro ω h1 h2
    exact absurd (show σ ω < m from h2.2) (not_lt.2 (show m ≤ σ ω from h1.2))
  have e1 : ∫ ω in A₁, Y (min (τ ω) m) ω ∂P = ∫ ω in A₁, Y (min (σ ω) m) ω ∂P := by
    refine setIntegral_congr_fun hA₁m fun ω hω => ?_
    have h1 : m ≤ σ ω := hω.2
    simp only [min_eq_right h1, min_eq_right (h1.trans (hστ ω))]
  -- the part where `σ < m`, exhausted by `-K < σ`
  set AK : ℕ → Set Ω := fun K => A₂ ∩ {ω | -(K : ℝ) < σ ω} with hAK
  have hAKm : ∀ K, MeasurableSet (AK K) := fun K =>
    hA₂m.inter (measurableSet_lt measurable_const hσm)
  have hmono : Monotone AK := fun K L h ω hω =>
    ⟨hω.1, lt_of_le_of_lt (neg_le_neg (Nat.cast_le.2 h)) (show -(K : ℝ) < σ ω from hω.2)⟩
  have hU : ⋃ K, AK K = A₂ := by
    ext ω; simp only [mem_iUnion, hAK, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨K, h, _⟩; exact h
    · intro h
      obtain ⟨K, hK⟩ := exists_nat_gt (-σ ω)
      exact ⟨K, h, by linarith⟩
  have eK : ∀ K : ℕ, ∫ ω in AK K, Y (min (τ ω) m) ω ∂P = ∫ ω in AK K, Y (min (σ ω) m) ω ∂P := by
    intro K
    have hos := setIntegral_comp_eq_of_isStopping (P := P) hY hYa hmart (isStopping_clamp hσ K m)
      (isStopping_clamp hτ K m)
      (fun ω => max_le_max le_rfl (min_le_min (hστ ω) le_rfl)) (K := K) (M := max (-K) m)
      (fun ω => le_max_left _ _) (fun ω => max_le_max le_rfl (min_le_right _ _)) (A := AK K)
      (fun u => ?_)
    · have hσeq : ∫ ω in AK K, Y (max (-(K : ℝ)) (min (σ ω) m)) ω ∂P =
          ∫ ω in AK K, Y (min (σ ω) m) ω ∂P := setIntegral_congr_fun (hAKm K) fun ω hω => by
        have h1 : -(K : ℝ) < σ ω := hω.2
        have h2 : σ ω < m := hω.1.2
        rw [min_eq_left h2.le, max_eq_right h1.le]
      have hτeq : ∫ ω in AK K, Y (max (-(K : ℝ)) (min (τ ω) m)) ω ∂P =
          ∫ ω in AK K, Y (min (τ ω) m) ω ∂P := setIntegral_congr_fun (hAKm K) fun ω hω => by
        have h1 : -(K : ℝ) < σ ω := hω.2
        have h2 : σ ω < m := hω.1.2
        rw [max_eq_right (le_of_lt (lt_of_lt_of_le h1 (le_min (hστ ω) h2.le)))]
      rw [hσeq, hτeq] at hos
      exact hos.symm
    · -- `AK K` is in the stopping σ-algebra of the clamped `σ`
      have e : AK K ∩ {ω | max (-(K : ℝ)) (min (σ ω) m) ≤ u} =
          (A ∩ {ω | σ ω ≤ u}) ∩ ({ω | σ ω < m} ∩ {ω | -(K : ℝ) < σ ω}) := by
        ext ω
        simp only [hAK, hA₂, mem_inter_iff, mem_ofPred_eq, max_le_iff, min_le_iff]
        constructor
        · rintro ⟨⟨⟨hA, hm⟩, hK⟩, _, h | h⟩
          · exact ⟨⟨hA, h⟩, hm, hK⟩
          · exact ⟨⟨hA, by linarith⟩, hm, hK⟩
        · rintro ⟨⟨hA, hu⟩, hm, hK⟩
          exact ⟨⟨⟨hA, hm⟩, hK⟩, by linarith, Or.inl hu⟩
      rw [e]
      rcases lt_or_ge u (-(K : ℝ)) with hu | hu
      · have : (A ∩ {ω | σ ω ≤ u}) ∩ ({ω | σ ω < m} ∩ {ω | -(K : ℝ) < σ ω}) = ∅ := by
          ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          rintro ⟨⟨_, h1⟩, _, h2⟩; linarith
        rw [this]; exact @MeasurableSet.empty _ (𝓗 u)
      · have hK : MeasurableSet[𝓗 u] {ω | -(K : ℝ) < σ ω} := by
          have := (hσ (-(K : ℝ))).compl
          simp only [compl_ofPred, not_le] at this
          exact (𝓗.mono hu) _ this
        have hlt : MeasurableSet[𝓗 u] ({ω | σ ω ≤ u} ∩ {ω | σ ω < m}) := by
          rcases lt_or_ge u m with hum | hum
          · have : {ω | σ ω ≤ u} ∩ {ω | σ ω < m} = {ω | σ ω ≤ u} := by
              ext ω; simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
              intro h; linarith
            rw [this]; exact hσ u
          · have hm' : MeasurableSet[𝓗 m] {ω | σ ω < m} := by
              have : {ω | σ ω < m} = ⋃ n : ℕ, {ω | σ ω ≤ m - 1 / ((n : ℝ) + 1)} := by
                ext ω; simp only [mem_ofPred_eq, mem_iUnion]
                constructor
                · intro h
                  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
                  exact ⟨n, by linarith⟩
                · rintro ⟨n, hn⟩
                  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
                  linarith
              rw [this]
              exact MeasurableSet.iUnion fun n => (𝓗.mono (by
                have : 0 < 1 / ((n : ℝ) + 1) := by positivity
                linarith)) _ (hσ _)
            exact (hσ u).inter ((𝓗.mono hum) _ hm')
        have e2 : (A ∩ {ω | σ ω ≤ u}) ∩ ({ω | σ ω < m} ∩ {ω | -(K : ℝ) < σ ω}) =
            (A ∩ {ω | σ ω ≤ u}) ∩ ({ω | σ ω ≤ u} ∩ {ω | σ ω < m}) ∩ {ω | -(K : ℝ) < σ ω} := by
          ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
        rw [e2]
        exact ((hA u).inter hlt).inter hK
  -- limits
  have hlim : ∀ ρ : Ω → ℝ, Measurable ρ → Tendsto (fun K => ∫ ω in AK K, Y (min (ρ ω) m) ω ∂P)
      atTop (𝓝 (∫ ω in A₂, Y (min (ρ ω) m) ω ∂P)) := fun ρ hρ => by
    have := tendsto_setIntegral_of_monotone (μ := P) (f := fun ω => Y (min (ρ ω) m) ω) hAKm hmono
      (hint ρ hρ).integrableOn
    rwa [hU] at this
  have e2 : ∫ ω in A₂, Y (min (τ ω) m) ω ∂P = ∫ ω in A₂, Y (min (σ ω) m) ω ∂P :=
    tendsto_nhds_unique ((hlim τ hτm).congr eK) (hlim σ hσm)
  rw [hsplit, setIntegral_union hdisj hA₂m (hint τ hτm).integrableOn (hint τ hτm).integrableOn,
    setIntegral_union hdisj hA₂m (hint σ hσm).integrableOn (hint σ hσm).integrableOn, e1, e2]

/-- **Starting from `-∞`.** If moreover `|Y_u| ≤ C₀ e^u` for `u ≤ 0`, then `E[Y(τ ∧ m)] = 0`. -/
theorem integral_min_eq_zero {Y : ℝ → Ω → ℝ} (hY : IsRegProc Y)
    (hYa : ∀ u, Measurable[𝓗 u] (Y u))
    (hmart : ∀ w x, w ≤ x → ∀ A, MeasurableSet[𝓗 w] A →
      ∫ ω in A, Y x ω ∂P = ∫ ω in A, Y w ω ∂P)
    {τ : Ω → ℝ} (hτ : ∀ u, MeasurableSet[𝓗 u] {ω | τ ω ≤ u}) {m : ℝ} (hm : 0 ≤ m) {C C₀ : ℝ}
    (hYb : ∀ u ω, u ≤ m → |Y u ω| ≤ C) (hY0 : ∀ u ω, u ≤ 0 → |Y u ω| ≤ C₀ * exp u) :
    ∫ ω, Y (min (τ ω) m) ω ∂P = 0 := by
  have hτm := measurable_of_isStopping hτ
  -- optional sampling between `-K` and the clamped `τ`
  have hos : ∀ K : ℕ, ∫ ω, Y (-(K : ℝ)) ω ∂P = ∫ ω, Y (max (-(K : ℝ)) (min (τ ω) m)) ω ∂P := by
    intro K
    have := setIntegral_comp_eq_of_isStopping (P := P) hY hYa hmart (σ := fun _ => -(K : ℝ))
      (fun u => MeasurableSet.const _) (isStopping_clamp hτ K m) (fun ω => le_max_left _ _)
      (K := K) (M := max (-K) m) (fun ω => le_rfl) (fun ω => max_le_max le_rfl (min_le_right _ _))
      (A := univ) (fun u => by simp only [univ_inter]; exact MeasurableSet.const _)
    simpa using this
  have h1 : Tendsto (fun K : ℕ => ∫ ω, Y (-(K : ℝ)) ω ∂P) atTop (𝓝 0) := by
    have hb : ∀ K : ℕ, |∫ ω, Y (-(K : ℝ)) ω ∂P| ≤ P.real univ * C₀ * exp (-(K : ℝ)) := fun K => by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |Y (-(K : ℝ)) ω| ∂P ≤ ∫ _ω, C₀ * exp (-(K : ℝ)) ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
              (ae_of_all _ fun ω => hY0 _ ω (by simp))
        _ = P.real univ * C₀ * exp (-(K : ℝ)) := by simp [mul_assoc]
    have hexp : Tendsto (fun K : ℕ => P.real univ * C₀ * exp (-(K : ℝ))) atTop (𝓝 0) := by
      have := (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        tendsto_natCast_atTop_atTop)).const_mul (P.real univ * C₀)
      simpa using this
    exact squeeze_zero_norm (fun K => by rw [Real.norm_eq_abs]; exact hb K) hexp
  have h2 : Tendsto (fun K : ℕ => ∫ ω, Y (max (-(K : ℝ)) (min (τ ω) m)) ω ∂P) atTop
      (𝓝 (∫ ω, Y (min (τ ω) m) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun K => ?_)
      (integrable_const C) (fun K => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hY.measurable_uncurry.comp ((measurable_const.max (hτm.min measurable_const)).prodMk
        measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine hYb _ ω (max_le ?_ (min_le_right _ _))
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨K₀, hK₀⟩ := exists_nat_gt (-min (τ ω) m)
      filter_upwards [eventually_ge_atTop K₀] with K hK
      rw [max_eq_right]
      have : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
      linarith
  have := tendsto_nhds_unique (h1.congr hos) h2
  exact this.symm

end Sampling

end TwoSeed

end Sec2

end InteractingSLE
