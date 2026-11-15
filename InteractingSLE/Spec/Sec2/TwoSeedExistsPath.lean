/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedExistsMart
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries

/-!
# Two seeds: almost sure path properties of the Jacobi diffusion

Packet PROVE-SEC2-JAC3. For a Jacobi diffusion `U` (`Jacobi.IsJacobiDiffusion κ a b P 𝓗 U`,
`κ, a, b > 0`) on the logarithmic clock (Specification L512–L514):

* `measure_eq_one`, `measure_eq_zero`: `U_v` has no atom at `1` or `0`: the beta moments
  `m_n → 0` (`tendsto_jacobiMoment_zero`), and `1 - U` is a Jacobi diffusion with `a, b` swapped
  (`IsJacobiDiffusion.isJacobiMP_one_sub`, through polynomial test functions `genPoly`);
* `ae_volume_boundary_eq_zero`: almost surely the boundary set `{u : U_u ∈ {0, 1}}` is
  Lebesgue-null (Fubini);
* `ae_tendsto_clock`: almost surely the clock `t(u) = ½ ∫_{-∞}^u e^{2v} U (1 - U)` tends to `∞`.
  The source argues by ergodicity; here only the shift invariance of the path law (landed
  `map_toCPathR_eq`) is used: with `F_n = ∫_n^{n+1} U(1 - U)`, the events
  `⋂_{n ≥ N} {F_n < e^{-n}}` increase in `N` and have probability `≤ P(F_0 < e^{-N}) → P(F_0 = 0) = 0`,
  so almost surely `F_n ≥ e^{-n}` infinitely often and `t(n + 1) ≥ e^{2n} F_n / 2 ≥ e^n / 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Jacobi

/-! ### The beta moments tend to zero -/

theorem jacobiMoment_bound {κ a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 ≤ jacobiMoment κ a b n ∧ jacobiMoment κ a b n ≤
      exp (-((b / 2) / (κ / 4 + (a + b) / 2)) * ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)) := by
  set c := (b / 2) / (κ / 4 + (a + b) / 2) with hc
  have hden : 0 < κ / 4 + (a + b) / 2 := by positivity
  induction n with
  | zero => simp [jacobiMoment]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
    have hD : 0 ≤ dcoef κ a (n + 1) := by
      unfold dcoef; push_cast
      have : 0 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1 - 1) := by nlinarith
      positivity
    have hC : 0 < -ccoef κ a b (n + 1) := by
      have := ccoef_neg hκ (by linarith : 0 < a + b) (Nat.le_add_left 1 n)
      linarith
    have hCeq : -ccoef κ a b (n + 1) = dcoef κ a (n + 1) + ((n : ℝ) + 1) * b / 2 := by
      unfold ccoef dcoef; push_cast; ring
    -- the ratio
    set r := dcoef κ a (n + 1) / -ccoef κ a b (n + 1) with hr
    have hr0 : 0 ≤ r := div_nonneg hD hC.le
    have ht : c / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * b / 2 / -ccoef κ a b (n + 1) := by
      rw [hc, div_div, div_le_div_iff₀ (by positivity) hC]
      have hCle : -ccoef κ a b (n + 1) ≤ (κ / 4 + (a + b) / 2) * ((n : ℝ) + 1) ^ 2 := by
        rw [hCeq]; unfold dcoef; push_cast
        set k : ℝ := (n : ℝ) + 1
        have e1 : κ / 4 * (k * (k - 1)) ≤ κ / 4 * k ^ 2 := by
          have : k * (k - 1) ≤ k ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_left this (by positivity)
        have e2 : k * a / 2 + k * b / 2 ≤ (a + b) / 2 * k ^ 2 := by
          have : k ≤ k ^ 2 := by nlinarith
          have hab : 0 ≤ (a + b) / 2 := by positivity
          nlinarith
        nlinarith
      nlinarith
    have hr1 : r ≤ exp (-(c / ((n : ℝ) + 1))) := by
      have e : r = 1 - ((n : ℝ) + 1) * b / 2 / -ccoef κ a b (n + 1) := by
        rw [hr, eq_sub_iff_add_eq, ← add_div, ← hCeq, div_self hC.ne']
      rw [e]
      refine le_trans ?_ (exp_le_exp.2 (neg_le_neg ht))
      linarith [add_one_le_exp (-(((n : ℝ) + 1) * b / 2 / -ccoef κ a b (n + 1)))]
    refine ⟨?_, ?_⟩
    · rw [jacobiMoment]; exact mul_nonneg h0 hr0
    · rw [jacobiMoment, Finset.sum_range_succ, mul_add, exp_add]
      calc jacobiMoment κ a b n * r ≤ exp (-c * ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)) *
            exp (-(c / ((n : ℝ) + 1))) := mul_le_mul h1 hr1 hr0 (exp_pos _).le
        _ = _ := by congr 2; ring

/-- The beta moments tend to `0` (no atom at `1`). -/
theorem tendsto_jacobiMoment_zero {κ a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (jacobiMoment κ a b) atTop (𝓝 0) := by
  set c := (b / 2) / (κ / 4 + (a + b) / 2)
  have hc : 0 < c := by positivity
  have hsum := tendsto_sum_range_one_div_nat_succ_atTop
  have hlin : Tendsto (fun x : ℝ => -c * x) atTop atBot := by
    have := tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc)
    refine this.congr fun x => ?_
    simp [neg_mul]
  have hexp : Tendsto (fun n : ℕ => exp (-c * ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1))) atTop
      (𝓝 0) := tendsto_exp_atBot.comp (hlin.comp hsum)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
    (fun n => (jacobiMoment_bound hκ ha hb n).1) fun n => (jacobiMoment_bound hκ ha hb n).2

/-! ### Polynomial test functions and the symmetry `U ↦ 1 - U` -/

section Poly

open Polynomial

/-- The Jacobi generator on a polynomial. -/
def genPoly (κ a b : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  κ / 4 * (x * (1 - x)) * (derivative (derivative p)).eval x +
    (a * (1 - x) - b * x) / 2 * (derivative p).eval x

theorem gen_eval (κ a b : ℝ) (p : ℝ[X]) (x : ℝ) :
    gen κ a b (fun y => p.eval y) x = genPoly κ a b p x := by
  have h1 : deriv (fun y => p.eval y) = fun y => (derivative p).eval y :=
    funext fun y => Polynomial.deriv p
  simp only [gen, genPoly, h1, Polynomial.deriv]

theorem continuous_genPoly (κ a b : ℝ) (p : ℝ[X]) : Continuous (genPoly κ a b p) := by
  unfold genPoly
  have h1 := (derivative (derivative p)).continuous
  have h2 := (derivative p).continuous
  fun_prop

theorem genPoly_add (κ a b : ℝ) (p q : ℝ[X]) (x : ℝ) :
    genPoly κ a b (p + q) x = genPoly κ a b p x + genPoly κ a b q x := by
  simp only [genPoly, derivative_add, eval_add]; ring

theorem genPoly_monomial (κ a b : ℝ) (n : ℕ) (c x : ℝ) :
    genPoly κ a b (monomial n c) x = c * gen κ a b (fun y => y ^ n) x := by
  have : (fun y : ℝ => y ^ n) = fun y => (X ^ n : ℝ[X]).eval y := by funext y; simp
  rw [this, gen_eval, ← C_mul_X_pow_eq_monomial]
  simp only [genPoly, derivative_C_mul, eval_C_mul]; ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {𝓗 : Filtration ℝ mΩ} {Y Y' β β' : ℝ → Ω → ℝ}

omit [IsFiniteMeasure P] in
theorem HasCompensator.congr (h : HasCompensator P 𝓗 Y β) (hX : ∀ u ω, Y u ω = Y' u ω)
    (hα : ∀ u ω, β u ω = β' u ω) : HasCompensator P 𝓗 Y' β' := by
  have e1 : Y = Y' := funext fun u => funext fun ω => hX u ω
  have e2 : β = β' := funext fun u => funext fun ω => hα u ω
  exact e1 ▸ e2 ▸ h

theorem HasCompensator.add (h : HasCompensator P 𝓗 Y β) (h' : HasCompensator P 𝓗 Y' β')
    (hX : IsRegProc Y) (hX' : IsRegProc Y') (hα : IsRegProc β) (hα' : IsRegProc β') :
    HasCompensator P 𝓗 (fun u ω => Y u ω + Y' u ω) (fun u ω => β u ω + β' u ω) := by
  refine hasCompensator_of_integral_sub (hX.add hX') (hα.add hα') fun r x hrx Z hZ C hZC => ?_
  have hZm : Measurable Z := (hZ.mono (𝓗.le r)).measurable
  have e1 := h.integral_mul_sub hX hα hrx hZ hZC
  have e2 := h'.integral_mul_sub hX' hα' hrx hZ hZC
  have hs : ∀ (V : ℝ → Ω → ℝ) (V' : ℝ → Ω → ℝ), IsRegProc V → IsRegProc V' → ∀ u,
      ∫ ω, Z ω * (V u ω + V' u ω) ∂P = ∫ ω, Z ω * V u ω ∂P + ∫ ω, Z ω * V' u ω ∂P :=
    fun V V' hY hY' u => by
      simp only [mul_add]
      exact integral_add (hY.integrable_mul hZm hZC u) (hY'.integrable_mul hZm hZC u)
  rw [hs Y Y' hX hX' x, hs Y Y' hX hX' r]
  simp only [hs β β' hα hα']
  rw [intervalIntegral.integral_add ((hα.continuous_integral_mul hZm hZC).intervalIntegrable _ _)
    ((hα'.continuous_integral_mul hZm hZC).intervalIntegrable _ _)]
  linarith

omit [IsFiniteMeasure P] in
theorem HasCompensator.const_mul (h : HasCompensator P 𝓗 Y β) (c : ℝ) :
    HasCompensator P 𝓗 (fun u ω => c * Y u ω) (fun u ω => c * β u ω) := by
  intro r x hrx Z hZ hZC
  have := h r x hrx Z hZ hZC
  have e : (fun ω => Z ω * (c * Y x ω - c * Y r ω - ∫ s in r..x, c * β s ω)) =
      fun ω => c * (Z ω * (Y x ω - Y r ω - ∫ s in r..x, β s ω)) := by
    funext ω; rw [intervalIntegral.integral_const_mul]; ring
  rw [e, integral_const_mul, this, mul_zero]

variable {κ a b : ℝ} {U : ℝ → Ω → ℝ}

/-- **Polynomial test functions.** -/
theorem IsJacobiDiffusion.hasCompensator_poly (hU : IsJacobiDiffusion κ a b P 𝓗 U) (p : ℝ[X]) :
    HasCompensator P 𝓗 (fun u ω => p.eval (U u ω)) (fun u ω => genPoly κ a b p (U u ω)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine (hp.add hq (hU.isRegProc_comp p.continuous) (hU.isRegProc_comp q.continuous)
      (hU.isRegProc_comp (continuous_genPoly κ a b p))
      (hU.isRegProc_comp (continuous_genPoly κ a b q))).congr (fun u ω => ?_) (fun u ω => ?_)
    · simp [eval_add]
    · rw [genPoly_add]
  | monomial n c =>
    refine ((hU.hasCompensator_pow n).const_mul c).congr (fun u ω => ?_) (fun u ω => ?_)
    · simp [← C_mul_X_pow_eq_monomial]
    · rw [genPoly_monomial]

theorem genPoly_one_sub_pow (κ a b : ℝ) (n : ℕ) (x : ℝ) :
    genPoly κ a b ((1 - X) ^ n) x = gen κ b a (fun y => y ^ n) (1 - x) := by
  have d1 : (derivative ((1 - X) ^ n : ℝ[X])).eval x = -(n * (1 - x) ^ (n - 1)) := by
    simp [derivative_pow]
  have d2 : (derivative (derivative ((1 - X) ^ n : ℝ[X]))).eval x =
      n * ((n - 1 : ℕ) * (1 - x) ^ (n - 1 - 1)) := by
    simp [derivative_pow]
  rw [gen_pow, genPoly, d1, d2]
  simp only [dcoef, ccoef]
  rcases n with _ | _ | n
  · simp
  · simp; ring
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- **Symmetry.** `1 - U` solves the polynomial martingale problem with `a` and `b` swapped. -/
theorem IsJacobiDiffusion.isJacobiMP_one_sub (hU : IsJacobiDiffusion κ a b P 𝓗 U) :
    IsJacobiMP κ b a P fun u ω => 1 - U u ω := by
  have hmem : ∀ u ω, 1 - U u ω ∈ Icc (0 : ℝ) 1 := fun u ω =>
    ⟨by linarith [(hU.mem_Icc u ω).2], by linarith [(hU.mem_Icc u ω).1]⟩
  refine ⟨hmem, fun ω => continuous_const.sub (hU.continuous ω),
    fun u => measurable_const.sub (hU.measurable u), fun m s k n w v hs hwv => ?_⟩
  have h := (hU.hasCompensator_poly ((1 - X) ^ n)).congr
    (Y' := fun u ω => (1 - U u ω) ^ n) (β' := fun u ω => gen κ b a (fun y => y ^ n) (1 - U u ω))
    (fun u ω => by simp) (fun u ω => genPoly_one_sub_pow κ a b n _)
  refine h w v hwv _ ?_ ⟨1, fun ω => ?_⟩
  · refine (Finset.measurable_prod _ fun i _ => ?_).stronglyMeasurable
    exact (measurable_const.sub ((hU.adapted (s i)).mono (𝓗.mono (hs i)) le_rfl)).pow_const _
  · have h0 : 0 ≤ ∏ i, (1 - U (s i) ω) ^ k i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (hmem _ ω).1 _
    rw [abs_of_nonneg h0]
    exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (hmem _ ω).1 _) fun i _ =>
      pow_le_one₀ (hmem _ ω).1 (hmem _ ω).2

end Poly

/-! ### No atoms at the endpoints; the boundary set is null -/

section Atoms

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {κ a b : ℝ} {U : ℝ → Ω → ℝ}

theorem IsJacobiMP.measure_eq_one (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hb : 0 < b) (v : ℝ) : P {ω | U v ω = 1} = 0 := by
  have hmeas : MeasurableSet {ω | U v ω = 1} := hU.measurable v (measurableSet_singleton 1)
  have hle : ∀ n, P.real {ω | U v ω = 1} ≤ jacobiMoment κ a b n := fun n => by
    rw [← hU.moment_eq hκ (by linarith) n v, ← integral_indicator_one hmeas]
    refine integral_mono ((integrable_const 1).indicator hmeas) ?_ fun ω => ?_
    · refine Integrable.of_bound ((hU.measurable v).pow_const n).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hU.mem_Icc v ω).1 n)]
      exact pow_le_one₀ (hU.mem_Icc v ω).1 (hU.mem_Icc v ω).2
    · by_cases h : U v ω = 1
      · simp [Set.indicator, h]
      · simp only [Set.indicator, mem_ofPred_eq, h, ite_false]
        exact pow_nonneg (hU.mem_Icc v ω).1 n
  have h0 := ge_of_tendsto' (tendsto_jacobiMoment_zero hκ ha hb) hle
  exact (measureReal_eq_zero_iff).1 (le_antisymm h0 measureReal_nonneg)

theorem IsJacobiDiffusion.measure_eq_zero {𝓗 : Filtration ℝ mΩ}
    (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    P {ω | U v ω = 0} = 0 := by
  have := hU.isJacobiMP_one_sub.measure_eq_one hκ hb ha v
  simpa [sub_eq_self] using this

/-- **The boundary set is Lebesgue-null almost surely.** -/
theorem IsJacobiDiffusion.ae_volume_boundary {𝓗 : Filtration ℝ mΩ}
    (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂P, volume {v | U v ω = 0 ∨ U v ω = 1} = 0 := by
  have hJ := hU.isJacobiMP
  set S : Set (Ω × ℝ) := {p | U p.2 p.1 = 0 ∨ U p.2 p.1 = 1} with hS
  have hSm : MeasurableSet S :=
    (hJ.measurable_uncurry (measurableSet_singleton 0)).union
      (hJ.measurable_uncurry (measurableSet_singleton 1))
  have h0 : (P.prod volume) S = 0 := by
    rw [Measure.prod_apply_symm hSm]
    have : ∀ v : ℝ, P ((fun ω => (ω, v)) ⁻¹' S) = 0 := fun v => by
      have e : (fun ω => (ω, v)) ⁻¹' S = {ω | U v ω = 0} ∪ {ω | U v ω = 1} := by
        ext ω; simp [hS]
      rw [e]
      exact measure_union_null (hU.measure_eq_zero hκ ha hb v) (hJ.measure_eq_one hκ ha hb v)
    simp [this]
  rw [Measure.prod_apply hSm] at h0
  have := (lintegral_eq_zero_iff (measurable_measure_prodMk_left hSm)).1 h0
  filter_upwards [this] with ω hω
  simpa [hS] using hω

end Atoms


/-! ### Divergence of the clock -/

section Clock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {κ a b : ℝ} {U : ℝ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem IsJacobiMP.shift (hU : IsJacobiMP κ a b P U) (c : ℝ) :
    IsJacobiMP κ a b P fun u ω => U (u + c) ω := by
  refine ⟨fun u ω => hU.mem_Icc _ ω, fun ω => (hU.continuous ω).comp (continuous_id.add continuous_const),
    fun u => hU.measurable _, fun m s k n w v hs hwv => ?_⟩
  have := hU.2.2.2 m (fun i => s i + c) k n (w + c) (v + c) (fun i => by linarith [hs i])
    (by linarith)
  rw [← this]
  congr 1; funext ω; congr 2
  exact intervalIntegral.integral_comp_add_right (fun x => gen κ a b (fun y => y ^ n) (U x ω)) c

/-- The functional `f ↦ ∫_0^1 f (1 - f)` on paths. -/
def unitMass (f : TwoSeed.CPathR) : ℝ :=
  ∫ v in (0 : ℝ)..1, TwoSeed.clampU f v * (1 - TwoSeed.clampU f v)

theorem measurable_unitMass : Measurable unitMass := by
  have h := TwoSeed.measurable_integral_clampU (F := fun (_ : ℝ) (y : ℝ) => y * (1 - y))
    (by fun_prop) (volume.restrict (Ioc (0 : ℝ) 1))
  have e : unitMass = fun f : TwoSeed.CPathR =>
      ∫ v in Ioc (0 : ℝ) 1, TwoSeed.clampU f v * (1 - TwoSeed.clampU f v) := by
    funext f; simp only [unitMass, intervalIntegral.integral_of_le zero_le_one]
  rw [e]; exact h

omit [IsProbabilityMeasure P] in
theorem unitMass_shift (hU : IsJacobiMP κ a b P U) (c : ℝ) (ω : Ω) :
    unitMass (TwoSeed.toCPathR (fun u ω => U (u + c) ω) (hU.shift c).continuous ω) =
      ∫ v in c..(c + 1), U v ω * (1 - U v ω) := by
  unfold unitMass
  rw [TwoSeed.clampU_eq fun v => hU.mem_Icc _ ω]
  have := intervalIntegral.integral_comp_add_right (fun v => U v ω * (1 - U v ω)) c
    (a := 0) (b := 1)
  simp only [zero_add] at this
  rw [add_comm c 1]
  exact this

/-- **The clock diverges almost surely.** -/
theorem IsJacobiDiffusion.ae_tendsto_clock {𝓗 : Filtration ℝ mΩ}
    (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂P, Tendsto (TwoSeed.clock (U · ω)) atTop atTop := by
  have hJ := hU.isJacobiMP
  have hab : 0 < a + b := by linarith
  set G : ℕ → Ω → ℝ := fun n ω => ∫ v in (n : ℝ)..((n : ℝ) + 1), U v ω * (1 - U v ω) with hG
  -- the law of `G n` does not depend on `n`
  have hlaw : ∀ (n : ℕ) (ε : ℝ), P {ω | G n ω < ε} = P {ω | G 0 ω < ε} := by
    intro n ε
    have hmap := TwoSeed.map_toCPathR_eq (hJ.shift n) (hJ.shift 0) hκ hab
    have hS : MeasurableSet {f : TwoSeed.CPathR | unitMass f < ε} :=
      measurableSet_lt measurable_unitMass measurable_const
    have h1 := Measure.map_apply (TwoSeed.measurable_toCPathR (hJ.shift (n : ℝ)).measurable
      (hJ.shift (n : ℝ)).continuous) hS (μ := P)
    have h2 := Measure.map_apply (TwoSeed.measurable_toCPathR (hJ.shift 0).measurable
      (hJ.shift 0).continuous) hS (μ := P)
    rw [hmap, h2] at h1
    have e : ∀ c : ℝ, (TwoSeed.toCPathR (fun u ω => U (u + c) ω) (hJ.shift c).continuous) ⁻¹'
        {f | unitMass f < ε} = {ω | ∫ v in c..(c + 1), U v ω * (1 - U v ω) < ε} := by
      intro c; ext ω; simp only [mem_preimage, mem_ofPred_eq, unitMass_shift hJ c ω]
    rw [e, e] at h1
    simpa [hG] using h1.symm
  -- `G 0 > 0` almost surely
  have hpos : ∀ᵐ ω ∂P, 0 < G 0 ω := by
    filter_upwards [hU.ae_volume_boundary hκ ha hb] with ω hω
    simp only [hG, Nat.cast_zero, zero_add]
    rw [intervalIntegral.integral_of_le zero_le_one]
    have hcont : Continuous fun v => U v ω * (1 - U v ω) :=
      (hU.continuous ω).mul (continuous_const.sub (hU.continuous ω))
    have hnn : ∀ v, 0 ≤ U v ω * (1 - U v ω) := fun v =>
      mul_nonneg (hU.mem_Icc v ω).1 (by linarith [(hU.mem_Icc v ω).2])
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun v => hnn v)
      (hcont.integrableOn_Ioc)]
    have hsub : Ioc (0 : ℝ) 1 ⊆ (Function.support fun v => U v ω * (1 - U v ω)) ∩ Ioc 0 1 ∪
        {v | U v ω = 0 ∨ U v ω = 1} := by
      intro v hv
      by_cases h : U v ω * (1 - U v ω) = 0
      · right
        rcases mul_eq_zero.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (by linarith)
      · exact Or.inl ⟨h, hv⟩
    have := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
    rw [hω, add_zero, Real.volume_Ioc] at this
    refine lt_of_lt_of_le (by simp) this
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (hU.isRegProc.mul ((isRegProc_const_time (X := fun _ (_ : Ω) => (1 : ℝ))
      ⟨fun _ => continuous_const, fun _ => measurable_const, fun _ => ⟨1, fun _ _ _ => by simp⟩⟩
      0).sub hU.isRegProc)).measurable_intervalIntegral _ _
  -- `P(G 0 < e^{-N}) → 0`
  have hlim : Tendsto (fun N : ℕ => P {ω | G 0 ω < exp (-(N : ℝ))}) atTop (𝓝 0) := by
    have hanti : Antitone fun N : ℕ => {ω | G 0 ω < exp (-(N : ℝ))} := fun N M h ω hω =>
      lt_of_lt_of_le hω (exp_le_exp.2 (neg_le_neg (by exact_mod_cast h)))
    have h := tendsto_measure_iInter_atTop (μ := P)
      (fun N => (measurableSet_lt (hGm 0) measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have hI : P (⋂ N : ℕ, {ω | G 0 ω < exp (-(N : ℝ))}) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
      simp only [mem_iInter, mem_ofPred_eq] at hω
      simp only [mem_ofPred_eq, not_lt]
      by_contra hc
      push Not at hc
      have hexp : Tendsto (fun N : ℕ => exp (-(N : ℝ))) atTop (𝓝 0) :=
        tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨N, hN⟩ := (hexp.eventually (gt_mem_nhds hc)).exists
      exact lt_irrefl _ ((hω N).trans hN)
    rw [hI] at h
    exact h
  -- the events `⋂_{n ≥ N} {G n < e^{-n}}` are null
  have hE : ∀ N : ℕ, P (⋂ n ≥ N, {ω | G n ω < exp (-(n : ℝ))}) = 0 := by
    intro N
    refine le_antisymm (ge_of_tendsto hlim (eventually_atTop.2 ⟨N, fun M hM => ?_⟩)) bot_le
    calc P (⋂ n ≥ N, {ω | G n ω < exp (-(n : ℝ))}) ≤ P {ω | G M ω < exp (-(M : ℝ))} :=
          measure_mono (biInter_subset_of_mem hM)
      _ = P {ω | G 0 ω < exp (-(M : ℝ))} := hlaw M _
  have hU0 : P (⋃ N : ℕ, ⋂ n ≥ N, {ω | G n ω < exp (-(n : ℝ))}) = 0 :=
    measure_iUnion_null (μ := P) hE
  have hae : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ n ≥ N, exp (-(n : ℝ)) ≤ G n ω := by
    refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) hU0)
    simp only [mem_ofPred_eq, not_forall, not_exists] at hω
    obtain ⟨N, hN⟩ := hω
    exact mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => lt_of_not_ge fun h => hN n ⟨hn, h⟩⟩
  filter_upwards [hae] with ω hω
  have hc : Continuous fun v => U v ω := hU.continuous ω
  have h01 : ∀ v, U v ω ∈ Icc (0 : ℝ) 1 := fun v => hU.mem_Icc v ω
  refine (TwoSeed.monotone_clock hc h01).tendsto_atTop_atTop fun B => ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * B)
  obtain ⟨n, hnN, hn⟩ := hω N
  refine ⟨(n : ℝ) + 1, ?_⟩
  have hsub := TwoSeed.clock_sub hc h01 (n : ℝ) ((n : ℝ) + 1)
  have hnn := TwoSeed.clock_nonneg (U := fun v => U v ω) h01 (n : ℝ)
  have hgc : Continuous fun v => U v ω * (1 - U v ω) := hc.mul (continuous_const.sub hc)
  have hint : exp (2 * (n : ℝ)) / 2 * G n ω ≤
      ∫ v in (n : ℝ)..((n : ℝ) + 1), TwoSeed.clockDensity (fun v => U v ω) v := by
    simp only [hG]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) ((continuous_const.mul hgc).intervalIntegrable _ _)
      ((TwoSeed.continuous_clockDensity hc).intervalIntegrable _ _) fun v hv => ?_
    simp only [TwoSeed.clockDensity]
    have he := exp_le_exp.2 (show 2 * (n : ℝ) ≤ 2 * v by linarith [hv.1])
    have hg : 0 ≤ U v ω * (1 - U v ω) := mul_nonneg (h01 v).1 (by linarith [(h01 v).2])
    nlinarith
  have hexpn : exp (2 * (n : ℝ)) / 2 * exp (-(n : ℝ)) = exp (n : ℝ) / 2 := by
    rw [div_mul_eq_mul_div, ← exp_add]; ring_nf
  have h2 : (n : ℝ) + 1 ≤ exp (n : ℝ) := by linarith [add_one_le_exp (n : ℝ)]
  have h3 : exp (2 * (n : ℝ)) / 2 * exp (-(n : ℝ)) ≤ exp (2 * (n : ℝ)) / 2 * G n ω :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hnN
  linarith

end Clock


end Jacobi

end Sec2

end InteractingSLE
