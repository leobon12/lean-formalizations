/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65DDSFlat
import InteractingSLE.GFF.LocalSets.SubdomainMGF

/-!
# Proposition 6.5, Brownian representation, part 2: the time-changed exponential martingale

Packet PROVE-SEC6-E (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, pp. 157–159).

For a conditionally Gaussian exploration `(X, v, ρ)` (`Prop65Time`) with version `Y` of the stopped
conditional mean, run the mean at the clock `A = v₀ − v_{·∧ρ}`: `σ_u` is the first time `A ≥ u`
(capped at `ρ`, `lvlTime`), `N_u = 1_G (Y_{σ_u} − Y₀)` and `ℓ_u = A_{σ_u} = min(u, A_ρ)`
(`tcN`, `tcL`). The route recorded in `planning/handoffs/PROVE-SEC6-B.md` ("What remains" 1) needs no
stochastic calculus: the conditional Gaussian law at `σ_u` gives directly

  `E[W e^{a N_u − a² ℓ_u / 2}] = E[W 1_G e^{a X − a Y₀ − a² v₀ / 2}] + E[W 1_{Gᶜ}]`

for every `𝓕_{σ_s}`-measurable `W ≥ 0`, `s ≤ u`, so the right side does not depend on `u`
(`lintegral_exp_tc`): `e^{a N_u − a² ℓ_u / 2}` is a martingale in the time-changed filtration
`𝓕_{σ_u}` (`tcFilt`), in the integral form used later on the enlarged space.

* `lintegral_mul_exp_eq`: `E[W e^{aX}] = E[W e^{a E[X|𝓕_T] + a² v_T / 2}]` for `𝓕_T`-measurable
  `W ≥ 0` (conditional moment generating function, PROVE-LS-C's `lintegral_mul_exp_of_condCharFun`).
* `lintegral_exp_tc_sq_le`: `E[(e^{a N_u − a² ℓ_u/2})²] ≤ e^{a² u}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The first time the clock `A = v₀ − v_{·∧ρ}` reaches the deterministic level `u`, capped at `ρ`. -/
def lvlTime (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  lvl (clockA v ρ) ρ (fun _ => (u : ℝ)) ω

/-- The time-changed clock `ℓ_u = A_{σ_u}` (`= min(u, A_ρ)`). -/
def tcL (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  clockA v ρ (lvlTime v ρ u ω) ω

/-- The time-changed mean `N_u = 1_G (Y_{σ_u} − Y₀)`. -/
def tcN (G : Set Ω) (Y : ℝ≥0 → Ω → ℝ) (v : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  G.indicator (fun ω => Y (lvlTime v ρ u ω) ω - Y 0 ω) ω

namespace IsGaussianExploration

variable {X : Ω → ℝ} {v : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} {K : ℝ}

theorem isStoppingTime_lvlTime (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => (lvlTime v ρ u ω : WithTop ℝ≥0) :=
  isStoppingTime_lvl h.isClockAt h.stopping fun t =>
    measurableSet_le measurable_const (h.measurable_clockA t)

omit mΩ in
theorem lvlTime_le (u : ℝ≥0) (ω : Ω) : lvlTime v ρ u ω ≤ ρ ω := IsClockAt.lvl_le _

omit mΩ in
theorem lvlTime_mono {u u' : ℝ≥0} (huu : u ≤ u') (ω : Ω) :
    lvlTime v ρ u ω ≤ lvlTime v ρ u' ω :=
  IsClockAt.lvl_mono (by exact_mod_cast huu)

theorem tcL_eq (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) (ω : Ω) :
    tcL v ρ u ω = min (u : ℝ) (clockA v ρ (ρ ω) ω) :=
  (h.isClockAt ω).clock_lvl u.2

theorem tcL_nonneg (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) (ω : Ω) :
    0 ≤ tcL v ρ u ω :=
  (h.isClockAt ω).nonneg _

theorem tcL_le (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) (ω : Ω) :
    tcL v ρ u ω ≤ u := by
  rw [h.tcL_eq]; exact min_le_left _ _

theorem lvlTime_zero (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) : lvlTime v ρ 0 ω = 0 := by
  have h0 : ((0 : ℝ≥0) : ℝ) ≤ clockA v ρ (ρ ω) ω := by
    simpa using (h.isClockAt ω).nonneg (ρ ω)
  simp only [lvlTime, lvl, h0, ↓reduceIte]
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) ?_) zero_le
  simpa using (h.isClockAt ω).nonneg 0

/-- The time-changed filtration `u ↦ 𝓕_{σ_u}`. -/
def tcFilt (h : IsGaussianExploration P 𝓕 X v ρ K) : Filtration ℝ≥0 mΩ where
  seq u := (h.isStoppingTime_lvlTime u).measurableSpace
  mono' _ _ huu := IsStoppingTime.measurableSpace_mono _ _ fun ω =>
    WithTop.coe_le_coe.2 (lvlTime_mono huu ω)
  le' u := (h.isStoppingTime_lvlTime u).measurableSpace_le

theorem tcFilt_apply (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    h.tcFilt u = (h.isStoppingTime_lvlTime u).measurableSpace := rfl

/-- A finite stopping time is measurable. -/
theorem measurable_of_isStoppingTime {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) : Measurable σ :=
  measurable_of_Iic fun t => by
    have := (𝓕.le t) _ (hσ t)
    simpa only [preimage, mem_Iic, WithTop.coe_le_coe] using this

/-- `𝓕₀ ≤ 𝓕_σ` for every finite stopping time `σ`. -/
theorem zero_le_measurableSpace {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0)) : 𝓕 0 ≤ hσ.measurableSpace := by
  have := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓕 0) hσ fun ω =>
    WithTop.coe_le_coe.2 (zero_le (a := σ ω))
  rwa [IsStoppingTime.measurableSpace_const] at this

/-! ### The conditional moment generating function -/

/-- **Conditional moment generating function** at a stopping time `T ≤ ρ`:
`E[W e^{aX}] = E[W e^{a E[X | 𝓕_T] + a² v_T / 2}]` for every `𝓕_T`-measurable `W ≥ 0`. -/
theorem lintegral_mul_exp_eq [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hTρ : ∀ ω, T ω ≤ ρ ω)
    {W : Ω → ℝ≥0∞} (hW : Measurable[hT.measurableSpace] W) (a : ℝ) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * X ω)) ∂P =
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * P[X | hT.measurableSpace] ω +
        a ^ 2 * v (T ω) ω / 2)) ∂P := by
  have g := h.gauss T hT hTρ
  set μ := P[X | hT.measurableSpace] with hμ
  have hc : ∀ t : ℝ, P[fun ω => cexp (I * ((t * (X ω - μ ω) : ℝ) : ℂ)) | hT.measurableSpace]
      =ᵐ[P] fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * v (T ω) ω)) : ℝ) : ℂ) := fun t =>
    condCharFun_sub_of_condCharFun g.measurable_X g.measurable_mean g.le t (g.charFun t)
  have hW' : Measurable[hT.measurableSpace] fun ω => W ω * ENNReal.ofReal (Real.exp (a * μ ω)) :=
    hW.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (g.measurable_mean.const_mul a)))
  have key := LocalSets.lintegral_mul_exp_of_condCharFun g.le
    (g.measurable_X.sub (g.measurable_mean.mono g.le le_rfl)) g.measurable_var'
    (ae_of_all _ g.nonneg) hc hW' a
  have e1 : ∀ ω, W ω * ENNReal.ofReal (Real.exp (a * μ ω)) *
      ENNReal.ofReal (Real.exp (a * (X - μ) ω)) = W ω * ENNReal.ofReal (Real.exp (a * X ω)) := by
    intro ω
    rw [Pi.sub_apply, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    ring
  have e2 : ∀ ω, W ω * ENNReal.ofReal (Real.exp (a * μ ω)) *
      ENNReal.ofReal (Real.exp (a ^ 2 * v (T ω) ω / 2)) =
        W ω * ENNReal.ofReal (Real.exp (a * μ ω + a ^ 2 * v (T ω) ω / 2)) := by
    intro ω
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp only [e1, e2] at key
  exact key

/-! ### The time-changed exponential martingale -/

theorem ae_eq_condExp_zero {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) :
    Y 0 =ᵐ[P] P[X | 𝓕 0] := by
  have := hY.eq (fun _ => 0) (isStoppingTime_const 𝓕 0) fun _ => zero_le
  rw [IsStoppingTime.measurableSpace_const] at this
  exact this

/-- The two terms that make up `E[W e^{a N_r − a² ℓ_r/2}]`; the right side does not depend on `r`. -/
theorem lintegral_exp_tc_eq [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {G : Set Ω} (hG : MeasurableSet[𝓕 0] G)
    (hvG : ∀ ω ∉ G, ∀ t, v t ω = v 0 ω) (a : ℝ) (r : ℝ≥0) {W : Ω → ℝ≥0∞}
    (hW : Measurable[h.tcFilt r] W) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * tcN G Y v ρ r ω - a ^ 2 * tcL v ρ r ω / 2)) ∂P =
      ∫⁻ ω, G.indicator (fun ω => W ω * ENNReal.ofReal (Real.exp
        (-(a * P[X | 𝓕 0] ω) - a ^ 2 * v 0 ω / 2)) * ENNReal.ofReal (Real.exp (a * X ω))) ω ∂P +
        ∫⁻ ω, Gᶜ.indicator W ω ∂P := by
  set hσ := h.isStoppingTime_lvlTime r
  set σ := lvlTime v ρ r with hσdef
  set μ₀ := P[X | 𝓕 0] with hμ₀
  have hσρ : ∀ ω, σ ω ≤ ρ ω := lvlTime_le r
  have h0 := zero_le_measurableSpace hσ
  have hGσ : MeasurableSet[hσ.measurableSpace] G := h0 _ hG
  set c₀ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-(a * μ₀ ω) - a ^ 2 * v 0 ω / 2))
    with hc₀
  have hc₀m : Measurable[𝓕 0] c₀ := by
    have hμm : Measurable[𝓕 0] μ₀ := stronglyMeasurable_condExp.measurable
    have hvm : Measurable[𝓕 0] (v 0) := h.adapted 0
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((hμm.const_mul a).neg).sub ((hvm.const_mul (a ^ 2)).div_const 2)))
  have hW' : Measurable[hσ.measurableSpace] W := hW
  have hW₁ : Measurable[hσ.measurableSpace] (G.indicator fun ω => W ω * c₀ ω) :=
    (hW'.mul (hc₀m.mono h0 le_rfl)).indicator hGσ
  have key := h.lintegral_mul_exp_eq hσ hσρ hW₁ a
  have hWm : Measurable W := hW'.mono hσ.measurableSpace_le le_rfl
  -- pointwise identity, almost surely
  have hpt : (fun ω => W ω * ENNReal.ofReal (Real.exp (a * tcN G Y v ρ r ω -
      a ^ 2 * tcL v ρ r ω / 2))) =ᵐ[P] fun ω => (G.indicator (fun ω => W ω * c₀ ω) ω *
        ENNReal.ofReal (Real.exp (a * P[X | hσ.measurableSpace] ω + a ^ 2 * v (σ ω) ω / 2))) +
          Gᶜ.indicator W ω := by
    filter_upwards [hY.eq σ hσ hσρ, ae_eq_condExp_zero hY] with ω h1 h2
    by_cases hω : ω ∈ G
    · have hN : tcN G Y v ρ r ω = P[X | hσ.measurableSpace] ω - μ₀ ω := by
        simp only [tcN, indicator_of_mem hω]
        rw [← hσdef, h1, h2]
      have hL : tcL v ρ r ω = v 0 ω - v (σ ω) ω := by
        simp only [tcL, clockA, ← hσdef, min_eq_left (hσρ ω)]
      rw [hN, hL, indicator_of_mem hω, indicator_of_notMem (show ω ∉ Gᶜ from fun h => h hω),
        add_zero, hc₀, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring
    · have hN : tcN G Y v ρ r ω = 0 := by simp only [tcN, indicator_of_notMem hω]
      have hL : tcL v ρ r ω = 0 := by
        simp only [tcL, clockA, hvG ω hω, sub_self]
      rw [hN, hL, indicator_of_notMem hω, indicator_of_mem (show ω ∈ Gᶜ from hω), zero_mul,
        zero_add]
      simp
  rw [lintegral_congr_ae hpt, lintegral_add_right _ (hWm.indicator (MeasurableSet.compl
    ((𝓕.le 0) _ hG))), ← key]
  congr 1
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, hc₀]
  · simp only [indicator_of_notMem hω, zero_mul]

/-- **The time-changed exponential martingale** (integral form): for `s ≤ u` and every
`𝓕_{σ_s}`-measurable `W ≥ 0`, `E[W e^{a N_u − a² ℓ_u/2}] = E[W e^{a N_s − a² ℓ_s/2}]`. -/
theorem lintegral_exp_tc [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {G : Set Ω} (hG : MeasurableSet[𝓕 0] G)
    (hvG : ∀ ω ∉ G, ∀ t, v t ω = v 0 ω) (a : ℝ) {s u : ℝ≥0} (hsu : s ≤ u) {W : Ω → ℝ≥0∞}
    (hW : Measurable[h.tcFilt s] W) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * tcN G Y v ρ u ω - a ^ 2 * tcL v ρ u ω / 2)) ∂P =
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a * tcN G Y v ρ s ω - a ^ 2 * tcL v ρ s ω / 2)) ∂P := by
  rw [h.lintegral_exp_tc_eq hY hG hvG a u (hW.mono (h.tcFilt.mono hsu) le_rfl),
    h.lintegral_exp_tc_eq hY hG hvG a s hW]

theorem tcN_zero (h : IsGaussianExploration P 𝓕 X v ρ K) (G : Set Ω) (Y : ℝ≥0 → Ω → ℝ)
    (ω : Ω) : tcN G Y v ρ 0 ω = 0 := by
  simp [tcN, h.lvlTime_zero]

theorem tcL_zero (h : IsGaussianExploration P 𝓕 X v ρ K) (ω : Ω) : tcL v ρ 0 ω = 0 := by
  simp only [tcL, h.lvlTime_zero, clockA_zero]

/-- `E[W e^{a N_u − a² ℓ_u/2}] = E[W]` for `𝓕₀`-measurable `W ≥ 0`. -/
theorem lintegral_exp_tc_eq_zero [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {G : Set Ω} (hG : MeasurableSet[𝓕 0] G)
    (hvG : ∀ ω ∉ G, ∀ t, v t ω = v 0 ω) (a : ℝ) (u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * tcN G Y v ρ u ω - a ^ 2 * tcL v ρ u ω / 2)) ∂P = 1 := by
  have := h.lintegral_exp_tc hY hG hvG a (zero_le (a := u)) (W := fun _ => 1) measurable_const
  simp only [one_mul, h.tcN_zero, h.tcL_zero, mul_zero, zero_div, sub_zero, Real.exp_zero,
    ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one] at this
  exact this

/-- **Square bound**: `E[(e^{a N_u − a² ℓ_u/2})²] ≤ e^{a² u}`. -/
theorem lintegral_exp_tc_sq_le [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {G : Set Ω} (hG : MeasurableSet[𝓕 0] G)
    (hvG : ∀ ω ∉ G, ∀ t, v t ω = v 0 ω) (a : ℝ) (u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * tcN G Y v ρ u ω - a ^ 2 * tcL v ρ u ω / 2)) ^ 2 ∂P ≤
      ENNReal.ofReal (Real.exp (a ^ 2 * u)) := by
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (a * tcN G Y v ρ u ω - a ^ 2 * tcL v ρ u ω / 2)) ^ 2
      ≤ ENNReal.ofReal (Real.exp (a ^ 2 * u)) * ENNReal.ofReal (Real.exp
        ((2 * a) * tcN G Y v ρ u ω - (2 * a) ^ 2 * tcL v ρ u ω / 2)) := by
    intro ω
    rw [sq, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 := h.tcL_le u ω
    have h2 : 0 ≤ a ^ 2 := sq_nonneg a
    nlinarith
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (a ^ 2 * u)) * ENNReal.ofReal (Real.exp
          ((2 * a) * tcN G Y v ρ u ω - (2 * a) ^ 2 * tcL v ρ u ω / 2)) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (a ^ 2 * u)) * ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((2 * a) * tcN G Y v ρ u ω - (2 * a) ^ 2 * tcL v ρ u ω / 2)) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (a ^ 2 * u)) := by
        rw [h.lintegral_exp_tc_eq_zero hY hG hvG, mul_one]

/-! ### Adaptedness -/

theorem measurable_tcL (h : IsGaussianExploration P 𝓕 X v ρ K) (u : ℝ≥0) :
    Measurable[h.tcFilt u] (tcL v ρ u) :=
  (stronglyMeasurable_comp_stoppingTime h.continuous_clockA h.measurable_clockA
    (h.isStoppingTime_lvlTime u)).measurable

theorem measurable_tcN [IsProbabilityMeasure P] (h : IsGaussianExploration P 𝓕 X v ρ K)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y) {G : Set Ω} (hG : MeasurableSet[𝓕 0] G)
    (u : ℝ≥0) : Measurable[h.tcFilt u] (tcN G Y v ρ u) := by
  set hσ := h.isStoppingTime_lvlTime u
  have h0 := zero_le_measurableSpace hσ
  have hnσ : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[hσ.measurableSpace] s :=
    fun s hs hs0 => h0 _ (hnull s hs hs0)
  have hYσm : Measurable fun ω => Y (lvlTime v ρ u ω) ω :=
    measurable_uncurry_of_continuous_of_measurable hY.cont hY.meas |>.comp
      ((measurable_of_isStoppingTime hσ).prodMk measurable_id)
  have h1 : Measurable[hσ.measurableSpace] fun ω => Y (lvlTime v ρ u ω) ω :=
    measurable_of_ae_eq_of_null hnσ hYσm stronglyMeasurable_condExp.measurable
      hσ.measurableSpace_le (hY.eq _ hσ (lvlTime_le u))
  have h2 : Measurable[hσ.measurableSpace] (Y 0) :=
    measurable_of_ae_eq_of_null hnσ (hY.meas 0)
      ((stronglyMeasurable_condExp (m := 𝓕 0)).measurable.mono h0 le_rfl)
      hσ.measurableSpace_le (ae_eq_condExp_zero hY)
  exact (h1.sub h2).indicator (h0 _ hG)

end IsGaussianExploration

end InteractingSLE.Sec6.Prop65
