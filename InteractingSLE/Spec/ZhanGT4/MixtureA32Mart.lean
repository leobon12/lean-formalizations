/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA32Field

/-!
# A.3.2, (G2): the martingale `M_t(u) = f(X_t(u)) ∂_u X_t(u)` and its Girsanov transform

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L670–L693, ruling R38; follow-up note pp. 12–13):

> Set `f(u) = Z⁻¹ e^{2σu/κ} cosh(u/2)^{−4/κ}`. For the upper-point flow `X_t(u) = Re ψ_t(u + iπ) − ξ_t`,
> `dX_t = −√κ dB_t + [tanh(X_t/2) − σ] dt`, one has `∂_t ∂_u X_t = ½ sech²(X_t/2) ∂_u X_t`. Itô gives
>   `M_t(u) = f(X_t(u)) ∂_u X_t(u)`,  `dM_t(u)/M_t(u) = −(2/√κ) [σ − tanh(X_t(u)/2)] dB_t`.            (G2)
> The function `f` is bounded, and `∂_u X_t ≤ e^{t/2}`; hence `M_t(u)` is a true martingale on every fixed finite
> horizon. Girsanov with density `M_t(u)/f(u)` changes the strip driver to
> `dξ_t = √κ dB̂_t − σ dt + 2 tanh(X_t(u)/2) dt` … The map `u ↦ X_t(u)` is an increasing bijection of `ℝ`, so
> `∫_ℝ M_t(u) du = 1`.

## Setting

`B` is a Brownian motion of a filtration `𝓕` with every path continuous and `B_0 = 0`, `0 < κ`, `|σ| < 1` (in the
source `σ = 3 − κ/2 ∈ (−1, 1)` for `4 < κ < 8`), the strip driver is `ξ_t = √κ B_t + σ t` (`stripDrv`), and
`X_t(u) = upFlow ξ u t` (`MixtureA32Flow.lean`; `∂_u X_t(u) = upDeriv ξ u t`, `hasDerivAt_upFlow`).

## Main results

* `mixDensity κ σ` (`f`), `integral_mixDensity` (`∫ f = 1`), `mixMart κ σ B u t ω` (**`M_t(u) = f(X_t(u)) ∂_u X_t(u)`**);
* `mixMart_zero`: `M_0(u) = f(u)`; `mixMart_le`: `M_t(u) ≤ (sup f) e^{t/2}`;
* **`lintegral_mixMart`**: `∫_ℝ M_t(u) du = 1` for every path and every `t`;
* **`martingale_mixMart`**: `t ↦ M_t(u)` is an `𝓕`-martingale (a true martingale);
* **`isFilteredBrownianReal_mixBM`** (Girsanov, the content of the `dB` coefficient in (G2)): under
  `Q_u^T = (M_T(u)/f(u)) · P` (`mixMeasure`, a probability measure), `B̂_t = B_t + ∫₀^{t∧T} (2/√κ)(σ − tanh(X_s(u)/2)) ds`
  (`mixBM`) is a Brownian motion of `𝓕`;
* **`stripDrv_eq_forced`**: for `t ≤ T`, `ξ_t = √κ B̂_t − σ t + 2 ∫₀ᵗ tanh(X_s(u)/2) ds` — the strip driver with charge
  `−4` at `u + iπ`.

The stochastic-integral form of (G2) (`M_t/M_0` equal to the Doléans exponential of `−(2/√κ)(σ − tanh(X/2)) · B`) is
not stated: its only use in the source is the Girsanov step, which is proved here directly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

/-! ### The mixture density -/

/-- The normalizing constant `Z = ∫ w_σ`. -/
def mixZ (κ σ : ℝ) : ℝ := ∫ x, Zhan.scaleDensity κ σ x

/-- **The mixture density** `f(u) = Z⁻¹ e^{2σu/κ} cosh(u/2)^{−4/κ}`. -/
def mixDensity (κ σ u : ℝ) : ℝ := Zhan.scaleDensity κ σ u / mixZ κ σ

variable {κ σ : ℝ}

theorem mixZ_pos (hκ : 0 < κ) (hσ : |σ| < 1) : 0 < mixZ κ σ := by
  have hi := Zhan.integrable_scaleDensity hκ hσ
  rw [mixZ, integral_pos_iff_support_of_nonneg (fun x => (Zhan.scaleDensity_pos κ σ x).le) hi]
  have : Function.support (Zhan.scaleDensity κ σ) = univ := by
    ext x; simp [Function.mem_support, (Zhan.scaleDensity_pos κ σ x).ne']
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

theorem mixDensity_pos (hκ : 0 < κ) (hσ : |σ| < 1) (u : ℝ) : 0 < mixDensity κ σ u :=
  div_pos (Zhan.scaleDensity_pos κ σ u) (mixZ_pos hκ hσ)

theorem integral_mixDensity (hκ : 0 < κ) (hσ : |σ| < 1) : ∫ u, mixDensity κ σ u = 1 := by
  simp only [mixDensity]
  rw [integral_div, ← mixZ, div_self (mixZ_pos hκ hσ).ne']

theorem integrable_mixDensity (hκ : 0 < κ) (hσ : |σ| < 1) : Integrable (mixDensity κ σ) :=
  (Zhan.integrable_scaleDensity hκ hσ).div_const _

theorem lintegral_mixDensity (hκ : 0 < κ) (hσ : |σ| < 1) : ∫⁻ u, ENNReal.ofReal (mixDensity κ σ u) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_mixDensity hκ hσ)
    (Eventually.of_forall fun u => (mixDensity_pos hκ hσ u).le), integral_mixDensity hκ hσ, ENNReal.ofReal_one]

theorem continuous_mixDensity : Continuous (mixDensity κ σ) := (Zhan.continuous_scaleDensity κ σ).div_const _

theorem mixDensity_le (hκ : 0 < κ) (hσ : |σ| < 1) (u : ℝ) :
    mixDensity κ σ u ≤ Real.exp (4 / κ * Real.log 2) / mixZ κ σ :=
  div_le_div_of_nonneg_right (by rw [← exp_logDens]; exact Real.exp_le_exp.2 (logDens_le hκ hσ.le u))
    (mixZ_pos hκ hσ).le

/-! ### The martingale `M_t(u)` and the tilted objects -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **(G2): `M_t(u) = f(X_t(u)) ∂_u X_t(u)`.** -/
def mixMart (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  mixDensity κ σ (upFlow (stripDrv κ σ B ω) u t) * upDeriv (stripDrv κ σ B ω) u t

/-- The Girsanov drift rate `θ_s(u) = (2/√κ)(σ − tanh(X_s(u)/2))`. -/
def mixTheta (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  2 / Real.sqrt κ * (σ - Real.tanh (upFlow (stripDrv κ σ B ω) u s / 2))

/-- **The Brownian motion of the tilted law**, `B̂_t = B_t + ∫₀^{t∧T} θ_s(u) ds`. -/
def mixBM (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  B t ω + ∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), mixTheta κ σ B u s ω

/-- **The tilted measure** `Q_u^T = (M_T(u)/f(u)) · P`. -/
def mixMeasure (P : Measure Ω) (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (T : ℝ≥0) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (mixMart κ σ B u T ω / mixDensity κ σ u)

theorem mixMart_pos (hκ : 0 < κ) (hσ : |σ| < 1) (u : ℝ) (t : ℝ≥0) (ω : Ω) : 0 < mixMart κ σ B u t ω :=
  mul_pos (mixDensity_pos hκ hσ _) (upDeriv_pos _ _)

theorem mixMart_zero {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω = 0) (u : ℝ) :
    mixMart κ σ B u 0 ω = mixDensity κ σ u := by
  have hξ := continuous_stripDrv (κ := κ) (σ := σ) hc
  simp only [mixMart, NNReal.coe_zero, upFlow_zero hξ (stripDrv_zero h0), upDeriv,
    intervalIntegral.integral_same, Real.exp_zero, mul_one]

/-- `M_t(u) ≤ (sup f) e^{t/2}` ("`f` is bounded, and `∂_u X_t ≤ e^{t/2}`"). -/
theorem mixMart_le (hκ : 0 < κ) (hσ : |σ| < 1) {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ) (t : ℝ≥0) :
    mixMart κ σ B u t ω ≤ Real.exp (4 / κ * Real.log 2) / mixZ κ σ * Real.exp (t / 2) :=
  mul_le_mul (mixDensity_le hκ hσ _) (upDeriv_le (continuous_stripDrv hc) u t.coe_nonneg)
    (upDeriv_pos _ _).le (div_pos (Real.exp_pos _) (mixZ_pos hκ hσ)).le

/-- **`∫_ℝ M_t(u) du = 1`**, for every path and every time. -/
theorem lintegral_mixMart (hκ : 0 < κ) (hσ : |σ| < 1) {ω : Ω} (hc : Continuous (B · ω)) (t : ℝ≥0) :
    ∫⁻ u, ENNReal.ofReal (mixMart κ σ B u t ω) = 1 := by
  have h := lintegral_upDeriv_mul_comp (continuous_stripDrv (κ := κ) (σ := σ) hc) t.coe_nonneg
    (fun x => ENNReal.ofReal (mixDensity κ σ x))
  rw [lintegral_mixDensity hκ hσ] at h
  rw [← h]
  refine lintegral_congr fun u => ?_
  rw [mixMart, mul_comm, ENNReal.ofReal_mul (upDeriv_pos _ _).le]

/-! ### Identification with the frozen-curve Girsanov objects -/

section Ident

variable {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω = 0) (u : ℝ)
include hc h0

omit hc in
theorem mixEll_zero_driver : mixEll κ σ B u ω 0 (Real.sqrt κ * B 0 ω) = logDens κ σ u := by
  simp only [mixEll, lamX_zero, gamX_zero, h0, mul_zero, add_zero, sub_zero]

theorem exp_mixEll_sub (hκ : 0 < κ) (hσ : |σ| < 1) (t : ℝ≥0) :
    Real.exp (mixEll κ σ B u ω t (Real.sqrt κ * B t ω) - mixEll κ σ B u ω 0 (Real.sqrt κ * B 0 ω)) =
      mixMart κ σ B u t ω / mixDensity κ σ u := by
  have hd := mixEll_driver (κ := κ) (σ := σ) hc u t.coe_nonneg
  rw [Real.toNNReal_coe] at hd
  rw [hd, mixEll_zero_driver h0 u, mixMart, mixDensity, mixDensity, sub_eq_add_neg, Real.exp_add, Real.exp_add,
    exp_logDens, exp_gamX u t.coe_nonneg, Real.exp_neg, exp_logDens]
  have hZ := mixZ_pos hκ hσ
  have hs := Zhan.scaleDensity_pos κ σ u
  field_simp

end Ident

/-! ### (G2): the true martingale and the Girsanov transform -/

section G2

variable {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- The constants of the localization (`MixtureA32Loc.lean`). -/
theorem loc_bounds (hκ : 0 < κ) (hσ : |σ| < 1) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (u : ℝ)
    (T : ℝ≥0) :
    (∀ ω (r : ℝ≥0), r ≤ T → mixEll κ σ B u ω r (Real.sqrt κ * B r ω) - mixEll κ σ B u ω 0 (Real.sqrt κ * B 0 ω) ≤
        4 / κ * Real.log 2 + T / 2 - logDens κ σ u) ∧
      ∀ ω (r : ℝ≥0), r ≤ T → |Real.sqrt κ * mixEllX κ σ B u ω r (Real.sqrt κ * B r ω)| ≤
        Real.sqrt κ * (2 / κ * (|σ| + 1)) := by
  refine ⟨fun ω r hr => ?_, fun ω r _ => ?_⟩
  · have hd := mixEll_driver (κ := κ) (σ := σ) (hBc ω) u r.coe_nonneg
    rw [Real.toNNReal_coe] at hd
    rw [hd, mixEll_zero_driver (hB0 ω) u]
    have h1 := logDens_le hκ hσ.le (upFlow (stripDrv κ σ B ω) u r)
    have h2 := gamX_le (κ := κ) (σ := σ) (hBc ω) u r.coe_nonneg
    have h3 : (r : ℝ) ≤ T := NNReal.coe_le_coe.2 hr
    linarith
  · have hd := mixEllX_driver (κ := κ) (σ := σ) (hBc ω) u r.coe_nonneg
    rw [Real.toNNReal_coe] at hd
    rw [hd, abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg κ)]
    exact mul_le_mul_of_nonneg_left (abs_dLogDens_le hκ _) (Real.sqrt_nonneg κ)

theorem girsDensity_mix (hκ : 0 < κ) (hσ : |σ| < 1) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (u : ℝ) (T : ℝ≥0) (ω : Ω) :
    girsDensity (Real.sqrt κ) B (fun _ => T) (mixEll κ σ B u) ω = mixMart κ σ B u T ω / mixDensity κ σ u :=
  exp_mixEll_sub (hBc ω) (hB0 ω) u hκ hσ T

theorem mixMeasure_eq (hκ : 0 < κ) (hσ : |σ| < 1) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (u : ℝ) (T : ℝ≥0) :
    mixMeasure P κ σ B u T = girsMeasure P (Real.sqrt κ) B (fun _ => T) (mixEll κ σ B u) := by
  simp only [mixMeasure, girsMeasure, girsDensity_mix hκ hσ hBc hB0]

theorem locN_mix (hκ : 0 < κ) (hσ : |σ| < 1) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (u : ℝ) (T t : ℝ≥0) (ω : Ω) :
    locN (Real.sqrt κ) B (fun _ => T) (mixEll κ σ B u) t ω = mixMart κ σ B u (min t T) ω / mixDensity κ σ u :=
  exp_mixEll_sub (hBc ω) (hB0 ω) u hκ hσ (min t T)

theorem girsProcess_mix (hκ : 0 < κ) (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (u : ℝ) (T t : ℝ≥0) (ω : Ω) :
    girsProcess (Real.sqrt κ) B (fun _ => T) (mixEllX κ σ B u) t ω = mixBM κ σ B u T t ω := by
  obtain ⟨n, hn⟩ := (eventually_locS_eq (κ := κ) (σ := σ) hBc u T ω).exists
  have hL := isDriverLogField_mixEll (σ := σ) (𝓕 := 𝓕) hκ hBm hBc hB0 u T n
  have hS := isStoppingTime_locS (κ := κ) (σ := σ) hBm hBc u T n
  rw [← girsProcess_congr (S := locS κ σ B u T n) hn t, girsProcess, hL.drvInt_min hBc one_pos hS ω t, hn,
    IsDriverLogField.drvInt_eq ω ⟨(min t T).coe_nonneg, by rw [hn]; exact NNReal.coe_le_coe.2 (min_le_right _ _)⟩,
    mixBM, sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (min t T).coe_nonneg] at hs
  have hd := mixEllX_driver (κ := κ) (σ := σ) (hBc ω) u hs.1
  simp only [drvRate, hd, mixTheta, dLogDens]
  have hk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hk2 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have key : Real.sqrt κ * (2 / κ) = 2 / Real.sqrt κ := by
    field_simp
    linarith [Real.sq_sqrt hκ.le, Real.mul_self_sqrt hκ.le]
  linear_combination (σ - Real.tanh (upFlow (stripDrv κ σ B ω) u s / 2)) * key

/-- **(G2): `M(u)` is a true martingale.** -/
theorem martingale_mixMart (hκ : 0 < κ) (hσ : |σ| < 1) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (u : ℝ) :
    Martingale (mixMart κ σ B u) 𝓕 P := by
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => hB.2.1 t
  have hLB := loc_bounds hκ hσ hBc hB0 u
  have hM : ∀ T : ℝ≥0, Martingale (locN (Real.sqrt κ) B (fun _ => T) (mixEll κ σ B u)) 𝓕 P := fun T =>
    martingale_locN_const hB hBc (Real.sqrt_pos.2 hκ) one_pos
      (fun n => isDriverLogField_mixEll (σ := σ) hκ hBm hBc hB0 u T n)
      (fun n => isStoppingTime_locS hBm hBc u T n) (fun n ω => locS_le u T n ω)
      (fun ω => eventually_locS_eq hBc u T ω) (hLB T).1 (by positivity) (hLB T).2
  have hf := (mixDensity_pos hκ hσ u).ne'
  have e : ∀ T : ℝ≥0, ∀ t ≤ T, mixMart κ σ B u t =
      mixDensity κ σ u • locN (Real.sqrt κ) B (fun _ => T) (mixEll κ σ B u) t := fun T t ht => by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul, locN_mix hκ hσ hBc hB0, min_eq_left ht]
    field_simp
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · rw [e t t le_rfl]; exact ((hM t).stronglyAdapted t).const_smul _
  · rw [e t t le_rfl, e t s hst]
    exact (condExp_smul (μ := P) (mixDensity κ σ u) _ _).trans (((hM t).condExp_ae_eq hst).const_smul _)

/-- **(G2), Girsanov**: under `Q_u^T = (M_T(u)/f(u)) · P` the process `B̂ = B + ∫₀^{·∧T} θ(u)` is a Brownian motion of
`𝓕`, and `Q_u^T` is a probability measure. -/
theorem isFilteredBrownianReal_mixBM (hκ : 0 < κ) (hσ : |σ| < 1) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (u : ℝ) (T : ℝ≥0) :
    IsProbabilityMeasure (mixMeasure P κ σ B u T) ∧
      IsFilteredBrownianReal 𝓕 (mixBM κ σ B u T) (mixMeasure P κ σ B u T) := by
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => hB.2.1 t
  obtain ⟨hC, hC'⟩ := loc_bounds hκ hσ hBc hB0 u T
  have h := isFilteredBrownianReal_girsProcess_const hB hBc (Real.sqrt_pos.2 hκ) one_pos
    (fun n => isDriverLogField_mixEll (σ := σ) hκ hBm hBc hB0 u T n)
    (fun n => isStoppingTime_locS hBm hBc u T n) (fun n ω => locS_le u T n ω)
    (fun ω => eventually_locS_eq hBc u T ω) hC (by positivity) hC'
  have e : girsProcess (Real.sqrt κ) B (fun _ => T) (mixEllX κ σ B u) = mixBM κ σ B u T := by
    funext t ω; exact girsProcess_mix hκ hBm hBc hB0 u T t ω
  rw [mixMeasure_eq hκ hσ hBc hB0, ← e]
  exact h

/-- **The forced strip driver** (the source's `dξ_t = √κ dB̂_t − σ dt + 2 tanh(X_t(u)/2) dt`): for `t ≤ T`,
`ξ_t = √κ B̂_t − σ t + 2 ∫₀ᵗ tanh(X_s(u)/2) ds` — strip SLE with charge `−4` at `u + iπ`. -/
theorem stripDrv_eq_forced (hκ : 0 < κ) {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    stripDrv κ σ B ω t =
      Real.sqrt κ * mixBM κ σ B u T t ω - σ * t +
        2 * ∫ s in (0 : ℝ)..t, Real.tanh (upFlow (stripDrv κ σ B ω) u s / 2) := by
  have hX := (continuousOn_upFlow (continuous_stripDrv (κ := κ) (σ := σ) hc) u).mono
    (Icc_subset_Ici_self : Icc (0 : ℝ) t ⊆ Ici 0)
  have hi : IntervalIntegrable (fun s => Real.tanh (upFlow (stripDrv κ σ B ω) u s / 2)) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le t.coe_nonneg]
    exact continuous_tanh_half.comp_continuousOn hX
  have hθ : ∫ s in (0 : ℝ)..t, mixTheta κ σ B u s ω =
      2 / Real.sqrt κ * (σ * t - ∫ s in (0 : ℝ)..t, Real.tanh (upFlow (stripDrv κ σ B ω) u s / 2)) := by
    simp only [mixTheta]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [mixBM, min_eq_left ht, hθ, stripDrv, Real.toNNReal_coe]
  field_simp
  ring

end G2

end InteractingSLE.ZhanGT4.Mix
