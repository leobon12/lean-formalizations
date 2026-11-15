/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA32Flow
import InteractingSLE.Spec.ZhanGT4.MixtureA32Loc
import InteractingSLE.Spec.Zhan.ConstDriftGapProc

/-!
# A.3.2: `log M_t(u)` is a driver log-field along the strip Brownian motion, with a localizing sequence

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L670–L684, ruling R38). The strip driver is
`ξ_t = √κ B_t + σ t` (`stripDrv`) for a Brownian motion `B` of a filtration `𝓕`, and `X_t(u) = upFlow ξ u t`
(`MixtureA32Flow.lean`). With `L = log w_σ`, `w_σ(y) = e^{2σy/κ} cosh(y/2)^{−4/κ}` (`Zhan.scaleDensity`), the logarithm of
`M_t(u)/f(u) = w_σ(X_t(u)) ∂_u X_t(u) / w_σ(u)` is `ℓ(t, √κ B_t) − ℓ(0, 0)` for the field

  `ℓ(t, x) = L(u + Λ_t − x) + Γ_t`,  `Λ_t = ∫₀ᵗ (tanh(X_s/2) − σ) ds`,  `Γ_t = ∫₀ᵗ ½ sech²(X_s/2) ds`

(`mixEll`; `u + Λ_t − √κ B_t = X_t`, `add_lamX_sub`). Its generator vanishes along the driver
(`mixEll_gen`: the drift identity of (G2), `L′(tanh − σ) + ½ sech² + (κ/2)(L″ + L′²) = 0`), and up to the exit time
`S_n` of `|X| ≤ n + 1 + |u|` (capped at `T`, `locS`) it is a regular log-field (`isDriverLogField_mixEll`).
Every path has `S_n = T` for large `n` (`eventually_locS_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

/-! ### The log scale density and its derivatives -/

/-- `L(y) = log w_σ(y) = 2σy/κ − (4/κ) log cosh(y/2)`. -/
def logDens (κ σ y : ℝ) : ℝ := 2 * σ * y / κ - 4 / κ * Real.log (Real.cosh (y / 2))

/-- `L′(y) = (2/κ)(σ − tanh(y/2))`. -/
def dLogDens (κ σ y : ℝ) : ℝ := 2 / κ * (σ - Real.tanh (y / 2))

/-- `L″(y) = −(2/κ) · ½ sech²(y/2)`. -/
def ddLogDens (κ y : ℝ) : ℝ := -(2 / κ) * sechHalf y

/-- `L‴(y) = (2/κ) sinh y/(1 + cosh y)²`. -/
def dddLogDens (κ y : ℝ) : ℝ := 2 / κ * (Real.sinh y / (1 + Real.cosh y) ^ 2)

variable {κ σ : ℝ}

theorem exp_logDens (κ σ y : ℝ) : Real.exp (logDens κ σ y) = Zhan.scaleDensity κ σ y := rfl

theorem hasDerivAt_logDens (y : ℝ) : HasDerivAt (logDens κ σ) (dLogDens κ σ y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * σ * y / κ) (2 * σ / κ) y := by
    simpa using ((hasDerivAt_id y).const_mul (2 * σ)).div_const κ
  refine (h1.sub ((Zhan.hasDerivAt_log_cosh_half y).const_mul (4 / κ))).congr_deriv ?_
  simp only [dLogDens]; ring

theorem hasDerivAt_dLogDens (y : ℝ) : HasDerivAt (dLogDens κ σ) (ddLogDens κ y) y := by
  refine (((hasDerivAt_tanh_half y).const_sub σ).const_mul (2 / κ)).congr_deriv ?_
  simp only [ddLogDens]; ring

theorem hasDerivAt_ddLogDens (y : ℝ) : HasDerivAt (ddLogDens κ) (dddLogDens κ y) y := by
  refine ((hasDerivAt_sechHalf y).const_mul (-(2 / κ))).congr_deriv ?_
  simp only [dddLogDens]; ring

theorem continuous_logDens : Continuous (logDens κ σ) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_logDens y).continuousAt

theorem continuous_dLogDens : Continuous (dLogDens κ σ) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_dLogDens y).continuousAt

theorem continuous_ddLogDens : Continuous (ddLogDens κ) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_ddLogDens y).continuousAt

theorem continuous_dddLogDens : Continuous (dddLogDens κ) := by
  unfold dddLogDens
  exact continuous_const.mul (Real.continuous_sinh.div ((continuous_const.add Real.continuous_cosh).pow 2)
    fun y => (pow_pos (one_add_cosh_pos y) 2).ne')

theorem abs_dLogDens_le (hκ : 0 < κ) (y : ℝ) : |dLogDens κ σ y| ≤ 2 / κ * (|σ| + 1) := by
  rw [dLogDens, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / κ)]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (by positivity)
  linarith [(Real.abs_tanh_lt_one (y / 2)).le]

theorem abs_ddLogDens_le (hκ : 0 < κ) (y : ℝ) : |ddLogDens κ y| ≤ 1 / κ := by
  rw [ddLogDens, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 / κ),
    abs_of_pos (sechHalf_pos y)]
  have := sechHalf_le y
  calc 2 / κ * sechHalf y ≤ 2 / κ * (1 / 2) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 / κ := by ring

theorem abs_dddLogDens_le (hκ : 0 < κ) (y : ℝ) : |dddLogDens κ y| ≤ 1 / κ := by
  have h := abs_deriv_sechHalf_le y
  rw [neg_div, abs_neg] at h
  rw [dddLogDens, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / κ)]
  calc 2 / κ * |Real.sinh y / (1 + Real.cosh y) ^ 2| ≤ 2 / κ * (1 / 4) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / κ / 2 := by ring
    _ ≤ 1 / κ := by have := one_div_pos.2 hκ; linarith

theorem abs_logDens_le (hκ : 0 < κ) (y : ℝ) : |logDens κ σ y| ≤ 2 * (|σ| + 1) / κ * |y| := by
  have hc0 : 0 ≤ Real.log (Real.cosh (y / 2)) := Real.log_nonneg (Real.one_le_cosh _)
  have hc1 := Zhan.log_cosh_le_abs (y / 2)
  rw [abs_div, abs_two] at hc1
  rw [logDens]
  refine (abs_sub _ _).trans ?_
  have e1 : |2 * σ * y / κ| = 2 * |σ| / κ * |y| := by
    rw [abs_div, abs_mul, abs_mul, abs_two, abs_of_pos hκ]; ring
  have e2 : |4 / κ * Real.log (Real.cosh (y / 2))| = 4 / κ * Real.log (Real.cosh (y / 2)) := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) hc0)]
  rw [e1, e2]
  have h4 : 4 / κ * Real.log (Real.cosh (y / 2)) ≤ 4 / κ * (|y| / 2) :=
    mul_le_mul_of_nonneg_left hc1 (by positivity)
  have e3 : 2 * (|σ| + 1) / κ * |y| = 2 * |σ| / κ * |y| + 4 / κ * (|y| / 2) := by ring
  linarith

/-- For `|σ| ≤ 1`, `L ≤ (4/κ) log 2` (`w_σ` is bounded). -/
theorem logDens_le (hκ : 0 < κ) (hσ : |σ| ≤ 1) (y : ℝ) : logDens κ σ y ≤ 4 / κ * Real.log 2 := by
  have h := Zhan.abs_div_two_sub_log_two_le_log_cosh (y / 2)
  rw [abs_div, abs_two] at h
  have hσy : σ * y ≤ |y| := (le_abs_self _).trans (by rw [abs_mul]; nlinarith [abs_nonneg y])
  have h4 : 4 / κ * (|y| / 2 - Real.log 2) ≤ 4 / κ * Real.log (Real.cosh (y / 2)) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e : 2 * σ * y / κ = 2 / κ * (σ * y) := by ring
  have h5 : 2 / κ * (σ * y) ≤ 2 / κ * |y| := mul_le_mul_of_nonneg_left hσy (by positivity)
  rw [logDens, e]
  have e2 : 4 / κ * (|y| / 2 - Real.log 2) = 2 / κ * |y| - 4 / κ * Real.log 2 := by ring
  linarith

/-- **The drift identity of (G2)**: `L′(y)(tanh(y/2) − σ) + ½ sech²(y/2) + (κ/2)(L″(y) + L′(y)²) = 0`. -/
theorem logDens_gen (hκ : 0 < κ) (y : ℝ) :
    dLogDens κ σ y * (Real.tanh (y / 2) - σ) + sechHalf y +
      Real.sqrt κ ^ 2 / 2 * (ddLogDens κ y + (-dLogDens κ σ y) ^ 2) = 0 := by
  rw [Real.sq_sqrt hκ.le, dLogDens, ddLogDens]
  field_simp
  ring

/-! ### The strip driver path and the time integrals -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The strip driver path** `ξ_r = √κ B_r + σ r` (`r ≥ 0`). -/
def stripDrv (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (r : ℝ) : ℝ := Real.sqrt κ * B r.toNNReal ω + σ * r

theorem continuous_stripDrv {ω : Ω} (hc : Continuous (B · ω)) : Continuous (stripDrv κ σ B ω) :=
  (continuous_const.mul (hc.comp continuous_real_toNNReal)).add (continuous_const.mul continuous_id)

theorem stripDrv_zero {ω : Ω} (h0 : B 0 ω = 0) : stripDrv κ σ B ω 0 = 0 := by
  simp [stripDrv, h0]

/-- `Λ_t = ∫₀ᵗ (tanh(X_s/2) − σ) ds` (read through `max · 0`). -/
def lamX (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (Real.tanh (upFlow (stripDrv κ σ B ω) u (max s 0) / 2) - σ)

/-- `Γ_t = ∫₀ᵗ ½ sech²(X_s/2) ds` (read through `max · 0`). -/
def gamX (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, sechHalf (upFlow (stripDrv κ σ B ω) u (max s 0))

section Path

variable {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ)
include hc

theorem hasDerivAt_lamX (t : ℝ) :
    HasDerivAt (lamX κ σ B u ω) (Real.tanh (upFlow (stripDrv κ σ B ω) u (max t 0) / 2) - σ) t :=
  ((continuous_tanh_half.comp (continuous_upFlow_max (continuous_stripDrv (κ := κ) (σ := σ) hc) u)).sub
    continuous_const).integral_hasStrictDerivAt 0 t |>.hasDerivAt

theorem hasDerivAt_gamX (t : ℝ) :
    HasDerivAt (gamX κ σ B u ω) (sechHalf (upFlow (stripDrv κ σ B ω) u (max t 0))) t :=
  (continuous_sechHalf.comp (continuous_upFlow_max (continuous_stripDrv (κ := κ) (σ := σ) hc) u)).integral_hasStrictDerivAt 0 t
    |>.hasDerivAt

theorem continuous_lamX : Continuous (lamX κ σ B u ω) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_lamX hc u t).continuousAt

theorem continuous_gamX : Continuous (gamX κ σ B u ω) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gamX hc u t).continuousAt

omit hc in
theorem gamX_eq {t : ℝ} (ht : 0 ≤ t) :
    gamX κ σ B u ω t = ∫ s in (0 : ℝ)..t, sechHalf (upFlow (stripDrv κ σ B ω) u s) :=
  intervalIntegral.integral_congr fun s hs => by
    rw [uIcc_of_le ht] at hs
    simp only [max_eq_left hs.1]

omit hc in
theorem exp_gamX {t : ℝ} (ht : 0 ≤ t) : Real.exp (gamX κ σ B u ω t) = upDeriv (stripDrv κ σ B ω) u t := by
  rw [gamX_eq u ht, upDeriv]

omit hc in
theorem gamX_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gamX κ σ B u ω t :=
  intervalIntegral.integral_nonneg ht fun _ _ => (sechHalf_pos _).le

theorem gamX_le {t : ℝ} (ht : 0 ≤ t) : gamX κ σ B u ω t ≤ t / 2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) ht
    (f := fun s => sechHalf (upFlow (stripDrv κ σ B ω) u (max s 0)))
    ((continuous_sechHalf.comp (continuous_upFlow_max (continuous_stripDrv (κ := κ) (σ := σ) hc) u)).intervalIntegrable 0 t)
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) fun s _ => sechHalf_le _
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  unfold gamX; linarith

/-- **`u + Λ_t − √κ B_t = X_t(u)`** for `t ≥ 0`. -/
theorem add_lamX_sub {t : ℝ} (ht : 0 ≤ t) :
    u + lamX κ σ B u ω t - Real.sqrt κ * B t.toNNReal ω = upFlow (stripDrv κ σ B ω) u t := by
  have hξ := continuous_stripDrv (κ := κ) (σ := σ) hc
  have hi : IntervalIntegrable (fun s => Real.tanh (upFlow (stripDrv κ σ B ω) u (max s 0) / 2)) volume 0 t :=
    (continuous_tanh_half.comp (continuous_upFlow_max hξ u)).intervalIntegrable _ _
  have hcongr : ∫ s in (0 : ℝ)..t, Real.tanh (upFlow (stripDrv κ σ B ω) u (max s 0) / 2) =
      ∫ s in (0 : ℝ)..t, Real.tanh (upFlow (stripDrv κ σ B ω) u s / 2) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le ht] at hs
      simp only [max_eq_left hs.1]
  rw [lamX, intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul, hcongr, upFlow_eq hξ u ht, stripDrv]
  ring

omit hc in
theorem lamX_zero : lamX κ σ B u ω 0 = 0 := intervalIntegral.integral_same

omit hc in
theorem gamX_zero : gamX κ σ B u ω 0 = 0 := intervalIntegral.integral_same

end Path

/-! ### The log-field -/

/-- **The log-field** `ℓ(t, x) = L(u + Λ_t − x) + Γ_t`. -/
def mixEll (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  logDens κ σ (u + lamX κ σ B u ω t - x) + gamX κ σ B u ω t

/-- `ℓ_x = −L′(u + Λ_t − x)`. -/
def mixEllX (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  -dLogDens κ σ (u + lamX κ σ B u ω t - x)

/-- `ℓ_xx = L″(u + Λ_t − x)`. -/
def mixEllXX (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  ddLogDens κ (u + lamX κ σ B u ω t - x)

/-- `ℓ_xxx = −L‴(u + Λ_t − x)`. -/
def mixEllXXX (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  -dddLogDens κ (u + lamX κ σ B u ω t - x)

/-- `ℓ_t = L′(u + Λ_t − x)(tanh(X_t/2) − σ) + ½ sech²(X_t/2)`. -/
def mixEllT (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  dLogDens κ σ (u + lamX κ σ B u ω t - x) * (Real.tanh (upFlow (stripDrv κ σ B ω) u (max t 0) / 2) - σ) +
    sechHalf (upFlow (stripDrv κ σ B ω) u (max t 0))

section Field

variable {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ)
include hc

theorem mixEll_driver {t : ℝ} (ht : 0 ≤ t) :
    mixEll κ σ B u ω t (Real.sqrt κ * B t.toNNReal ω) =
      logDens κ σ (upFlow (stripDrv κ σ B ω) u t) + gamX κ σ B u ω t := by
  rw [mixEll, add_lamX_sub hc u ht]

theorem mixEllX_driver {t : ℝ} (ht : 0 ≤ t) :
    mixEllX κ σ B u ω t (Real.sqrt κ * B t.toNNReal ω) = -dLogDens κ σ (upFlow (stripDrv κ σ B ω) u t) := by
  rw [mixEllX, add_lamX_sub hc u ht]

theorem mixEllXX_driver {t : ℝ} (ht : 0 ≤ t) :
    mixEllXX κ σ B u ω t (Real.sqrt κ * B t.toNNReal ω) = ddLogDens κ (upFlow (stripDrv κ σ B ω) u t) := by
  rw [mixEllXX, add_lamX_sub hc u ht]

/-- **The generator vanishes along the driver** (the (G2) drift identity). -/
theorem mixEll_gen (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) :
    mixEllT κ σ B u ω t (Real.sqrt κ * B t.toNNReal ω) + Real.sqrt κ ^ 2 / 2 *
      (mixEllXX κ σ B u ω t (Real.sqrt κ * B t.toNNReal ω) +
        mixEllX κ σ B u ω t (Real.sqrt κ * B t.toNNReal ω) ^ 2) = 0 := by
  rw [mixEllXX_driver hc u ht, mixEllX_driver hc u ht, mixEllT, add_lamX_sub hc u ht, max_eq_left ht]
  have h := logDens_gen (σ := σ) hκ (upFlow (stripDrv κ σ B ω) u t)
  linarith

/-- The log-field is a regular log-field on every rectangle, with the bound `K` as soon as the argument
`u + Λ_t − x` stays in `[−R', R']` and `t ≤ T`. -/
theorem isLogField_mixEll (hκ : 0 < κ) {b c y ρ R' T : ℝ} (hρ : 0 < ρ) (hb : 0 ≤ b) (hT : 0 ≤ T) (hcT : c ≤ T)
    (harg : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → |u + lamX κ σ B u ω t - x| ≤ R') :
    IsLogField (mixEll κ σ B u ω) (mixEllX κ σ B u ω) (mixEllXX κ σ B u ω) (mixEllXXX κ σ B u ω)
      (mixEllT κ σ B u ω) b c y ρ
      (2 * (|σ| + 1) / κ * |R'| + T / 2 + 2 / κ * (|σ| + 1) * (|σ| + 1) + 2 / κ * (|σ| + 1) + 1 / κ + 1) := by
  have hξ := continuous_stripDrv (κ := κ) (σ := σ) hc
  have hXc := continuous_upFlow_max hξ u
  have hL := continuous_lamX (κ := κ) (σ := σ) hc u
  have hG := continuous_gamX (κ := κ) (σ := σ) hc u
  have harg' : Continuous fun p : ℝ × ℝ => u + lamX κ σ B u ω p.1 - p.2 :=
    (continuous_const.add (hL.comp continuous_fst)).sub continuous_snd
  have hin : ∀ t x : ℝ, HasDerivAt (fun x => u + lamX κ σ B u ω t - x) (-1) x := fun t x => by
    simpa using (hasDerivAt_id x).const_sub (u + lamX κ σ B u ω t)
  have hσ1 : 0 ≤ |σ| + 1 := by positivity
  have hK0 : 0 ≤ 2 / κ * (|σ| + 1) * (|σ| + 1) := by positivity
  refine ⟨hρ, by positivity, fun t _ x _ => ?_, fun t _ x _ => ?_, fun t _ x _ => ?_, fun t _ x _ => ?_,
    ?_, ?_, ?_, ?_, fun t ht x hx => ?_⟩
  · refine ((hasDerivAt_logDens _).comp x (hin t x)).add_const _ |>.congr_deriv ?_
    simp only [mixEllX]; ring
  · refine ((hasDerivAt_dLogDens _).comp x (hin t x)).neg.congr_deriv ?_
    simp only [mixEllXX]; ring
  · refine ((hasDerivAt_ddLogDens _).comp x (hin t x)).congr_deriv ?_
    simp only [mixEllXXX]; ring
  · have hlt : HasDerivAt (fun s => u + lamX κ σ B u ω s - x)
        (Real.tanh (upFlow (stripDrv κ σ B ω) u (max t 0) / 2) - σ) t := by
      simpa using ((hasDerivAt_lamX hc u t).const_add u).sub_const x
    exact (((hasDerivAt_logDens _).comp t hlt).add (hasDerivAt_gamX hc u t)).hasDerivWithinAt
  · exact ((continuous_logDens.comp harg').add (hG.comp continuous_fst)).continuousOn
  · exact (continuous_dLogDens.comp harg').neg.continuousOn
  · exact (continuous_ddLogDens.comp harg').continuousOn
  · exact ((continuous_dLogDens.comp harg').mul
      ((continuous_tanh_half.comp (hXc.comp continuous_fst)).sub continuous_const)).add
      (continuous_sechHalf.comp (hXc.comp continuous_fst)) |>.continuousOn
  · have ht0 : 0 ≤ t := hb.trans ht.1
    have hz := harg t ht x hx
    set z := u + lamX κ σ B u ω t - x
    have hzR : |z| ≤ |R'| := hz.trans (le_abs_self _)
    have h1 : |logDens κ σ z| ≤ 2 * (|σ| + 1) / κ * |R'| :=
      (abs_logDens_le hκ z).trans (mul_le_mul_of_nonneg_left hzR (by positivity))
    have h2 : |gamX κ σ B u ω t| ≤ T / 2 := by
      rw [abs_of_nonneg (gamX_nonneg u ht0)]
      linarith [gamX_le (κ := κ) (σ := σ) hc u ht0, ht.2, hcT]
    have h3 := abs_dLogDens_le (σ := σ) hκ z
    have h4 := abs_ddLogDens_le hκ z
    have h5 := abs_dddLogDens_le hκ z
    have h6 : |Real.tanh (upFlow (stripDrv κ σ B ω) u (max t 0) / 2) - σ| ≤ |σ| + 1 := by
      refine (abs_sub _ _).trans ?_
      linarith [(Real.abs_tanh_lt_one (upFlow (stripDrv κ σ B ω) u (max t 0) / 2)).le]
    have h7 : |sechHalf (upFlow (stripDrv κ σ B ω) u (max t 0))| ≤ 1 := by
      rw [abs_of_pos (sechHalf_pos _)]; linarith [sechHalf_le (upFlow (stripDrv κ σ B ω) u (max t 0))]
    have hκi : 0 ≤ 1 / κ := by positivity
    have hA0 : 0 ≤ 2 * (|σ| + 1) / κ * |R'| := by positivity
    have hT0 : 0 ≤ T / 2 := by linarith [ht.2, ht.1, hb]
    have hd0 : 0 ≤ 2 / κ * (|σ| + 1) := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [mixEll]
      calc |logDens κ σ z + gamX κ σ B u ω t| ≤ |logDens κ σ z| + |gamX κ σ B u ω t| := abs_add_le _ _
        _ ≤ _ := by linarith
    · simp only [mixEllX, abs_neg]; linarith
    · simp only [mixEllXX]; linarith
    · simp only [mixEllXXX, abs_neg]; linarith
    · simp only [mixEllT]
      have h8 : |dLogDens κ σ z * (Real.tanh (upFlow (stripDrv κ σ B ω) u (max t 0) / 2) - σ)| ≤
          2 / κ * (|σ| + 1) * (|σ| + 1) := by
        rw [abs_mul]; exact mul_le_mul h3 h6 (abs_nonneg _) hd0
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ 2 / κ * (|σ| + 1) * (|σ| + 1) + 1 := add_le_add h8 h7
        _ ≤ _ := by linarith

end Field

/-! ### Adaptedness -/

section Adapted

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- The flow along the strip driver is the adapted upper gap `Zhan.upGapProc`. -/
theorem upFlow_stripDrv_eq {ω : Ω} (hc : Continuous (B · ω)) (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    upFlow (stripDrv κ σ B ω) u t = Zhan.upGapProc κ σ u B t.toNNReal ω := by
  have hξ := continuous_stripDrv (κ := κ) (σ := σ) hc
  refine Zhan.eqOn_upGapProc hc ht ((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self) (fun s hs => ?_)
    t ⟨ht, le_rfl⟩
  rw [upFlow_eq hξ u hs.1, stripDrv]

theorem measurable_upFlow_stripDrv (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (u : ℝ) (t : ℝ≥0) : Measurable[𝓕 t] fun ω => upFlow (stripDrv κ σ B ω) u t := by
  have e : (fun ω => upFlow (stripDrv κ σ B ω) u t) = Zhan.upGapProc κ σ u B t := by
    funext ω; rw [upFlow_stripDrv_eq (hBc ω) u t.coe_nonneg, Real.toNNReal_coe]
  rw [e]
  have h1 : Measurable[𝓕 t] fun ω => Real.sqrt κ * B t ω := (hBm t).const_mul _
  have h2 := Zhan.measurable_upGapDrift (κ := κ) (σ := σ) (q := u) hBm t
  exact (h1.const_sub u).add h2

theorem isStronglyProgressive_upFlow (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (u : ℝ) : IsStronglyProgressive 𝓕 fun (t : ℝ≥0) ω => upFlow (stripDrv κ σ B ω) u t :=
  StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (measurable_upFlow_stripDrv hBm hBc u t).stronglyMeasurable)
    fun ω => (continuousOn_upFlow (continuous_stripDrv (hBc ω)) u).comp_continuous NNReal.continuous_coe
      fun t => t.coe_nonneg

theorem measurable_gamX (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ)
    (t : ℝ≥0) : Measurable[𝓕 t] fun ω => gamX κ σ B u ω t := by
  have h := Girsanov.stronglyMeasurable_integral_comp (isStronglyProgressive_upFlow (κ := κ) (σ := σ) hBm hBc u)
    continuous_sechHalf.measurable t
  have e : (fun ω => gamX κ σ B u ω t) =
      fun ω => ∫ s in (0 : ℝ)..(t : ℝ), sechHalf (upFlow (stripDrv κ σ B ω) u (s.toNNReal : ℝ)) := by
    funext ω
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    simp only [max_eq_left hs.1, Real.coe_toNNReal _ hs.1]
  rw [e]; exact h.measurable

end Adapted

/-! ### The localizing sequence -/

section Loc

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- The level process `n + 1 + |u| − |X_t(u)|`. -/
def locY (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (n : ℝ) + 1 + |u| - |upFlow (stripDrv κ σ B ω) u t|

/-- **The localizing time** `S_n`: the first time `|X_t(u)| ≥ n + 1 + |u|`, capped at `T`. -/
def locS (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  Sec6.Prop65.hitLe (locY κ σ B u n) 0 T ω

theorem continuous_locY (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun t => locY κ σ B u n t ω :=
  continuous_const.sub (((continuousOn_upFlow (continuous_stripDrv (hBc ω)) u).comp_continuous
    NNReal.continuous_coe fun t => t.coe_nonneg).abs)

theorem isStoppingTime_locS (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ)
    (T : ℝ≥0) (n : ℕ) : IsStoppingTime 𝓕 fun ω => (locS κ σ B u T n ω : WithTop ℝ≥0) :=
  Sec6.Prop65.isStoppingTime_hitLe (continuous_locY hBc u n)
    (fun t => (by fun_prop : Continuous fun y : ℝ => (n : ℝ) + 1 + |u| - |y|).measurable.comp
      (measurable_upFlow_stripDrv (κ := κ) (σ := σ) hBm hBc u t)) 0 T

theorem locS_le (u : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : locS κ σ B u T n ω ≤ T := Sec6.Prop65.hitLe_le _ _ _ _

theorem abs_upFlow_le_of_le_locS (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (u : ℝ) (T : ℝ≥0)
    (n : ℕ) {ω : Ω} {t : ℝ≥0} (ht : t ≤ locS κ σ B u T n ω) :
    |upFlow (stripDrv κ σ B ω) u t| ≤ n + 1 + |u| := by
  have h0 : (0 : ℝ) < locY κ σ B u n 0 ω := by
    simp only [locY, NNReal.coe_zero, upFlow_zero (continuous_stripDrv (hBc ω)) (stripDrv_zero (hB0 ω))]
    linarith
  have h := Sec6.Prop65.le_of_le_hitLe (continuous_locY hBc u n) h0 ht
  simp only [locY] at h
  linarith

theorem eventually_locS_eq (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ) (T : ℝ≥0) (ω : Ω) :
    ∀ᶠ n in atTop, locS κ σ B u T n ω = T := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).exists_bound_of_continuousOn
    ((continuousOn_upFlow (continuous_stripDrv (κ := κ) (σ := σ) (hBc ω)) u).mono Icc_subset_Ici_self)
  filter_upwards [eventually_ge_atTop ⌈M⌉₊] with n hn
  refine le_antisymm (locS_le u T n ω) (Sec6.Prop65.le_hitLe_of_forall (continuous_locY hBc u n) le_rfl
    fun s hs => ?_)
  have h1 := hM s ⟨s.coe_nonneg, NNReal.coe_le_coe.2 hs⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : M ≤ n := (Nat.le_ceil M).trans (by exact_mod_cast hn)
  simp only [locY]
  linarith [abs_nonneg u]

/-- **`log M_t(u)` is a driver log-field up to each `S_n`.** -/
theorem isDriverLogField_mixEll (hκ : 0 < κ) (hBm : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (u : ℝ) (T : ℝ≥0) (n : ℕ) :
    IsDriverLogField 𝓕 (Real.sqrt κ) 1
      (2 * (|σ| + 1) / κ * |(n : ℝ) + 1 + |u| + 4| + T / 2 + 2 / κ * (|σ| + 1) * (|σ| + 1) +
        2 / κ * (|σ| + 1) + 1 / κ + 1) B (locS κ σ B u T n)
      (mixEll κ σ B u) (mixEllX κ σ B u) (mixEllXX κ σ B u) (mixEllXXX κ σ B u) (mixEllT κ σ B u) := by
  have hSm := isStoppingTime_locS (κ := κ) (σ := σ) hBm hBc u T n
  refine ⟨fun ω b c y hb hbc hcS hdr => ?_, fun ω r hr0 hrS => mixEll_gen (hBc ω) u hκ hr0,
    fun r => ?_, fun r => ?_, fun r => ?_⟩
  · refine isLogField_mixEll (hBc ω) u hκ one_pos hb T.coe_nonneg (hcS.trans (NNReal.coe_le_coe.2 (locS_le u T n ω)))
      fun t ht x hx => ?_
    have ht0 : 0 ≤ t := hb.trans ht.1
    have htS : t.toNNReal ≤ locS κ σ B u T n ω := by
      rw [Real.toNNReal_le_iff_le_coe]; exact ht.2.trans hcS
    have hX := abs_upFlow_le_of_le_locS hBc hB0 u T n htS
    rw [Real.coe_toNNReal t ht0] at hX
    have hd := hdr t ht
    have e := add_lamX_sub (κ := κ) (σ := σ) (hBc ω) u ht0
    have : u + lamX κ σ B u ω t - x =
        upFlow (stripDrv κ σ B ω) u t + (Real.sqrt κ * B t.toNNReal ω - y) + (y - x) := by linarith
    rw [this]
    calc |upFlow (stripDrv κ σ B ω) u t + (Real.sqrt κ * B t.toNNReal ω - y) + (y - x)|
        ≤ |upFlow (stripDrv κ σ B ω) u t| + |Real.sqrt κ * B t.toNNReal ω - y| + |y - x| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
      _ ≤ (n + 1 + |u|) + 1 + 3 := by
          have : |y - x| < 3 := by rw [abs_sub_comm]; linarith
          linarith
      _ = (n : ℝ) + 1 + |u| + 4 := by ring
  · have hG : MeasurableSet[𝓕 r] {ω | r ≤ locS κ σ B u T n ω} := measurableSet_ge_of_isStoppingTime hSm r
    have hm : Measurable[𝓕 r] fun ω => logDens κ σ (upFlow (stripDrv κ σ B ω) u r) + gamX κ σ B u ω r :=
      (continuous_logDens.measurable.comp (measurable_upFlow_stripDrv hBm hBc u r)).add
        (measurable_gamX hBm hBc u r)
    have e : (fun ω => mixEll κ σ B u ω r (Real.sqrt κ * B r ω)) = fun ω => logDens κ σ (upFlow (stripDrv κ σ B ω) u r) + gamX κ σ B u ω r := by
      funext ω
      have h := mixEll_driver (κ := κ) (σ := σ) (hBc ω) u r.coe_nonneg
      rwa [Real.toNNReal_coe] at h
    rw [e]; exact hm.indicator hG
  · have hG : MeasurableSet[𝓕 r] {ω | r ≤ locS κ σ B u T n ω} := measurableSet_ge_of_isStoppingTime hSm r
    have hm : Measurable[𝓕 r] fun ω => -dLogDens κ σ (upFlow (stripDrv κ σ B ω) u r) :=
      (continuous_dLogDens.measurable.comp (measurable_upFlow_stripDrv hBm hBc u r)).neg
    have e : (fun ω => mixEllX κ σ B u ω r (Real.sqrt κ * B r ω)) = fun ω => -dLogDens κ σ (upFlow (stripDrv κ σ B ω) u r) := by
      funext ω
      have h := mixEllX_driver (κ := κ) (σ := σ) (hBc ω) u r.coe_nonneg
      rwa [Real.toNNReal_coe] at h
    rw [e]; exact hm.indicator hG
  · have hG : MeasurableSet[𝓕 r] {ω | r ≤ locS κ σ B u T n ω} := measurableSet_ge_of_isStoppingTime hSm r
    have hm : Measurable[𝓕 r] fun ω => ddLogDens κ (upFlow (stripDrv κ σ B ω) u r) :=
      continuous_ddLogDens.measurable.comp (measurable_upFlow_stripDrv hBm hBc u r)
    have e : (fun ω => mixEllXX κ σ B u ω r (Real.sqrt κ * B r ω)) = fun ω => ddLogDens κ (upFlow (stripDrv κ σ B ω) u r) := by
      funext ω
      have h := mixEllXX_driver (κ := κ) (σ := σ) (hBc ω) u r.coe_nonneg
      rwa [Real.toNNReal_coe] at h
    rw [e]; exact hm.indicator hG

end Loc

end InteractingSLE.ZhanGT4.Mix
