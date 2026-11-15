/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Loc

/-!
# Aux. lemma 102: the total angular clock is finite

Packet PROVE-SEC7-C7. Specification p. 348, Aux. lemma 102: "If `s ≤ −2` or `q ≤ −2`, then the total angular clock
`∫ D_t^{-2} dt` until the continuation threshold […] is finite almost surely."

The proof here replaces the Brownian tubes of the source by a Lyapunov function. With `a = 2 + Σρ^L`,
`b = 2 + Σρ^R` (`a ≤ 0` or `b ≤ 0`), take `f = −cosh(λ(u − c))` with `f'(a/u − b/(1 − u)) + (κ/2) f'' ≤ −c₀`
on `(0, 1)` (`exists_lyap`). Along the evolution, off the Lebesgue-null collision times, the Itô generator of
`f(U)` is `(f'g + (κ/2) f'')(U)/D² + f'(U) E/D ≤ −c₀/D² + |f'|_∞ |E|/D₀` (`genExpr_le`), and the error has the
pathwise bound (P4) `∫₀^σ |E| ≤ Σ |ρ^{L,i}| (x^{L,0} − x^{L,i})/2 + Σ |ρ^{R,j}| (x^{R,j} − x^{R,0})/2`
(`integral_errAbs_le`): the reciprocal gaps integrate to the displacements of the marks, and the spreads are
nonincreasing. The localized Itô formula at `σ_n` (`martingale_angLoc`, with the stopped angular clock as the extra
coordinate, which makes it measurable) gives `c₀ E ∫₀^{σ_n} D^{-2} ≤ 2 sup|f| + sup|f'| K₁/D₀` for every `n`
(`lintegral_clock_le`), and Fatou's lemma with the exhaustion of `[0, ζ)` by the `σ_n` concludes.

## Main results

* `genExpr`, `itoGen_pathCoord_eq`, `intervalIntegrable_genExpr`, `integral_genExpr_le`;
* `clockI`, `lintegral_clock_le`;
* **`ae_bddAbove_clock`**: almost surely on `{ζ = ∞}`, `sup_t ∫₀ᵗ D^{-2} < ∞`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Clock

open Zhan

variable {nL nR : ℕ}

/-! ### Along one path -/

section Path

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The coordinates of a path at time `t`, with extra coordinate `I`. -/
def pathCoord (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (I : ℝ) (t : ℝ≥0) :
    SCoord nL (nR + 1) × ℝ :=
  ((fun i => vL i t, fun j => vR j t, I), b t)

/-- The cross-gap at time `t`. -/
def gapAt (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := vR 0 t - vL 0 t

/-- The angular coordinate at time `t`. -/
def angAt (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (w t - vL 0 t) / gapAt vL vR t

/-- The numerator of the drift of `U` at time `t`. -/
def numAt (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ)
    (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (∑ i, ρL i * (w t - vL i t)⁻¹) + (∑ j, ρR j * (w t - vR j t)⁻¹) - 2 / (vL 0 t - w t) -
    angAt w vL vR t * (2 / (vR 0 t - w t) - 2 / (vL 0 t - w t))

/-- The Itô generator of `φ(U)` along the path, at real time `s`. -/
def genExpr (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (φ' φ'' : ℝ → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  φ' (angAt w vL vR s.toNNReal) * (numAt ρL ρR w vL vR s.toNNReal / gapAt vL vR s.toNNReal) +
    κ / 2 * φ'' (angAt w vL vR s.toNNReal) / gapAt vL vR s.toNNReal ^ 2

/-- The absolute error rate (P3) at real time `s`. -/
def errAbs (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ)
    (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  (∑ i, |ρL i| * ((w s.toNNReal - vL 0 s.toNNReal)⁻¹ - (w s.toNNReal - vL i s.toNNReal)⁻¹)) +
    ∑ j, |ρR j| * ((vR 0 s.toNNReal - w s.toNNReal)⁻¹ - (vR j s.toNNReal - w s.toNNReal)⁻¹)

/-- The pathwise error constant (P4). -/
def errK (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) :
    ℝ :=
  (∑ i, |ρL i| * ((xL 0 - xL i) / 2)) + ∑ j, |ρR j| * ((xR j - xR 0) / 2)

variable (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
include hp

/-- (N1) in the coordinates: `drv = W`, so `angU = (W − V^{L,0})/D`. -/
theorem angU_pathCoord (I : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    angU κ xL xR ρL ρR (pathCoord vL vR b I t) = angAt w vL vR t := by
  have hN := hp.isForcePath.w_eq_N1 hp.driverEq ht
  simp only [angU, angAt, gapAt, gapD, pathCoord, drv, driftLin, hN]
  congr 1
  ring

theorem le_gapAt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : xR 0 - xL 0 ≤ gapAt vL vR t := by
  have hF := hp.isForcePath
  have h := hF.crossGap_le 0 0 (zero_le (a := t)) ht
  rwa [hF.vR_zero, hF.vL_zero] at h

/-- **The generator of `φ(U)` along the path**, for `t < ζ`. -/
theorem itoGen_pathCoord_eq (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {φ φ' φ'' : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (h1 : ∀ x, HasDerivAt φ (φ' x) x) (h2 : ∀ x, HasDerivAt φ' (φ'' x) x) (I c : ℝ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    Ito.itoGen (fun q => φ (angU κ xL xR ρL ρR q)) (pathCoord vL vR b I t)
        (angDens (w t) (fun i => vL i t) (fun j => vR j t) c) =
      genExpr κ ρL ρR φ' φ'' w vL vR t := by
  have hD : 0 < gapD (pathCoord vL vR b I t) := hx.trans_le (le_gapAt hp ht)
  rw [itoGen_comp_angU κ xL xR ρL ρR hκ hφ h1 h2 hD, angU_pathCoord hp I ht, driftLin₀_angDens]
  simp only [genExpr, Real.toNNReal_coe, numAt, angDens]
  rfl

omit hp in
theorem mapsTo_toNNReal {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    MapsTo Real.toNNReal (Icc 0 (σ : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun _ hr =>
  Sec2.toNNReal_lt_of_mem_Icc hσ hr

theorem continuousOn_gapAt {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    ContinuousOn (fun s : ℝ => gapAt vL vR s.toNNReal) (Icc 0 (σ : ℝ)) := by
  have hF := hp.isForcePath
  exact ((hF.continuousOn_vR 0).comp continuous_real_toNNReal.continuousOn (mapsTo_toNNReal hσ)).sub
    ((hF.continuousOn_vL 0).comp continuous_real_toNNReal.continuousOn (mapsTo_toNNReal hσ))

theorem gapAt_pos (hx : 0 < xR 0 - xL 0) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Icc 0 (σ : ℝ)) :
    0 < gapAt vL vR s.toNNReal :=
  hx.trans_le (le_gapAt hp (Sec2.toNNReal_lt_of_mem_Icc hσ hs))

theorem continuousOn_angAt (hx : 0 < xR 0 - xL 0) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    ContinuousOn (fun s : ℝ => angAt w vL vR s.toNNReal) (Icc 0 (σ : ℝ)) := by
  have hF := hp.isForcePath
  exact (((hF.continuousOn_w).comp continuous_real_toNNReal.continuousOn (mapsTo_toNNReal hσ)).sub
    ((hF.continuousOn_vL 0).comp continuous_real_toNNReal.continuousOn (mapsTo_toNNReal hσ))).div
    (continuousOn_gapAt hp hσ) fun s hs => (gapAt_pos hp hx hσ hs).ne'

theorem intervalIntegrable_numAt (hx : 0 < xR 0 - xL 0) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => numAt ρL ρR w vL vR s.toNNReal) volume 0 σ := by
  have hF := hp.isForcePath
  have hL : IntervalIntegrable (fun s : ℝ => ∑ i, ρL i * (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 σ := by
    have h := IntervalIntegrable.sum Finset.univ fun i _ => (hF.integrable_gapL hσ i).const_mul (ρL i)
    rw [Finset.sum_fn] at h; exact h
  have hR : IntervalIntegrable (fun s : ℝ => ∑ j, ρR j * (w s.toNNReal - vR j s.toNNReal)⁻¹) volume 0 σ := by
    have h := IntervalIntegrable.sum Finset.univ fun j _ => (hF.integrable_gapR hσ j).const_mul (ρR j)
    rw [Finset.sum_fn] at h; exact h
  have hU : ContinuousOn (fun s : ℝ => angAt w vL vR s.toNNReal) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]; exact continuousOn_angAt hp hx hσ
  exact ((hL.add hR).sub (hF.intervalIntegrable_forceL hσ 0)).sub
    (((hF.intervalIntegrable_forceR hσ 0).sub (hF.intervalIntegrable_forceL hσ 0)).continuousOn_mul hU)

/-- **The generator expression is integrable** on `[0, σ]`, `σ < ζ`. -/
theorem intervalIntegrable_genExpr (hx : 0 < xR 0 - xL 0) {φ' φ'' : ℝ → ℝ} (hφ' : Continuous φ')
    (hφ'' : Continuous φ'') {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    IntervalIntegrable (genExpr κ ρL ρR φ' φ'' w vL vR) volume 0 σ := by
  have hU : ContinuousOn (fun s : ℝ => angAt w vL vR s.toNNReal) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]; exact continuousOn_angAt hp hx hσ
  have hDc : ContinuousOn (fun s : ℝ => gapAt vL vR s.toNNReal) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]; exact continuousOn_gapAt hp hσ
  have hDne : ∀ s ∈ uIcc 0 (σ : ℝ), gapAt vL vR s.toNNReal ≠ 0 := fun s hs => by
    rw [uIcc_of_le σ.coe_nonneg] at hs; exact (gapAt_pos hp hx hσ hs).ne'
  have h1 : IntervalIntegrable (fun s : ℝ => φ' (angAt w vL vR s.toNNReal) *
      (numAt ρL ρR w vL vR s.toNNReal / gapAt vL vR s.toNNReal)) volume 0 σ := by
    have h := ((intervalIntegrable_numAt hp hx hσ).mul_continuousOn (hDc.inv₀ hDne)).continuousOn_mul
      (hφ'.comp_continuousOn hU)
    simp only [div_eq_mul_inv]
    exact h
  have h2 : ContinuousOn (fun s : ℝ => κ / 2 * φ'' (angAt w vL vR s.toNNReal) / gapAt vL vR s.toNNReal ^ 2)
      (uIcc 0 (σ : ℝ)) :=
    (continuousOn_const.mul (hφ''.comp_continuousOn hU)).div (hDc.pow 2) fun s hs => pow_ne_zero 2 (hDne s hs)
  exact h1.add h2.intervalIntegrable

theorem continuousOn_clockRate {σ : ℝ≥0} (hx : 0 < xR 0 - xL 0) (hσ : (σ : ℝ≥0∞) < ζ) :
    ContinuousOn (fun s : ℝ => (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2) (Icc 0 (σ : ℝ)) :=
  ((continuousOn_gapAt hp hσ).inv₀ fun _ hs => (gapAt_pos hp hx hσ hs).ne').pow 2

theorem intervalIntegrable_clockRate {σ : ℝ≥0} (hx : 0 < xR 0 - xL 0) (hσ : (σ : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2) volume 0 σ :=
  (continuousOn_clockRate hp hx hσ).intervalIntegrable_of_Icc σ.coe_nonneg

theorem integral_inv_gapL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin (nL + 1)) :
    ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL i s.toNNReal)⁻¹ = (xL i - vL i t) / 2 := by
  have hF := hp.isForcePath
  have h := hF.vL_eq ht i
  have hfun : (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) =
      fun s => -2 * (w s.toNNReal - vL i s.toNNReal)⁻¹ := funext fun s => by
    rw [two_div_sub_eq]; ring
  rw [hfun, intervalIntegral.integral_const_mul] at h
  linarith

theorem integral_inv_gapR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (j : Fin (nR + 1)) :
    ∫ s in (0 : ℝ)..t, (vR j s.toNNReal - w s.toNNReal)⁻¹ = (vR j t - xR j) / 2 := by
  have hF := hp.isForcePath
  have h := hF.vR_eq ht j
  have hfun : (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) =
      fun s => 2 * (vR j s.toNNReal - w s.toNNReal)⁻¹ := funext fun s => by rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul] at h
  linarith

theorem intervalIntegrable_inv_gapR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (j : Fin (nR + 1)) :
    IntervalIntegrable (fun s : ℝ => (vR j s.toNNReal - w s.toNNReal)⁻¹) volume 0 t := by
  have h := (hp.isForcePath.integrable_gapR ht j).neg
  refine h.congr fun s _ => ?_
  simp only [Pi.neg_apply]
  rw [← inv_neg, neg_sub]

theorem intervalIntegrable_errAbs {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    IntervalIntegrable (errAbs ρL ρR w vL vR) volume 0 σ := by
  have hF := hp.isForcePath
  have hL := IntervalIntegrable.sum Finset.univ fun i _ =>
    ((hF.integrable_gapL hσ 0).sub (hF.integrable_gapL hσ i)).const_mul |ρL i|
  have hR := IntervalIntegrable.sum Finset.univ fun j _ =>
    ((intervalIntegrable_inv_gapR hp hσ 0).sub (intervalIntegrable_inv_gapR hp hσ j)).const_mul |ρR j|
  rw [Finset.sum_fn] at hL hR
  exact hL.add hR

/-- **(P4)**: `∫₀^σ |E| ≤ K₁`. -/
theorem integral_errAbs_le {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    ∫ s in (0 : ℝ)..σ, errAbs ρL ρR w vL vR s ≤ errK xL xR ρL ρR := by
  have hF := hp.isForcePath
  have hLi : ∀ i, IntervalIntegrable (fun s : ℝ => |ρL i| * ((w s.toNNReal - vL 0 s.toNNReal)⁻¹ -
      (w s.toNNReal - vL i s.toNNReal)⁻¹)) volume 0 σ := fun i =>
    ((hF.integrable_gapL hσ 0).sub (hF.integrable_gapL hσ i)).const_mul |ρL i|
  have hRj : ∀ j, IntervalIntegrable (fun s : ℝ => |ρR j| * ((vR 0 s.toNNReal - w s.toNNReal)⁻¹ -
      (vR j s.toNNReal - w s.toNNReal)⁻¹)) volume 0 σ := fun j =>
    ((intervalIntegrable_inv_gapR hp hσ 0).sub (intervalIntegrable_inv_gapR hp hσ j)).const_mul |ρR j|
  have hL := IntervalIntegrable.sum Finset.univ fun i _ => hLi i
  have hR := IntervalIntegrable.sum Finset.univ fun j _ => hRj j
  rw [Finset.sum_fn] at hL hR
  unfold errAbs
  rw [intervalIntegral.integral_add hL hR, intervalIntegral.integral_finsetSum fun i _ => hLi i,
    intervalIntegral.integral_finsetSum fun j _ => hRj j]
  unfold errK
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun j _ => ?_)
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hF.integrable_gapL hσ 0)
      (hF.integrable_gapL hσ i), integral_inv_gapL hp hσ, integral_inv_gapL hp hσ]
    have hanti := hF.antitone_vL hσ (Fin.zero_le i)
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    linarith
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (intervalIntegrable_inv_gapR hp hσ 0) (intervalIntegrable_inv_gapR hp hσ j),
      integral_inv_gapR hp hσ, integral_inv_gapR hp hσ]
    have hmono := hF.monotone_vR hσ (Fin.zero_le j)
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    linarith

omit hp in
theorem abs_angErr_le {wt : ℝ} {vLt : Fin (nL + 1) → ℝ} {vRt : Fin (nR + 1) → ℝ} (hL0 : vLt 0 < wt)
    (hR0 : wt < vRt 0) (hanti : Antitone vLt) (hmono : Monotone vRt) :
    |angErr ρL ρR wt vLt vRt| ≤ (∑ i, |ρL i| * ((wt - vLt 0)⁻¹ - (wt - vLt i)⁻¹)) +
      ∑ j, |ρR j| * ((vRt 0 - wt)⁻¹ - (vRt j - wt)⁻¹) := by
  unfold angErr
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (abs_nonneg _)
    have h1 : 0 < wt - vLt 0 := sub_pos.2 hL0
    have h2 : wt - vLt 0 ≤ wt - vLt i := by linarith [hanti (Fin.zero_le i)]
    rw [abs_of_nonpos (sub_nonpos.2 (inv_anti₀ h1 h2))]
    ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (abs_nonneg _)
    have h1 : 0 < vRt 0 - wt := sub_pos.2 hR0
    have h2 : vRt 0 - wt ≤ vRt j - wt := by linarith [hmono (Fin.zero_le j)]
    rw [abs_of_nonpos (sub_nonpos.2 (inv_anti₀ h1 h2))]
    ring

omit hp in
theorem errAbs_nonneg {wt : ℝ} {vLt : Fin (nL + 1) → ℝ} {vRt : Fin (nR + 1) → ℝ} (hL0 : vLt 0 < wt)
    (hR0 : wt < vRt 0) (hanti : Antitone vLt) (hmono : Monotone vRt) :
    0 ≤ (∑ i, |ρL i| * ((wt - vLt 0)⁻¹ - (wt - vLt i)⁻¹)) + ∑ j, |ρR j| * ((vRt 0 - wt)⁻¹ - (vRt j - wt)⁻¹) :=
  (abs_nonneg _).trans (abs_angErr_le hL0 hR0 hanti hmono (ρL := ρL) (ρR := ρR))

/-- **The pathwise generator bound** at a non-collision time: with the Lyapunov inequality `lyapGen ≤ −c₀`,
`genExpr ≤ −c₀ D^{-2} + (λ cosh λ / D₀) |E|`. -/
theorem genExpr_le (hx : 0 < xR 0 - xL 0) {lam c c₀ : ℝ} (hlam : 0 ≤ lam) (hc : c ∈ Icc (0 : ℝ) 1)
    (hgen : ∀ u ∈ Ioo (0 : ℝ) 1, lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c u ≤ -c₀)
    {s : ℝ} (hs : (s.toNNReal : ℝ≥0∞) < ζ) (hL0 : vL 0 s.toNNReal < w s.toNNReal)
    (hR0 : w s.toNNReal < vR 0 s.toNNReal) :
    genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) w vL vR s ≤
      -c₀ * (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2 +
        lam * Real.cosh lam / (xR 0 - xL 0) * errAbs ρL ρR w vL vR s := by
  have hF := hp.isForcePath
  set t := s.toNNReal
  have hD : 0 < gapAt vL vR t := sub_pos.2 (hL0.trans hR0)
  have hDx : xR 0 - xL 0 ≤ gapAt vL vR t := le_gapAt hp hs
  have hU : angAt w vL vR t ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (sub_pos.2 hL0) hD, (div_lt_one hD).2 ?_⟩
    simp only [gapAt]; linarith
  have hnum : numAt ρL ρR w vL vR t / gapAt vL vR t =
      angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) (angAt w vL vR t) / gapAt vL vR t ^ 2 +
        angErr ρL ρR (w t) (fun i => vL i t) (fun j => vR j t) / gapAt vL vR t := by
    have h := drift_angU_eq ρL ρR (w := w t) (vL := fun i => vL i t) (vR := fun j => vR j t) hL0 hR0 0
    rw [driftLin₀_angDens] at h
    simpa only [numAt, angAt, gapAt, angDens] using h
  have hE := abs_angErr_le (ρL := ρL) (ρR := ρR) hL0 hR0 (hF.antitone_vL hs) (hF.monotone_vR hs)
  have hEn := errAbs_nonneg (ρL := ρL) (ρR := ρR) hL0 hR0 (hF.antitone_vL hs) (hF.monotone_vR hs)
  have hf' := abs_lyapF'_le hlam hc ⟨hU.1.le, hU.2.le⟩
  have hlg := hgen _ hU
  simp only [genExpr]
  rw [hnum]
  set U := angAt w vL vR t
  set D := gapAt vL vR t
  set E := angErr ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)
  have herr : errAbs ρL ρR w vL vR s = (∑ i, |ρL i| * ((w t - vL 0 t)⁻¹ - (w t - vL i t)⁻¹)) +
      ∑ j, |ρR j| * ((vR 0 t - w t)⁻¹ - (vR j t - w t)⁻¹) := rfl
  rw [herr]
  set A := (∑ i, |ρL i| * ((w t - vL 0 t)⁻¹ - (w t - vL i t)⁻¹)) +
      ∑ j, |ρR j| * ((vR 0 t - w t)⁻¹ - (vR j t - w t)⁻¹)
  have hDinv : (vR 0 t - vL 0 t)⁻¹ ^ 2 = 1 / D ^ 2 := by simp only [D, gapAt]; rw [inv_pow, one_div]
  rw [hDinv]
  -- the main part
  have hmain : lyapF' lam c U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2) +
      κ / 2 * lyapF'' lam c U / D ^ 2 = lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c U / D ^ 2 := by
    simp only [lyapGen]; ring
  have hmain' : lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c U / D ^ 2 ≤ -c₀ * (1 / D ^ 2) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hlg (by positivity)
  -- the error part
  have herr' : lyapF' lam c U * (E / D) ≤ lam * Real.cosh lam / (xR 0 - xL 0) * A := by
    calc lyapF' lam c U * (E / D) ≤ |lyapF' lam c U * (E / D)| := le_abs_self _
      _ = |lyapF' lam c U| * |E| / D := by rw [abs_mul, abs_div, abs_of_pos hD]; ring
      _ ≤ lam * Real.cosh lam * A / (xR 0 - xL 0) := by
          rw [div_le_div_iff₀ hD hx]
          have h1 : |lyapF' lam c U| * |E| ≤ lam * Real.cosh lam * A :=
            mul_le_mul hf' hE (abs_nonneg _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hDx (by positivity : (0 : ℝ) ≤ lam * Real.cosh lam * A),
            abs_nonneg (lyapF' lam c U), abs_nonneg E]
      _ = lam * Real.cosh lam / (xR 0 - xL 0) * A := by ring
  have hsplit : lyapF' lam c U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2 + E / D) +
      κ / 2 * lyapF'' lam c U / D ^ 2 = (lyapF' lam c U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2) +
      κ / 2 * lyapF'' lam c U / D ^ 2) + lyapF' lam c U * (E / D) := by ring
  rw [hsplit, hmain]
  linarith

/-- **The integrated generator bound** on `[0, σ]`: `∫ genExpr ≤ −c₀ ∫ D^{-2} + (λ cosh λ / D₀) K₁`. -/
theorem integral_genExpr_le (hx : 0 < xR 0 - xL 0) {lam c c₀ : ℝ} (hlam : 0 ≤ lam) (hc : c ∈ Icc (0 : ℝ) 1)
    (hgen : ∀ u ∈ Ioo (0 : ℝ) 1, lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c u ≤ -c₀)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) :
    ∫ s in (0 : ℝ)..σ, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) w vL vR s ≤
      -c₀ * (∫ s in (0 : ℝ)..σ, (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2) +
        lam * Real.cosh lam / (xR 0 - xL 0) * errK xL xR ρL ρR := by
  have hF := hp.isForcePath
  have hcont' : Continuous (lyapF' lam c) := continuous_iff_continuousAt.2 fun u =>
    (hasDerivAt_lyapF' lam c u).continuousAt
  have hcont'' : Continuous (lyapF'' lam c) := by unfold lyapF''; fun_prop
  have hgi := intervalIntegrable_genExpr hp hx hcont' hcont'' hσ (ρL := ρL) (ρR := ρR)
  have hci := intervalIntegrable_clockRate hp hx hσ
  have hei := intervalIntegrable_errAbs hp hσ (ρL := ρL) (ρR := ρR)
  have hK : 0 ≤ lam * Real.cosh lam / (xR 0 - xL 0) := by
    have := Real.cosh_pos lam; positivity
  calc ∫ s in (0 : ℝ)..σ, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) w vL vR s
      ≤ ∫ s in (0 : ℝ)..σ, (-c₀ * (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2 +
          lam * Real.cosh lam / (xR 0 - xL 0) * errAbs ρL ρR w vL vR s) := by
        refine intervalIntegral.integral_mono_ae_restrict σ.coe_nonneg hgi
          ((hci.const_mul _).add (hei.const_mul _)) ?_
        have hnc := ae_not_collision hF hσ
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := Measure.ae_ne volume 0
        filter_upwards [hnc, h0] with s hs hs0 hsI
        have hsI' : s ∈ Ioc 0 (σ : ℝ) := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
        obtain ⟨hL, hR⟩ := hs hsI'
        have hsζ := Sec2.toNNReal_lt_of_mem_Icc hσ hsI
        exact genExpr_le hp hx hlam hc hgen hsζ (lt_of_le_of_ne (hF.vL_le_w hsζ 0) (hL 0))
          (lt_of_le_of_ne (hF.w_le_vR hsζ 0) (Ne.symm (hR 0)))
    _ = -c₀ * (∫ s in (0 : ℝ)..σ, (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2) +
          lam * Real.cosh lam / (xR 0 - xL 0) * ∫ s in (0 : ℝ)..σ, errAbs ρL ρR w vL vR s := by
        rw [intervalIntegral.integral_add (hci.const_mul _) (hei.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ _ := by
        have := integral_errAbs_le hp hσ (ρL := ρL) (ρR := ρR)
        nlinarith

theorem errK_nonneg (h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ) : 0 ≤ errK xL xR ρL ρR := by
  have hF := hp.isForcePath
  unfold errK
  refine add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) ?_)
    (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) ?_)
  · have := hF.antitone_vL h0 (Fin.zero_le i)
    simp only [hF.vL_zero] at this; linarith
  · have := hF.monotone_vR h0 (Fin.zero_le j)
    simp only [hF.vR_zero] at this; linarith

theorem angAt_mem_Icc (hx : 0 < xR 0 - xL 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    angAt w vL vR t ∈ Icc (0 : ℝ) 1 := by
  have hF := hp.isForcePath
  have hD : 0 < gapAt vL vR t := hx.trans_le (le_gapAt hp ht)
  refine ⟨div_nonneg (sub_nonneg.2 (hF.vL_le_w ht 0)) hD.le, (div_le_one hD).2 ?_⟩
  simp only [gapAt]; linarith [hF.w_le_vR ht 0]

end Path

/-! ### The stopped angular clock as an extra coordinate -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The cross-gap stopped at `σ` on the good event (`D₀` off it). -/
def gapStopA (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (r : ℝ≥0) (ω : Ω) : ℝ :=
  open scoped Classical in
  if ω ∈ G then VR 0 (min r (σ ω)) ω - VL 0 (min r (σ ω)) ω else xR 0 - xL 0

/-- The rate `D^{-2}` of the stopped angular clock. -/
def clockC (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (s : ℝ) (ω : Ω) : ℝ :=
  (gapStopA xL xR G VL VR σ s.toNNReal ω)⁻¹ ^ 2

/-- The stopped angular clock `∫₀ᵗ D_{u∧σ}^{-2} du`. -/
def clockI (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..t, clockC xL xR G VL VR σ u ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

section Facts

variable (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (n : ℕ)
include hgood

theorem le_gapStopA (r : ℝ≥0) (ω : Ω) :
    xR 0 - xL 0 ≤ gapStopA xL xR G VL VR (angLoc G T W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · simp only [gapStopA, hω, ↓reduceIte]
    exact le_gapAt (hgood ω hω).1 (lt_of_le_of_lt (by exact_mod_cast min_le_right _ _)
      (angLoc_lt_lifetime (hgood ω hω)))
  · simp only [gapStopA, hω, ↓reduceIte, le_refl]

theorem continuous_gapStopA (ω : Ω) :
    Continuous fun r => gapStopA xL xR G VL VR (angLoc G T W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (angLoc G T W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    have hc := ((hF.continuousOn_vR 0).sub (hF.continuousOn_vL 0)).mono hsub
    simp only [gapStopA, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [gapStopA, hω, ↓reduceIte]; exact continuous_const

theorem continuous_clockC (hx : 0 < xR 0 - xL 0) (ω : Ω) :
    Continuous fun s : ℝ => clockC xL xR G VL VR (angLoc G T W VL VR B ζ n) s ω := by
  unfold clockC
  refine (((continuous_gapStopA hgood n ω).comp continuous_real_toNNReal).inv₀ fun s => ?_).pow 2
  exact (hx.trans_le (le_gapStopA hgood n _ ω)).ne'

omit hgood in
theorem clockC_nonneg (s : ℝ) (ω : Ω) : 0 ≤ clockC xL xR G VL VR (angLoc G T W VL VR B ζ n) s ω := by
  unfold clockC; positivity

theorem clockC_le (hx : 0 < xR 0 - xL 0) (s : ℝ) (ω : Ω) :
    clockC xL xR G VL VR (angLoc G T W VL VR B ζ n) s ω ≤ ((xR 0 - xL 0) ^ 2)⁻¹ := by
  unfold clockC
  rw [inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hx.le (le_gapStopA hgood n _ ω) 2)

theorem clockI_le (hx : 0 < xR 0 - xL 0) {t : ℝ≥0} (ht : t ≤ n) (ω : Ω) :
    |clockI xL xR G VL VR (angLoc G T W VL VR B ζ n) t ω| ≤ n * ((xR 0 - xL 0) ^ 2)⁻¹ := by
  unfold clockI
  have hi : IntervalIntegrable (fun s => clockC xL xR G VL VR (angLoc G T W VL VR B ζ n) s ω) volume 0 t :=
    (continuous_clockC hgood n hx ω).intervalIntegrable _ _
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg t.coe_nonneg fun s _ => clockC_nonneg n s ω)]
  calc ∫ s in (0 : ℝ)..t, clockC xL xR G VL VR (angLoc G T W VL VR B ζ n) s ω
      ≤ ∫ s in (0 : ℝ)..t, ((xR 0 - xL 0) ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on t.coe_nonneg hi intervalIntegrable_const fun s _ =>
          clockC_le hgood n hx s ω
    _ = t * ((xR 0 - xL 0) ^ 2)⁻¹ := by simp
    _ ≤ n * ((xR 0 - xL 0) ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast ht

omit hgood in
/-- Before `σ`, the stopped clock is the angular clock. -/
theorem clockI_eq {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0} (ht : t ≤ angLoc G T W VL VR B ζ n ω) :
    clockI xL xR G VL VR (angLoc G T W VL VR B ζ n) t ω =
      ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 := by
  unfold clockI
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le t.coe_nonneg] at hu
  have hus : u.toNNReal ≤ angLoc G T W VL VR B ζ n ω := (Sec2.toNNReal_le_of_mem_Icc hu).trans ht
  simp only [clockC, gapStopA, hω, ↓reduceIte, min_eq_left hus]

end Facts

section Meas

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)

include hE hGm hGc hgood hT in
theorem measurable_gapStopA (n : ℕ) (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (gapStopA xL xR G VL VR (angLoc G T W VL VR B ζ n) r) := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_angLoc hE hGm hGc hgood hT n
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      killedAt ζ (VR 0) s ω - killedAt ζ (VL 0) s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed (hVRa 0) s).sub (Sec2.TwoSeed.measurable_killed (hVLa 0) s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => VR 0 s ω - VL 0 s ω) hσ hK hG0
    (xR 0 - xL 0) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [gapStopA, hω]
  · have hsζ : (s : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    simp only [killedAt, hsζ, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (angLoc G T W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    exact ((hF.continuousOn_vR 0).sub (hF.continuousOn_vL 0)).mono hsub

include hE hGm hGc hgood hT in
theorem measurable_clockI (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] (clockI xL xR G VL VR (angLoc G T W VL VR B ζ n) t) := by
  have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P)
      (gapStopA xL xR G VL VR (angLoc G T W VL VR B ζ n)) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_gapStopA hE hGm hGc hgood hT n r).stronglyMeasurable)
      (continuous_gapStopA hgood n)
  exact (Girsanov.stronglyMeasurable_integral_comp hprog (g := fun x : ℝ => x⁻¹ ^ 2) (by fun_prop)
    t).measurable

end Meas

/-! ### The expectation bound and the finite clock -/

section Bound

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

/-- The angular clock up to `σ_n` on the good event (`0` off it), read from the stopped coordinates. -/
def clockY (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (n : ℕ) (ω : Ω) : ℝ :=
  (coordA xL xR G VL VR (clockI xL xR G VL VR (angLoc G T W VL VR B ζ n))
    (min (n : ℝ≥0) (angLoc G T W VL VR B ζ n ω)) ω).2.2

include hgood hx in
theorem continuousOn_clockI (n : ℕ) (ω : Ω) :
    ContinuousOn (clockI xL xR G VL VR (angLoc G T W VL VR B ζ n) · ω)
      (Iic (angLoc G T W VL VR B ζ n ω)) :=
  ((intervalIntegral.continuous_primitive (fun a b =>
    (continuous_clockC hgood n hx ω).intervalIntegrable a b) 0).comp NNReal.continuous_coe).continuousOn

include hE hGm hGc hgood hT hx in
theorem measurable_clockY (n : ℕ) : Measurable (clockY xL xR G T W VL VR B ζ n) := by
  have h := measurable_coordA_angLoc hE hGm hGc hgood hT n (I := clockI xL xR G VL VR
    (angLoc G T W VL VR B ζ n)) ⟨_, measurable_clockI hE hGm hGc hgood hT n, fun _ _ _ _ => rfl⟩
    (fun ω _ => continuousOn_clockI hgood hx n ω) (n : ℝ≥0)
  exact (measurable_snd.comp (measurable_snd.comp h)).mono ((usualAugmentation 𝓕 P).le _) le_rfl

theorem clockY_eq {n : ℕ} {ω : Ω} (hω : ω ∈ G) :
    clockY xL xR G T W VL VR B ζ n ω =
      ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ), (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 := by
  have hmin : min (n : ℝ≥0) (angLoc G T W VL VR B ζ n ω) = angLoc G T W VL VR B ζ n ω :=
    min_eq_right (angLoc_le_n n ω)
  simp only [clockY, coordA, hω, ↓reduceIte, hmin]
  exact clockI_eq n hω le_rfl

theorem clockY_nonneg (n : ℕ) (ω : Ω) : 0 ≤ clockY xL xR G T W VL VR B ζ n ω := by
  by_cases hω : ω ∈ G
  · simp only [clockY, coordA, hω, ↓reduceIte, clockI]
    exact intervalIntegral.integral_nonneg (by positivity) fun s _ => by unfold clockC; positivity
  · simp only [clockY, coordA, hω, ↓reduceIte, le_refl]

include hκ hE hGm hGc hgood hT hx in
/-- **The expectation bound**: for every `n`, `E ∫₀^{σ_n} D^{-2} ≤ C`, with `C` independent of `n`. -/
theorem exists_lintegral_clockY_le (hab : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) :
    ∃ C : ℝ, ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω) ∂P ≤ ENNReal.ofReal C := by
  have hP := hE.1.isProbabilityMeasure'
  have hab' : 2 + ∑ i, ρL i ≤ 0 ∨ 2 + ∑ j, ρR j ≤ 0 := by
    rcases hab with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  obtain ⟨lam, c, c₀, hlam, hc, hc₀, hgen⟩ := exists_lyap hκ hab'
  -- a good path, for the constants
  obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hGc
    exact one_ne_zero hGc
  have hp₀ := (hgood ω₀ hω₀).1
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω₀ := lt_of_le_of_lt bot_le ((hgood ω₀ hω₀).2.2.2.1 0)
  have hK₀ : 0 ≤ lam * Real.cosh lam / (xR 0 - xL 0) * errK xL xR ρL ρR := by
    have h1 := errK_nonneg hp₀ h0
    have := Real.cosh_pos lam
    positivity
  set K₂ := lam * Real.cosh lam / (xR 0 - xL 0) * errK xL xR ρL ρR + Real.cosh lam with hK₂
  refine ⟨(K₂ + Real.cosh lam) / c₀, fun n => ?_⟩
  set σ := angLoc G T W VL VR B ζ n with hσdef
  set Φ : SCoord nL (nR + 1) × ℝ → ℝ := fun q => lyapF lam c (angU κ xL xR ρL ρR q) with hΦdef
  have hΦc : ContDiffOn ℝ 3 Φ angRegion := contDiffOn_comp_angU κ xL xR ρL ρR (contDiff_lyapF lam c)
  have hcb : ∀ ω ∈ G, ∫ s in (0 : ℝ)..(σ ω : ℝ), |clockC xL xR G VL VR σ s ω| ≤ n * ((xR 0 - xL 0) ^ 2)⁻¹ := by
    intro ω _
    have h := clockI_le hgood n hx (t := σ ω) (angLoc_le_n n ω) ω
    have e : ∫ s in (0 : ℝ)..(σ ω : ℝ), |clockC xL xR G VL VR σ s ω| = clockI xL xR G VL VR σ (σ ω) ω :=
      intervalIntegral.integral_congr fun s _ => abs_of_nonneg (clockC_nonneg n s ω)
    rw [e]; exact (le_abs_self _).trans h
  have hM := martingale_angLoc hE hGm hGc hgood hT hx hΦc n
    (I := clockI xL xR G VL VR σ) (c := clockC xL xR G VL VR σ) (KI := n * ((xR 0 - xL 0) ^ 2)⁻¹)
    (Kc := n * ((xR 0 - xL 0) ^ 2)⁻¹) (fun _ _ _ _ => rfl)
    (fun ω _ => (continuous_clockC hgood n hx ω).intervalIntegrable _ _) hcb
    (fun ω _ t ht => clockI_le hgood n hx (ht.trans (angLoc_le_n n ω)) ω)
    ⟨_, measurable_clockI hE hGm hGc hgood hT n, fun _ _ _ _ => rfl⟩
    (fun ω _ => continuousOn_clockI hgood hx n ω)
  set M := fun t ω => Φ (coordA xL xR G VL VR (clockI xL xR G VL VR σ) (min t (σ ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen Φ (coordA xL xR G VL VR (clockI xL xR G VL VR σ)
      s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) (densA G W VL VR (clockC xL xR G VL VR σ) s ω)
    with hMdef
  -- the initial value
  have hM0 : ∀ ω, M 0 ω = Φ (angInit xL xR) := fun ω => by
    simp only [hMdef, zero_min, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    by_cases hω : ω ∈ G
    · have hF := (hgood ω hω).1.isForcePath
      have e1 : (fun i => VL i 0 ω) = xL := funext hF.vL_zero
      have e2 : (fun j => VR j 0 ω) = xR := funext hF.vR_zero
      simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, e1, e2, (hgood ω hω).2.2.1, clockI,
        NNReal.coe_zero, intervalIntegral.integral_same, angInit]
    · simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, angInit]
  have hEM : ∫ ω, M n ω ∂P = Φ (angInit xL xR) := by
    have h := hM.setIntegral_eq (zero_le (a := (n : ℝ≥0))) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [← h]
    simp only [hM0, integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- `|Φ| ≤ cosh λ` at the initial point
  have hinit : |Φ (angInit xL xR)| ≤ Real.cosh lam := by
    have e : angInit xL xR = pathCoord (fun i t => VL i t ω₀) (fun j t => VR j t ω₀) (B · ω₀) 0 0 := by
      have hF := hp₀.isForcePath
      simp only [angInit, pathCoord, hF.vL_zero, hF.vR_zero, (hgood ω₀ hω₀).2.2.1]
    simp only [hΦdef]
    rw [e, angU_pathCoord hp₀ _ h0]
    exact abs_lyapF_le hlam hc (angAt_mem_Icc hp₀ hx h0)
  -- the pathwise inequality
  have hpt : ∀ ω, c₀ * clockY xL xR G T W VL VR B ζ n ω ≤ K₂ + M n ω := by
    intro ω
    have hmin : min (n : ℝ≥0) (σ ω) = σ ω := min_eq_right (angLoc_le_n n ω)
    by_cases hω : ω ∈ G
    · have hω' := hgood ω hω
      have hp := hω'.1
      have hσζ : (σ ω : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
      rw [clockY_eq hω]
      have hint : ∫ s in (0 : ℝ)..(σ ω : ℝ), Ito.itoGen Φ (coordA xL xR G VL VR (clockI xL xR G VL VR σ)
          s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω) (densA G W VL VR (clockC xL xR G VL VR σ) s ω) =
          ∫ s in (0 : ℝ)..(σ ω : ℝ), genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) (W · ω)
            (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le (σ ω).coe_nonneg] at hs
        have hsζ := Sec2.toNNReal_lt_of_mem_Icc hσζ hs
        have h := itoGen_pathCoord_eq hp hκ.le hx (contDiff_lyapF lam c) (hasDerivAt_lyapF lam c)
          (hasDerivAt_lyapF' lam c) (clockI xL xR G VL VR σ s.toNNReal ω) (clockC xL xR G VL VR σ s ω) hsζ
        simp only [coordA, densA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
        refine h.trans ?_
        simp only [genExpr, Real.toNNReal_coe]
      have hle := integral_genExpr_le hp hx hlam hc hgen hσζ
      have hMn : M n ω = Φ (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω)
          (clockI xL xR G VL VR σ (σ ω) ω) (σ ω)) -
          ∫ s in (0 : ℝ)..(σ ω : ℝ), genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) (W · ω)
            (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
        rw [← hint]
        simp only [hMdef, hmin, coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
        rfl
      have hΦ : |Φ (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω)
          (clockI xL xR G VL VR σ (σ ω) ω) (σ ω))| ≤ Real.cosh lam := by
        simp only [hΦdef]
        rw [angU_pathCoord hp _ hσζ]
        exact abs_lyapF_le hlam hc (angAt_mem_Icc hp hx hσζ)
      rw [hMn, hK₂]
      have habs := (abs_le.1 hΦ).1
      nlinarith
    · have hσ0 : σ ω = 0 := angLoc_of_not_mem hω n
      have hY : clockY xL xR G T W VL VR B ζ n ω = 0 := by
        simp only [clockY, coordA, hω, ↓reduceIte]
      rw [hY, mul_zero]
      have hMn : M n ω = Φ (angInit xL xR) := by
        rw [← hM0 ω]
        simp only [hMdef, hσ0, min_zero]
      rw [hMn, hK₂]
      linarith [(abs_le.1 hinit).1]
  -- integrate
  have hZi : Integrable (fun ω => (K₂ + M n ω) / c₀) P :=
    ((integrable_const K₂).add (hM.integrable n)).div_const c₀
  have hZ0 : ∀ ω, 0 ≤ (K₂ + M n ω) / c₀ := fun ω =>
    div_nonneg ((mul_nonneg hc₀.le (clockY_nonneg n ω)).trans (hpt ω)) hc₀.le
  calc ∫⁻ ω, ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((K₂ + M n ω) / c₀) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ((le_div_iff₀ hc₀).2 (by linarith [hpt ω]))
    _ = ENNReal.ofReal (∫ ω, (K₂ + M n ω) / c₀ ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hZi (ae_of_all _ hZ0)).symm
    _ ≤ ENNReal.ofReal ((K₂ + Real.cosh lam) / c₀) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div, integral_add (integrable_const K₂) (hM.integrable n), integral_const, hEM]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        exact div_le_div_of_nonneg_right (by linarith [(abs_le.1 hinit).2]) hc₀.le

include hκ hE hGm hGc hgood hT hx in
/-- **The finite angular clock on good paths** (Fatou over the localizing times). -/
theorem ae_bddAbove_clock_of_good (hab : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ M : ℝ, ∀ t : ℝ≥0,
      ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ M := by
  obtain ⟨C, hC⟩ := exists_lintegral_clockY_le hκ hE hGm hGc hgood hT hx hab
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω) with hfdef
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_clockY hE hGm hGc hgood hT hx n).ennreal_ofReal
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop) fun n => (hfm n).aemeasurable
  have hlim : ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P ≤ ENNReal.ofReal C :=
    hfat.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => hC n))
  have hfin : ∀ᵐ ω ∂P, liminf (fun n => f n ω) atTop < ⊤ :=
    ae_lt_top (Measurable.liminf hfm) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  filter_upwards [hfin, measure_eq_zero_iff_ae_notMem.1 hGc] with ω hω hωG' hζ
  have hωG : ω ∈ G := by simpa using hωG'
  refine ⟨(liminf (fun n => f n ω) atTop).toReal, fun t => ?_⟩
  have ht : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_angLoc (hgood ω hωG) hgood hωG (hT.2.1 ω) ht
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal (∫ s in (0 : ℝ)..t,
      (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2) ≤ f n ω := by
    refine eventually_atTop.2 ⟨n₀, fun n hn => ENNReal.ofReal_le_ofReal ?_⟩
    rw [clockY_eq hωG]
    have hσζ := angLoc_lt_lifetime (G := G) (n := n) (hgood ω hωG)
    exact intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg (by exact_mod_cast hn₀ n hn)
      (ae_of_all _ fun s => by positivity) (intervalIntegrable_clockRate (hgood ω hωG).1 hx hσζ)
  have hle := le_liminf_of_le (by isBoundedDefault) hev
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 hle

end Bound

section Evolution

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- An admissible seed, or the conclusion holds vacuously: if the seed satisfies the threshold condition, the
lifetime is `0` almost surely. -/
theorem ae_ne_top_of_thresholdCondition (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ∀ᵐ ω ∂P, ζ ω ≠ ⊤ := by
  filter_upwards [hE.2.2.2.2] with ω hp hζ
  have hF := hp.isForcePath
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hn := hF.not_threshold h0
  have e1 : (fun i => VL i 0 ω) = xL := funext hF.vL_zero
  have e2 : (fun j => VR j 0 ω) = xR := funext hF.vR_zero
  rw [e1, e2, hF.w_zero] at hn
  exact hn hthr

/-- **The good event and the announcing sequence** for an evolution with an admissible seed. -/
theorem exists_setup (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (T : ℕ → Ω → ℝ≥0) (G : Set Ω), Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T ∧
      MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω := by
  have hP := hE.1.isProbabilityMeasure'
  obtain ⟨T, hT⟩ := Coupling.exists_isAnnouncingSeq hE hκ hthr
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_ang hE hT
  exact ⟨T, G, hT, hGm, hGc, hgood⟩

/-- **Aux. lemma 102, the finite total angular clock** (Specification p. 348). For `κ > 0` and an evolution of a
separated word with marks on both sides whose left or right total weight is at most `−2`: almost surely on
`{ζ = ∞}`, `sup_t ∫₀ᵗ (V^{R,0} − V^{L,0})^{-2} < ∞`. -/
theorem ae_bddAbove_clock (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hsep : ∀ i j, xL i < xR j) (hab : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ M : ℝ, ∀ t : ℝ≥0,
      ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ M := by
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [ae_ne_top_of_thresholdCondition hE hthr] with ω hω hζ
    exact absurd hζ hω
  obtain ⟨T, G, hT, hGm, hGc, hgood⟩ := exists_setup hκ hE hthr
  exact ae_bddAbove_clock_of_good hκ hE hGm hGc hgood hT (sub_pos.2 (hsep 0 0)) hab

end Evolution

end Stopped

end Clock

end Sec7

end InteractingSLE
