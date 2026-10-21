import SmallGammaGeodesics.Variance.Lemma31
import SmallGammaGeodesics.Inputs.Moments
import SmallGammaGeodesics.Inputs.EuclidFine
import GaussianLQG.LQG.FirstOrder
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 3.2′: the residual variance, Route F form (packet P-A5)

Source: `source/small-parameter-lqg-geodesics.pdf`, §3, (3.3)–(3.4) (Lemma 3.2). Mathematics:
planning audit GA2, "Details for later use", D2; GA5 Details (a2) (the Gaussian residual skeleton)
and (a3) ("Proof of the (3.4) row"); GA3 recommendation R3; rulings G16 and G23 (`a = 99/100`).

Notation (coordinate `Setup` `S`): `ξ = S.ξ γ`, `L = log(1/ξ)`, `λ = segMeasure 0 1`,
`F = S.firstOrderErr γ 0 1 = (log D(0,1) − b_γ)/ξ − (h, λ)` and `Z = ξ F` (the source's residual
(3.3); `log|0 − 1| = 0`), `Δ₃ = S.euclidErr γ 3`, and `T`, `B`, `Θ` the localization variables of
`B̄₁(0)` (`S.locT`, `S.locB`, `S.locTheta`; Lemma 2.1′). `‖ν − λ‖_G² = energyDistSq ν λ`.

* `eLpNorm_firstOrderErr_le_of_majorant`, `firstOrder_of_majorant` (GA5 (a2)): the proof of
  GaussianLQG's `Setup.firstOrder` with an abstract majorant: if a.s. some geodesic `η` from `z` to
  `w` has a regular length measure with `‖ν_η − λ_{z,w}‖_G² ≤ Y²`, then `‖F‖_p ≤ c_p ‖Y‖_p`,
  `c_p = (π/2) ‖N‖_p`;
* `firstOrder_sq_of_majorant`: the case `p = 2` with `c₂² = π²/4` and a majorant `W = Y²`;
* `residualVariance` (**Lemma 3.2′**, rulings G16, G23): for small `γ` and every measurable a.s.
  selection `P01` of constant-speed geodesics from `0` to `1`,
  `E Z² ≤ C ξ² (E M(P01) + ξ^{99/100} log(1/ξ))`.

Proof of `residualVariance` (GA2 D2, GA5 (a3)). The Gaussian Poincaré inequality gives
`E F² ≤ (π²/4) E W` for any a.s. majorant `W` of `‖ν_{P01} − λ‖_G²`. Take
`W = 66 M + 140 Δ₃ B + 70 L Δ₃ + 70 ξ + 400 Θ² Δ₃`:
* on `{Δ₃ ≤ 1/100}`, Lemma 3.1′ (`lemma31`, `s = 1/2`, `A = B`, `d = e^{-b} D`) gives
  `‖ν − λ‖_G² ≤ 66 M + 70 Δ₃ (1 + log⁺ B + |log Δ₃|)`, and `1 + log⁺ B ≤ 2B`,
  `x |log x| ≤ L x + ξ` on `[0,1]` (`mul_abs_log_le`);
* on `{Δ₃ > 1/100}`, `‖ν − λ‖_G² ≤ 2ℰ(ν,ν) + 2ℰ(λ,λ) ≤ 2Θ² + 3 ≤ 4Θ² ≤ 400 Θ² Δ₃`
  (`energyDistSq_le_two_mul_add`, `ℰ(λ,λ) = 3/2`, `Θ² ≥ 2`).
Then `E W ≤ 66 m + C ξ^{99/100} L` by Cauchy–Schwarz (`lintegral_mul_le_of_sq`) with
`‖Δ₃‖₂ ≤ C ξ^{99/100}` (`euclidFine`), `E B²`, `E Θ⁴ < C` (`exists_locMoments_closedBall_one`) and
`L ≥ 1` (`ξ ≤ 1/10`). The tail bound `P[Δ₃ > 1/100] ≤ C ξ⁴` is not needed:
`1_{Δ₃ > 1/100} ≤ 100 Δ₃`.
Finally `M ≤ T` a.s. gives `E M < ∞`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Real

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-! ## The abstract first-order bound with a majorant (GA5 (a2)) -/

/-- **`Setup.firstOrder` with an abstract majorant** (GA5 Details (a2); the proof of GaussianLQG's
`Setup.firstOrder`, `GaussianLQG/LQG/FirstOrder.lean`). Let `0 < γ < 2`, `z ≠ w`, `p ≥ 1`, assume
`log D(z,w) ∈ L^p` with mean `b_γ + ξ Q log|w − z|`, and let `Y` be a `[0,∞]`-valued function
such that almost surely some constant-speed geodesic `η` from `z` to `w` has a regular length
measure with `‖ν_η − λ_{z,w}‖_G² ≤ Y²`. Then `F = S.firstOrderErr γ z w` is in `L^p`, `E F = 0` and
`‖F‖_p ≤ c_p (E Y^p)^{1/p}` with `c_p = (π/2) (E|N|^p)^{1/p}`. -/
theorem eLpNorm_firstOrderErr_le_of_majorant (S : Setup) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {z w : ℂ} (hzw : z ≠ w) {p : ℝ} (hp : 1 ≤ p)
    (hlogp : MemLp (fun ω => Real.log ((S.D γ ω).1 (z, w))) (ENNReal.ofReal p) stdP)
    (hE : ∫ ω, Real.log ((S.D γ ω).1 (z, w)) ∂stdP =
      S.b γ + S.ξ γ * Q γ * Real.log ‖w - z‖)
    {Y : Coord → ℝ≥0∞}
    (hY : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η ∧
      IsRegular (lengthMeasure η) ∧
      ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure z w)) ≤ Y ω ^ 2) :
    MemLp (S.firstOrderErr γ z w) (ENNReal.ofReal p) stdP ∧
      ∫ ω, S.firstOrderErr γ z w ω ∂stdP = 0 ∧
      eLpNorm (S.firstOrderErr γ z w) (ENNReal.ofReal p) stdP ≤
        ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)) *
          (∫⁻ ω, Y ω ^ p ∂stdP) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ hγ2
  set F : Coord → ℝ := S.firstOrderErr γ z w with hF
  -- measurability and moments
  have hFm : Measurable F := S.measurable_firstOrderErr γ z w
  have hlam : IsRegular (segMeasure z w) := isRegular_segMeasure hzw
  have hpairp : MemLp (pairing S.e (segMeasure z w)) (ENNReal.ofReal p) stdP :=
    memLp_pairing S.frame hlam ENNReal.ofReal_ne_top
  have hFp : MemLp F (ENNReal.ofReal p) stdP := by
    have h := (((hlogp.sub (memLp_const (S.b γ))).sub
      (memLp_const (S.ξ γ * Q γ * Real.log ‖z - w‖))).mul_const (S.ξ γ)⁻¹).sub hpairp
    refine h.congr_norm hFm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [hF, Setup.firstOrderErr, div_eq_mul_inv, Pi.sub_apply]
  -- `E F = 0`
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hF0 : ∫ ω, F ω ∂stdP = 0 := by
    have hi1 : Integrable (fun ω => Real.log ((S.D γ ω).1 (z, w))) stdP := hlogp.integrable hp1
    have hP := integral_pairing S.frame hlam
    have hi2 : Integrable (fun ω => Real.log ((S.D γ ω).1 (z, w)) - S.b γ) stdP :=
      hi1.sub (integrable_const _)
    have hi3 : Integrable (fun ω => Real.log ((S.D γ ω).1 (z, w)) - S.b γ -
        S.ξ γ * Q γ * Real.log ‖z - w‖) stdP := hi2.sub (integrable_const _)
    simp only [hF, Setup.firstOrderErr]
    rw [integral_sub (hi3.div_const _) (hpairp.integrable hp1), integral_div,
      integral_sub hi2 (integrable_const _), integral_sub hi1 (integrable_const _),
      integral_const, integral_const, probReal_univ, one_smul, one_smul, hE, hP, norm_sub_rev w z]
    simp
  refine ⟨hFp, hF0, ?_⟩
  -- hypothesis (H) of the Gaussian `L^p` inequality on `𝒢 = Ω_γ ∩ Ω_{λ_{z,w}}`
  obtain ⟨Ω, hΩm, hΩc, hΩ⟩ := S.exists_logD_shiftLipschitz hγ hγ2
  have h𝒢m : MeasurableSet (Ω ∩ pairingSet S.e (segMeasure z w)) :=
    hΩm.inter (measurableSet_pairingSet _ _)
  have h𝒢c : stdP (Ω ∩ pairingSet S.e (segMeasure z w))ᶜ = 0 := by
    rw [compl_inter]
    exact measure_union_null hΩc (ae_iff.1 (ae_mem_pairingSet S.frame hlam))
  have hH : ∀ ω ∈ Ω ∩ pairingSet S.e (segMeasure z w), ∀ v v' : ℕ →₀ ℝ,
      |F (shiftBy ω v) - F (shiftBy ω v')| ≤
        ∑ j ∈ v.support ∪ v'.support, (2 * S.supE j) * |v j - v' j| :=
    fun ω hω v v' => S.abs_firstOrderErr_shiftBy_sub_le hξ (hΩ ω hω.1 z w hzw) hω.2 v v'
  have hW1 := gaussian_Lp_inequality (L := fun j => 2 * S.supE j) hFm h𝒢m h𝒢c hH hp hFp
  -- the square function: `∑_j (∂_j F)² = ‖ν_η - λ_{z,w}‖_G² ≤ Y²` almost surely
  have hsq : ∀ᵐ ω ∂stdP, (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ≤ Y ω ^ 2 := by
    filter_upwards [S.ae_hasDerivAt_logD hγ hγ2 hzw, ae_mem_pairingSet S.frame hlam, hY]
      with ω hd hωlam hYω
    obtain ⟨η, hη, hνreg, hE'⟩ := hYω
    have hderiv : ∀ j, coordDeriv F j ω =
        ∫ x, S.e j x ∂(lengthMeasure η) - ∫ x, S.e j x ∂(segMeasure z w) :=
      fun j => (S.hasDerivAt_firstOrderErr hξ.ne' hωlam ((hd j).2 η hη)).deriv
    simp_rw [hderiv]
    have hs := S.hasSum_sq_sub_frameCoef hνreg hlam
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hs.summable, hs.tsum_eq]
    exact hE'
  -- conclusion
  have hlhs : eLpNorm F (ENNReal.ofReal p) stdP =
      eLpNorm (fun ω => F ω - ∫ ω', F ω' ∂stdP) (ENNReal.ofReal p) stdP := by
    rw [hF0]
    simp only [sub_zero]
  rw [hlhs]
  refine hW1.trans ?_
  have hint2 : (∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2) ∂stdP) ≤
      ∫⁻ ω, Y ω ^ p ∂stdP := by
    refine lintegral_mono_ae ?_
    filter_upwards [hsq] with ω hω
    calc (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2) ≤ (Y ω ^ 2) ^ (p / 2) :=
          ENNReal.rpow_le_rpow hω (by positivity)
      _ = Y ω ^ p := by
          rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
          congr 1
          ring
  gcongr

/-- **GA5 (a2), uniform form**: for `p ≥ 1` there is `γs ∈ (0, 2)` such that for every
`γ ∈ (0, γs]`, all `z ≠ w` and every `[0,∞]`-valued `Y` such that a.s. `‖ν_η − λ_{z,w}‖_G² ≤ Y²`
for some constant-speed geodesic `η` from `z` to `w` with `ν_η` regular:
`F = S.firstOrderErr γ z w ∈ L^p`, `E F = 0` and `‖F‖_p ≤ c_p (E Y^p)^{1/p}`. The thresholds come
from `Setup.exists_memLp_log_D_pair` and `Setup.exists_integral_log_D` only. -/
theorem firstOrder_of_majorant (S : Setup) {p : ℝ} (hp : 1 ≤ p) :
    ∃ γs : ℝ, 0 < γs ∧ γs < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ z w : ℂ, z ≠ w →
      ∀ Y : Coord → ℝ≥0∞,
        (∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η ∧
          IsRegular (lengthMeasure η) ∧
          ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure z w)) ≤ Y ω ^ 2) →
        MemLp (S.firstOrderErr γ z w) (ENNReal.ofReal p) stdP ∧
          ∫ ω, S.firstOrderErr γ z w ω ∂stdP = 0 ∧
          eLpNorm (S.firstOrderErr γ z w) (ENNReal.ofReal p) stdP ≤
            ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)) *
              (∫⁻ ω, Y ω ^ p ∂stdP) ^ (1 / p) := by
  obtain ⟨γ1, hγ1, hγ12, hmem⟩ := S.exists_memLp_log_D_pair hp
  obtain ⟨γ2, hγ2, hint⟩ := S.exists_integral_log_D
  refine ⟨min γ1 γ2, lt_min hγ1 hγ2, (min_le_left _ _).trans_lt hγ12,
    fun γ hγ z w hzw Y hY => ?_⟩
  have hγ1' : γ ≤ γ1 := hγ.2.trans (min_le_left _ _)
  have hγ2' : γ ≤ γ2 := hγ.2.trans (min_le_right _ _)
  exact eLpNorm_firstOrderErr_le_of_majorant S hγ.1 (hγ1'.trans_lt hγ12) hzw hp
    (hmem γ ⟨hγ.1, hγ1'⟩ z w hzw) (hint γ ⟨hγ.1, hγ2'⟩ z w hzw) hY

/-- `E|N|² = 1` for a standard Gaussian `N`. -/
theorem integral_abs_rpow_two_gaussianReal : ∫ x, |x| ^ (2 : ℝ) ∂gaussianReal 0 1 = 1 := by
  have h1 : (fun x : ℝ => |x| ^ (2 : ℝ)) = fun x => x ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  rw [h1]
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_sub (memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top)] at h
  simp only [id_eq, Pi.pow_apply] at h
  rw [integral_id_gaussianReal] at h
  simpa using h

/-- The Gaussian `L²` constant: `c₂ = (π/2) (E N²)^{1/2} = π/2`. -/
theorem gaussLp_const_two :
    Real.pi / 2 * (∫ x, |x| ^ (2 : ℝ) ∂gaussianReal 0 1) ^ (1 / (2 : ℝ)) = Real.pi / 2 := by
  rw [integral_abs_rpow_two_gaussianReal, Real.one_rpow, mul_one]

/-- **The Gaussian Poincaré inequality with a majorant** (`p = 2` in `firstOrder_of_majorant`, with
`c₂² = π²/4`): there is `γs ∈ (0, 2)` such that for `γ ∈ (0, γs]`, `z ≠ w` and every `[0,∞]`-valued
`W` such that a.s. some constant-speed geodesic `η` from `z` to `w` has a regular length measure
with `‖ν_η − λ_{z,w}‖_G² ≤ W`: `F = S.firstOrderErr γ z w ∈ L²`, `E F = 0` and
`E F² ≤ (π²/4) E W`. -/
theorem firstOrder_sq_of_majorant (S : Setup) :
    ∃ γs : ℝ, 0 < γs ∧ γs < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ z w : ℂ, z ≠ w →
      ∀ W : Coord → ℝ≥0∞,
        (∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η ∧
          IsRegular (lengthMeasure η) ∧
          ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure z w)) ≤ W ω) →
        MemLp (S.firstOrderErr γ z w) 2 stdP ∧
          ∫ ω, S.firstOrderErr γ z w ω ∂stdP = 0 ∧
          ENNReal.ofReal (∫ ω, S.firstOrderErr γ z w ω ^ 2 ∂stdP) ≤
            ENNReal.ofReal (Real.pi ^ 2 / 4) * ∫⁻ ω, W ω ∂stdP := by
  obtain ⟨γs, hγs, hγs2, h⟩ := firstOrder_of_majorant S (p := 2) one_le_two
  refine ⟨γs, hγs, hγs2, fun γ hγ z w hzw W hW => ?_⟩
  set Y : Coord → ℝ≥0∞ := fun ω => W ω ^ (1 / (2 : ℝ)) with hY_def
  have hYW : ∀ ω, Y ω ^ (2 : ℝ) = W ω := fun ω => by
    rw [hY_def, ← ENNReal.rpow_mul]
    norm_num
  have hY : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η ∧
      IsRegular (lengthMeasure η) ∧
      ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure z w)) ≤ Y ω ^ 2 := by
    filter_upwards [hW] with ω hω
    obtain ⟨η, hη, hreg, hle⟩ := hω
    refine ⟨η, hη, hreg, ?_⟩
    rw [← ENNReal.rpow_two, hYW]
    exact hle
  obtain ⟨hFp, hF0, hnorm⟩ := h γ hγ z w hzw Y hY
  rw [ENNReal.ofReal_ofNat] at hFp hnorm
  refine ⟨hFp, hF0, ?_⟩
  set F := S.firstOrderErr γ z w with hF
  have hsq : ∀ ω, ENNReal.ofReal (F ω ^ 2) = ‖F ω‖ₑ ^ (2 : ℝ) := fun ω => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
      Real.rpow_two, sq_abs]
  have hint : ENNReal.ofReal (∫ ω, F ω ^ 2 ∂stdP) = eLpNorm F 2 stdP ^ (2 : ℝ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFp.integrable_sq
      (ae_of_all _ fun ω => sq_nonneg (F ω))]
    simp_rw [hsq]
    rw [lintegral_enorm_rpow_eq (μ := stdP) two_pos F, ENNReal.ofReal_ofNat]
  rw [hint, gaussLp_const_two] at *
  calc eLpNorm F 2 stdP ^ (2 : ℝ)
      ≤ (ENNReal.ofReal (Real.pi / 2) * (∫⁻ ω, Y ω ^ (2 : ℝ) ∂stdP) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hnorm zero_le_two
    _ = ENNReal.ofReal (Real.pi ^ 2 / 4) * ∫⁻ ω, W ω ∂stdP := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two]
        simp_rw [hYW]
        norm_num
        ring_nf

/-! ## Elementary bounds -/

/-- `x |log x| ≤ L x + ξ` for `0 ≤ x ≤ 1` and `ξ > 0`, where `L = log(1/ξ)` (GA2-08, without the
condition `ξ ≤ 1/e`). Proof: for `x > 0`, `x log(1/x) = x L + x log(ξ/x) ≤ x L + (ξ − x)` by
`log y ≤ y − 1`. -/
theorem mul_abs_log_le {x ξ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hξ : 0 < ξ) :
    x * |Real.log x| ≤ Real.log (1 / ξ) * x + ξ := by
  rcases hx0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, mul_zero, zero_add]
    exact hξ.le
  have hlog : |Real.log x| = Real.log (1 / ξ) + Real.log (ξ / x) := by
    rw [abs_of_nonpos (Real.log_nonpos hpos.le hx1), Real.log_div hξ.ne' hpos.ne', one_div,
      Real.log_inv]
    ring
  have hle : Real.log (ξ / x) ≤ ξ / x - 1 := Real.log_le_sub_one_of_pos (div_pos hξ hpos)
  have hx : x * (ξ / x - 1) = ξ - x := by
    field_simp
  calc x * |Real.log x| = Real.log (1 / ξ) * x + x * Real.log (ξ / x) := by rw [hlog]; ring
    _ ≤ Real.log (1 / ξ) * x + x * (ξ / x - 1) := by gcongr
    _ ≤ Real.log (1 / ξ) * x + ξ := by rw [hx]; linarith

/-- `‖ν − μ‖_G² ≤ 2 ℰ(ν,ν) + 2 ℰ(μ,μ)` for regular `ν`, `μ`: along a GFF frame,
`‖ν − μ‖_G² = ∑_j (a_j − b_j)²` and `(a − b)² ≤ 2a² + 2b²` (GA2 D2 step 4). -/
theorem energyDistSq_le_two_mul_add {e : ℕ → ℂ → ℝ} (he : IsGFFFrame e) {ν μ : Measure ℂ}
    (hν : IsRegular ν) (hμ : IsRegular μ) :
    energyDistSq ν μ ≤ 2 * energy ν ν + 2 * energy μ μ := by
  have h1 := he.2.2 ν ν hν hν
  have h2 := (he.2.2 ν μ hν hμ).mul_left 2
  have h3 := he.2.2 μ μ hμ hμ
  have hL := (h1.sub h2).add h3
  have hR := (h1.mul_left 2).add (h3.mul_left 2)
  unfold energyDistSq
  refine hasSum_le (fun j => ?_) hL hR
  nlinarith [sq_nonneg ((∫ x, e j x ∂ν) + ∫ x, e j x ∂μ)]

/-- `‖ν − μ‖_G² ≥ 0` for regular `ν`, `μ` (a sum of squares along a GFF frame). -/
theorem energyDistSq_nonneg {e : ℕ → ℂ → ℝ} (he : IsGFFFrame e) {ν μ : Measure ℂ}
    (hν : IsRegular ν) (hμ : IsRegular μ) : 0 ≤ energyDistSq ν μ := by
  have h1 := he.2.2 ν ν hν hν
  have h2 := (he.2.2 ν μ hν hμ).mul_left 2
  have h3 := he.2.2 μ μ hμ hμ
  have hL := (h1.sub h2).add h3
  unfold energyDistSq
  refine hL.nonneg fun j => ?_
  nlinarith [sq_nonneg ((∫ x, e j x ∂ν) - ∫ x, e j x ∂μ)]

/-- **Cauchy–Schwarz** for `[0,∞]`-valued functions, with real bounds on the second moments:
`∫⁻ f g ≤ a b` when `∫⁻ f² ≤ a²` and `∫⁻ g² ≤ b²` (`a, b ≥ 0`). -/
theorem lintegral_mul_le_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hfa : ∫⁻ x, f x ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal (a ^ 2))
    (hgb : ∫⁻ x, g x ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal (b ^ 2)) :
    ∫⁻ x, f x * g x ∂μ ≤ ENNReal.ofReal (a * b) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have hsq : ∀ c : ℝ, 0 ≤ c → ENNReal.ofReal (c ^ 2) ^ (1 / (2 : ℝ)) = ENNReal.ofReal c := by
    intro c hc
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hc]
  calc ∫⁻ x, f x * g x ∂μ = ∫⁻ x, (f * g) x ∂μ := rfl
    _ ≤ (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := h
    _ ≤ ENNReal.ofReal (a ^ 2) ^ (1 / (2 : ℝ)) * ENNReal.ofReal (b ^ 2) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (a * b) := by rw [hsq a ha, hsq b hb, ENNReal.ofReal_mul ha]

/-! ## The good event: Lemma 3.1′ with `s = 1/2`, `A = B` -/

/-- **Lemma 3.2′ on the good event** (GA2 D2 step 2, with the bounds of GA5 (a3) step 2 applied
pointwise). Let `d` be any function with additive Euclidean error `Δ ≤ 1/100` on `B̄₃(0)`, `η` a
constant-speed `d`-geodesic from `0` to `1` whose occupation measure has the Frostman bound
`ν_η(B_r(u)) ≤ B r^{1/2}` (`0 < r ≤ 1`, `B ≥ 1`), and `ξ > 0`. Then
`‖ν_η − λ‖_G² ≤ 66 M + 140 Δ B + 70 log(1/ξ) Δ + 70 ξ`, `M = maxDev η`. -/
theorem energyDistSq_le_of_good {d : ℂ × ℂ → ℝ} {η : C(unitInterval, ℂ)} {Δ B ξ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1 / 100) (hB : 1 ≤ B) (hξ : 0 < ξ)
    (hd : ∀ z w : ℂ, ‖z‖ ≤ 3 → ‖w‖ ≤ 3 → |d (z, w) - ‖z - w‖| ≤ Δ)
    (h0 : η 0 = 0) (h1 : η 1 = 1)
    (hgeo : ∀ s t : unitInterval, d (η s, η t) = |(t : ℝ) - s| * d (0, 1))
    (hfr : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (lengthMeasure η (Metric.ball u r)).toReal ≤ B * r ^ (1 / 2 : ℝ)) :
    energyDistSq (lengthMeasure η) (segMeasure 0 1) ≤
      66 * maxDev η + 140 * Δ * B + 70 * Real.log (1 / ξ) * Δ + 70 * ξ := by
  obtain ⟨-, h31⟩ := lemma31 d η Δ B (1 / 2) hΔ0 hΔ (by norm_num) (by norm_num) (by linarith)
    hd h0 h1 hgeo hfr
  have hposlog : log⁺ B ≤ B := (Real.posLog_le_abs B).trans (abs_of_nonneg (by linarith)).le
  have hxlog := mul_abs_log_le hΔ0 (by linarith) hξ
  have hc : (66 : ℝ) + 2 / (1 / 2) = 70 := by norm_num
  rw [hc] at h31
  calc energyDistSq (lengthMeasure η) (segMeasure 0 1)
      ≤ 66 * maxDev η + 70 * Δ * (1 + log⁺ B + |Real.log Δ|) := h31
    _ = 66 * maxDev η + 70 * (Δ * (1 + log⁺ B)) + 70 * (Δ * |Real.log Δ|) := by ring
    _ ≤ 66 * maxDev η + 70 * (Δ * (2 * B)) + 70 * (Real.log (1 / ξ) * Δ + ξ) := by
        gcongr
        linarith
    _ = 66 * maxDev η + 140 * Δ * B + 70 * Real.log (1 / ξ) * Δ + 70 * ξ := by ring

/-! ## The energy majorant and its almost-sure bound -/

/-- Pointwise form of `Δ_R = S.euclidErr γ R`: if `Δ_R(ω) < ∞`, then
`|e^{-b_γ} D(z,w) − |z − w|| ≤ Δ_R(ω)` for `|z|, |w| ≤ R`. -/
theorem abs_sub_le_toReal_euclidErr (S : Setup) {γ R : ℝ} {ω : Coord}
    (hfin : S.euclidErr γ R ω ≠ ⊤) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖| ≤ (S.euclidErr γ R ω).toReal := by
  refine (ENNReal.ofReal_le_iff_le_toReal hfin).1 ?_
  exact le_iSup₂_of_le (f := fun z (_ : z ∈ Metric.closedBall (0 : ℂ) R) =>
      ⨆ w ∈ Metric.closedBall (0 : ℂ) R,
        ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖|)
    z (mem_closedBall_zero_iff.2 hz)
    (le_iSup₂_of_le (f := fun w (_ : w ∈ Metric.closedBall (0 : ℂ) R) =>
        ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖|)
      w (mem_closedBall_zero_iff.2 hw) le_rfl)

/-- The energy majorant of Lemma 3.2′, valued in `[0, ∞]`:
`W = 66 M + 140 Δ₃ B + 70 L Δ₃ + 70 ξ + 400 Θ² Δ₃`, where `M = maxDev (P01 ω)`,
`Δ₃ = S.euclidErr γ 3`, `B = S.locB γ B̄₁(0) 1`, `Θ = S.locTheta γ B̄₁(0) 1` and `L = log(1/ξ)`. -/
def residualMajorant (S : Setup) (γ : ℝ) (P01 : Coord → C(unitInterval, ℂ)) (ω : Coord) :
    ℝ≥0∞ :=
  66 * ENNReal.ofReal (maxDev (P01 ω)) +
    140 * (S.euclidErr γ 3 ω * S.locB γ (Metric.closedBall 0 1) 1 ω) +
    ENNReal.ofReal (70 * Real.log (1 / S.ξ γ)) * S.euclidErr γ 3 ω +
    ENNReal.ofReal (70 * S.ξ γ) +
    400 * (S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 * S.euclidErr γ 3 ω)

/-- **The almost-sure energy bound** (GA2 D2 steps 2 and 4; GA5 (a2)): there is `γs > 0` such that
for `γ ∈ (0, γs]` and every a.s. selection `P01` of constant-speed geodesics from `0` to `1`, almost
surely `ν_{P01}` is regular and `‖ν_{P01} − λ‖_G² ≤ W` (`residualMajorant`). On `{Δ₃ ≤ 1/100}` this
is `energyDistSq_le_of_good` for `d = e^{-b} D`; on `{Δ₃ > 1/100}`,
`‖ν − λ‖_G² ≤ 2ℰ(ν,ν) + 2ℰ(λ,λ) ≤ 2Θ² + 3 ≤ 4Θ² ≤ 400 Θ² Δ₃`. -/
theorem ae_energyDistSq_le_residualMajorant (S : Setup) :
    ∃ γs : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ P01 : Coord → C(unitInterval, ℂ),
      (∀ᵐ ω ∂stdP, IsGeod01 (S.D γ ω) 0 1 (P01 ω)) →
      ∀ᵐ ω ∂stdP, IsRegular (lengthMeasure (P01 ω)) ∧
        ENNReal.ofReal (energyDistSq (lengthMeasure (P01 ω)) (segMeasure 0 1)) ≤
          residualMajorant S γ P01 ω := by
  obtain ⟨γT, hγT, hloc⟩ := ae_localization_zero_one S
  obtain ⟨γe, C₁, hγe, hγe2, hexp⟩ := S.exists_exponents
  refine ⟨min γT γe, lt_min hγT hγe, fun γ hγ P01 hgeo => ?_⟩
  have hγT' : γ ≤ γT := hγ.2.trans (min_le_left _ _)
  have hγe' : γ ≤ γe := hγ.2.trans (min_le_right _ _)
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ.1 (hγe'.trans_lt hγe2)
  have hξ1 : S.ξ γ ≤ 1 / 10 := (hexp γ ⟨hγ.1, hγe'⟩).2.2.1
  have hL : 0 ≤ Real.log (1 / S.ξ γ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hξ]; linarith)
  filter_upwards [hloc γ ⟨hγ.1, hγT'⟩, hgeo] with ω hω hη
  obtain ⟨hT, hB, hΘ, hT4, hB1, hgeos⟩ := hω
  obtain ⟨-, -, hfr, hreg, hen⟩ := hgeos (P01 ω) hη
  refine ⟨hreg, ?_⟩
  set η := P01 ω with hη_def
  set Δe := S.euclidErr γ 3 ω with hΔe_def
  set Be := S.locB γ (Metric.closedBall 0 1) 1 ω with hBe_def
  set Θe := S.locTheta γ (Metric.closedBall 0 1) 1 ω with hΘe_def
  by_cases hgood : Δe ≤ ENNReal.ofReal (1 / 100)
  · -- the good event: Lemma 3.1′
    have hfin : Δe ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgood
    have hΔ : Δe.toReal ≤ 1 / 100 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hgood
    have hd : ∀ z w : ℂ, ‖z‖ ≤ 3 → ‖w‖ ≤ 3 →
        |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖| ≤ Δe.toReal :=
      fun z w hz hw => abs_sub_le_toReal_euclidErr S hfin hz hw
    have hgeo' : ∀ s t : unitInterval, Real.exp (-S.b γ) * (S.D γ ω).1 (η s, η t) =
        |(t : ℝ) - s| * (Real.exp (-S.b γ) * (S.D γ ω).1 (0, 1)) := by
      intro s t
      rw [hη.2.2 s t]
      ring
    have hbound := energyDistSq_le_of_good (d := fun p => Real.exp (-S.b γ) * (S.D γ ω).1 p)
      ENNReal.toReal_nonneg hΔ hB1 hξ hd hη.1 hη.2.1 hgeo' hfr
    have e1 : ENNReal.ofReal (66 * maxDev η) = 66 * ENNReal.ofReal (maxDev η) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have e2 : ENNReal.ofReal (140 * Δe.toReal * Be.toReal) = 140 * (Δe * Be) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hfin, ENNReal.ofReal_toReal hB, mul_assoc]
    have e3 : ENNReal.ofReal (70 * Real.log (1 / S.ξ γ) * Δe.toReal) =
        ENNReal.ofReal (70 * Real.log (1 / S.ξ γ)) * Δe := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin]
    calc ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure 0 1))
        ≤ ENNReal.ofReal (66 * maxDev η + 140 * Δe.toReal * Be.toReal +
            70 * Real.log (1 / S.ξ γ) * Δe.toReal + 70 * S.ξ γ) :=
          ENNReal.ofReal_le_ofReal hbound
      _ ≤ ENNReal.ofReal (66 * maxDev η) + ENNReal.ofReal (140 * Δe.toReal * Be.toReal) +
            ENNReal.ofReal (70 * Real.log (1 / S.ξ γ) * Δe.toReal) +
            ENNReal.ofReal (70 * S.ξ γ) := by
          refine ENNReal.ofReal_add_le.trans ?_
          gcongr
          refine ENNReal.ofReal_add_le.trans ?_
          gcongr
          exact ENNReal.ofReal_add_le
      _ = 66 * ENNReal.ofReal (maxDev η) + 140 * (Δe * Be) +
            ENNReal.ofReal (70 * Real.log (1 / S.ξ γ)) * Δe + ENNReal.ofReal (70 * S.ξ γ) := by
          rw [e1, e2, e3]
      _ ≤ residualMajorant S γ P01 ω := le_self_add
  · -- the bad event: `‖ν − λ‖_G² ≤ 2Θ² + 3 ≤ 4Θ²` and `1 < 100 Δ₃`
    have hbad : ENNReal.ofReal (1 / 100) < Δe := not_le.1 hgood
    have hlam : IsRegular (segMeasure 0 1) := isRegular_segMeasure zero_ne_one
    have h2 := energyDistSq_le_two_mul_add S.frame hreg hlam
    rw [energy_segMeasure_zero_one] at h2
    have hΘ2 : 2 ≤ Θe.toReal ^ 2 := by
      rw [hΘe_def, Setup.toReal_locTheta_sq hT hB]
      have h1 := Real.log_nonneg hB1
      have h2 := Real.log_nonneg (show (1 : ℝ) ≤ (S.locT γ (Metric.closedBall 0 1) ω).toReal by
        linarith)
      linarith
    have hle : energyDistSq (lengthMeasure η) (segMeasure 0 1) ≤ 4 * Θe.toReal ^ 2 := by
      linarith
    have h100 : 1 ≤ 100 * Δe := by
      calc (1 : ℝ≥0∞) = 100 * ENNReal.ofReal (1 / 100) := by
            rw [← ENNReal.ofReal_ofNat 100, ← ENNReal.ofReal_mul (by norm_num),
              show (100 : ℝ) * (1 / 100) = 1 by norm_num, ENNReal.ofReal_one]
        _ ≤ 100 * Δe := by gcongr
    calc ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure 0 1))
        ≤ ENNReal.ofReal (4 * Θe.toReal ^ 2) := ENNReal.ofReal_le_ofReal hle
      _ = 4 * Θe ^ 2 * 1 := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hΘ, ENNReal.ofReal_ofNat, mul_one]
      _ ≤ 4 * Θe ^ 2 * (100 * Δe) := by gcongr
      _ = 400 * (Θe ^ 2 * Δe) := by ring
      _ ≤ residualMajorant S γ P01 ω := le_add_self

/-! ## The expectation of the majorant (GA5 (a3), "Proof of the (3.4) row") -/

/-- `L = log(1/ξ) ≥ 1` for `0 < ξ ≤ 1/10` (since `e < 10`). -/
theorem one_le_log_one_div {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 10) : 1 ≤ Real.log (1 / ξ) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  calc Real.exp 1 ≤ 10 := by linarith [Real.exp_one_lt_d9]
    _ ≤ 1 / ξ := by rw [le_div_iff₀ hξ]; linarith

/-- **The expectation of the majorant** (GA5 (a3), "Proof of the (3.4) row", with `ε = 1/100`;
rulings G16, G23): there are `γs > 0` and `K ≥ 0` such that for `γ ∈ (0, γs]` and every measurable
`P01`: `0 < ξ ≤ 1/10` and `E W ≤ 66 E M(P01) + K ξ^{99/100} L`. Proof: Cauchy–Schwarz
(`lintegral_mul_le_of_sq`) with `‖Δ₃‖₂ ≤ √C ξ^{99/100}`, `E B² ≤ C`, `E Θ⁴ ≤ C`;
`E Δ₃ ≤ C ξ^{99/100}`; `ξ ≤ ξ^{99/100}` and `L ≥ 1`. -/
theorem lintegral_residualMajorant_le (S : Setup) : ∃ γs K : ℝ, 0 < γs ∧ 0 ≤ K ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ P01 : Coord → C(unitInterval, ℂ), Measurable P01 →
      0 < S.ξ γ ∧ S.ξ γ ≤ 1 / 10 ∧
      ∫⁻ ω, residualMajorant S γ P01 ω ∂stdP ≤
        66 * ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP +
          ENNReal.ofReal (K * S.ξ γ ^ (99 / 100 : ℝ) * Real.log (1 / S.ξ γ)) := by
  obtain ⟨γa, Ca, hγa, hCa, ha⟩ := exists_lintegral_euclidErr_rpow_le S (R := 3) (by norm_num)
    (ε := 1 / 100) (by norm_num) (p := 2) one_le_two
  obtain ⟨γb, Cb, hγb, hCb, hb⟩ := exists_lintegral_euclidErr_rpow_le S (R := 3) (by norm_num)
    (ε := 1 / 100) (by norm_num) (p := 1) le_rfl
  obtain ⟨γc, CB, hγc, hc⟩ := exists_locMoments_closedBall_one S 2 one_le_two
  obtain ⟨γd, CΘ, hγd, hd⟩ := exists_locMoments_closedBall_one S 4 (by norm_num)
  obtain ⟨γe, C₁, hγe, hγe2, hexp⟩ := S.exists_exponents
  set CB' : ℝ := max CB 0 with hCB'
  set CΘ' : ℝ := max CΘ 0 with hCΘ'
  set K : ℝ := 140 * (Real.sqrt Ca * Real.sqrt CB') + 70 * Cb + 70 +
    400 * (Real.sqrt CΘ' * Real.sqrt Ca) with hK
  refine ⟨min (min (min γa γb) (min γc γd)) γe, K,
    lt_min (lt_min (lt_min hγa hγb) (lt_min hγc hγd)) hγe, by positivity,
    fun γ hγ P01 hP01 => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγa' : γ ≤ γa :=
    hγle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hγb' : γ ≤ γb :=
    hγle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hγc' : γ ≤ γc :=
    hγle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hγd' : γ ≤ γd :=
    hγle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hγe' : γ ≤ γe := hγle.trans (min_le_right _ _)
  obtain ⟨hξ, hξ1, hΔ2⟩ := ha γ ⟨hγ0, hγa'⟩
  obtain ⟨-, -, hΔ1⟩ := hb γ ⟨hγ0, hγb'⟩
  obtain ⟨-, hB2, -⟩ := hc γ ⟨hγ0, hγc'⟩
  obtain ⟨-, -, hΘ4⟩ := hd γ ⟨hγ0, hγd'⟩
  have hξ10 : S.ξ γ ≤ 1 / 10 := (hexp γ ⟨hγ0, hγe'⟩).2.2.1
  refine ⟨hξ, hξ10, ?_⟩
  -- measurability
  have hMm : Measurable fun ω => ENNReal.ofReal (maxDev (P01 ω)) :=
    ENNReal.measurable_ofReal.comp (measurable_maxDev_comp hP01)
  have hΔm : Measurable (S.euclidErr γ 3) := S.measurable_euclidErr γ 3
  have hBm : Measurable (S.locB γ (Metric.closedBall 0 1) 1) := S.measurable_locB γ _ 1
  have hΘm : Measurable fun ω => S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 :=
    (S.measurable_locTheta γ _ 1).pow_const 2
  -- split the integral
  have hsplit : ∫⁻ ω, residualMajorant S γ P01 ω ∂stdP =
      66 * ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP +
        140 * ∫⁻ ω, S.euclidErr γ 3 ω * S.locB γ (Metric.closedBall 0 1) 1 ω ∂stdP +
        ENNReal.ofReal (70 * Real.log (1 / S.ξ γ)) * ∫⁻ ω, S.euclidErr γ 3 ω ∂stdP +
        ENNReal.ofReal (70 * S.ξ γ) +
        400 * ∫⁻ ω, S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 * S.euclidErr γ 3 ω ∂stdP := by
    have hm5 : Measurable fun ω =>
        400 * (S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 * S.euclidErr γ 3 ω) :=
      (hΘm.mul hΔm).const_mul 400
    have hm4 : Measurable fun _ : Coord => ENNReal.ofReal (70 * S.ξ γ) := measurable_const
    have hm3 : Measurable fun ω =>
        ENNReal.ofReal (70 * Real.log (1 / S.ξ γ)) * S.euclidErr γ 3 ω := hΔm.const_mul _
    have hm2 : Measurable fun ω =>
        140 * (S.euclidErr γ 3 ω * S.locB γ (Metric.closedBall 0 1) 1 ω) :=
      (hΔm.mul hBm).const_mul 140
    have hm2' : Measurable fun ω => S.euclidErr γ 3 ω * S.locB γ (Metric.closedBall 0 1) 1 ω :=
      hΔm.mul hBm
    have hm5' : Measurable fun ω =>
        S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 * S.euclidErr γ 3 ω := hΘm.mul hΔm
    simp only [residualMajorant]
    rw [lintegral_add_right _ hm5, lintegral_add_right _ hm4, lintegral_add_right _ hm3,
      lintegral_add_right _ hm2, lintegral_const_mul _ hMm, lintegral_const_mul _ hm2',
      lintegral_const_mul _ hΔm, lintegral_const, lintegral_const_mul _ hm5',
      measure_univ, mul_one]
  rw [hsplit]
  set ξ := S.ξ γ with hξ_def
  set L := Real.log (1 / ξ) with hL_def
  have hL1 : 1 ≤ L := one_le_log_one_div hξ hξ10
  have hL0 : 0 ≤ L := by linarith
  set u := ξ ^ (99 / 100 : ℝ) with hu_def
  have hu0 : 0 ≤ u := Real.rpow_nonneg hξ.le _
  have hξu : ξ ≤ u := by
    have h := Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (show (99 / 100 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  -- the moment bounds in the form of `lintegral_mul_le_of_sq`
  have hΔsq : ∫⁻ ω, S.euclidErr γ 3 ω ^ (2 : ℝ) ∂stdP ≤
      ENNReal.ofReal ((Real.sqrt Ca * u) ^ 2) := by
    refine hΔ2.trans (le_of_eq ?_)
    congr 1
    rw [mul_pow, Real.sq_sqrt hCa, hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hξ.le]
    norm_num
  have hBsq : ∫⁻ ω, S.locB γ (Metric.closedBall 0 1) 1 ω ^ (2 : ℝ) ∂stdP ≤
      ENNReal.ofReal (Real.sqrt CB' ^ 2) := by
    rw [Real.sq_sqrt (le_max_right _ _)]
    exact hB2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hΘsq : ∫⁻ ω, (S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2) ^ (2 : ℝ) ∂stdP ≤
      ENNReal.ofReal (Real.sqrt CΘ' ^ 2) := by
    rw [Real.sq_sqrt (le_max_right _ _)]
    have e : ∀ ω, (S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2) ^ (2 : ℝ) =
        S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ (4 : ℝ) := by
      intro ω
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    simp_rw [e]
    exact hΘ4.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the three expectations
  have hP1 : ∫⁻ ω, S.euclidErr γ 3 ω * S.locB γ (Metric.closedBall 0 1) 1 ω ∂stdP ≤
      ENNReal.ofReal (Real.sqrt Ca * u * Real.sqrt CB') :=
    lintegral_mul_le_of_sq hΔm.aemeasurable hBm.aemeasurable (by positivity) (by positivity)
      hΔsq hBsq
  have hP2 : ∫⁻ ω, S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 * S.euclidErr γ 3 ω ∂stdP ≤
      ENNReal.ofReal (Real.sqrt CΘ' * (Real.sqrt Ca * u)) :=
    lintegral_mul_le_of_sq hΘm.aemeasurable hΔm.aemeasurable (by positivity) (by positivity)
      hΘsq hΔsq
  have hP3 : ∫⁻ ω, S.euclidErr γ 3 ω ∂stdP ≤ ENNReal.ofReal (Cb * u) := by
    have e : (1 : ℝ) * (1 - 1 / 100) = 99 / 100 := by norm_num
    rw [e] at hΔ1
    simp only [ENNReal.rpow_one] at hΔ1
    exact hΔ1
  -- conclusion
  have hreal : 140 * (Real.sqrt Ca * u * Real.sqrt CB') + 70 * L * (Cb * u) + 70 * ξ +
      400 * (Real.sqrt CΘ' * (Real.sqrt Ca * u)) ≤ K * u * L := by
    have hP0 : 0 ≤ Real.sqrt Ca * Real.sqrt CB' := by positivity
    have hQ0 : 0 ≤ Real.sqrt CΘ' * Real.sqrt Ca := by positivity
    have h1 : Real.sqrt Ca * Real.sqrt CB' * u ≤ Real.sqrt Ca * Real.sqrt CB' * u * L :=
      le_mul_of_one_le_right (by positivity) hL1
    have h2 : Real.sqrt CΘ' * Real.sqrt Ca * u ≤ Real.sqrt CΘ' * Real.sqrt Ca * u * L :=
      le_mul_of_one_le_right (by positivity) hL1
    have h3 : u ≤ u * L := le_mul_of_one_le_right hu0 hL1
    rw [hK]
    linarith
  have hsum : 140 * ENNReal.ofReal (Real.sqrt Ca * u * Real.sqrt CB') +
      ENNReal.ofReal (70 * L) * ENNReal.ofReal (Cb * u) + ENNReal.ofReal (70 * ξ) +
      400 * ENNReal.ofReal (Real.sqrt CΘ' * (Real.sqrt Ca * u)) =
      ENNReal.ofReal (140 * (Real.sqrt Ca * u * Real.sqrt CB') + 70 * L * (Cb * u) + 70 * ξ +
        400 * (Real.sqrt CΘ' * (Real.sqrt Ca * u))) := by
    have e1 : (140 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt Ca * u * Real.sqrt CB') =
        ENNReal.ofReal (140 * (Real.sqrt Ca * u * Real.sqrt CB')) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 140), ENNReal.ofReal_ofNat]
    have e2 : ENNReal.ofReal (70 * L) * ENNReal.ofReal (Cb * u) =
        ENNReal.ofReal (70 * L * (Cb * u)) := (ENNReal.ofReal_mul (by positivity)).symm
    have e3 : (400 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt CΘ' * (Real.sqrt Ca * u)) =
        ENNReal.ofReal (400 * (Real.sqrt CΘ' * (Real.sqrt Ca * u))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 400), ENNReal.ofReal_ofNat]
    rw [e1, e2, e3, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc 66 * ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP +
        140 * ∫⁻ ω, S.euclidErr γ 3 ω * S.locB γ (Metric.closedBall 0 1) 1 ω ∂stdP +
        ENNReal.ofReal (70 * L) * ∫⁻ ω, S.euclidErr γ 3 ω ∂stdP + ENNReal.ofReal (70 * ξ) +
        400 * ∫⁻ ω, S.locTheta γ (Metric.closedBall 0 1) 1 ω ^ 2 * S.euclidErr γ 3 ω ∂stdP
      ≤ 66 * ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP +
        140 * ENNReal.ofReal (Real.sqrt Ca * u * Real.sqrt CB') +
        ENNReal.ofReal (70 * L) * ENNReal.ofReal (Cb * u) + ENNReal.ofReal (70 * ξ) +
        400 * ENNReal.ofReal (Real.sqrt CΘ' * (Real.sqrt Ca * u)) := by
        gcongr
    _ = 66 * ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP +
        (140 * ENNReal.ofReal (Real.sqrt Ca * u * Real.sqrt CB') +
          ENNReal.ofReal (70 * L) * ENNReal.ofReal (Cb * u) + ENNReal.ofReal (70 * ξ) +
          400 * ENNReal.ofReal (Real.sqrt CΘ' * (Real.sqrt Ca * u))) := by ring
    _ ≤ 66 * ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP + ENNReal.ofReal (K * u * L) := by
        rw [hsum]
        gcongr

/-! ## Lemma 3.2′ -/

/-- **Lemma 3.2′, the residual variance** (source §3, (3.3)–(3.4); GA2 D2, GA5 (a2)–(a3), GA3 R3;
rulings G16, G23). There are `γ₀ > 0` and `C` such that for every `γ ∈ (0, γ₀]` and every measurable
`P01 : ℝ^ℕ → C([0,1], ℂ)` that is almost surely a constant-speed geodesic from `0` to `1` for
`S.D γ`: `M(P01) = maxDev (P01 ·)` is integrable, `Z = ξ F ∈ L²` (`F = S.firstOrderErr γ 0 1`), and
`E Z² ≤ C ξ² (E M(P01) + ξ^{99/100} log(1/ξ))`. -/
theorem residualVariance (S : Setup) : ∃ γ₀ C : ℝ, 0 < γ₀ ∧ ∀ γ ∈ Ioc (0 : ℝ) γ₀,
    ∀ P01 : Coord → C(unitInterval, ℂ), Measurable P01 →
      (∀ᵐ ω ∂stdP, LQGMetric.Blueprint.IsGeod01 (S.D γ ω) 0 1 (P01 ω)) →
      Integrable (fun ω => maxDev (P01 ω)) stdP ∧
      MemLp (fun ω => S.ξ γ * S.firstOrderErr γ 0 1 ω) 2 stdP ∧
      ∫ ω, (S.ξ γ * S.firstOrderErr γ 0 1 ω) ^ 2 ∂stdP ≤
        C * S.ξ γ ^ 2 * ((∫ ω, maxDev (P01 ω) ∂stdP) +
          S.ξ γ ^ (99 / 100 : ℝ) * Real.log (1 / S.ξ γ)) := by
  obtain ⟨γ1, hγ1, -, hPoin⟩ := firstOrder_sq_of_majorant S
  obtain ⟨γ2, hγ2, hW⟩ := ae_energyDistSq_le_residualMajorant S
  obtain ⟨γ3, K, hγ3, hK, hEW⟩ := lintegral_residualMajorant_le S
  obtain ⟨γ4, CT, hγ4, hT1⟩ := exists_locMoments_closedBall_one S 1 le_rfl
  obtain ⟨γ5, hγ5, hloc⟩ := ae_localization_zero_one S
  refine ⟨min (min γ1 γ2) (min γ3 (min γ4 γ5)), Real.pi ^ 2 / 4 * max 66 K,
    lt_min (lt_min hγ1 hγ2) (lt_min hγ3 (lt_min hγ4 hγ5)), fun γ hγ P01 hP01 hgeo => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγ1' : γ ≤ γ1 := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγ2' : γ ≤ γ2 := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ3' : γ ≤ γ3 := hγle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ4' : γ ≤ γ4 :=
    hγle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hγ5' : γ ≤ γ5 :=
    hγle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- `E M ≤ E T < ∞`
  have hTint : Integrable (fun ω => (S.locT γ (Metric.closedBall 0 1) ω).toReal) stdP := by
    refine integrable_toReal_of_lintegral_ne_top (S.measurable_locT γ _).aemeasurable ?_
    have h := (hT1 γ ⟨hγ0, hγ4'⟩).1
    simp only [ENNReal.rpow_one] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hMint : Integrable (fun ω => maxDev (P01 ω)) stdP := by
    refine hTint.mono' (measurable_maxDev_comp hP01).aestronglyMeasurable ?_
    filter_upwards [hloc γ ⟨hγ0, hγ5'⟩, hgeo] with ω hω hη
    rw [Real.norm_eq_abs, abs_of_nonneg (maxDev_nonneg _)]
    exact (hω.2.2.2.2.2 (P01 ω) hη).2.1
  -- the Gaussian Poincaré inequality with the majorant `W`
  have hWae : ∀ᵐ ω ∂stdP, ∃ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) 0 1 η ∧
      IsRegular (lengthMeasure η) ∧
      ENNReal.ofReal (energyDistSq (lengthMeasure η) (segMeasure 0 1)) ≤
        residualMajorant S γ P01 ω := by
    filter_upwards [hW γ ⟨hγ0, hγ2'⟩ P01 hgeo, hgeo] with ω h1 h2
    exact ⟨P01 ω, h2, h1.1, h1.2⟩
  obtain ⟨hFp, -, hF2⟩ :=
    hPoin γ ⟨hγ0, hγ1'⟩ 0 1 zero_ne_one (residualMajorant S γ P01) hWae
  obtain ⟨hξ, -, hEW'⟩ := hEW γ ⟨hγ0, hγ3'⟩ P01 hP01
  refine ⟨hMint, hFp.const_mul (S.ξ γ), ?_⟩
  set F := S.firstOrderErr γ 0 1 with hF
  set m := ∫ ω, maxDev (P01 ω) ∂stdP with hm
  set ξ := S.ξ γ with hξ_def
  set u := ξ ^ (99 / 100 : ℝ) with hu_def
  set L := Real.log (1 / ξ) with hL_def
  have hm0 : 0 ≤ m := integral_nonneg fun ω => maxDev_nonneg _
  have hu0 : 0 ≤ u := Real.rpow_nonneg hξ.le _
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    have := (hEW γ ⟨hγ0, hγ3'⟩ P01 hP01).2.1
    rw [le_div_iff₀ hξ]
    linarith)
  have hK0 : 0 ≤ K * u * L := by positivity
  have huL : 0 ≤ u * L := by positivity
  have hlinM : ∫⁻ ω, ENNReal.ofReal (maxDev (P01 ω)) ∂stdP = ENNReal.ofReal m :=
    (ofReal_integral_eq_lintegral_ofReal hMint (ae_of_all _ fun ω => maxDev_nonneg _)).symm
  -- `E F² ≤ (π²/4)(66 m + K u L)`
  have hF2' : ∫ ω, F ω ^ 2 ∂stdP ≤ Real.pi ^ 2 / 4 * (66 * m + K * u * L) := by
    have h : ENNReal.ofReal (∫ ω, F ω ^ 2 ∂stdP) ≤
        ENNReal.ofReal (Real.pi ^ 2 / 4 * (66 * m + K * u * L)) := by
      refine hF2.trans ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 66), ENNReal.ofReal_ofNat, ← hlinM]
      gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hsqint : ∫ ω, (ξ * F ω) ^ 2 ∂stdP = ξ ^ 2 * ∫ ω, F ω ^ 2 ∂stdP := by
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  have hmax : 66 * m + K * u * L ≤ max 66 K * (m + u * L) := by
    have h1 : 66 * m ≤ max 66 K * m := mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
    have h2 : K * (u * L) ≤ max 66 K * (u * L) := mul_le_mul_of_nonneg_right (le_max_right _ _) huL
    nlinarith
  rw [hsqint]
  calc ξ ^ 2 * ∫ ω, F ω ^ 2 ∂stdP ≤ ξ ^ 2 * (Real.pi ^ 2 / 4 * (66 * m + K * u * L)) := by
        gcongr
    _ ≤ ξ ^ 2 * (Real.pi ^ 2 / 4 * (max 66 K * (m + u * L))) := by gcongr
    _ = Real.pi ^ 2 / 4 * max 66 K * ξ ^ 2 * (m + u * L) := by ring

end SmallGammaGeodesics
