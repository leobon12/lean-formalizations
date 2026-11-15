/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi2OscGen
import InteractingSLE.Spec.Sec7.TrialsHiEnergy

/-!
# The oscillation clock of the inner reference has finite expectation

Packet PROVE-TRIALS-HI2. For an evolution of a separated word whose only nonzero weights sit at the nearest marks,
with `a = 2 + Σρ^L > 0` and `b = 2 + Σρ^R > κ/2`, the localized Itô martingale of the Lyapunov function
`Φ_ε = D^{−θ}(ψ_ε(1 − U) + λ)` (`oscMart`, PROVE-SEC7-C7's `Clock.martingale_angLoc`) gives, with the generator bound
`oscGen ≤ −c₀ D^{−θ−2}((1 − U)² + ε²)^{−θ/2−1}` and `Φ_ε ≥ 0`,

  `c₀ ∫₀^{σ_n} D^{−θ−2} ((1 − U)² + ε²)^{−θ/2−1} ≤ M_n`,  `E M_n = Φ_ε(start) ≤ Φ̄`  (uniformly in `ε`)

(`oscRate`, `oscClock_le_oscMart`, `integral_oscMart`). Fatou's lemma along `ε_n = 1/(n + 1)` then bounds the
expected limit inferior (`exists_lintegral_liminf_le`).

## Main results

* `oscMart`, `martingale_oscMart`, `oscMart_eq`, `oscRate`, `oscClock_le_oscMart`, `integral_oscMart`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi2

open Zhan Clock

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The localized martingale of the side-oscillation Lyapunov function.** -/
def oscMart (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (θ ε lam : ℝ) (n : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  oscΦ κ xL xR ρL ρR θ ε lam
      (coordA xL xR G VL VR (fun _ _ => 0) (min t (angLoc G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
      Ito.itoGen (oscΦ κ xL xR ρL ρR θ ε lam)
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)

/-- The rate `D^{−θ−2} ((1 − U)² + ε²)^{−θ/2−1}` of the oscillation clock, along a path. -/
def oscRate (θ ε : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  gapAt vL vR s.toNNReal ^ (-θ) / gapAt vL vR s.toNNReal ^ 2 *
    ((1 - angAt w vL vR s.toNNReal) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)

section Facts

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hE hGm hGc hgood hT hx in
theorem martingale_oscMart {θ ε : ℝ} (hε : 0 < ε) (lam : ℝ) (n : ℕ) :
    Martingale (oscMart κ xL xR ρL ρR G T W VL VR B ζ θ ε lam n) (usualAugmentation 𝓕 P) P :=
  martingale_angLoc hE hGm hGc hgood hT hx (contDiffOn_oscΦ hε lam) n
    (I := fun _ _ => 0) (c := fun _ _ => 0) (KI := 0) (Kc := 0) (fun _ _ _ _ => by simp)
    (fun _ _ => intervalIntegrable_const) (fun _ _ => by simp) (fun _ _ _ _ => by simp)
    ⟨fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ => rfl⟩ (fun _ _ => continuousOn_const)

include hgood hx in
/-- **The martingale along a good path**: `Φ_ε(X_r) − ∫₀^r oscGen`, `r = t ∧ σ_n`. -/
theorem oscMart_eq (hκ : 0 ≤ κ) {θ ε : ℝ} (hε : 0 < ε) (lam : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    oscMart κ xL xR ρL ρR G T W VL VR B ζ θ ε lam n t ω =
      oscΦ κ xL xR ρL ρR θ ε lam (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0
          (min t (angLoc G T W VL VR B ζ n ω))) -
        ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
          oscGen κ ρL ρR θ ε lam (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
  have hω' := hgood ω hω
  have hp := hω'.1
  set σ := angLoc G T W VL VR B ζ n ω
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hrζ : ((min t σ : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hσζ
  have hc0 : (coordA xL xR G VL VR (fun _ _ => 0) (min t σ) ω, Sec2.TwoSeed.brownG G B (min t σ) ω) =
      pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 (min t σ) := by
    simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]; rfl
  simp only [oscMart]
  rw [hc0]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (min t σ).coe_nonneg] at hs
  have hsζ := Sec2.toNNReal_lt_of_mem_Icc hrζ hs
  have h := itoGen_oscΦ_pathCoord hp hκ hx (θ := θ) hε lam 0 0 hsζ
  simp only [coordA, densA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
  refine h.trans ?_
  simp only [oscGen, genExpr, Real.toNNReal_coe]

end Facts

/-! ### Integrability along a path -/

section Path

variable {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ₀ : ℝ≥0∞}

theorem continuousOn_oscRate (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ₀) (hx : 0 < xR 0 - xL 0)
    {θ ε : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ₀) :
    ContinuousOn (oscRate θ ε w vL vR) (Icc 0 (σ : ℝ)) := by
  have hD := continuousOn_gapAt hp hσ
  have hU := continuousOn_angAt hp hx hσ
  have hDpos : ∀ s ∈ Icc 0 (σ : ℝ), 0 < gapAt vL vR s.toNNReal := fun s hs => gapAt_pos hp hx hσ hs
  refine ((hD.rpow_const fun s hs => Or.inl (hDpos s hs).ne').div (hD.pow 2)
    fun s hs => pow_ne_zero 2 (hDpos s hs).ne').mul ?_
  exact ((continuousOn_const.sub hU).pow 2 |>.add continuousOn_const).rpow_const fun s _ =>
    Or.inl (sq_add_sq_pos' hε _).ne'

theorem intervalIntegrable_oscGen (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ₀) (hx : 0 < xR 0 - xL 0)
    {θ ε : ℝ} (hε : 0 < ε) (lam : ℝ) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ₀) :
    IntervalIntegrable (oscGen κ ρL ρR θ ε lam w vL vR) volume 0 σ := by
  have hF := hp.isForcePath
  have hD := continuousOn_gapAt hp hσ
  have hU := continuousOn_angAt hp hx hσ
  have hDpos : ∀ s ∈ Icc 0 (σ : ℝ), 0 < gapAt vL vR s.toNNReal := fun s hs => gapAt_pos hp hx hσ hs
  have hc' : Continuous (oscH' θ ε) := continuous_iff_continuousAt.2 fun u => (hasDerivAt_oscH' hε u).continuousAt
  have hc'' : Continuous (oscH'' θ ε) := by
    unfold oscH'' psiE''
    refine (continuous_const.mul ?_).add ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).mul ?_)
    · exact ((continuous_const.sub continuous_id).pow 2 |>.add continuous_const).rpow_const fun u =>
        Or.inl (sq_add_sq_pos' hε _).ne'
    · exact ((continuous_const.sub continuous_id).pow 2 |>.add continuous_const).rpow_const fun u =>
        Or.inl (sq_add_sq_pos' hε _).ne'
  have h1 := intervalIntegrable_genExpr hp hx hc' hc'' hσ (ρL := ρL) (ρR := ρR)
  have hDθ : ContinuousOn (fun s : ℝ => gapAt vL vR s.toNNReal ^ (-θ)) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]; exact hD.rpow_const fun s hs => Or.inl (hDpos s hs).ne'
  have h2 : ContinuousOn (fun s : ℝ => oscH θ ε lam (angAt w vL vR s.toNNReal) *
      (-θ * gapAt vL vR s.toNNReal ^ (-θ - 1))) (uIcc 0 (σ : ℝ)) := by
    rw [uIcc_of_le σ.coe_nonneg]
    exact ((contDiff_oscH (n := 0) hε lam).continuous.comp_continuousOn hU).mul
      (continuousOn_const.mul (hD.rpow_const fun s hs => Or.inl (hDpos s hs).ne'))
  have h3 := ((hF.intervalIntegrable_forceR hσ 0).sub (hF.intervalIntegrable_forceL hσ 0)).continuousOn_mul h2
  have h4 := h1.continuousOn_mul hDθ
  refine (h4.add h3).congr fun s _ => ?_
  simp only [oscGen]
  ring

/-- **The oscillation clock is dominated by the generator** on `[0, σ]`, `σ < ζ`. -/
theorem integral_oscRate_le (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ₀) (hx : 0 < xR 0 - xL 0)
    (hρL : ∀ i, i ≠ 0 → ρL i = 0) (hρR : ∀ j, j ≠ 0 → ρR j = 0) {θ ε lam c₀ : ℝ} (hε : 0 < ε)
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, oscJ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) θ ε lam u ≤
      -c₀ * ((1 - u) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ₀) :
    c₀ * ∫ s in (0 : ℝ)..σ, oscRate θ ε w vL vR s ≤ -∫ s in (0 : ℝ)..σ, oscGen κ ρL ρR θ ε lam w vL vR s := by
  have hF := hp.isForcePath
  have hgi := intervalIntegrable_oscGen hp hx (θ := θ) hε lam hσ (ρL := ρL) (ρR := ρR)
  have hri : IntervalIntegrable (oscRate θ ε w vL vR) volume 0 σ :=
    (continuousOn_oscRate hp hx hε hσ (θ := θ)).intervalIntegrable_of_Icc σ.coe_nonneg
  have hle : ∫ s in (0 : ℝ)..σ, oscGen κ ρL ρR θ ε lam w vL vR s ≤
      ∫ s in (0 : ℝ)..σ, -c₀ * oscRate θ ε w vL vR s := by
    refine intervalIntegral.integral_mono_ae_restrict σ.coe_nonneg hgi (hri.const_mul _) ?_
    have hnc := ae_not_collision hF hσ
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := Measure.ae_ne volume 0
    filter_upwards [hnc, h0] with s hs hs0 hsI
    have hsI' : s ∈ Ioc 0 (σ : ℝ) := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
    obtain ⟨hL, hR⟩ := hs hsI'
    have hsζ := Sec2.toNNReal_lt_of_mem_Icc hσ hsI
    exact oscGen_le hρL hρR hJ (lt_of_le_of_ne (hF.vL_le_w hsζ 0) (hL 0))
      (lt_of_le_of_ne (hF.w_le_vR hsζ 0) (Ne.symm (hR 0)))
  rw [intervalIntegral.integral_const_mul] at hle
  linarith

end Path

/-! ### The side oscillation is dominated by the oscillation clock -/

section Pointwise

/-- `min(a, b) ≤ a^{1−θ} b^θ`, in the form `X ≤ a, X ≤ b ⇒ X ≤ a^{1−θ} b^θ` (`0 ≤ θ ≤ 1`). -/
theorem le_rpow_mul_rpow_of_le {X a b θ : ℝ} (hX : 0 ≤ X) (hXa : X ≤ a) (hXb : X ≤ b) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : X ≤ a ^ (1 - θ) * b ^ θ := by
  rcases hX.eq_or_lt with h | h
  · rw [← h]; exact mul_nonneg (Real.rpow_nonneg (hX.trans hXa) _) (Real.rpow_nonneg (hX.trans hXb) _)
  have e : X = X ^ (1 - θ) * X ^ θ := by
    rw [← Real.rpow_add h]; simp
  rw [e]
  exact mul_le_mul (Real.rpow_le_rpow hX hXa (by linarith)) (Real.rpow_le_rpow hX hXb hθ0)
    (Real.rpow_nonneg hX _) (Real.rpow_nonneg (hX.trans hXa) _)

/-- **The pointwise comparison**: for `R > 0`, `0 ≤ Δ ≤ Δ₀`, `0 < θ ≤ 1`, `D > 0`, `y = R/D ≥ ε > 0`,
`1/R² − 1/(R + Δ)² ≤ (2Δ₀)^θ 2^{θ/2+1} D^{−θ}/D² (y² + ε²)^{−θ/2−1}`. -/
theorem inv_sq_sub_inv_sq_le {R Δ Δ₀ D y ε θ : ℝ} (hR : 0 < R) (hΔ : 0 ≤ Δ) (hΔ₀ : Δ ≤ Δ₀) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hD : 0 < D) (hy : y = R / D) (hε : 0 < ε) (hεy : ε ≤ y) :
    1 / R ^ 2 - 1 / (R + Δ) ^ 2 ≤
      (2 * Δ₀) ^ θ * (2 : ℝ) ^ (θ / 2 + 1) * (D ^ (-θ) / D ^ 2 * (y ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) := by
  have hRΔ : 0 < R + Δ := by linarith
  set X := 1 / R ^ 2 - 1 / (R + Δ) ^ 2 with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef, sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hR.le (by linarith) 2)
  have hXa : X ≤ 1 / R ^ 2 := by rw [hXdef]; have : 0 ≤ 1 / (R + Δ) ^ 2 := by positivity
                                 linarith
  have hXb : X ≤ 2 * Δ₀ / R ^ 3 := by
    have e : X = Δ * (2 * R + Δ) / (R ^ 2 * (R + Δ) ^ 2) := by rw [hXdef]; field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Δ * (2 * R + Δ) * R ^ 3 ≤ 2 * Δ * (R ^ 2 * (R + Δ) ^ 2) := by
      have : 0 ≤ Δ * R ^ 2 * (3 * R * Δ + 2 * Δ ^ 2) := by positivity
      nlinarith
    have h2 : 2 * Δ * (R ^ 2 * (R + Δ) ^ 2) ≤ 2 * Δ₀ * (R ^ 2 * (R + Δ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hmin := le_rpow_mul_rpow_of_le hX0 hXa hXb hθ0.le hθ1
  -- `(1/R²)^{1−θ} (2Δ₀/R³)^θ = (2Δ₀)^θ R^{−2−θ}`
  have hΔ₀ : 0 ≤ Δ₀ := hΔ.trans hΔ₀
  have hR2 : (1 / R ^ 2) ^ (1 - θ) = R ^ (-2 * (1 - θ)) := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hR.le, ← Real.rpow_mul hR.le]; norm_num
  have hR3 : (2 * Δ₀ / R ^ 3) ^ θ = (2 * Δ₀) ^ θ * R ^ (-3 * θ) := by
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hR.le, div_eq_mul_inv,
      ← Real.rpow_neg hR.le]
    norm_num
  have hprod : (1 / R ^ 2) ^ (1 - θ) * (2 * Δ₀ / R ^ 3) ^ θ = (2 * Δ₀) ^ θ * R ^ (-θ - 2) := by
    rw [hR2, hR3, mul_left_comm, ← Real.rpow_add hR]
    congr 2; ring
  rw [hprod] at hmin
  -- `R^{−θ−2} ≤ 2^{θ/2+1} D^{−θ}/D² (y² + ε²)^{−θ/2−1}`
  have hy0 : 0 < y := by rw [hy]; positivity
  have hRy : R = y * D := by rw [hy]; field_simp
  have hpow : y ^ 2 + ε ^ 2 ≤ 2 * y ^ 2 := by nlinarith
  have h1 : (2 * y ^ 2) ^ (-θ / 2 - 1) ≤ (y ^ 2 + ε ^ 2) ^ (-θ / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hpow (by linarith)
  have h2 : R ^ (-θ - 2) = (2 : ℝ) ^ (θ / 2 + 1) * (D ^ (-θ) / D ^ 2 * (2 * y ^ 2) ^ (-θ / 2 - 1)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), hRy, Real.mul_rpow hy0.le hD.le]
    have e1 : (y ^ 2) ^ (-θ / 2 - 1) = y ^ (-θ - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; congr 1; push_cast; ring
    have e2 : D ^ (-θ) / D ^ 2 = D ^ (-θ - 2) := by
      rw [Real.rpow_sub hD, Real.rpow_two]
    have e3 : (2 : ℝ) ^ (θ / 2 + 1) * (2 : ℝ) ^ (-θ / 2 - 1) = 1 := by
      rw [← Real.rpow_add (by norm_num), show θ / 2 + 1 + (-θ / 2 - 1) = 0 by ring, Real.rpow_zero]
    rw [e1, e2]
    calc y ^ (-θ - 2) * D ^ (-θ - 2) = ((2 : ℝ) ^ (θ / 2 + 1) * (2 : ℝ) ^ (-θ / 2 - 1)) *
          (y ^ (-θ - 2) * D ^ (-θ - 2)) := by rw [e3, one_mul]
      _ = _ := by ring
  have hK : 0 ≤ (2 * Δ₀) ^ θ * (2 : ℝ) ^ (θ / 2 + 1) * (D ^ (-θ) / D ^ 2) := by positivity
  calc X ≤ (2 * Δ₀) ^ θ * R ^ (-θ - 2) := hmin
    _ = (2 * Δ₀) ^ θ * (2 : ℝ) ^ (θ / 2 + 1) * (D ^ (-θ) / D ^ 2) * (2 * y ^ 2) ^ (-θ / 2 - 1) := by
        rw [h2]; ring
    _ ≤ (2 * Δ₀) ^ θ * (2 : ℝ) ^ (θ / 2 + 1) * (D ^ (-θ) / D ^ 2) * (y ^ 2 + ε ^ 2) ^ (-θ / 2 - 1) :=
        mul_le_mul_of_nonneg_left h1 hK
    _ = _ := by ring

end Pointwise

/-! ### Fatou's lemma along `ε_n = 1/(n + 1)` -/

section Fatou

/-- The regularization parameter `ε_n = 1/(n + 1)`. -/
def epsN (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsN_pos (n : ℕ) : 0 < epsN n := by unfold epsN; positivity

/-- The upper bound `Φ̄ = D₀^{−θ} (((x^{R,0}/D₀)²)^{−θ/2} + λ)` of the initial value, uniform in `ε`. -/
def oscInit (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (θ lam : ℝ) : ℝ :=
  (xR 0 - xL 0) ^ (-θ) * (((xR 0 / (xR 0 - xL 0)) ^ 2) ^ (-θ / 2) + lam)

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hE hGm hGc hgood hT hx in
/-- **The expected oscillation clock, by Fatou's lemma.** There are measurable `g_n` with
`∫ liminf g_n ≤ Φ̄/c₀` and, almost surely on the good event, `∫₀^{σ_n} oscRate_{ε_n} ≤ g_n` for every `n`. -/
theorem exists_lintegral_liminf_le (hκ : 0 < κ) (hρL : ∀ i, i ≠ 0 → ρL i = 0) (hρR : ∀ j, j ≠ 0 → ρR j = 0)
    (hxR0 : 0 < xR 0) {θ lam c₀ : ℝ} (hθ0 : 0 < θ) (hlam : 0 ≤ lam) (hc₀ : 0 < c₀)
    (hJ : ∀ ε : ℝ, 0 < ε → ∀ u ∈ Ioo (0 : ℝ) 1, oscJ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) θ ε lam u ≤
      -c₀ * ((1 - u) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) :
    ∃ g : ℕ → Ω → ℝ≥0∞, (∀ n, Measurable (g n)) ∧
      ∫⁻ ω, liminf (fun n => g n ω) atTop ∂P ≤ ENNReal.ofReal (oscInit xL xR θ lam / c₀) ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ, ω ∈ G → ENNReal.ofReal (∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ),
        oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) ≤ g n ω := by
  have hP := hE.1.isProbabilityMeasure'
  set Mn : ℕ → ℝ≥0 → Ω → ℝ := fun n => oscMart κ xL xR ρL ρR G T W VL VR B ζ θ (epsN n) lam n with hMndef
  have hM : ∀ n, Martingale (Mn n) (usualAugmentation 𝓕 P) P := fun n =>
    martingale_oscMart hE hGm hGc hgood hT hx (epsN_pos n) lam n
  -- the initial value
  obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hGc
    exact one_ne_zero hGc
  have hp₀ := (hgood ω₀ hω₀).1
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω₀ := lt_of_le_of_lt bot_le ((hgood ω₀ hω₀).2.2.2.1 0)
  have hinit_eq : angInit xL xR = pathCoord (fun i t => VL i t ω₀) (fun j t => VR j t ω₀) (B · ω₀) 0 0 := by
    have hF := hp₀.isForcePath
    simp only [angInit, pathCoord, hF.vL_zero, hF.vR_zero, (hgood ω₀ hω₀).2.2.1]
  have hM0 : ∀ n ω, Mn n 0 ω = oscΦ κ xL xR ρL ρR θ (epsN n) lam (angInit xL xR) := fun n ω => by
    simp only [hMndef, oscMart, zero_min, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    by_cases hω : ω ∈ G
    · have hF := (hgood ω hω).1.isForcePath
      have e1 : (fun i => VL i 0 ω) = xL := funext hF.vL_zero
      have e2 : (fun j => VR j 0 ω) = xR := funext hF.vR_zero
      simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, e1, e2, (hgood ω hω).2.2.1, angInit]
    · simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte, angInit]
  have hEM : ∀ n : ℕ, ∫ ω, Mn n n ω ∂P = oscΦ κ xL xR ρL ρR θ (epsN n) lam (angInit xL xR) := fun n => by
    have h := (hM n).setIntegral_eq (zero_le (a := (n : ℝ≥0))) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [← h]
    simp only [hM0, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hinit : ∀ n : ℕ, oscΦ κ xL xR ρL ρR θ (epsN n) lam (angInit xL xR) ≤ oscInit xL xR θ lam := fun n => by
    have hU : angU κ xL xR ρL ρR (angInit xL xR) = (0 - xL 0) / (xR 0 - xL 0) := by
      rw [hinit_eq, angU_pathCoord hp₀ _ h0]
      simp only [angAt, gapAt, hp₀.1, hp₀.isForcePath.vL_zero, hp₀.isForcePath.vR_zero]
    have h1U : 1 - (0 - xL 0) / (xR 0 - xL 0) = xR 0 / (xR 0 - xL 0) := by field_simp; ring
    simp only [oscΦ, oscH, gapD_angInit, hU, h1U, oscInit]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx.le _)
    exact add_le_add (psiE_le hθ0.le (div_pos hxR0 hx).ne') le_rfl
  -- the pathwise bound
  have hpt : ∀ n : ℕ, ∀ ω ∈ G, c₀ * ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ),
      oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s ≤ Mn n n ω := by
    intro n ω hω
    have hω' := hgood ω hω
    have hp := hω'.1
    set σ := angLoc G T W VL VR B ζ n ω
    have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
    have hmin : min (n : ℝ≥0) σ = σ := min_eq_right (angLoc_le_n n ω)
    have hMe := oscMart_eq hgood hx hκ.le (epsN_pos n) lam n hω (n : ℝ≥0) (θ := θ)
    rw [hmin] at hMe
    have hle := integral_oscRate_le hp hx hρL hρR (epsN_pos n) (hJ _ (epsN_pos n)) hσζ
    have hΦ : 0 ≤ oscΦ κ xL xR ρL ρR θ (epsN n) lam
        (pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 σ) :=
      oscΦ_nonneg hlam (hx.trans_le (le_gapAt hp hσζ))
    have : Mn n n ω = _ := hMe
    rw [this]
    linarith
  have hMnn : ∀ n : ℕ, ∀ ω, 0 ≤ Mn n n ω := by
    intro n ω
    by_cases hω : ω ∈ G
    · refine le_trans ?_ (hpt n ω hω)
      have hω' := hgood ω hω
      have hσζ : ((angLoc G T W VL VR B ζ n ω : ℝ≥0) : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
      refine mul_nonneg hc₀.le (intervalIntegral.integral_nonneg (angLoc G T W VL VR B ζ n ω).coe_nonneg
        fun s hs => ?_)
      unfold oscRate
      exact mul_nonneg (div_nonneg (Real.rpow_nonneg (gapAt_pos hω'.1 hx hσζ hs).le _) (sq_nonneg _))
        (Real.rpow_nonneg (by positivity) _)
    · have h0 : angLoc G T W VL VR B ζ n ω = 0 := angLoc_of_not_mem hω n
      have : Mn n n ω = Mn n 0 ω := by
        simp only [hMndef, oscMart, h0, min_zero]
      rw [this, hM0]
      exact oscΦ_nonneg hlam (by rw [gapD_angInit]; exact hx)
  -- Fatou
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Mn n n ω / c₀) with hfdef
  have hfm : ∀ n, AEMeasurable (f n) P := fun n => (((hM n).integrable n).div_const c₀).aemeasurable.ennreal_ofReal
  set g : ℕ → Ω → ℝ≥0∞ := fun n => (hfm n).mk (f n) with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n => (hfm n).measurable_mk
  have hfg : ∀ᵐ ω ∂P, ∀ n, f n ω = g n ω := ae_all_iff.2 fun n => (hfm n).ae_eq_mk
  have hgl : ∀ n : ℕ, ∫⁻ ω, g n ω ∂P ≤ ENNReal.ofReal (oscInit xL xR θ lam / c₀) := by
    intro n
    rw [← lintegral_congr_ae (hfm n).ae_eq_mk, hfdef]
    rw [← ofReal_integral_eq_lintegral_ofReal (((hM n).integrable n).div_const c₀)
      (Eventually.of_forall fun ω => div_nonneg (hMnn n ω) hc₀.le), integral_div, hEM n]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hinit n) hc₀.le)
  refine ⟨g, hgm, (lintegral_liminf_le' fun n => (hgm n).aemeasurable).trans
    (liminf_le_of_frequently_le' (Frequently.of_forall hgl)), ?_⟩
  filter_upwards [hfg] with ω hω n hωG
  rw [← hω n, hfdef]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hc₀, mul_comm]
  exact hpt n ω hωG

end Fatou

/-! ### The side oscillation on a horizon, and its tail bound -/

section Osc

/-- The constant `K' = (2 Δ₀)^θ 2^{θ/2+1}` of the pointwise comparison, `Δ₀ = x^{R,j₁} − x^{R,0}`. -/
def oscKp (xR : Fin (nR + 1) → ℝ) (j₁ : Fin (nR + 1)) (θ : ℝ) : ℝ :=
  (2 * (xR j₁ - xR 0)) ^ θ * (2 : ℝ) ^ (θ / 2 + 1)

/-- The constant of the tail bound: `K' Φ̄ / c₀`. -/
def oscK (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (j₁ : Fin (nR + 1)) (θ lam c₀ : ℝ) : ℝ :=
  oscKp xR j₁ θ * oscInit xL xR θ lam / c₀

theorem oscKp_nonneg {j₁ : Fin (nR + 1)} (hxR : xR 0 ≤ xR j₁) {θ : ℝ} : 0 ≤ oscKp xR j₁ θ := by
  unfold oscKp
  have : 0 ≤ xR j₁ - xR 0 := sub_nonneg.2 hxR
  positivity

variable (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hgood hT hx in
/-- **The side oscillation on a horizon is dominated by the oscillation clock** along a good noncolliding path of
infinite lifetime: for every `T`, eventually in `n`, `osc^R_T ≤ K' ∫₀^{σ_n} oscRate_{ε_n}` (on `[0, T]` the relative
distance `y` has a positive minimum, which exceeds `ε_n` for large `n`). -/
theorem eventually_sideOsc_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {ω : Ω} (hω : ω ∈ G) (hζ : ζ ω = ⊤)
    (hnc : ∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω) (j₁ : Fin (nR + 1)) (T₀ : ℝ≥0) :
    ∀ᶠ n in atTop, TrialsHi.sideOsc (fun s => VR 0 s ω - W s ω) (fun s => VR j₁ s ω - W s ω) T₀ ≤
      oscKp xR j₁ θ * ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ),
        oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
  have hω' := hgood ω hω
  have hp := hω'.1
  have hF := hp.isForcePath
  have hT₀ζ : (T₀ : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  -- the minimum of `y = 1 − U` on `[0, T₀]`
  set y : ℝ → ℝ := fun s => 1 - angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal with hydef
  have hyc : ContinuousOn y (Icc 0 (T₀ : ℝ)) := continuousOn_const.sub (continuousOn_angAt hp hx hT₀ζ)
  have hypos : ∀ s ∈ Icc 0 (T₀ : ℝ), 0 < y s := fun s hs => by
    have hD := gapAt_pos hp hx hT₀ζ hs
    simp only [hydef, angAt, sub_pos]
    rw [div_lt_one hD]
    simp only [gapAt]
    linarith [(hnc s.toNNReal).2]
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 T₀.coe_nonneg) hyc
  have hm := hypos s₀ hs₀
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt (1 / y s₀)
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_angLoc hω' hgood hω (hT.2.1 ω) hT₀ζ
  refine eventually_atTop.2 ⟨max n₀ n₁, fun n hn => ?_⟩
  have hσn := hn₀ n (le_of_max_le_left hn)
  set σ := angLoc G T W VL VR B ζ n ω with hσdef
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hεm : epsN n ≤ y s₀ := by
    have h1 : (n₁ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    have h2 : 1 / y s₀ < (n : ℝ) + 1 := by linarith
    unfold epsN
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hm] at h2
    linarith
  have hri : IntervalIntegrable (oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω))
      volume 0 σ := (continuousOn_oscRate hp hx (epsN_pos n) hσζ (θ := θ)).intervalIntegrable_of_Icc σ.coe_nonneg
  have hri' : IntervalIntegrable (oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω))
      volume 0 T₀ := hri.mono_set (by
        rw [uIcc_of_le T₀.coe_nonneg, uIcc_of_le σ.coe_nonneg]
        exact Icc_subset_Icc_right (by exact_mod_cast hσn))
  -- the side-oscillation integrand is continuous on `[0, T₀]`
  have hsub : MapsTo Real.toNNReal (Icc 0 (T₀ : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := mapsTo_toNNReal hT₀ζ
  have hnear : ContinuousOn (fun s : ℝ => VR 0 s.toNNReal ω - W s.toNNReal ω) (Icc 0 (T₀ : ℝ)) :=
    ((hF.continuousOn_vR 0).comp continuous_real_toNNReal.continuousOn hsub).sub
      (hF.continuousOn_w.comp continuous_real_toNNReal.continuousOn hsub)
  have hfar : ContinuousOn (fun s : ℝ => VR j₁ s.toNNReal ω - W s.toNNReal ω) (Icc 0 (T₀ : ℝ)) :=
    ((hF.continuousOn_vR j₁).comp continuous_real_toNNReal.continuousOn hsub).sub
      (hF.continuousOn_w.comp continuous_real_toNNReal.continuousOn hsub)
  have hnpos : ∀ s : ℝ, 0 < VR 0 s.toNNReal ω - W s.toNNReal ω := fun s => sub_pos.2 (hnc s.toNNReal).2
  have hfpos : ∀ s ∈ Icc 0 (T₀ : ℝ), 0 < VR j₁ s.toNNReal ω - W s.toNNReal ω := fun s hs => by
    have := hF.monotone_vR (Sec2.toNNReal_lt_of_mem_Icc hT₀ζ hs) (Fin.zero_le j₁)
    linarith [hnpos s]
  have hgi : IntervalIntegrable (fun s : ℝ => 1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
      1 / (VR j₁ s.toNNReal ω - W s.toNNReal ω) ^ 2) volume 0 T₀ := by
    refine ContinuousOn.intervalIntegrable_of_Icc T₀.coe_nonneg ?_
    exact (continuousOn_const.div (hnear.pow 2) fun s _ => pow_ne_zero 2 (hnpos s).ne').sub
      (continuousOn_const.div (hfar.pow 2) fun s hs => pow_ne_zero 2 (hfpos s hs).ne')
  have hstep : TrialsHi.sideOsc (fun s => VR 0 s ω - W s ω) (fun s => VR j₁ s ω - W s ω) T₀ ≤
      ∫ s in (0 : ℝ)..T₀, oscKp xR j₁ θ *
        oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
    unfold TrialsHi.sideOsc
    refine intervalIntegral.integral_mono_on T₀.coe_nonneg hgi (hri'.const_mul _) fun s hs => ?_
    have hsζ := Sec2.toNNReal_lt_of_mem_Icc hT₀ζ hs
    have hD := gapAt_pos hp hx hT₀ζ hs
    have hΔ0 : 0 ≤ VR j₁ s.toNNReal ω - VR 0 s.toNNReal ω :=
      sub_nonneg.2 (hF.monotone_vR hsζ (Fin.zero_le j₁))
    have hΔ1 := hF.vR_sub_vR_le hsζ (Fin.zero_le j₁)
    have hyR : y s = (VR 0 s.toNNReal ω - W s.toNNReal ω) / gapAt (fun i t => VL i t ω) (fun j t => VR j t ω)
        s.toNNReal := by
      simp only [hydef, angAt]
      field_simp
      simp only [gapAt]
      ring
    have h := inv_sq_sub_inv_sq_le (hnpos s) hΔ0 hΔ1 hθ0 hθ1 hD hyR (epsN_pos n) (hεm.trans (hmin hs))
    have e : VR 0 s.toNNReal ω - W s.toNNReal ω + (VR j₁ s.toNNReal ω - VR 0 s.toNNReal ω) =
        VR j₁ s.toNNReal ω - W s.toNNReal ω := by ring
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    simp only [oscKp, oscRate, hydef]
  refine hstep.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h00 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hx0 := hF.monotone_vR h00 (Fin.zero_le j₁)
  simp only [hF.vR_zero] at hx0
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) σ)]
      oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun s hs => ?_
    have hs' : s ∈ Icc 0 (σ : ℝ) := Ioc_subset_Icc_self hs
    show 0 ≤ oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s
    unfold oscRate
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (gapAt_pos hp hx hσζ hs').le _) (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)
  have hTσ : (T₀ : ℝ) ≤ σ := by exact_mod_cast hσn
  exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl T₀.coe_nonneg hTσ hnn hri)
    (oscKp_nonneg hx0)

end Osc

/-! ### The tail bound of the right side oscillation -/

section Tail

/-- **The tail bound of the right side oscillation** (every evolution of a separated word whose only nonzero weights
sit at the nearest marks, with the Lyapunov inequality for `(θ, λ, c₀)` and almost sure strict noncollision on an
infinite lifetime): `P(∃ T, osc^R_T > C) ≤ K/C`, `K = oscK` independent of the evolution. -/
theorem measure_sideOsc_gt_le (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hsep : ∀ i j, xL i < xR j) (hxR0 : 0 < xR 0) (hρL : ∀ i, i ≠ 0 → ρL i = 0) (hρR : ∀ j, j ≠ 0 → ρR j = 0)
    (hnc : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω)
    {θ lam c₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hlam : 0 ≤ lam) (hc₀ : 0 < c₀)
    (hJ : ∀ ε : ℝ, 0 < ε → ∀ u ∈ Ioo (0 : ℝ) 1, oscJ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) θ ε lam u ≤
      -c₀ * ((1 - u) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) (j₁ : Fin (nR + 1)) {C : ℝ} (hC : 0 < C) :
    P {ω | ∃ T₀ : ℝ≥0, C < TrialsHi.sideOsc (fun s => VR 0 s ω - W s ω) (fun s => VR j₁ s ω - W s ω) T₀} ≤
      ENNReal.ofReal (oscK xL xR j₁ θ lam c₀ / C) := by
  have hP := hE.1.isProbabilityMeasure'
  have hx : 0 < xR 0 - xL 0 := sub_pos.2 (hsep 0 0)
  have hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
    intro h
    have h1 := ae_ne_top_of_thresholdCondition hE h
    have h2 : ∀ᵐ ω ∂P, False := by filter_upwards [h1, hnc] with ω h1 h2 using h1 h2.1
    rw [ae_iff] at h2
    simp at h2
  obtain ⟨T, G, hT, hGm, hGc, hgood⟩ := exists_setup hκ hE hthr
  obtain ⟨g, hgm, hgl, hgb⟩ := exists_lintegral_liminf_le hE hGm hGc hgood hT hx hκ hρL hρR hxR0 hθ0 hlam hc₀ hJ
  set S := {ω | ∃ T₀ : ℝ≥0, C < TrialsHi.sideOsc (fun s => VR 0 s ω - W s ω) (fun s => VR j₁ s ω - W s ω) T₀}
  set K' := oscKp xR j₁ θ with hK'def
  -- on a good path, the oscillation is eventually below `K' ∫₀^{σ_n} oscRate_{ε_n} ≤ K' g_n`
  have hkey : ∀ᵐ ω ∂P, ω ∈ S → ∀ᶠ n in atTop, ENNReal.ofReal (C / K') ≤ g n ω ∧ 0 < K' := by
    filter_upwards [hgb, hnc, measure_eq_zero_iff_ae_notMem.1 hGc] with ω hω hncω hωG' hS
    have hωG : ω ∈ G := by simpa using hωG'
    obtain ⟨T₀, hT₀⟩ := hS
    have hev := eventually_sideOsc_le hgood hT hx hθ0 hθ1 hωG hncω.1 hncω.2 j₁ T₀
    refine hev.mono fun n hn => ?_
    set Y := ∫ s in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ),
      oscRate θ (epsN n) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s
    have hCY : C < K' * Y := hT₀.trans_le hn
    have hY0 : 0 ≤ Y := by
      have hω' := hgood ω hωG
      have hσζ := angLoc_lt_lifetime (G := G) (n := n) hω'
      refine intervalIntegral.integral_nonneg (angLoc G T W VL VR B ζ n ω).coe_nonneg fun s hs => ?_
      unfold oscRate
      exact mul_nonneg (div_nonneg (Real.rpow_nonneg (gapAt_pos hω'.1 hx hσζ hs).le _) (sq_nonneg _))
        (Real.rpow_nonneg (by positivity) _)
    have hK : 0 < K' := by
      by_contra hK
      have : K' * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hK) hY0
      linarith
    refine ⟨(ENNReal.ofReal_le_ofReal ?_).trans (hω n hωG), hK⟩
    rw [div_le_iff₀ hK]
    linarith
  by_cases hK : 0 < K'
  · have hsub : S ≤ᵐ[P] {ω | ENNReal.ofReal (C / K') ≤ liminf (fun n => g n ω) atTop} := by
      filter_upwards [hkey] with ω hω hS
      exact le_liminf_of_le (by isBoundedDefault) ((hω hS).mono fun n h => h.1)
    have hCK : 0 < C / K' := div_pos hC hK
    calc P S ≤ P {ω | ENNReal.ofReal (C / K') ≤ liminf (fun n => g n ω) atTop} := measure_mono_ae hsub
      _ ≤ (∫⁻ ω, liminf (fun n => g n ω) atTop ∂P) / ENNReal.ofReal (C / K') :=
          meas_ge_le_lintegral_div (Measurable.liminf hgm).aemeasurable
            (ENNReal.ofReal_pos.2 hCK).ne' ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (oscInit xL xR θ lam / c₀) / ENNReal.ofReal (C / K') := by gcongr
      _ = ENNReal.ofReal (oscK xL xR j₁ θ lam c₀ / C) := by
          rw [← ENNReal.ofReal_div_of_pos hCK]
          congr 1
          simp only [oscK, ← hK'def]
          field_simp
  · have hnull : P S = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hkey] with ω hω hS
      obtain ⟨n, -, hn⟩ := (hω hS).exists
      exact hK hn
    rw [hnull]; exact zero_le

end Tail

end TrialsHi2

end Sec7

end InteractingSLE
