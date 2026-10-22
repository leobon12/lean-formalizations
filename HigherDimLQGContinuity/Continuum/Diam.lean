import HigherDimLQGContinuity.Continuum.Log
import HigherDimLQGMetric.Metric.Internal
import Mathlib.Analysis.Convex.Segment

/-!
# Buffered internal diameters in the continuum

The unit-ball case is the finite straight-chain estimate used by relative
escape. General compact subsets require a finite connected cover inside the
ambient open set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem l2_unit_internalDiam_le {d : ℕ} (D : ContMetric d) {H : ℝ}
    (_hH : 0 ≤ H)
    (hlocal : ∀ z ∈ closedBall (0 : Rd d) 1,
      internalDiamRd D (ball z (1 / 4)) (ball z (1 / 2)) ≤ ENNReal.ofReal H) :
    internalDiamRd D (closedBall (0 : Rd d) 1) (ball 0 2) ≤
      ENNReal.ofReal (16 * H) := by
  unfold internalDiamRd
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
  let w : ℕ → Rd d := fun i => x + ((i : ℝ) / 16) • (y - x)
  have hw0 : w 0 = x := by simp [w]
  have hwn : w 16 = y := by simp [w]
  have hmem (i : ℕ) (hi : i ≤ 16) : w i ∈ closedBall (0 : Rd d) 1 := by
    let a : ℝ := (i : ℝ) / 16
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by dsimp [a]; exact (div_le_iff₀ (by norm_num)).2 (by exact_mod_cast hi)
    have heq : w i = AffineMap.lineMap x y a := by
      dsimp [w, a]
      rw [AffineMap.lineMap_apply_module']
      module
    rw [heq]
    exact (convex_closedBall (0 : Rd d) 1).segment_subset hx hy
      (lineMap_mem_segment ℝ x y ⟨ha0, ha1⟩)
  have hsub (i : ℕ) : w (i + 1) - w i = ((1 : ℝ) / 16) • (y - x) := by
    simp only [w, Nat.cast_add, Nat.cast_one]
    module
  have hnear (i : ℕ) : w (i + 1) ∈ ball (w i) (1 / 4) := by
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    norm_num
    have hxnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hynorm : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hxy : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
    nlinarith
  have hball (i : ℕ) (hi : i ≤ 16) : ball (w i) (1 / 2) ⊆ ball (0 : Rd d) 2 := by
    intro u hu
    have hwi : ‖w i‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hmem i hi
    have hwu : ‖u - w i‖ < 1 / 2 := by simpa only [mem_ball, dist_eq_norm] using hu
    have htri : ‖u‖ ≤ ‖w i‖ + ‖u - w i‖ := by
      calc
        ‖u‖ = ‖w i + (u - w i)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [mem_ball, dist_zero_right]
    linarith
  have hstep (i : ℕ) (hi : i ≤ 16) :
      D.internal (ball 0 2) (w i) (w (i + 1)) ≤ ENNReal.ofReal H := by
    have hwi : w i ∈ ball (w i) (1 / 4) := mem_ball_self (by norm_num)
    calc
      D.internal (ball 0 2) (w i) (w (i + 1)) ≤
          D.internal (ball (w i) (1 / 2)) (w i) (w (i + 1)) :=
        D.internal_anti (hball i hi) _ _
      _ ≤ internalDiamRd D (ball (w i) (1 / 4)) (ball (w i) (1 / 2)) :=
        le_iSup₂_of_le (w i) hwi (le_iSup₂_of_le (w (i + 1)) (hnear i) le_rfl)
      _ ≤ ENNReal.ofReal H := hlocal (w i) (hmem i hi)
  have hbound : ∀ i : ℕ, i ≤ 16 →
      D.internal (ball 0 2) x (w i) ≤ (i : ℝ≥0∞) * ENNReal.ofReal H := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [hw0, D.internal_self]
        · simp
        · have hnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
          rw [mem_ball, dist_zero_right]
          linarith
    | succ i ih =>
        intro hi
        have hii : i ≤ 16 := by omega
        calc
          D.internal (ball 0 2) x (w (i + 1)) ≤
              D.internal (ball 0 2) x (w i) +
                D.internal (ball 0 2) (w i) (w (i + 1)) :=
            D.internal_triangle _ _ _ _
          _ ≤ (i : ℝ≥0∞) * ENNReal.ofReal H + ENNReal.ofReal H :=
            add_le_add (ih hii) (hstep i hii)
          _ = ((i + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal H := by
            push_cast
            ring
  have hxy := hbound 16 le_rfl
  rw [hwn] at hxy
  calc
    D.internal (ball 0 2) x y ≤ (16 : ℝ≥0∞) * ENNReal.ofReal H := hxy
    _ = ENNReal.ofReal (16 * H) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num

/-- A uniform positive moment of the buffered diameter of the unit ball. -/
theorem continuum_unitDiam {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d)) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        (∫⁻ g, (internalDiamRd (rho D g)
          (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p ∂(normLGFLaw d)) ≤
          ENNReal.ofReal C := by
  obtain ⟨C₀, A, hfatou⟩ := continuum_fatou hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  refine ⟨16 ^ p * (C₀ * (1 + 1) ^ A), fun ξ hξ D hD => ?_⟩
  obtain ⟨H, hHm, hH1, hHmom, hHpt⟩ := (hfatou ξ hξ D hD).2 1 le_rfl
  have hsmall : (1 / 4 : ℝ) ^ σ ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) hσ.le
  have hpt : ∀ᵐ g ∂(normLGFLaw d),
      internalDiamRd (rho D g) (closedBall (0 : Rd d) 1) (ball 0 2) ≤
        ENNReal.ofReal (16 * H g) := by
    filter_upwards [hHpt] with g hg
    apply l2_unit_internalDiam_le (rho D g) (by linarith [hH1 g])
    intro z hz
    have hloc := hg z hz (1 / 4) ⟨by norm_num, by norm_num⟩
    have hm : H g * (1 / 4 : ℝ) ^ σ ≤ H g := by
      nlinarith [hH1 g]
    simpa only [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] using
      hloc.trans (ENNReal.ofReal_le_ofReal hm)
  have hpow : ∀ᵐ g ∂(normLGFLaw d),
      (internalDiamRd (rho D g) (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p ≤
        ENNReal.ofReal (16 ^ p) * ENNReal.ofReal (H g ^ p) := by
    filter_upwards [hpt] with g hg
    calc
      (internalDiamRd (rho D g) (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p ≤
          ENNReal.ofReal (16 * H g) ^ p := ENNReal.rpow_le_rpow hg hp.le
      _ = ENNReal.ofReal (16 ^ p) * ENNReal.ofReal (H g ^ p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by nlinarith [hH1 g]) hp.le,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (by linarith [hH1 g]),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 16) _)]
  calc
    (∫⁻ g, (internalDiamRd (rho D g) (closedBall (0 : Rd d) 1) (ball 0 2)) ^ p
        ∂(normLGFLaw d)) ≤
        ∫⁻ g, ENNReal.ofReal (16 ^ p) * ENNReal.ofReal (H g ^ p)
          ∂(normLGFLaw d) := lintegral_mono_ae hpow
    _ = ENNReal.ofReal (16 ^ p) *
        (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d)) :=
      lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hHm.pow_const p))
    _ ≤ ENNReal.ofReal (16 ^ p) * ENNReal.ofReal (C₀ * (1 + 1) ^ A) := by
      gcongr
    _ = ENNReal.ofReal (16 ^ p * (C₀ * (1 + 1) ^ A)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 16) _)]

end HigherDimLQGContinuity
