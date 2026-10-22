import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Metric.ContMetric

/-! Rounding a separated bad pair to a deterministic net, equation (4.26). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A sufficiently fine net preserves the separated lower violation. -/
theorem net_rounding {d : ℕ} {D E : ContMetric d}
    {R c Cb ε g H dsep σ w t : ℝ}
    (hR : 2 ≤ R) (hc : 1 ≤ c) (hcCb : c ≤ Cb) (_hε : 0 ≤ ε)
    (hg : 0 < g) (hg1 : g ≤ 1) (hH : 0 < H) (_hdsep : 0 < dsep)
    (hσ : 0 < σ) (_hσ1 : σ ≤ 1) (_hw : 0 < w) (hw1 : w ≤ 1)
    (ht : 0 < t) (htw : t ≤ w / 8)
    (hsmall : 4 * Cb * H * t ^ σ + 2 * ε ≤ 7 / 8 * g * dsep)
    (hcompare : ∀ p ∈ closedBall (0 : Rd d) R, ∀ q ∈ closedBall (0 : Rd d) R,
      E.1 (p, q) ≤ c * D.1 (p, q) + ε)
    (hupper : ∀ p ∈ closedBall (0 : Rd d) 2, ∀ q ∈ closedBall (0 : Rd d) 2,
      ‖p - q‖ ≤ 1 / 2 → D.1 (p, q) ≤ H * ‖p - q‖ ^ σ)
    (hlower : ∀ p ∈ closedBall (0 : Rd d) 2, ∀ q ∈ closedBall (0 : Rd d) 2,
      w / 2 ≤ ‖p - q‖ → dsep ≤ D.1 (p, q))
    {x' y' x y : Rd d}
    (hx' : x' ∈ closedBall (0 : Rd d) 2) (hy' : y' ∈ closedBall (0 : Rd d) 2)
    (hx : x ∈ closedBall (0 : Rd d) 2) (hy : y ∈ closedBall (0 : Rd d) 2)
    (hxy' : 3 / 4 * w ≤ ‖x' - y'‖)
    (hbad : (c - g / 8) * D.1 (x', y') < E.1 (x', y'))
    (hxx' : ‖x - x'‖ ≤ t) (hyy' : ‖y - y'‖ ≤ t) :
    w / 2 ≤ ‖x - y‖ ∧ (c - g) * D.1 (x, y) ≤ E.1 (x, y) := by
  have hsep : w / 2 ≤ ‖x - y‖ := by
    have htri := dist_triangle4 x' x y y'
    simp only [dist_eq_norm] at htri
    have hnorm : ‖x' - x‖ = ‖x - x'‖ := norm_sub_rev _ _
    rw [hnorm] at htri
    linarith
  have hcoef : 0 ≤ c - g / 8 := by linarith
  have hcoefCb : c - g / 8 ≤ Cb := by linarith
  have hCb : 0 ≤ Cb := by linarith
  have hc0 : 0 ≤ c := by linarith
  have ht12 : t ≤ 1 / 2 := by linarith
  have hpow : 0 ≤ t ^ σ := Real.rpow_nonneg (le_of_lt ht) _
  have hDx : D.1 (x, x') ≤ H * t ^ σ := by
    have hu := hupper x hx x' hx' (hxx'.trans ht12)
    exact hu.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hxx' hσ.le) hH.le)
  have hDy : D.1 (y, y') ≤ H * t ^ σ := by
    have hu := hupper y hy y' hy' (hyy'.trans ht12)
    exact hu.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hyy' hσ.le) hH.le)
  have hxR : x ∈ closedBall (0 : Rd d) R := (closedBall_subset_closedBall hR) hx
  have hyR : y ∈ closedBall (0 : Rd d) R := (closedBall_subset_closedBall hR) hy
  have hx'R : x' ∈ closedBall (0 : Rd d) R := (closedBall_subset_closedBall hR) hx'
  have hy'R : y' ∈ closedBall (0 : Rd d) R := (closedBall_subset_closedBall hR) hy'
  have hEx : E.1 (x, x') ≤ c * (H * t ^ σ) + ε := by
    exact (hcompare x hxR x' hx'R).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left hDx hc0) _)
  have hEy : E.1 (y, y') ≤ c * (H * t ^ σ) + ε := by
    exact (hcompare y hyR y' hy'R).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left hDy hc0) _)
  have hDtri : D.1 (x, y) ≤ D.1 (x, x') + D.1 (x', y') + D.1 (y', y) := by
    have h₁ := D.apply_triangle x x' y
    have h₂ := D.apply_triangle x' y' y
    linarith
  have hEtri : E.1 (x', y') ≤ E.1 (x, x') + E.1 (x, y) + E.1 (y, y') := by
    have h₁ := E.apply_triangle x' x y'
    have h₂ := E.apply_triangle x y y'
    rw [E.apply_comm x' x] at h₁
    linarith
  have hDsep : dsep ≤ D.1 (x, y) := hlower x hx y hy hsep
  have hDmult := mul_le_mul_of_nonneg_left hDtri hcoef
  rw [D.apply_comm y' y] at hDmult
  have hgap : 4 * Cb * H * t ^ σ + 2 * ε ≤ 7 / 8 * g * D.1 (x, y) := by
    exact hsmall.trans (mul_le_mul_of_nonneg_left hDsep (by positivity))
  have hcoefDx := mul_le_mul_of_nonneg_left hDx hcoef
  have hcoefDy := mul_le_mul_of_nonneg_left hDy hcoef
  have hcoefH := mul_le_mul_of_nonneg_right hcoefCb (mul_nonneg hH.le hpow)
  have hcH := mul_le_mul_of_nonneg_right hcCb (mul_nonneg hH.le hpow)
  constructor
  · exact hsep
  · nlinarith only [hbad, hEx, hEy, hEtri, hDmult, hcoefDx, hcoefDy,
      hgap, hcoefH, hcH]

end HigherDimLQGContinuity
