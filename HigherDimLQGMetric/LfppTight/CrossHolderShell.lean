import HigherDimLQGMetric.LfppTight.SmallBall
import HigherDimLQGMetric.DGZ.Crossing
import HigherDimLQGMetric.B3.Interfaces

/-! Unit crossing from a local Hölder bound and a larger-shell lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_cross_of_holder_shell {d : ℕ} (ξ : ℝ)
    (φ : Rd d → ℝ) (hφ : Continuous φ)
    {a M m β b C : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hβ : 0 < β) (hb : 0 < b) (hb4 : b ≤ 1 / 4) (hC : 0 < C)
    (hsmall : M * (2 * b) ^ β ≤ m / C)
    (hholder : ∀ x ∈ closedBall (0 : Rd d) 1,
      ∀ y ∈ closedBall (0 : Rd d) 1,
        DGZ.lfppMetric ξ φ x y ≤ M * a * ‖x - y‖ ^ β)
    (hshell : m * a < DGZ.lfppSetDist ξ φ univ
      (sphere (0 : Rd d) (1 / 2)) (sphere 0 1)) :
    supPairs (fun p : Rd d × Rd d => DGZ.lfppMetric ξ φ p.1 p.2)
      (ball (0 : Rd d) b) ≤
      ENNReal.ofReal C⁻¹ * infPairs
        (fun p : Rd d × Rd d => DGZ.lfppMetric ξ φ p.1 p.2)
        (sphere 0 b) (sphere 0 1) := by
  have hba : b < 1 := lt_of_le_of_lt hb4 (by norm_num)
  have hS : supPairs (fun p : Rd d × Rd d => DGZ.lfppMetric ξ φ p.1 p.2)
      (ball (0 : Rd d) b) ≤ ENNReal.ofReal (M * a * (2 * b) ^ β) := by
    unfold supPairs
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    have hx1 : x ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall]
      exact (mem_ball.mp hx).le.trans (by linarith)
    have hy1 : y ∈ closedBall (0 : Rd d) 1 := by
      rw [mem_closedBall]
      exact (mem_ball.mp hy).le.trans (by linarith)
    have hxy : ‖x - y‖ ≤ 2 * b := by
      have hxn : ‖x‖ < b := by simpa only [mem_ball, dist_zero_right] using hx
      have hyn : ‖y‖ < b := by simpa only [mem_ball, dist_zero_right] using hy
      linarith [norm_sub_le x y]
    have hpow : ‖x - y‖ ^ β ≤ (2 * b) ^ β :=
      Real.rpow_le_rpow (norm_nonneg _) hxy hβ.le
    have hD := hholder x hx1 y hy1
    exact ENNReal.ofReal_le_ofReal (hD.trans
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hM ha.le)))
  have hI : ENNReal.ofReal (m * a) ≤
      infPairs (fun p : Rd d × Rd d => DGZ.lfppMetric ξ φ p.1 p.2)
        (sphere 0 b) (sphere 0 1) := by
    unfold infPairs
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    have hx' : x ∈ closedBall (0 : Rd d) (1 / 2) := by
      rw [mem_closedBall, dist_zero_right]
      have hxn : ‖x‖ = b := by simpa only [mem_sphere, dist_zero_right] using hx
      linarith
    have hy' : y ∉ ball (0 : Rd d) 1 := by
      rw [mem_ball, dist_zero_right, not_lt]
      have hyn : ‖y‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hy
      exact hyn.ge
    have hxy : DGZ.lfppSetDist ξ φ univ (sphere (0 : Rd d) (1 / 2))
        (sphere 0 1) ≤ DGZ.lfppMetric ξ φ x y := by
      exact DGZ.lfppSetDist_sphere_le_lfppDistOn hφ (by norm_num)
        hx' hy' (HigherDimLFPP.PcwJoined.of_convex convex_univ
          (mem_univ _) (mem_univ _))
    exact ENNReal.ofReal_le_ofReal (hshell.le.trans hxy)
  calc
    supPairs (fun p : Rd d × Rd d => DGZ.lfppMetric ξ φ p.1 p.2)
        (ball (0 : Rd d) b) ≤ ENNReal.ofReal (M * a * (2 * b) ^ β) := hS
    _ ≤ ENNReal.ofReal C⁻¹ * ENNReal.ofReal (m * a) := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr hC).le]
      apply ENNReal.ofReal_le_ofReal
      have h : M * a * (2 * b) ^ β ≤ C⁻¹ * (m * a) := by
        have hs := mul_le_mul_of_nonneg_right hsmall ha.le
        have heq : (m / C) * a = C⁻¹ * (m * a) := by ring
        rw [heq] at hs
        nlinarith [hs]
      exact h
    _ ≤ ENNReal.ofReal C⁻¹ * infPairs
        (fun p : Rd d × Rd d => DGZ.lfppMetric ξ φ p.1 p.2)
        (sphere 0 b) (sphere 0 1) := by gcongr

end HigherDimLQGMetric
