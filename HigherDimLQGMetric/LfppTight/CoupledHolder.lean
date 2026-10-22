import HigherDimLQGMetric.LfppTight.BallSup

/-! Hölder control of the coupled centered field on adapter good events. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_coupled_holder_on_gap {d : ℕ} (ξ β a B C L c : ℝ)
    (H Ψ : Rd d → ℝ) (hH : Continuous H) (hΨ : Continuous Ψ)
    {r R : ℝ} (hrr : r < R)
    (hgap : ¬ DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R) ≤
      ⨆ p : ball (0 : Rd d) r × ball (0 : Rd d) r,
        DGZ.lfppMetric ξ H p.1 p.2)
    (hC : |c| ≤ C) (hL : ∀ z ∈ ball (0 : Rd d) R, |Ψ z| ≤ L)
    (hHolder : ∀ x ∈ closedBall (0 : Rd d) r,
      ∀ y ∈ closedBall (0 : Rd d) r,
        DGZ.lfppMetric ξ H x y ≤ B * a * ‖x - y‖ ^ β)
    {x y : Rd d} (hx : x ∈ ball (0 : Rd d) r) (hy : y ∈ ball (0 : Rd d) r) :
    DGZ.lfppMetric ξ (fun z => H z - c + Ψ z) x y ≤
      Real.exp (|ξ| * (C + L)) * (B * a * ‖x - y‖ ^ β) := by
  have hfield : (fun z => H z - c + Ψ z) = fun z => (H z + Ψ z) + -c := by
    funext z
    ring
  have hφ : DGZ.lfppMetric ξ (fun z => H z - c + Ψ z) x y =
      Real.exp (ξ * -c) * DGZ.lfppMetric ξ (fun z => H z + Ψ z) x y := by
    rw [hfield]
    exact HigherDimLFPP.lfppDistOn_add_const ξ (fun z => H z + Ψ z) (-c) univ x y
  have hcExp : Real.exp (ξ * -c) ≤ Real.exp (|ξ| * C) := by
    apply Real.exp_le_exp.mpr
    calc
      ξ * -c ≤ |ξ * -c| := le_abs_self _
      _ = |ξ| * |c| := by rw [abs_mul, abs_neg]
      _ ≤ |ξ| * C := mul_le_mul_of_nonneg_left hC (abs_nonneg _)
  have hLp : 0 ≤ DGZ.lfppMetric ξ (fun z => H z + Ψ z) x y :=
    DGZ.lfppMetric_nonneg ξ _ x y
  have hHp : 0 ≤ DGZ.lfppMetric ξ H x y := DGZ.lfppMetric_nonneg ξ _ x y
  have hcomp := l6a_global_coupled_upper_of_gap ξ L H Ψ hH hΨ hrr hgap hL hx hy
  have hHH := hHolder x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  calc
    DGZ.lfppMetric ξ (fun z => H z - c + Ψ z) x y =
        Real.exp (ξ * -c) * DGZ.lfppMetric ξ (fun z => H z + Ψ z) x y := hφ
    _ ≤ Real.exp (|ξ| * C) * DGZ.lfppMetric ξ (fun z => H z + Ψ z) x y :=
      mul_le_mul_of_nonneg_right hcExp hLp
    _ ≤ Real.exp (|ξ| * C) * (Real.exp (|ξ| * L) * DGZ.lfppMetric ξ H x y) :=
      mul_le_mul_of_nonneg_left hcomp (Real.exp_pos _).le
    _ ≤ Real.exp (|ξ| * C) * (Real.exp (|ξ| * L) * (B * a * ‖x - y‖ ^ β)) := by
      gcongr
    _ = Real.exp (|ξ| * (C + L)) * (B * a * ‖x - y‖ ^ β) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      rw [mul_add]

end HigherDimLQGMetric
