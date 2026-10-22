import HigherDimLQGMetric.LfppTight.FarFieldSup
import HigherDimLQGMetric.DGZ.AdapterFixed

/-! Deterministic metric bounds from a field bound on a fixed Euclidean ball. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6a_fieldBound_unitLower {d : ℕ} (hd : 0 < d)
    {φ : Rd d → ℝ} (hφ : Continuous φ) {ξ L : ℝ} (hξ : 0 < ξ)
    (hL : ∀ z ∈ closedBall (0 : Rd d) (Real.sqrt d + 1), |φ z| ≤ L) :
    Real.exp (-(ξ * L)) ≤ DGZ.lfppMetric ξ φ 0 (e₁ d) := by
  have h0 : (0 : Rd d) ∈ HigherDimLFPP.DGZ.cbox 0 0 := by
    intro i
    simp only [PiLp.zero_apply, sub_self, abs_zero]
    exact le_rfl
  have he : e₁ d ∉ HigherDimLFPP.DGZ.obox 0 1 := by
    intro he
    have hh := he ⟨0, hd⟩
    simp [PiLp.zero_apply, HigherDimLFPP.e₁_ofLp] at hh
  have hshell : ∀ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) 1 \
      HigherDimLFPP.DGZ.obox 0 0, -(ξ * L) ≤ ξ * φ z := by
    intro z hz
    have hnorm : ‖z‖ ≤ Real.sqrt d := by
      have h := DGZ.norm_sub_le_of_forall_abs_le (x := (0 : Rd d)) (y := z)
        (fun i => by
          simpa only [abs_sub_comm] using hz.1 i)
      simpa only [zero_sub, norm_neg, mul_one] using h
    have hzball : z ∈ closedBall (0 : Rd d) (Real.sqrt d + 1) := by
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hf := hL z hzball
    have hlow := neg_abs_le (φ z)
    nlinarith [mul_nonneg (sub_nonneg.2 (by linarith : 0 ≤ φ z + L)) hξ.le]
  have hcross := DGZ.exp_mul_le_acrossDist hd hφ
    (c := (0 : Rd d)) (r₁ := 1) (r₂ := 0) (by norm_num) (by norm_num) hshell
  have hle := DGZ.acrossDist_le_lfppMetric_of_mem
    (ξ := ξ) hφ (c := (0 : Rd d)) (r₁ := 1) (r₂ := 0)
    (by norm_num) h0 he
  simpa only [sub_zero, mul_one] using hcross.trans hle

theorem l6a_fieldBound_localUpper {d : ℕ}
    {φ : Rd d → ℝ} (hφ : Continuous φ) {ξ L R : ℝ}
    (hL : ∀ z ∈ closedBall (0 : Rd d) (R + 1), |φ z| ≤ L) :
    ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
        DGZ.lfppMetric ξ φ x y ≤ Real.exp (|ξ| * L) * ‖x - y‖ := by
  intro x hx y hy
  have hxU : x ∈ ball (0 : Rd d) (R + 1) :=
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith))
  have hyU : y ∈ ball (0 : Rd d) (R + 1) :=
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith))
  have hfield : ∀ z ∈ ball (0 : Rd d) (R + 1),
      ξ * φ z ≤ |ξ| * L := by
    intro z hz
    have hf := hL z (ball_subset_closedBall hz)
    calc
      ξ * φ z ≤ |ξ * φ z| := le_abs_self _
      _ = |ξ| * |φ z| := abs_mul _ _
      _ ≤ |ξ| * L := mul_le_mul_of_nonneg_left hf (abs_nonneg ξ)
  have hbound := DGZ.lfppDistOn_le_exp_mul_norm_of_convex hφ
    (convex_ball (0 : Rd d) (R + 1)) hxU hyU hfield
  have hjoin : HigherDimLFPP.PcwJoined (ball (0 : Rd d) (R + 1)) x y :=
    HigherDimLFPP.PcwJoined.of_convex (convex_ball (0 : Rd d) (R + 1)) hxU hyU
  calc
    DGZ.lfppMetric ξ φ x y ≤ HigherDimLFPP.lfppDistOn ξ φ
        (ball (0 : Rd d) (R + 1)) x y := DGZ.lfppMetric_le_lfppDistOn hjoin
    _ ≤ Real.exp (|ξ| * L) * ‖y - x‖ := hbound
    _ = Real.exp (|ξ| * L) * ‖x - y‖ := by rw [norm_sub_rev]

end HigherDimLQGMetric
