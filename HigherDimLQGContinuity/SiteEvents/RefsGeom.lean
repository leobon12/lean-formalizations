import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Events.AnnulusDiameter

/-! Radius bound for doubled balls contained in the site annulus. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A doubled ball inside `A = {1/2 < |x| < 7/2}` has radius at most `3/4`. -/
theorem q10_site_ball_radius {d : ℕ} {z : Rd d} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z (2 * r) ⊆ siteA d) : r ≤ 3 / 4 := by
  have hzero : (0 : Rd d) ∉ siteA d := by
    simp only [siteA, annA, HigherDimLQGMetric.ann, sub_zero]
    norm_num
  have haz : 2 * r < ‖z‖ := by
    by_contra h
    have h0 : (0 : Rd d) ∈ closedBall z (2 * r) := by
      rw [mem_closedBall, dist_zero_left]
      exact le_of_not_gt h
    exact hzero (hsub h0)
  have ha : 0 < ‖z‖ := by linarith
  let v : Rd d := (2 * r / ‖z‖) • z
  have hv : ‖v‖ = 2 * r := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) ha)]
    field_simp
  let p : Rd d := z - v
  let q : Rd d := z + v
  have hp : p ∈ closedBall z (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    have he : p - z = -v := by dsimp [p]; abel
    rw [he, norm_neg, hv]
  have hq : q ∈ closedBall z (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    have he : q - z = v := by dsimp [q]; abel
    rw [he, hv]
  have hpnorm : ‖p‖ = ‖z‖ - 2 * r := by
    have he : p = (1 - 2 * r / ‖z‖) • z := by
      dsimp [p, v]
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 1 - 2 * r / ‖z‖ by
        rw [sub_pos, div_lt_one ha]
        linarith)]
    field_simp
  have hqnorm : ‖q‖ = ‖z‖ + 2 * r := by
    have he : q = (1 + 2 * r / ‖z‖) • z := by
      dsimp [q, v]
      rw [add_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 1 + 2 * r / ‖z‖ by positivity)]
    field_simp
  have hpa := hsub hp
  have hqa := hsub hq
  simp only [siteA, annA, HigherDimLQGMetric.ann, sub_zero] at hpa hqa
  change (1 / 2 : ℝ) < ‖p‖ ∧ ‖p‖ < 7 / 2 at hpa
  change (1 / 2 : ℝ) < ‖q‖ ∧ ‖q‖ < 7 / 2 at hqa
  rw [hpnorm] at hpa
  rw [hqnorm] at hqa
  linarith

/-- The uniform envelope at radius four supplies `DUpper` on the whole site annulus. -/
theorem q10_dupper_of_envelope {d : ℕ} {G : ContMetric d} {H σ : ℝ}
    (hup : ∀ z ∈ closedBall (0 : Rd d) 4, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      diamIn G (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H * r ^ σ)) :
    DUpper G (siteA d) H σ := by
  intro z r hr hball
  have hz : z ∈ closedBall (0 : Rd d) 4 := by
    have hzball : z ∈ closedBall z (2 * r) := mem_closedBall_self (by positivity)
    have hzA := hball hzball
    simp only [siteA, annA, ann, sub_zero] at hzA
    change (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 7 / 2 at hzA
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hr1 : r ≤ 1 := (q10_site_ball_radius hr hball).trans (by norm_num)
  exact hup z hz r ⟨hr, hr1⟩

theorem q10_siteC_subset_closedBall_four {d : ℕ} :
    siteC d ⊆ closedBall (0 : Rd d) 4 := by
  intro x hx
  simp only [siteC, annCl, sub_zero] at hx
  change (3 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 2 at hx
  rw [mem_closedBall, dist_zero_right]
  linarith

theorem q10_siteC_subset_siteA {d : ℕ} : siteC d ⊆ siteA d := by
  intro x hx
  simp only [siteC, annCl, sub_zero] at hx
  change (3 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 2 at hx
  simp only [siteA, annA, ann, sub_zero]
  constructor <;> linarith

theorem q10_siteC_isCompact {d : ℕ} : IsCompact (siteC d) := by
  refine (isCompact_closedBall (0 : Rd d) 3).of_isClosed_subset ?_ ?_
  · exact isClosed_annCl _ _ _
  · intro x hx
    simp only [siteC, annCl, sub_zero] at hx
    change (3 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 2 at hx
    rw [mem_closedBall, dist_zero_right]
    linarith

end HigherDimLQGContinuity
