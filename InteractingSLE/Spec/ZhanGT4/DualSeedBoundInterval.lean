/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBoundRegularity

/-!
# The transposed-configuration derivative estimate at arbitrary real points

Packet PROVE-ZHAN-GT4-A22. A6's other-time ODE argument applies at any alive
real coordinate with a separated image, and hence at every point of an
interval once the image-gap estimate has been supplied on that interval.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

namespace ImgData

/-- A6's derivative lower estimate for a reflection at any real point, rather
than just the other curve's current driver. The image-gap hypothesis is the
geometric input to the other-time logarithmic derivative ODE. -/
theorem exp_le_norm_deriv_reflection_at {W W' a : ℝ → ℝ}
    {A : Set ℂ} {φ : ℂ → ℂ} {T t x r ρ γ : ℝ}
    (h : ImgData W A φ T a W') (hr : 0 < r)
    (hclr : ∀ u ∈ Icc (0 : ℝ) T,
      Disjoint (ball (W u : ℂ) r) ((fun z => fwdMap W u z + W u) '' A))
    {v : ℝ → ℂ} (hv : IsForwardSol W' (x : ℂ) (a T) v)
    (hγ : 0 < γ) (hgap : ∀ u ∈ Icc (0 : ℝ) T, γ ≤ ‖fwdMap W' (a u) x‖)
    (ht : t ∈ Icc (0 : ℝ) T) {R G : ℂ → ℂ}
    (hR : IsMapOut (φ '' fwdHull W t) R) (hρ : 0 < ρ)
    (hclear : Disjoint (ball (x : ℂ) ρ) (φ '' fwdHull W t))
    (hGd : DifferentiableOn ℂ G (ball (x : ℂ) ρ))
    (hGR : EqOn G R (ball (x : ℂ) ρ ∩ H)) :
    Real.exp (-(2 / γ ^ 2 * t)) ≤ ‖deriv G x‖ := by
  have haT : 0 ≤ a T := (h.mapsTo_clock_Icc ⟨h.pos.le, le_rfl⟩).1
  have hat := h.mapsTo_clock_Icc ht
  obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hv haT
  let η := min ρ (aliveRad (a T) δ)
  have hη : 0 < η := lt_min hρ (aliveRad_pos hδ)
  have hE : IsHPHull (φ '' fwdHull W t) := by
    rw [← h.img t ht]
    exact isHPHull_fwdHull h.contW' hat.1
  have hgt : IsMapOut (φ '' fwdHull W t)
      (fun z => fwdMap W' (a t) z + W' (a t)) := by
    rw [← h.img t ht]
    exact isMapOut_fwdMap_gen h.contW' hat.1
  have hReq := IsMapOut.eqOn hE hR hgt
  have hf : DifferentiableOn ℂ (fun z => fwdMap W' (a t) z + W' (a t))
      (ball (x : ℂ) η) := by
    intro z hz
    exact ((hasDerivAt_fwdMap_aliveDisc h.contW' hv hδ hlow
      (ball_subset_ball (min_le_right _ _) hz) hat).add_const _).differentiableAt.differentiableWithinAt
  have hEq := ConformalImageFull.eqOn_ball_of_eqOn_upper hη
    (hGd.mono (ball_subset_ball (min_le_left _ _))) hf (fun z hz => by
      have hzρ := ball_subset_ball (min_le_left _ _) hz.1
      rw [hGR ⟨hzρ, hz.2⟩]
      exact hReq ⟨hz.2, fun hzE => Set.disjoint_left.1 hclear hzρ hzE⟩)
  have hde : deriv G (x : ℂ) =
      deriv (fun z => fwdMap W' (a t) z + W' (a t)) (x : ℂ) := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (x := (x : ℂ)) hη)] with z hz
    exact hEq hz
  rw [hde, deriv_add_const]
  exact (h.exp_neg_le_norm_deriv_fwdMap_image hr hclr hv hγ hgap ht).1

end ImgData

end InteractingSLE.ZhanGT4
