/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6LandOuterInf

/-!
# R.6: a driver collar yields physical inclusion near a singleton tip

PROVE-R6-LANDING; Astra's `r6_face_geometry`, Lemma 4.1, ruling R98.
The compactness argument uses the existing boundary chart's forward
bound in place of a separate spherical compactification. It applies to
bounded and seed-opening pockets, and asks for singleton access only at
the current tip. Exposed landings may have multiple active prime ends.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Land

open R6Tn R6Fc PocketStopSide

/-- A same-time driver collar gives physical local containment at the
current tip when that tip has a singleton real fibre. All boundary-chart
hypotheses are supplied by the existing one-pocket constructors. -/
theorem driver_collar_physical {C P V : Set ℂ} {O : Chart} {vL vR : ℝ}
    (M : BoundaryChart C P O vL vR) (hVO : V ⊆ (O.dom : Set ℂ))
    (hsingle : ∀ x : ℝ, M.inverse (x : ℂ) = M.inverse 0 → x = 0)
    {r : ℝ} (hr : 0 < r) (hcol : H ∩ ball (0 : ℂ) r ⊆ O.1 '' V) :
    ∃ e > 0, (O.dom : Set ℂ) ∩ ball (M.inverse 0) e ⊆ V := by
  have h0H : (0 : ℂ) ∈ Hbar := real_mem_Hbar 0
  have hp : M.inverse 0 ∈ P := M.inv_maps h0H
  have hpnot : M.inverse 0 ∉ (O.dom : Set ℂ) :=
    inverse_real_landing_notMem_dom (x := (0 : ℝ)) M.conformal
      (by simpa only [Complex.ofReal_zero] using tendsto_of_extension M.inv_eq M.inv_cont 0)
  have hfibre : ∀ z ∈ Hbar, M.inverse z = M.inverse 0 → z = 0 := by
    intro z hz heq
    by_cases hzH : z ∈ H
    · exact False.elim (hpnot (heq ▸ (M.inv_eq hzH ▸ M.conformal.inv_mem_dom hzH)))
    · have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hz
      have he : z = (z.re : ℂ) := Complex.ext rfl (by simp only [Complex.ofReal_im]; exact him)
      have hre : z.re = 0 := hsingle z.re (by rwa [← he])
      rw [he, hre, Complex.ofReal_zero]
  obtain ⟨ε, hε, hψ⟩ := Metric.continuousWithinAt_iff.1 (M.coord_cont _ hp) 1 one_pos
  obtain ⟨B, hB⟩ := M.norm_bound
  let N := ‖M.coord (M.inverse 0)‖ + 1 + B
  let K := (Hbar ∩ closedBall (0 : ℂ) N) \ ball (0 : ℂ) r
  have hHbar : IsClosed Hbar := by
    rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact isClosed_closure
  have hK : IsCompact K := ((isCompact_closedBall (0 : ℂ) N).inter_left hHbar).diff isOpen_ball
  have himage : IsClosed (M.inverse '' K) :=
    (hK.image_of_continuousOn (M.inv_cont.mono fun _ hz => hz.1.1)).isClosed
  have hpimage : M.inverse 0 ∉ M.inverse '' K := by
    rintro ⟨z, hz, heq⟩
    exact hz.2 (hfibre z hz.1.1 heq ▸ mem_ball_self hr)
  obtain ⟨δ, hδ, hδimage⟩ := Metric.mem_nhds_iff.1 (himage.isOpen_compl.mem_nhds hpimage)
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  rintro w ⟨hwO, hwball⟩
  have hwC : w ∈ C := by
    have hm := hwO
    rw [M.dom_eq] at hm
    exact hm.1
  have hwε : dist w (M.inverse 0) < ε := (mem_ball.1 hwball).trans_le (min_le_left _ _)
  have hnorm : ‖O.1 w‖ ≤ N := by
    have hdist := hψ (M.mem_boundary hwC) hwε
    have hnormdiff := norm_sub_norm_le (M.coord w) (M.coord (M.inverse 0))
    rw [dist_eq_norm] at hdist
    exact (hB w hwO).trans (by dsimp only [N]; linarith only [hdist, hnormdiff])
  have hzball : O.1 w ∈ ball (0 : ℂ) r := by
    by_contra hnot
    have hzK : O.1 w ∈ K := ⟨⟨QuantumZipper.H_subset_Hbar (M.conformal.fwd_mem hwO),
      by simpa only [mem_closedBall, dist_zero_right] using hnorm⟩, hnot⟩
    apply hδimage (mem_ball.2 ((mem_ball.1 hwball).trans_le (min_le_right _ _)))
    exact ⟨O.1 w, hzK, (M.inv_eq (M.conformal.fwd_mem hwO)).trans (M.conformal.inv_fwd hwO)⟩
  obtain ⟨u, huV, hueq⟩ := hcol ⟨M.conformal.fwd_mem hwO, hzball⟩
  have he : u = w := by
    calc u = O.2.1 (O.1 u) := (M.conformal.inv_fwd (hVO huV)).symm
      _ = O.2.1 (O.1 w) := congrArg O.2.1 hueq
      _ = w := M.conformal.inv_fwd hwO
  exact he ▸ huV

end InteractingSLE.Sec7.R6Land
