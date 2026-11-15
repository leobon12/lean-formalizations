/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatch

/-!
# Localizing the existing inverse-fibre cluster theorem

PROVE-POCKET-SIDEIN. A continuous radial retraction agrees with the identity
near a real centre and maps H into a prescribed upper half-disc. It lets
YuanFiber's existing cluster theorem apply to a map defined only on that
half-disc. No new cluster-set argument is needed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A continuous localization of H into an upper half-disc, equal to the
identity near its real centre. -/
theorem exists_halfDisc_retraction (x : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ P : ℂ → ℂ, Continuous P ∧ MapsTo P H (H ∩ ball (x : ℂ) r) ∧
      P =ᶠ[𝓝[H] (x : ℂ)] id := by
  let a : ℝ := r / 2
  have ha : 0 < a := half_pos hr
  let P : ℂ → ℂ := fun z => (x : ℂ) +
    (a / max a ‖z - (x : ℂ)‖) • (z - (x : ℂ))
  have hden (z : ℂ) : 0 < max a ‖z - (x : ℂ)‖ := ha.trans_le (le_max_left _ _)
  have hscale (z : ℂ) : 0 < a / max a ‖z - (x : ℂ)‖ := div_pos ha (hden z)
  have hPc : Continuous P := continuous_const.add
    ((continuous_const.div (continuous_const.max (continuous_id.sub continuous_const).norm)
      (fun z => (hden z).ne')).smul (continuous_id.sub continuous_const))
  refine ⟨P, hPc, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, ?_⟩
    · change 0 < (P z).im
      simpa only [P, Complex.add_im, Complex.ofReal_im, Complex.smul_im,
        Complex.sub_im, sub_zero, zero_add, smul_eq_mul] using mul_pos (hscale z) hz
    · rw [mem_ball, dist_eq_norm]
      change ‖(x : ℂ) + (a / max a ‖z - (x : ℂ)‖) • (z - (x : ℂ)) - x‖ < r
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hscale z)]
      have hle : a / max a ‖z - (x : ℂ)‖ * ‖z - (x : ℂ)‖ ≤ a := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (hden z)]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le
      exact hle.trans_lt (by dsimp only [a]; linarith)
  · filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) ha)] with z hz
    have hn : ‖z - (x : ℂ)‖ ≤ a := by
      exact (show ‖z - (x : ℂ)‖ < a by simpa only [mem_ball, dist_eq_norm] using hz).le
    dsimp only [P, id_eq]
    rw [max_eq_left hn, div_self ha.ne', one_smul, add_sub_cancel]

/-- YuanFiber's existing cluster theorem needs only a half-disc germ of G
at a real point. The global hypotheses concern the inverse extension F. -/
theorem exists_tendsto_of_tendsto_comp_local {F G : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F H) (hc : ContinuousOn F Hbar) (hinj : InjOn F H)
    (hR : ∀ z : ℂ, z.im = 0 → F z ∉ F '' H) {x r : ℝ} (hr : 0 < r)
    (hGc : ContinuousOn G (H ∩ ball (x : ℂ) r))
    (hGH : MapsTo G (H ∩ ball (x : ℂ) r) Hbar) {R : ℝ}
    (hGR : ∀ᶠ z in 𝓝[H] (x : ℂ), ‖G z‖ ≤ R) {p : ℂ}
    (hFG : Tendsto (fun z => F (G z)) (𝓝[H] (x : ℂ)) (𝓝 p)) :
    ∃ ξ ∈ Hbar, F ξ = p ∧ Tendsto G (𝓝[H] (x : ℂ)) (𝓝 ξ) := by
  obtain ⟨P, hPc, hPmaps, hPid⟩ := exists_halfDisc_retraction x hr
  have hEq : (G ∘ P) =ᶠ[𝓝[H] (x : ℂ)] G := hPid.mono fun z hz => congrArg G hz
  obtain ⟨ξ, hξ, hFξ, hlim⟩ := exists_tendsto_of_tendsto_comp hd hc hinj hR
    (mem_Hbar_of_im_eq_zero (by simp)) (hGc.comp hPc.continuousOn hPmaps)
    (hGH.comp hPmaps) (hGR.congr (hEq.mono fun _ hz => by rw [hz]))
    (hFG.congr' (hEq.mono fun z hz => congrArg F hz.symm))
  exact ⟨ξ, hξ, hFξ, hlim.congr' hEq⟩

end InteractingSLE.Sec7.PocketStopSide
