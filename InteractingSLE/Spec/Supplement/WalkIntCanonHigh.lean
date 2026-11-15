/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormLift
import InteractingSLE.Spec.Sec7.ReverseArcLift

/-!
# Normalization at imaginary infinity

PROVE-T14-WALKINT continuation. Canonical derivative logarithms tend to zero
when the imaginary part tends to infinity. Bounded inverse displacement
preserves this approach, allowing normalization to pass through walk stages.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.WalkIntCanon

/-- Approach infinity through the upper half-plane with imaginary part
tending to infinity. -/
def highHalfPlane : Filter ℂ := comap Complex.im atTop ⊓ 𝓟 H

theorem tendsto_im_highHalfPlane : Tendsto Complex.im highHalfPlane atTop :=
  tendsto_comap.mono_left inf_le_left

theorem eventually_mem_highHalfPlane : ∀ᶠ z in highHalfPlane, z ∈ H :=
  mem_inf_of_right (mem_principal_self H)

theorem highHalfPlane_neBot : NeBot highHalfPlane := by
  have hv : Tendsto (fun t : ℝ => (t : ℂ) * I) atTop highHalfPlane := by
    refine tendsto_inf.2 ⟨tendsto_comap_iff.2 ?_, tendsto_principal.2 ?_⟩
    · convert (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop) using 1
      ext t
      simp
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simpa [QuantumZipper.H] using ht
  exact hv.neBot

/-- A bounded displacement in H preserves approach to imaginary infinity. -/
theorem tendsto_highHalfPlane_of_bound {f : ℂ → ℂ}
    (hH : MapsTo f H H) {M : ℝ} (hM : ∀ z ∈ H, ‖f z - z‖ ≤ M) :
    Tendsto f highHalfPlane highHalfPlane := by
  refine tendsto_inf.2 ⟨tendsto_comap_iff.2 ?_, tendsto_principal.2 ?_⟩
  · refine tendsto_atTop_mono' _ ?_
      (tendsto_atTop_add_const_right _ (-M) tendsto_im_highHalfPlane)
    filter_upwards [eventually_mem_highHalfPlane] with z hz
    have hb := (le_abs_self (z - f z).im).trans (abs_im_le_norm (z - f z))
    rw [norm_sub_rev] at hb
    have hm := hM z hz
    simp only [sub_im] at hb
    dsimp only [Function.comp_apply]
    linarith
  · exact eventually_mem_highHalfPlane.mono fun z hz => hH hz

/-- The canonical logarithm itself, rather than only its imaginary part,
tends to zero high up. No boundary regularity is required. -/
theorem tendsto_canonicalLog_of_im_atTop {K : Set ℂ} {g L : ℂ → ℂ}
    (hK : IsHPHull K) (hg : IsMapOut K g)
    (hL : Restart.IsCanonicalDerivLog K g L) {F : Filter ℂ}
    (him : Tendsto Complex.im F atTop) : Tendsto L F (𝓝 0) := by
  obtain ⟨R, hR, hKR⟩ := hK.exists_subset_ball
  have hbound : Tendsto (fun z : ℂ => 2 * R / z.im) F (𝓝 0) :=
    Filter.Tendsto.div_atTop (g := Complex.im) (tendsto_const_nhds (x := 2 * R)) him
  have hder : Tendsto (deriv g) F (𝓝 1) := by
    have hzero : Tendsto (fun z => deriv g z - 1) F (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun z => 2 * R / z.im) ?_ hbound
      filter_upwards [him.eventually (eventually_gt_atTop (8 * R))] with z hz
      exact Restart.norm_deriv_sub_one_le_of_isMapOut hK hg hR
        (hKR.trans ball_subset_closedBall) hz
    simpa only [sub_add_cancel, zero_add] using hzero.add_const 1
  have hlog := (continuousAt_clog one_mem_slitPlane).tendsto.comp hder
  rw [log_one] at hlog
  obtain ⟨Y, hY⟩ := hL.2
  exact hlog.congr' ((him.eventually (eventually_gt_atTop Y)).mono
    fun z hz => (hY z hz).symm)

/-- Data preserved by every finite walk operation. The lift is normalized
after pulling it back to H by the chart inverse. -/
structure IsNormalized (c : Chart) : Prop where
  conformal : c.IsConformal
  derivLift : c.HasDerivLift
  inverse_bound : ∃ M : ℝ, ∀ z ∈ H, ‖c.2.1 z - z‖ ≤ M
  lift_limit : Tendsto (fun z => c.2.2 (c.2.1 z)) highHalfPlane (𝓝 0)

end InteractingSLE.Theorem14.WalkIntCanon
