/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailReference

/-!
# Correct incident accesses and the resulting approach filters

PROVE-POCKET-SIDEIN. A real limit of the old coordinate along a current
inverse-chart approach supplies the incident-access closure condition.
An unfilled old half-disc then carries the old inverse approach into the
actual current physical domain. Rational half-discs suffice to record it.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The correctly incident old access can be certified by a current
inverse-chart approach. It cannot be replaced by an arbitrary fibre over p. -/
theorem old_access_mem_closure_of_current_transition {current : Chart}
    (hCurrent : current.IsConformal) {old : Chart} {ξ x : ℝ}
    (hTransition : Tendsto (fun z => old.1 (current.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) :
    (x : ℂ) ∈ closure (old.1 '' (current.dom : Set ℂ)) := by
  have : NeBot (𝓝[H] (ξ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  exact mem_closure_of_tendsto hTransition
    (eventually_nhdsWithin_of_forall fun z hz =>
      mem_image_of_mem old.1 (hCurrent.inv_mem_dom hz))

/-- A constructed unfilled half-disc gives the precise physical-domain
approach filter needed for transporting a boundary germ. -/
theorem tendsto_old_inverse_within_current_of_halfDisc {old : Chart}
    {D : Set ℂ} {x : ℝ} {p : ℂ}
    (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    {d : ℝ} (hd : 0 < d)
    (hCurrent : old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ D) :
    Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝[D] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hLanding, ?_⟩
  have hBall : ∀ᶠ y in 𝓝[H] (x : ℂ), y ∈ ball (x : ℂ) d :=
    nhdsWithin_le_nhds (ball_mem_nhds _ hd)
  filter_upwards [self_mem_nhdsWithin, hBall] with y hyH hyd
  exact hCurrent (mem_image_of_mem old.2.1 ⟨hyH, hyd⟩)

/-- Every constructed unfilled incident collar has a rational centre and
radius recording the same access, with the same physical range bound. -/
theorem exists_rat_unfilled_halfDisc {old : Chart} {D : Set ℂ}
    {x : ℝ} {p : ℂ} {d r : ℝ} (hd : 0 < d)
    (hBall : old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ ball p r)
    (hCurrent : old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ D) :
    ∃ c ε : ℚ, 0 < (ε : ℝ) ∧ (x : ℂ) ∈ ball (c : ℂ) (ε : ℝ) ∧
      old.2.1 '' (H ∩ ball (c : ℂ) (ε : ℝ)) ⊆ ball p r ∧
      old.2.1 '' (H ∩ ball (c : ℂ) (ε : ℝ)) ⊆ D := by
  obtain ⟨c, ε, hε, hx, hSub⟩ := exists_rat_halfDisc_inside hd
  exact ⟨c, ε, hε, hx, (image_mono hSub).trans hBall, (image_mono hSub).trans hCurrent⟩

end InteractingSLE.Sec7.PocketStopSide
