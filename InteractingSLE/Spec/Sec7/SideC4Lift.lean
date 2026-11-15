/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitLog
import InteractingSLE.Spec.Sec7.PocketSideInFaceReflect

/-!
# Inherited lift limits at incident reference accesses

PROVE-SIDE-COLLAR2 continuation. A finite continuous extension on a shared
interval gives a single lattice value for the actual transition lift. Its
limit along the current inverse is proved, with no new branch choice.
Reference heights in their own coordinate also transport to the current
inverse. These statements do not assert physical filled-set agreement.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Sec7.PocketStopSide

/-- One integer controls the inherited lift at every incident access to a
connected shared interval. The extension is of the literal transition lift,
so its integer cannot be chosen separately from the two physical charts. -/
theorem exists_lattice_lift_limits_of_reflected_interval
    {old current : Chart} {C U : Set ℂ}
    (hOld : IsDomainChart C old) (hCurrent : IsDomainChart U current)
    (hIncl : (current.dom : Set ℂ) ⊆ old.dom) {G : ℂ → ℂ} {J : Set ℝ}
    (hJo : IsOpen J) (hJ : IsPreconnected J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart old current).dom : Set ℂ))
    (hExtension : ContinuousOn G
      (((pocketTransitionChart old current).dom : Set ℂ) ∪ ofReal '' J))
    (hEq : EqOn G (pocketTransitionChart old current).1
      (pocketTransitionChart old current).dom) :
    ∃ n : ℤ, ∀ x ∈ J,
      extendFrom ((pocketTransitionChart old current).dom : Set ℂ)
        (pocketTransitionChart old current).2.2 (x : ℂ) = 2 * Real.pi * n ∧
      ∀ ξ : ℝ, Tendsto (fun z => old.1 (current.2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
        Tendsto (fun z => current.2.2 (current.2.1 z) - old.2.2 (current.2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  have hT := isConformal_pocketTransitionChart hOld.1 hCurrent.1 hIncl
  have hReflect := realBoundaryConformal_of_shared_face hT hJo hCollars hExtension hEq
  obtain ⟨L, -, hInherited, hLc, hWithin, hExp⟩ :=
    exists_inherited_transition_log_of_domain_charts hOld hCurrent hIncl hEq
      hJo hCollars hReflect
  obtain ⟨n, hn⟩ := (R16.r6_phase_const hJ hReflect
    (hLc.comp continuous_ofReal.continuousOn
      (fun x hx => Or.inr (mem_image_of_mem _ hx))) hExp).1
  refine ⟨n, fun x hx => ?_⟩
  have hLim : Tendsto (fun z => (L z).im) (𝓝[H] (x : ℂ))
      (𝓝 (2 * Real.pi * n)) := by
    have hnx : (L (x : ℂ)).im = 2 * Real.pi * n := hn x hx
    rw [← hnx]
    exact (continuous_im.tendsto (L x)).comp ((hWithin x hx).mono
      QuantumZipper.H_subset_Hbar).tendsto
  have hDomLim : Tendsto (pocketTransitionChart old current).2.2
      (𝓝[((pocketTransitionChart old current).dom : Set ℂ)] (x : ℂ))
      (𝓝 (2 * Real.pi * n)) :=
    (hLim.mono_left (nhdsWithin_mono _ hT.dom_subset)).congr'
      (eventually_nhdsWithin_of_forall fun z hz => hInherited z hz)
  have hxcl : (x : ℂ) ∈ closure ((pocketTransitionChart old current).dom : Set ℂ) := by
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact mem_Hbar_of_im_eq_zero (by simp only [ofReal_im])
    exact closure_mono hsub (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩)
  refine ⟨extendFrom_eq hxcl hDomLim, fun ξ hTransition => ?_⟩
  have hInto : Tendsto (fun z => old.1 (current.2.1 z))
      (𝓝[H] (ξ : ℂ))
      (𝓝[((pocketTransitionChart old current).dom : Set ℂ)] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hTransition, ?_⟩
    exact eventually_nhdsWithin_of_forall fun z hz => by
      rw [dom_pocketTransitionChart hOld.1 hCurrent.1 hIncl]
      exact mem_image_of_mem _ (hCurrent.1.inv_mem_dom hz)
  refine (hDomLim.comp hInto).congr'
    (eventually_nhdsWithin_of_forall fun z hz => ?_)
  change current.2.2 (old.2.1 (old.1 (current.2.1 z))) -
    old.2.2 (old.2.1 (old.1 (current.2.1 z))) = _
  rw [hOld.1.inv_fwd (hIncl (hCurrent.1.inv_mem_dom hz))]

/-- An old-coordinate corrected height gives the reference term in the
native collar along the current inverse. No physical mean comparison is
needed for this clause. -/
theorem tendsto_reference_height_at_incident_access
    {old current : Chart} (hOld : old.IsConformal) (hCurrent : current.IsConformal)
    (hIncl : (current.dom : Set ℂ) ⊆ old.dom) {ξ x : ℝ}
    (hTransition : Tendsto (fun z => old.1 (current.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) {κ b : ℝ} {u v : ℂ → ℝ}
    (hHeight : Tendsto (sideMean κ old u v) (𝓝[H] (x : ℂ)) (𝓝 b)) :
    Tendsto (fun z => v (current.2.1 z) + u (current.2.1 z) +
        chiC κ * old.2.2 (current.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 b) := by
  have hInto : Tendsto (fun z => old.1 (current.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hTransition, ?_⟩
    exact eventually_nhdsWithin_of_forall fun z hz =>
      hOld.fwd_mem (hIncl (hCurrent.inv_mem_dom hz))
  refine (hHeight.comp hInto).congr'
    (eventually_nhdsWithin_of_forall fun z hz => ?_)
  dsimp only [sideMean, Function.comp_def]
  rw [hOld.inv_fwd (hIncl (hCurrent.inv_mem_dom hz))]

end InteractingSLE.Sec7.PocketStopSide
