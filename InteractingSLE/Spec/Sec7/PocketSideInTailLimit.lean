/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailActual
import InteractingSLE.Spec.Sec7.PocketSideInReachLimit

/-!
# Constructing the old incident access from its inverse extension

PROVE-POCKET-SIDEIN. The nested current inverse approaches a physical
boundary point of the old domain. The existing Yuan inverse-fibre theorem
and a local bound construct the real old access and its full inverse
landing. No shared half-disc is needed before this access is constructed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A bounded nested transition selects the correct old boundary fibre,
including when the old inverse has several fibres over the physical point. -/
theorem exists_old_incident_access_of_inverse_extension {old current : Chart}
    (hOld : old.IsConformal) (hCurrent : current.IsConformal)
    (hInclusion : (current.dom : Set ℂ) ⊆ old.dom) {E : ℂ → ℂ}
    (hE : EqOn E old.2.1 H) (hEc : ContinuousOn E Hbar) {ξ : ℝ} {p : ℂ}
    (hLanding : Tendsto current.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p))
    (hBoundary : p ∉ old.dom)
    (hBound : ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (ξ : ℂ), ‖old.1 (current.2.1 z)‖ ≤ M) :
    ∃ x : ℝ,
      Tendsto (fun z => old.1 (current.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) := by
  have hMaps : MapsTo current.2.1 H (old.dom : Set ℂ) :=
    fun z hz => hInclusion (hCurrent.inv_mem_dom hz)
  have hComposite : Tendsto (fun z => E (old.1 (current.2.1 z)))
      (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
    refine hLanding.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    exact ((hE (hOld.fwd_mem (hMaps hz))).trans (hOld.inv_fwd (hMaps hz))).symm
  obtain ⟨M, hM⟩ := hBound
  obtain ⟨y, hy, hEy, hLimit⟩ := exists_tendsto_of_tendsto_comp
    (hOld.1.congr fun z hz => hE hz) hEc (hOld.injOn.congr hE.symm)
    (inverse_extension_real_notMem_image hOld hE hEc)
    (mem_Hbar_of_im_eq_zero (by simp : (ξ : ℂ).im = 0))
    (hOld.differentiableOn_fwd.continuousOn.comp hCurrent.1.continuousOn hMaps)
    (fun z hz => QuantumZipper.H_subset_Hbar (hOld.fwd_mem (hMaps hz))) hM hComposite
  have hy0 : y.im = 0 := by
    apply le_antisymm (le_of_not_gt fun hyH => ?_) hy
    apply hBoundary
    rw [← hEy, hE hyH]
    exact hOld.inv_mem_dom hyH
  have hyr : (y.re : ℂ) = y := (eq_ofReal_re_of_im_eq_zero hy0).symm
  refine ⟨y.re, by rwa [hyr], ?_⟩
  have hlim := (hEc y hy).mono QuantumZipper.H_subset_Hbar |>.tendsto
  rw [hEy] at hlim
  rw [hyr]
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => hE hz)

end InteractingSLE.Sec7.PocketStopSide
