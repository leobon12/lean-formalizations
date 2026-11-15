/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInLogLocal

/-!
# Extending the inherited derivative logarithm to the shared interval

PROVE-POCKET-SIDEIN. The extension is constructed from limits of the given
interior logarithm. Boundary continuity, its reflected exponential identity,
and continuity from the closed half-plane are conclusions.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The actual inherited logarithm extends to an open shared real interval.
The extension agrees with the given logarithm everywhere in the current
domain, and hence retains its branch without an independent normalization. -/
theorem exists_inherited_log_extension {c : Chart} (hc : c.IsConformal)
    {L G : ℂ → ℂ} (hL : IsDerivLog c.1 L c.dom)
    (hExtensionEq : EqOn G c.1 c.dom)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ (c.dom : Set ℂ))
    (hReflect : ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r) :
    ∃ Lbar : ℂ → ℂ, EqOn Lbar L c.dom ∧
      ContinuousOn Lbar ((c.dom : Set ℂ) ∪ ofReal '' J) ∧
      (∀ x ∈ J, ContinuousWithinAt Lbar Hbar (x : ℂ)) ∧
      (∀ x ∈ J, exp (Lbar x) = deriv (schwarzReflect G) x) := by
  have hcl : ∀ x ∈ J, (x : ℂ) ∈ closure (c.dom : Set ℂ) := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact mem_Hbar_of_im_eq_zero (by simp)
    exact closure_mono hsub (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩)
  have hlim : ∀ x ∈ J, ∃ ℓ : ℂ, Tendsto L (𝓝[(c.dom : Set ℂ)] (x : ℂ)) (𝓝 ℓ) ∧
      exp ℓ = deriv (schwarzReflect G) x := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    obtain ⟨s, hs, hR⟩ := hReflect x hx
    obtain ⟨ℓ, hℓ, he⟩ := exists_tendsto_log_of_shared_halfDisc hc hL hExtensionEq hr hs hsub hR
    exact ⟨ℓ, hℓ.mono_left (nhdsWithin_mono _ hc.dom_subset), he⟩
  let Lbar := extendFrom (c.dom : Set ℂ) L
  have hbar : ContinuousOn Lbar ((c.dom : Set ℂ) ∪ ofReal '' J) := by
    apply continuousOn_extendFrom
    · rintro z (hz | ⟨x, hx, rfl⟩)
      · exact subset_closure hz
      · exact hcl x hx
    · rintro z (hz | ⟨x, hx, rfl⟩)
      · exact ⟨L z, hL.1.continuousOn z hz⟩
      · obtain ⟨ℓ, hℓ, -⟩ := hlim x hx
        exact ⟨ℓ, hℓ⟩
  refine ⟨Lbar, extendFrom_extends hL.1.continuousOn, hbar, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    apply (hbar _ (Or.inr (mem_image_of_mem _ hx))).mono_of_mem_nhdsWithin
    have hxre : (x : ℂ).re ∈ J := by simpa using hx
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr),
      nhdsWithin_le_nhds ((continuous_re.isOpen_preimage J hJo).mem_nhds hxre)]
      with z hzbar hzball hzre
    rcases (show 0 ≤ z.im from hzbar).lt_or_eq with hpos | hzero
    · exact Or.inl (hsub ⟨hpos, hzball⟩)
    · exact Or.inr ⟨z.re, hzre, by apply Complex.ext <;> simp [hzero.symm]⟩
  · intro x hx
    obtain ⟨ℓ, hℓ, he⟩ := hlim x hx
    change exp (extendFrom (c.dom : Set ℂ) L x) = _
    rw [extendFrom_eq (hcl x hx) hℓ, he]

end InteractingSLE.Sec7.PocketStopSide
