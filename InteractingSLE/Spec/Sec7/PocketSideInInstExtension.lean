/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFaceReflect
import InteractingSLE.Spec.Supplement.GB11FaceExtension

/-!
# Shared-face extension from the current gate-boundary construction

PROVE-POCKET-SIDEIN. Use GB11's actual compactified current face and its
mapping-out extension. Finite pre-mapping-out limits exclude its single pole.
Pulling back through the compactification constructs the extension and hence
reflection on the shared interval. No extension of the transition is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.PocketStopSide

open Theorem14.GB11Chart

/-- GB11's finite-boundary extension, transported to the actual current
outer coordinate. The named inputs identify its compactified face and the
finite pre-mapping-out limits on the shared incoming interval. -/
theorem exists_shared_extension_of_current_gate {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) (hOo : IsOpen (ownDomain W C t))
    (hOc : IsConnected (ownDomain W C t)) {ζ : ℝ → ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hζc : ContinuousOn ζ (Icc 0 s)) (hζH : MapsTo ζ (Icc 0 s) Hbar) (hζ0 : ζ 0 = 0)
    {f : ℂ → ℂ} (hf : IsConformalBijection f (mu '' ownDomain W C t)
      (H \ fillH (ζ '' Icc 0 s)))
    {c : Chart} (hc : c.IsConformal) {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ (c.dom : Set ℂ))
    {E : ℂ → ℂ}
    (hCompactification : ContinuousOn E ((c.dom : Set ℂ) ∪ Complex.ofReal '' J))
    (hCurrentImage : MapsTo E c.dom (mu '' ownDomain W C t))
    (hForwardFactor : ∀ z ∈ (c.dom : Set ℂ),
      c.1 z = ConformalImage.mapOut (fillH (ζ '' Icc 0 s)) (f (E z)))
    (hFiniteBeforeMapOut : ∀ x ∈ J,
      ContinuousWithinAt f (mu '' ownDomain W C t) (E x)) :
    ∃ G : ℂ → ℂ, EqOn G c.1 c.dom ∧
      ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
      ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  obtain ⟨q, hq, G₀, hG₀eq, hG₀c, -, hfinite⟩ :=
    exists_currentFace_mappingOut_extension b hOo hOc hs hζc hζH hζ0 hf
  have hqO : q ∉ mu '' ownDomain W C t := fun h => b.disjoint_domain.le_bot ⟨hq, h⟩
  have hboundary : ∀ x ∈ J, E x ∈ closure (mu '' ownDomain W C t) ∧ E x ≠ q := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact mem_Hbar_of_im_eq_zero (by simp)
    have hxD := closure_mono hsub (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩)
    have : NeBot (𝓝[(c.dom : Set ℂ)] (x : ℂ)) :=
      mem_closure_iff_nhdsWithin_neBot.1 hxD
    have hlim := ((hCompactification _
      (Or.inr (mem_image_of_mem _ hx))).mono subset_union_left).tendsto
    have hcl : E x ∈ closure (mu '' ownDomain W C t) :=
      isClosed_closure.mem_of_tendsto hlim
        (eventually_nhdsWithin_of_forall fun z hz => subset_closure (hCurrentImage hz))
    exact ⟨hcl, (hfinite _ hcl (hFiniteBeforeMapOut x hx)).1⟩
  have hmaps : MapsTo E ((c.dom : Set ℂ) ∪ Complex.ofReal '' J)
      (closure (mu '' ownDomain W C t) \ {q}) := by
    intro z hz
    rcases hz with hz | ⟨x, hx, rfl⟩
    · exact ⟨subset_closure (hCurrentImage hz), fun he => hqO (he ▸ hCurrentImage hz)⟩
    · exact hboundary x hx
  have heq : EqOn (G₀ ∘ E) c.1 c.dom := fun z hz =>
    (hG₀eq (hCurrentImage hz)).trans (hForwardFactor z hz).symm
  have hcont : ContinuousOn (G₀ ∘ E) ((c.dom : Set ℂ) ∪ Complex.ofReal '' J) :=
    hG₀c.comp hCompactification hmaps
  exact ⟨G₀ ∘ E, heq, hcont,
    realBoundaryConformal_of_shared_face hc hJo hCollars hcont heq⟩

end InteractingSLE.Sec7.PocketStopSide
