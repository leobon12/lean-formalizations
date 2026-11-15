/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFiniteBound
import InteractingSLE.Spec.Sec7.PocketSideInInstExtension

/-!
# Finite current-face extension from local bounds

PROVE-POCKET-SIDEIN. Apply the existing Jordan correspondence directly to
the current chart after its fixed compactification. A local norm bound
excludes the unique pole. The compactifying map and its factorization are
constructed; a continuous pre-mapping-out extension is unnecessary.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.PocketStopSide

open Theorem14.GB11Chart

/-- A local norm bound excludes a boundary pole on any nontrivial access. -/
theorem ne_pole_of_eventually_norm_bounded {D : Set ℂ} {f : ℂ → ℂ} {p x : ℂ}
    (hPole : Tendsto f (𝓝[D] p) (cobounded ℂ)) (hx : x ∈ closure D)
    (hBound : ∃ M : ℝ, ∀ᶠ z in 𝓝[D] x, ‖f z‖ ≤ M) : x ≠ p := by
  intro heq
  subst x
  have : (𝓝[D] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  obtain ⟨M, hM⟩ := hBound
  have hlarge := (tendsto_norm_atTop_iff_cobounded.2 hPole).eventually
    (eventually_gt_atTop M)
  obtain ⟨z, hz, hz'⟩ := (hM.and hlarge).exists
  exact (not_lt_of_ge hz) hz'

/-- The current chart itself has a finite extension across a shared interval
once its domain is the constructed GB11 face and the chart is locally
bounded there. Neither a candidate extension nor its factorization is an input. -/
theorem exists_shared_extension_of_current_face_bound {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) {c : Chart} (hc : c.IsConformal)
    (hDomain : (c.dom : Set ℂ) = ownDomain W C t)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ (c.dom : Set ℂ))
    (hLocalBound : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[(c.dom : Set ℂ)] (x : ℂ), ‖c.1 z‖ ≤ M) :
    ∃ G : ℂ → ℂ, EqOn G c.1 c.dom ∧
      ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
      ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  have hOo : IsOpen (ownDomain W C t) := hDomain ▸ c.dom.isOpen
  have hConn : IsConnected (c.dom : Set ℂ) := by
    refine ⟨⟨c.2.1 Complex.I, hc.inv_mem_dom (by simp [H])⟩, ?_⟩
    rw [hc.coe_dom]
    exact convex_H.isPreconnected.image _ hc.1.continuousOn
  have hOc : IsConnected (ownDomain W C t) := hDomain ▸ hConn
  obtain ⟨p, hp⟩ := hOc.nonempty.image mu
  have he := b.component_eq hOo hOc hp
  have hpΓ : p ∈ b.boundaryᶜ := fun h => b.disjoint_domain.le_bot ⟨h, hp⟩
  have hb : IsBounded (connectedComponentIn b.boundaryᶜ p) := by
    rw [he]
    exact isBounded_mu_ownDomain W C t
  have hfwd : IsConformalBijection c.1 (ownDomain W C t) H := by
    rw [← hDomain]
    exact ⟨hc.differentiableOn_fwd, fun _ hz => hc.fwd_mem hz,
      fun z hz w hw h => by rw [← hc.inv_fwd hz, ← hc.inv_fwd hw, h],
      fun z hz => ⟨c.2.1 z, hc.inv_mem_dom hz, hc.2.2 z hz⟩⟩
  have hΦ := isConformalBijection_comp hfwd (isConformalBijection_muInv_ownDomain W C t)
  rw [← he] at hΦ
  obtain ⟨q, hq, G₀, heq, hGc, -, hPole⟩ :=
    Sec6.exists_bdryExt_of_isConformalBijection b.isJordanCurve hpΓ hb hΦ
  rw [he] at heq hGc hPole
  have hqD : q ∉ mu '' ownDomain W C t := fun h => b.disjoint_domain.le_bot ⟨hq, h⟩
  have hBoundary : ∀ x ∈ J,
      mu x ∈ closure (mu '' ownDomain W C t) ∧ mu x ≠ q := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact mem_Hbar_of_im_eq_zero (by simp)
    have hxD := closure_mono hsub (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩)
    have : (𝓝[(c.dom : Set ℂ)] (x : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hxD
    have hxbar : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    have hμ := (continuousAt_mu (fun h => neg_I_notMem_Hbar (h ▸ hxbar))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[(c.dom : Set ℂ)] (x : ℂ) ≤ 𝓝 (x : ℂ))
    have hμmaps : ∀ᶠ z in 𝓝[(c.dom : Set ℂ)] (x : ℂ),
        mu z ∈ mu '' ownDomain W C t :=
      eventually_nhdsWithin_of_forall fun z hz => mem_image_of_mem _ (hDomain ▸ hz)
    have hcl := isClosed_closure.mem_of_tendsto hμ
      (hμmaps.mono fun _ hz => subset_closure hz)
    refine ⟨hcl, ?_⟩
    intro heqx
    have hμwithin := tendsto_nhdsWithin_iff.2 ⟨hμ, hμmaps⟩
    rw [heqx] at hμwithin
    have hbad : Tendsto c.1 (𝓝[(c.dom : Set ℂ)] (x : ℂ)) (cobounded ℂ) := by
      simpa only [Function.comp_def, muInv_mu] using hPole.comp hμwithin
    exact (ne_pole_of_eventually_norm_bounded hbad hxD (hLocalBound x hx)) rfl
  have hmaps : MapsTo mu ((c.dom : Set ℂ) ∪ Complex.ofReal '' J)
      (closure (mu '' ownDomain W C t) \ {q}) := by
    rintro z (hz | ⟨x, hx, rfl⟩)
    · have hzμ := mem_image_of_mem mu (hDomain ▸ hz)
      exact ⟨subset_closure hzμ, fun h => hqD (h ▸ hzμ)⟩
    · exact hBoundary x hx
  have heq' : EqOn (G₀ ∘ mu) c.1 c.dom := by
    intro z hz
    simpa only [Function.comp_def, muInv_mu] using heq (mem_image_of_mem mu (hDomain ▸ hz))
  have hGc' : ContinuousOn (G₀ ∘ mu) ((c.dom : Set ℂ) ∪ Complex.ofReal '' J) := by
    apply hGc.comp (continuousOn_mu_Hbar.mono ?_) hmaps
    rintro z (hz | ⟨x, -, rfl⟩)
    · exact QuantumZipper.H_subset_Hbar (hc.dom_subset hz)
    · exact mem_Hbar_of_im_eq_zero (by simp)
  exact ⟨G₀ ∘ mu, heq', hGc', realBoundaryConformal_of_shared_face hc hJo hCollars hGc' heq'⟩

end InteractingSLE.Sec7.PocketStopSide
