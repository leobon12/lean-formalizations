/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11Face
import InteractingSLE.Foundations.PrimeEnd.Jordan

/-!
# GB11: Carathéodory correspondence and the current mapping-out extension

The constructed current face has precisely the two-wall-and-base frontier. Its
prime ends are realized homeomorphically on this frontier. The map `h_s` has a
continuous boundary extension away from its pole; finite continuous relative-chart
limits exclude this pole at every point visited by the ambient own future.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.GB11Chart

/-- Any point of the current domain selects exactly the constructed Jordan face. -/
theorem CurrentGateBoundary.component_eq {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) (hOo : IsOpen (ownDomain W C t))
    (hOc : IsConnected (ownDomain W C t)) {p : ℂ} (hp : p ∈ mu '' ownDomain W C t) :
    connectedComponentIn b.boundaryᶜ p = mu '' ownDomain W C t := by
  obtain ⟨hFo, hFc⟩ := isOpen_isConnected_mu_ownDomain hOo hOc
  exact eq_connectedComponentIn_of_frontier_subset hFo hFc.isPreconnected hp
    (fun z hz hzb => b.disjoint_domain.le_bot ⟨hzb, hz⟩) b.frontier_subset

/-- The entire two-wall-and-base boundary is the frontier of the current face. -/
theorem CurrentGateBoundary.frontier_eq {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) (hOo : IsOpen (ownDomain W C t))
    (hOc : IsConnected (ownDomain W C t)) :
    frontier (mu '' ownDomain W C t) = b.boundary := by
  obtain ⟨p, hp⟩ := hOc.nonempty.image mu
  have he := b.component_eq hOo hOc hp
  have hpΓ : p ∈ b.boundaryᶜ := fun h => b.disjoint_domain.le_bot ⟨h, hp⟩
  have hb : IsBounded (connectedComponentIn b.boundaryᶜ p) := by
    rw [he]
    exact isBounded_mu_ownDomain W C t
  have hfr := (Foundations.Schoenflies.jordan_split b.isJordanCurve hpΓ hb).1
  rwa [he] at hfr

/-- Carathéodory boundary correspondence of the current face, including extra real
contacts: every prime end has a unique Euclidean realization, homeomorphically. -/
theorem CurrentGateBoundary.exists_primeEnd_homeomorph {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) (hOo : IsOpen (ownDomain W C t))
    (hOc : IsConnected (ownDomain W C t)) :
    ∃ e : PrimeEnd (mu '' ownDomain W C t) ≃ₜ frontier (mu '' ownDomain W C t),
      ∀ p : PrimeEnd (mu '' ownDomain W C t), p.IsRealizedAt (e p) := by
  obtain ⟨hFo, hFc⟩ := isOpen_isConnected_mu_ownDomain hOo hOc
  apply PrimeEnd.exists_homeomorph_frontier_of_isJordanCurve hFo hFc
    (isBounded_mu_ownDomain W C t)
  rw [b.frontier_eq hOo hOc]
  exact b.isJordanCurve

/-- A mapping-out pole cannot be a point where the pre-mapping-out function has a
finite continuous limit. The hydrodynamic bounded-displacement estimate suffices. -/
theorem ne_pole_of_continuousWithinAt {D K : Set ℂ} (hK : IsHPHull K)
    {f : ℂ → ℂ} (hf : MapsTo f D (H \ K)) {p x : ℂ}
    (hp : Tendsto (ConformalImage.mapOut K ∘ f) (𝓝[D] p) (cobounded ℂ))
    (hx : x ∈ closure D) (hc : ContinuousWithinAt f D x) : x ≠ p := by
  intro heq
  subst x
  have : (𝓝[D] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have hg : IsMapOut K (ConformalImage.mapOut K) := ConformalImage.isMapOut_mapOut hK
  obtain ⟨M, hM⟩ := hg.exists_norm_le hK
  have hsmall : ∀ᶠ w in 𝓝[D] p, ‖f w‖ < ‖f p‖ + 1 := by
    filter_upwards [hc.tendsto.eventually (Metric.ball_mem_nhds (f p) one_pos)] with w hw
    have := norm_sub_norm_le (f w) (f p)
    rw [dist_eq_norm] at hw
    linarith
  have hlarge : ∀ᶠ w in 𝓝[D] p, ‖f p‖ + 1 + M < ‖ConformalImage.mapOut K (f w)‖ :=
    (tendsto_norm_atTop_iff_cobounded.2 hp).eventually (eventually_gt_atTop _)
  obtain ⟨w, ⟨hws, hwl⟩, hw⟩ := ((hsmall.and hlarge).and self_mem_nhdsWithin).exists
  have hbound := hM _ (hf hw)
  linarith

/-- The current map `h_s = g_K ∘ f` has one continuous boundary extension, and at
EVERY boundary point with a finite continuous `f`-limit this extension avoids its
pole and inverts through `invExt K`. Apply this to the visited points `mu (δ_s u)`;
GB11OwnFutureFace proves their confinement and the required finite `f`-limits. -/
theorem exists_currentFace_mappingOut_extension {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (b : CurrentGateBoundary W C t) (hOo : IsOpen (ownDomain W C t))
    (hOc : IsConnected (ownDomain W C t)) {ζ : ℝ → ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hζc : ContinuousOn ζ (Icc 0 s)) (hζH : MapsTo ζ (Icc 0 s) Hbar) (hζ0 : ζ 0 = 0)
    {f : ℂ → ℂ} (hf : IsConformalBijection f (mu '' ownDomain W C t)
      (H \ fillH (ζ '' Icc 0 s))) :
    ∃ q ∈ b.boundary, ∃ G : ℂ → ℂ,
      EqOn G (ConformalImage.mapOut (fillH (ζ '' Icc 0 s)) ∘ f)
        (mu '' ownDomain W C t) ∧
      ContinuousOn G (closure (mu '' ownDomain W C t) \ {q}) ∧
      MapsTo G (closure (mu '' ownDomain W C t) \ {q}) Hbar ∧
      ∀ x ∈ closure (mu '' ownDomain W C t),
        ContinuousWithinAt f (mu '' ownDomain W C t) x →
          x ≠ q ∧ YuanCharacterisation.invExt (fillH (ζ '' Icc 0 s)) (G x) = f x := by
  set D := mu '' ownDomain W C t
  set K := fillH (ζ '' Icc 0 s)
  obtain ⟨p, hp⟩ := hOc.nonempty.image mu
  have he : connectedComponentIn b.boundaryᶜ p = D := b.component_eq hOo hOc hp
  have hpΓ : p ∈ b.boundaryᶜ := fun h => b.disjoint_domain.le_bot ⟨h, hp⟩
  have hb : IsBounded (connectedComponentIn b.boundaryᶜ p) := by
    rw [he]
    exact isBounded_mu_ownDomain W C t
  have hK : IsHPHull K := YuanCharacterisation.isHPHull_fillH_image hζc hs hζ0
  have hg : IsMapOut K (ConformalImage.mapOut K) := ConformalImage.isMapOut_mapOut hK
  have hconf := isConformalBijection_comp hg.1 hf
  rw [← he] at hconf
  obtain ⟨q, hqΓ, G, hGeq, hGc, hGH, hGp⟩ :=
    Sec6.exists_bdryExt_of_isConformalBijection b.isJordanCurve hpΓ hb hconf
  rw [he] at hGeq hGc hGH hGp
  obtain ⟨hinvc, hinvg⟩ := Sec6.invExt_facts hs hζc hζH hζ0
  have hqD : q ∉ D := fun h => b.disjoint_domain.le_bot ⟨hqΓ, h⟩
  have hsub : D ⊆ closure D \ {q} := fun w hw => ⟨subset_closure hw, fun he => hqD (he ▸ hw)⟩
  refine ⟨q, hqΓ, G, hGeq, hGc, hGH, fun x hx hfc => ?_⟩
  have hxq : x ≠ q := ne_pole_of_continuousWithinAt hK hf.2.mapsTo hGp hx hfc
  refine ⟨hxq, ?_⟩
  have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have hxD : x ∈ closure D \ {q} := ⟨hx, hxq⟩
  have hc : ContinuousWithinAt (fun w => YuanCharacterisation.invExt K (G w)) D x :=
    ((hinvc _ (hGH hxD)).comp (hGc _ hxD) hGH).mono hsub
  have hidentity : ∀ w ∈ D, YuanCharacterisation.invExt K (G w) = f w := by
    intro w hw
    rw [hGeq hw]
    exact hinvg _ (hf.2.mapsTo hw)
  exact tendsto_nhds_unique (hc.tendsto.congr'
    (eventually_nhdsWithin_of_forall hidentity)) hfc.tendsto

end InteractingSLE.Theorem14.GB11Chart
