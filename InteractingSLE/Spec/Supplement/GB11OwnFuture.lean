/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11LocalGrowthCurve
import InteractingSLE.Spec.Sec6.Aux41Full

/-!
# GB11: continuous own futures through a current Jordan face

The analytic boundary-extension step of GB11 (specification pp. 556–557). A conformal
bijection from a bounded Jordan face onto the complement of a path hull transports a
continuous path in the closed face to a continuous own future. Its mapping-out pole
cannot be reached wherever the original conformal map has a finite continuous limit.
The Jordan-face geometry is an explicit premise of this internal helper.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.GB11Chart

/-- The boundary-extension argument (RG4)–(RG5), allowing any bounded Jordan face and
any continuous path in its closure. Finiteness of `f` excludes the mapping-out pole. -/
theorem exists_lift_of_jordan_face {Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) {ζ : ℝ → ℂ} {s : ℝ}
    (hs : 0 ≤ s) (hζc : ContinuousOn ζ (Icc 0 s))
    (hζH : MapsTo ζ (Icc 0 s) Hbar) (hζ0 : ζ 0 = 0)
    {f : ℂ → ℂ}
    (hf : IsConformalBijection f (connectedComponentIn Γᶜ p)
      (H \ fillH (ζ '' Icc 0 s))) {δ : ℝ → ℂ} {T : ℝ}
    (hδc : ContinuousOn δ (Icc s T))
    (hδD : MapsTo δ (Icc s T) (closure (connectedComponentIn Γᶜ p)))
    (hfc : ∀ u ∈ Icc s T, ContinuousWithinAt f (connectedComponentIn Γᶜ p) (δ u)) :
    ∃ β : ℝ → ℂ, ContinuousOn β (Icc s T) ∧ MapsTo β (Icc s T) Hbar ∧
      ∀ u ∈ Icc s T, YuanCharacterisation.invExt (fillH (ζ '' Icc 0 s)) (β u) = f (δ u) := by
  set D := connectedComponentIn Γᶜ p
  set K := fillH (ζ '' Icc 0 s)
  set g := ConformalImage.mapOut K
  have hK : IsHPHull K := YuanCharacterisation.isHPHull_fillH_image hζc hs hζ0
  have hg : IsMapOut K g := ConformalImage.isMapOut_mapOut hK
  obtain ⟨hinvc, hinvg⟩ := Sec6.invExt_facts hs hζc hζH hζ0
  obtain ⟨q, hqΓ, F, hFeq, hFc, hFH, hFt⟩ :=
    Sec6.exists_bdryExt_of_isConformalBijection hΓ hp hb (isConformalBijection_comp hg.1 hf)
  have hqD : q ∉ D := fun h => (connectedComponentIn_subset _ _ h) hqΓ
  have hsub : D ⊆ closure D \ {q} := fun w hw => ⟨subset_closure hw, fun h => hqD (h ▸ hw)⟩
  have hδq : ∀ u ∈ Icc s T, δ u ≠ q := by
    intro u hu heq
    have hqcl : q ∈ closure D := heq ▸ hδD hu
    have : (𝓝[D] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqcl
    obtain ⟨M, hM⟩ := hg.exists_norm_le hK
    have hfinite := (hfc u hu).tendsto
    rw [heq] at hfinite
    have hsmall : ∀ᶠ w in 𝓝[D] q, ‖f w‖ < ‖f q‖ + 1 := by
      filter_upwards [hfinite.eventually (Metric.ball_mem_nhds (f q) one_pos)] with w hw
      have := norm_sub_norm_le (f w) (f q)
      rw [dist_eq_norm] at hw
      linarith
    have hlarge : ∀ᶠ w in 𝓝[D] q, ‖f q‖ + 1 + M < ‖(g ∘ f) w‖ :=
      (tendsto_norm_atTop_iff_cobounded.2 hFt).eventually (eventually_gt_atTop _)
    obtain ⟨w, ⟨hwsmall, hwlarge⟩, hwD⟩ := ((hsmall.and hlarge).and self_mem_nhdsWithin).exists
    have hbound := hM _ (hf.2.mapsTo hwD)
    simp only [Function.comp_apply] at hwlarge
    linarith
  refine ⟨fun u => F (δ u), hFc.comp hδc (fun u hu => ⟨hδD hu, hδq u hu⟩),
    fun u hu => hFH ⟨hδD hu, hδq u hu⟩, fun u hu => ?_⟩
  have : (𝓝[D] (δ u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hδD hu)
  have hmem : δ u ∈ closure D \ {q} := ⟨hδD hu, hδq u hu⟩
  have hc : ContinuousWithinAt (fun w => YuanCharacterisation.invExt K (F w)) D (δ u) :=
    ((hinvc _ (hFH hmem)).comp (hFc _ hmem) hFH).mono hsub
  have heq : ∀ w ∈ D, YuanCharacterisation.invExt K (F w) = f w := by
    intro w hw
    rw [hFeq hw]
    exact hinvg _ (hf.2.mapsTo hw)
  exact tendsto_nhds_unique (hc.tendsto.congr' (eventually_nhdsWithin_of_forall heq))
    (hfc u hu).tendsto

end InteractingSLE.Theorem14.GB11Chart
