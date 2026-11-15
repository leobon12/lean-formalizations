import InteractingSLE.Spec.Sec5.Aux61RestartFinInherited

/-!
# The canonical representation follows from the actual collar limits

Packet PROVE-AUX61-R1. The physical original-target map is unique up to positive
scale after translating its finite current access to zero. Thus no scale
representation needs to be supplied as an extra geometric hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

/-- The canonical choice of retained mapping-out function has the same finite
current access as the hydrodynamic map constructed by the nested-hull theorem. -/
theorem exists_canonical_access_of_finite_inverse {A B : Set ℂ}
    (hA : IsHPHull A) (hB : IsHPHull B) (hAB : A ⊆ B) {g F : ℂ → ℂ}
    (hg : IsMapOut A g) (hF : IsConformalBijection F H (H \ A)) {z₀ : ℂ}
    (hF₀ : Tendsto F (𝓝[H] 0) (𝓝 z₀))
    (hcollar : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) (H \ B)) :
    ∃ x : ℝ, Tendsto (ConformalImage.mapOut B ∘ F) (𝓝[H] 0) (𝓝 (x : ℂ)) := by
  obtain ⟨ψ, x, hψ, hx⟩ :=
    exists_chart_access_of_finite_inverse hA hB hAB hg hF hF₀ hcollar
  have heq := (ConformalImage.isMapOut_mapOut hB).eqOn hB hψ
  refine ⟨x, (hx.mono_right nhdsWithin_le_nhds).congr' ?_⟩
  exact (eventually_mem_of_collar hcollar).mono fun w hw => (heq hw).symm

/-- The canonical physical chart has finite seed value and infinite norm at
the actual original right target. -/
theorem exists_original_target_canonical_seed
    {D₀ D : Set ℂ} (hD₀o : IsOpen D₀) (hD₀s : IsSimplyConnected D₀)
    (hD₀H : D₀ ⊆ H) (hDo : IsOpen D) (hDs : IsSimplyConnected D)
    (hDD₀ : D ⊆ D₀) {F₀ : ℂ → ℂ}
    (hF₀ : IsConformalBijection F₀ H D₀) {z₀ : ℂ} (hz₀ : z₀ ∈ H)
    (hlim : Tendsto F₀ (𝓝[H] 0) (𝓝 z₀))
    (hcurrent : ∃ δ > 0, MapsTo F₀ (ball 0 δ ∩ H) D)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D) :
    ∃ x : ℝ,
      Tendsto (fun w => ConformalImage.mapOut (stripTargetHull D)
        (stripRightRetarget (F₀ w))) (𝓝[H] 0) (𝓝 (x : ℂ)) ∧
      Tendsto (fun w => ‖ConformalImage.mapOut (stripTargetHull D)
        (stripRightRetarget (w + 1))‖) (𝓝[H] 0) atTop := by
  let A := stripTargetHull D₀
  let B := stripTargetHull D
  have hDH : D ⊆ H := hDD₀.trans hD₀H
  have hA : IsHPHull A := isHPHull_stripTargetHull hD₀o hD₀s hD₀H
    (by obtain ⟨δ, hδ, hf⟩ := htarget; exact ⟨δ, hδ, hf.trans hDD₀⟩)
  have hB : IsHPHull B := isHPHull_stripTargetHull hDo hDs hDH htarget
  have hAB : A ⊆ B := sdiff_subset_sdiff_right (image_mono hDD₀)
  have hR₀ : IsConformalBijection stripRightRetarget D₀ (H \ A) := by
    rw [H_diff_stripTargetHull hD₀H]
    exact ⟨isConformalBijection_stripRightRetarget.1.mono hD₀H,
      (isConformalBijection_stripRightRetarget.2.injOn.mono hD₀H).bijOn_image⟩
  have hR : MapsTo stripRightRetarget D (H \ B) := by
    rw [H_diff_stripTargetHull hDH]
    exact mapsTo_image _ _
  have hRF₀ : Tendsto (stripRightRetarget ∘ F₀) (𝓝[H] 0)
      (𝓝 (stripRightRetarget z₀)) :=
    (isConformalBijection_stripRightRetarget.1.continuousOn.continuousAt
      (QuantumZipper.isOpen_H.mem_nhds hz₀)).tendsto.comp hlim
  have hRFc : ∃ δ > 0, MapsTo (stripRightRetarget ∘ F₀) (ball 0 δ ∩ H) (H \ B) := by
    obtain ⟨δ, hδ, hf⟩ := hcurrent
    exact ⟨δ, hδ, hR.comp hf⟩
  obtain ⟨x, hx⟩ := exists_canonical_access_of_finite_inverse hA hB hAB
    (ConformalImage.isMapOut_mapOut hA) (isConformalBijection_comp hR₀ hF₀) hRF₀ hRFc
  have hplus : Tendsto (fun w : ℂ => w + 1) (𝓝[H] 0) (𝓝[H] 1) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [id_eq, zero_add] using
        ((continuous_id.add_const (1 : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change 0 < (w + 1).im
      simpa only [add_im, one_im, add_zero] using (show 0 < w.im from hw)
  have htc : ∃ δ > 0, MapsTo (fun w : ℂ => w + 1) (ball 0 δ ∩ H) D := by
    obtain ⟨δ, hδ, hf⟩ := htarget
    refine ⟨δ, hδ, fun w hw => hf ⟨?_, ?_⟩⟩
    · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw.1
    · change 0 < (w + 1).im
      simpa only [add_im, one_im, add_zero] using (show 0 < w.im from hw.2)
  have hRt : Tendsto (fun w => stripRightRetarget (w + 1)) (𝓝[H] 0)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ B)) :=
    tendsto_inf.2 ⟨(tendsto_stripRightRetarget_target.comp hplus).mono_right inf_le_left,
      tendsto_principal.2 ((eventually_mem_of_collar htc).mono fun w hw => hR hw)⟩
  have ht := ((ConformalImage.isMapOut_mapOut hB).tendsto_cobounded hB Subset.rfl
    (ConformalImage.isMapOut_mapOut hB).1.2.mapsTo).comp hRt
  exact ⟨x, hx, tendsto_norm_cobounded_atTop.comp (ht.mono_right inf_le_left)⟩

/-- A chart normalized on these actual accesses has the canonical physical
formula, with positive scale and a real seed translation. -/
theorem exists_original_target_chart_scale
    {D₀ D : Set ℂ} (hD₀o : IsOpen D₀) (hD₀s : IsSimplyConnected D₀)
    (hD₀H : D₀ ⊆ H) (hDo : IsOpen D) (hDs : IsSimplyConnected D)
    (hDD₀ : D ⊆ D₀) {F₀ ψ : ℂ → ℂ}
    (hF₀ : IsConformalBijection F₀ H D₀) {z₀ : ℂ} (hz₀ : z₀ ∈ H)
    (hlim : Tendsto F₀ (𝓝[H] 0) (𝓝 z₀))
    (hcurrent : ∃ δ > 0, MapsTo F₀ (ball 0 δ ∩ H) D)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D)
    (hψ : IsConformalBijection ψ D H)
    (hψ₀ : Tendsto (ψ ∘ F₀) (𝓝[H] 0) (𝓝 0))
    (hψ₁ : Tendsto (fun w => ‖ψ (w + 1)‖) (𝓝[H] 0) atTop) :
    ∃ a x : ℝ, 0 < a ∧ EqOn ψ
      (fun z => (a : ℂ) * (ConformalImage.mapOut (stripTargetHull D)
        (stripRightRetarget z) - x)) D := by
  have hDH := hDD₀.trans hD₀H
  have hB := isHPHull_stripTargetHull hDo hDs hDH htarget
  obtain ⟨x, hx, hi⟩ := exists_original_target_canonical_seed
    hD₀o hD₀s hD₀H hDo hDs hDD₀ hF₀ hz₀ hlim hcurrent htarget
  have hR : IsConformalBijection stripRightRetarget D (H \ stripTargetHull D) := by
    rw [H_diff_stripTargetHull hDH]
    exact ⟨isConformalBijection_stripRightRetarget.1.mono hDH,
      (isConformalBijection_stripRightRetarget.2.injOn.mono hDH).bijOn_image⟩
  have ht : IsConformalBijection (fun w : ℂ => w - (x : ℂ)) H H := by
    refine ⟨differentiableOn_id.sub_const _, ?_, ?_, ?_⟩
    · intro w hw
      change 0 < (w - (x : ℂ)).im
      simpa only [sub_im, ofReal_im, sub_zero] using (show 0 < w.im from hw)
    · intro w hw z hz heq
      exact sub_left_inj.mp heq
    · intro w hw
      refine ⟨w + (x : ℂ), ?_, add_sub_cancel_right _ _⟩
      change 0 < (w + (x : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using (show 0 < w.im from hw)
  have hφ := isConformalBijection_comp ht
    (isConformalBijection_comp (ConformalImage.isMapOut_mapOut hB).1 hR)
  have hφ₀ := hx.sub_const (x : ℂ)
  rw [sub_self] at hφ₀
  have hsub : Tendsto (fun t : ℝ => t - ‖(x : ℂ)‖) atTop atTop :=
    le_of_eq (map_sub_atTop_eq _)
  have hφ₁ : Tendsto (fun w => ‖ConformalImage.mapOut (stripTargetHull D)
      (stripRightRetarget (w + 1)) - (x : ℂ)‖) (𝓝[H] 0) atTop :=
    tendsto_atTop_mono (fun w => norm_sub_norm_le _ _) (hsub.comp hi)
  have htc : ∃ δ > 0, MapsTo (fun w : ℂ => w + 1) (ball 0 δ ∩ H) D := by
    obtain ⟨δ, hδ, hf⟩ := htarget
    refine ⟨δ, hδ, fun w hw => hf ⟨?_, ?_⟩⟩
    · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw.1
    · change 0 < (w + 1).im
      simpa only [add_im, one_im, add_zero] using (show 0 < w.im from hw.2)
  obtain ⟨a, ha, heq⟩ := exists_pos_scale_of_same_collar_limits hDo hφ hψ
    hcurrent htc hφ₀ hψ₀ hφ₁ hψ₁
  exact ⟨a, x, ha, heq⟩

end InteractingSLE.Sec5.Aux61Restart
