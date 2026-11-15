import InteractingSLE.Spec.Sec5.Aux61RestartFinAccess
import InteractingSLE.Spec.Sec5.Aux61RestartFinCollar

/-!
# The two actual restart prime ends are distinct

Packet PROVE-AUX61-R1. A free original-target collar gives bounded nested hulls
after right-target retargeting. The current access is finite in their
hydrodynamic chart, while the original right target has infinite chart norm.
Thus the `CollarPrimeEndComparison` hypothesis is proved for these exact maps.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

/-- In the actual original-target coordinate, the retained current collar and
the physical right-target collar have distinct prime-end limits. -/
theorem collarPrimeEndComparison_of_original_target
    {D₀ D : Set ℂ} (hD₀o : IsOpen D₀) (hD₀s : IsSimplyConnected D₀)
    (hD₀H : D₀ ⊆ H) (hDo : IsOpen D) (hDs : IsSimplyConnected D)
    (hDD₀ : D ⊆ D₀) {F₀ : ℂ → ℂ}
    (hF₀ : IsConformalBijection F₀ H D₀) {z₀ : ℂ} (hz₀ : z₀ ∈ H)
    (hlim : Tendsto F₀ (𝓝[H] 0) (𝓝 z₀))
    (hcurrent : ∃ δ > 0, MapsTo F₀ (ball 0 δ ∩ H) D)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D) :
    CollarPrimeEndComparison D F₀ (fun w => w + 1) := by
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
  have hR : IsConformalBijection stripRightRetarget D (H \ B) := by
    rw [H_diff_stripTargetHull hDH]
    exact ⟨isConformalBijection_stripRightRetarget.1.mono hDH,
      (isConformalBijection_stripRightRetarget.2.injOn.mono hDH).bijOn_image⟩
  have hRF := isConformalBijection_comp hR₀ hF₀
  have hRF₀ : Tendsto (stripRightRetarget ∘ F₀) (𝓝[H] 0)
      (𝓝 (stripRightRetarget z₀)) :=
    (isConformalBijection_stripRightRetarget.1.continuousOn.continuousAt
      (QuantumZipper.isOpen_H.mem_nhds hz₀)).tendsto.comp hlim
  have hRFc : ∃ δ > 0, MapsTo (stripRightRetarget ∘ F₀) (ball 0 δ ∩ H) (H \ B) := by
    obtain ⟨δ, hδ, hf⟩ := hcurrent
    exact ⟨δ, hδ, hR.2.mapsTo.comp hf⟩
  obtain ⟨g, hg⟩ := hA.exists_isMapOut
  obtain ⟨ψ, x, hψ, hx⟩ :=
    exists_chart_access_of_finite_inverse hA hB hAB hg hRF hRF₀ hRFc
  let φ : HChart D := ⟨ψ.1 ∘ stripRightRetarget, isConformalBijection_comp ψ.2 hR⟩
  have hplus : Tendsto (fun w : ℂ => w + 1) (𝓝[H] 0) (𝓝[H] 1) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [id_eq, zero_add] using
        ((continuous_id.add_const (1 : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change 0 < (w + 1).im
      simpa only [add_im, one_im, add_zero] using (show 0 < w.im from hw)
  have htargetD : ∀ᶠ w in 𝓝[H] 0, w + 1 ∈ D := by
    obtain ⟨δ, hδ, hf⟩ := htarget
    filter_upwards [hplus.eventually
      (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (1 : ℂ) hδ)),
      self_mem_nhdsWithin] with w hw hwH
    exact hf ⟨hw, by
      change 0 < (w + 1).im
      simpa only [add_im, one_im, add_zero] using (show 0 < w.im from hwH)⟩
  have hRt : Tendsto (fun w => stripRightRetarget (w + 1)) (𝓝[H] 0)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ B)) := by
    exact tendsto_inf.2 ⟨(tendsto_stripRightRetarget_target.comp hplus).mono_right inf_le_left,
      tendsto_principal.2 (htargetD.mono fun w hw => hR.2.mapsTo hw)⟩
  have ht := (hψ.tendsto_cobounded hB Subset.rfl ψ.mapsTo).comp hRt
  refine ⟨φ, (x : OnePoint ℝ), OnePoint.infty, OnePoint.coe_ne_infty x, ?_, ?_⟩
  · exact hx
  · exact ht

end InteractingSLE.Sec5.Aux61Restart
