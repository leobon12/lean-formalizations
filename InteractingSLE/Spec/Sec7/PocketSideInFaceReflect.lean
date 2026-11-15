/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFaceGeometry
import InteractingSLE.Spec.Sec7.PocketStopSideLimR6

/-!
# R.6: reflection on the actual shared current face

PROVE-POCKET-SIDEIN. A finite continuous boundary extension of the current
chart has real values at a real boundary access: an interior image would,
by continuity of the inverse, place that real point inside the domain.
Shared half-disc collars then give exactly R16's reflection hypotheses.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A finite chart extension at an accessible real boundary point is real.
Real-valued boundary data need not be assumed in the extension input. -/
theorem chart_extension_im_eq_zero {c : Chart} (hc : c.IsConformal)
    {G : ℂ → ℂ} (heq : EqOn G c.1 c.dom) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (c.dom : Set ℂ))
    (hG : ContinuousWithinAt G c.dom (x : ℂ)) : (G x).im = 0 := by
  have : NeBot (𝓝[(c.dom : Set ℂ)] (x : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.1 hx
  have hGH : ∀ᶠ z in 𝓝[(c.dom : Set ℂ)] (x : ℂ), G z ∈ H :=
    eventually_nhdsWithin_of_forall fun z hz => heq hz ▸ hc.fwd_mem hz
  have hbar : G x ∈ Hbar := QuantumZipper.isClosed_Hbar.mem_of_tendsto hG.tendsto
    (hGH.mono fun _ hz => QuantumZipper.H_subset_Hbar hz)
  have hnot : G x ∉ H := by
    intro hpos
    have hi := (hc.1.continuousOn.continuousAt
      (QuantumZipper.isOpen_H.mem_nhds hpos)).tendsto.comp hG.tendsto
    have hevent : (fun z => c.2.1 (G z)) =ᶠ[𝓝[(c.dom : Set ℂ)] (x : ℂ)] id :=
      eventually_nhdsWithin_of_forall fun z hz => by
        change c.2.1 (G z) = z
        rw [heq hz, hc.inv_fwd hz]
    have hlim : Tendsto (fun z => c.2.1 (G z))
        (𝓝[(c.dom : Set ℂ)] (x : ℂ)) (𝓝 (x : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.congr' hevent.symm
    have hsame := tendsto_nhds_unique hi hlim
    have hxinH := hc.2.1 hpos
    rw [hsame] at hxinH
    change 0 < (x : ℂ).im at hxinH
    simp at hxinH
  exact le_antisymm (le_of_not_gt hnot) hbar

/-- Shared current half-discs and a finite continuous chart extension give
the exact local conformal boundary condition used by R.6. Positive reflected
derivative is then a theorem of R16, not a geometric hypothesis. -/
theorem realBoundaryConformal_of_shared_face {c : Chart} (hc : c.IsConformal)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ (c.dom : Set ℂ))
    {G : ℂ → ℂ}
    (hBoundaryExtension : ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J))
    (hExtensionEq : EqOn G c.1 c.dom) :
    ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  have hreal : ∀ x ∈ J, (G x).im = 0 := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact mem_Hbar_of_im_eq_zero (by simp)
    apply chart_extension_im_eq_zero hc hExtensionEq
      (closure_mono hsub (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩))
    exact (hBoundaryExtension _ (Or.inr (mem_image_of_mem _ hx))).mono subset_union_left
  intro x hx
  obtain ⟨r, hr, hsub⟩ := hCollars x hx
  obtain ⟨ε, hε, hεJ⟩ := Metric.isOpen_iff.1 hJo x hx
  let d := min r ε
  have hd : 0 < d := lt_min hr hε
  have hhalf : H ∩ ball (x : ℂ) d ⊆ (c.dom : Set ℂ) := fun z hz =>
    hsub ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  have hbase : ∀ z ∈ ball (x : ℂ) d, z.im = 0 → z.re ∈ J := by
    intro z hz hz0
    have hzr : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
    apply hεJ
    rw [mem_ball, ← Complex.isometry_ofReal.dist_eq, hzr]
    exact lt_of_lt_of_le hz (min_le_right _ _)
  refine ⟨d, hd, (hc.differentiableOn_fwd.mono hhalf).congr
    (fun z hz => hExtensionEq (hhalf hz)), ?_, ?_, ?_, ?_⟩
  · apply hBoundaryExtension.mono
    intro z hz
    rcases (show 0 ≤ z.im from hz.1).lt_or_eq with hpos | hzero
    · exact Or.inl (hhalf ⟨hpos, hz.2⟩)
    · exact Or.inr ⟨z.re, hbase z hz.2 hzero.symm, by
        apply Complex.ext <;> simp [hzero.symm]⟩
  · intro z hz hz0
    have hzre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
    simpa only [hzre] using hreal z.re (hbase z hz hz0)
  · intro z hz
    rw [hExtensionEq (hhalf hz)]
    exact hc.fwd_mem (hhalf hz)
  · intro z hz w hw he
    rw [hExtensionEq (hhalf hz), hExtensionEq (hhalf hw)] at he
    rw [← hc.inv_fwd (hhalf hz), ← hc.inv_fwd (hhalf hw), he]

end InteractingSLE.Sec7.PocketStopSide
