/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcLift
import InteractingSLE.Spec.Sec7.SideHeightLift
import InteractingSLE.Spec.Sec7.PocketSideInFiniteBound
import InteractingSLE.Spec.Sec7.PocketSideInSurviveLoewner

/-!
# Zero inherited lift difference for two stops of one pocket traversal

PROVE-SIDE-COLLAR2 continuation. An old inverse half-disc surviving in the
current domain excludes the actual own increment in that coordinate.
Aux. 57 then gives zero for the inherited lift difference. Both charts use
the same base chart and the same Loewner driver; its canonical normalization
removes the lattice ambiguity without a separately chosen branch.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Later own Loewner stages have smaller physical domains. -/
theorem own_stage_dom_antitone {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ((c.loewner W t).dom : Set ℂ) ⊆ (c.loewner W s).dom := by
  rw [dom_own_stage_as_initial_inverse_image hc hW hW0 (hs.trans hst),
    dom_own_stage_as_initial_inverse_image hc hW hW0 hs]
  exact image_mono (sdiff_subset_sdiff_right (QuantumZipper.fwdHull_mono.1 hst))

/-- A surviving inverse half-disc avoids the actual increment hull in the
old centered coordinate. No whole physical ball is asserted to be unfilled. -/
theorem disjoint_own_increment_of_inverse_halfDisc {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s t x r : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hCollar : (c.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((c.loewner W t).dom : Set ℂ)) :
    Disjoint (ball (x : ℂ) r) (fwdMap W s '' (fwdHull W t \ fwdHull W s)) := by
  refine disjoint_left.2 ?_
  rintro y hy ⟨z, hz, rfl⟩
  have hzH := QuantumZipper.fwdHull_mono.2 t hz.1
  have hzOld : z ∈ H \ fwdHull W s := ⟨hzH, hz.2⟩
  have hyH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hzOld
  have hp := hCollar (mem_image_of_mem _ ⟨hyH, hy⟩)
  have hActive := (initial_coordinate_of_current_mem hc hW hW0 ht hp).2
  change c.1 (c.2.1 (fwdMapInv W s (fwdMap W s z))) ∈ H \ fwdHull W t at hActive
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs hzOld, hc.2.2 z hzH] at hActive
  exact hActive.2 hz.1

/-- The actual inherited lift difference tends to ZERO on a surviving old
incident half-disc for two own stops. The base lift cancels and Aux. 57
compares the two canonical hydrodynamic logarithms along the current inverse. -/
theorem tendsto_own_stage_lift_sub_zero {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s t x ξ r : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hr : 0 < r)
    (hCollar : (c.loewner W s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((c.loewner W t).dom : Set ℂ))
    (hTransition : Tendsto (fun z => (c.loewner W s).1 ((c.loewner W t).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) :
    Tendsto (fun z => (c.loewner W t).2.2 ((c.loewner W t).2.1 z) -
      (c.loewner W s).2.2 ((c.loewner W t).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have ht := hs.trans hst
  let f : ℂ → ℂ := fun z => c.1 ((c.loewner W t).2.1 z)
  let F : Filter ℂ := Filter.map f (𝓝[H] (ξ : ℂ))
  have hCurrent := hc.loewner hW hW0 ht
  have hActive : ∀ z ∈ H, f z ∈ H \ fwdHull W t := fun z hz =>
    (initial_coordinate_of_current_mem hc hW hW0 ht (hCurrent.inv_mem_dom hz)).2
  have hF : F ≤ 𝓟 (H \ fwdHull W t) :=
    le_principal_iff.2 (eventually_nhdsWithin_of_forall hActive)
  have hg := isMapOut_fwdMap hW hW0 hs
  change Tendsto (fun z => fwdMap W s (f z))
    (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) at hTransition
  have hMap : Tendsto (fun z => fwdMap W s z + W s) F
      (𝓝[H] ((x + W s : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · apply tendsto_map'_iff.2
      simpa only [ofReal_add, Function.comp_def] using hTransition.add_const (W s : ℂ)
    · filter_upwards [hF (mem_principal_self _)] with z hz
      exact hg.1.2.mapsTo ⟨hz.1, fun h => hz.2 (QuantumZipper.fwdHull_mono.1 hst h)⟩
  have hClear := disjoint_own_increment_of_inverse_halfDisc hc hW hW0 hs ht hCollar
  have hClear' : Disjoint (ball ((x + W s : ℝ) : ℂ) r)
      ((fun z => fwdMap W s z + W s) '' (fwdHull W t \ fwdHull W s)) := by
    refine disjoint_left.2 ?_
    rintro y hy ⟨z, hz, rfl⟩
    exact disjoint_left.1 hClear (by
      simpa only [mem_ball, ofReal_add, dist_add_right] using hy) (mem_image_of_mem _ hz)
  have hLim := ReverseArc.tendsto_im_sub_of_le (isHPHull_fwdHull hW hs)
    (isHPHull_fwdHull hW ht) (QuantumZipper.fwdHull_mono.1 hst) hg
    (isMapOut_fwdMap hW hW0 ht) (SideHeight.isCanonicalDerivLog_fwdMap hW hW0 hs)
    (SideHeight.isCanonicalDerivLog_fwdMap hW hW0 ht) hF hr hClear' hMap
  have hPull := tendsto_map'_iff.1 hLim
  refine hPull.congr fun z => ?_
  change (logDerivFwd W t (f z)).im - (logDerivFwd W s (f z)).im =
    ((logDerivFwd W t (f z)).im + c.2.2 ((c.loewner W t).2.1 z)) -
      ((logDerivFwd W s (f z)).im + c.2.2 ((c.loewner W t).2.1 z))
  ring

end InteractingSLE.Sec7.PocketStopSide
