/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveNeighborhood
import InteractingSLE.Spec.ZhanGT4.CollarBoundary

/-!
# Surviving real coordinates and physical current neighborhoods

PROVE-POCKET-SIDEIN. Reuse the existing no-swallowing neighborhood and
forward boundary limit of a real solution. These give local survival in
the physical initial pocket and identify the initial inverse landing from
the already constructed current inverse landing.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The physical current domain is the initial inverse image of the own
active half-plane. This is the existing inverse-image formula specialized
to a frozen own Loewner stage. -/
theorem dom_own_stage_as_initial_inverse_image {B : Chart} (hB : B.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    ((B.loewner W T).dom : Set ℂ) = B.2.1 '' (H \ fwdHull W T) := by
  rw [(hB.loewner hW hW0 hT).coe_dom]
  change (B.2.1 ∘ fwdMapInv W T) '' H = _
  rw [image_comp, QuantumZipper.RS.image_fwdMapInv_H hW hW0 hT]

/-- A surviving original real coordinate leaves a whole relative
neighborhood of the initial physical pocket in the current domain. -/
theorem eventually_mem_own_stage_of_surviving_approach {B : Chart} (hB : B.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T x : ℝ} (hT : 0 ≤ T)
    {a : ℝ → ℂ} (hSurvives : QuantumZipper.IsForwardSol W x T a) {p : ℂ}
    (hInitial : Tendsto B.1 (𝓝[(B.dom : Set ℂ)] p) (𝓝[H] (x : ℂ))) :
    ∀ᶠ z in 𝓝[(B.dom : Set ℂ)] p, z ∈ ((B.loewner W T).dom : Set ℂ) := by
  filter_upwards [self_mem_nhdsWithin,
    hInitial.eventually (ZhanGT4.eventually_not_mem_fwdHull hW hT hSurvives)] with z hz hzOwn
  rw [dom_own_stage_as_initial_inverse_image hB hW hW0 hT]
  exact ⟨B.1 z, hzOwn, hB.inv_fwd hz⟩

/-- The own current forward chart has the inherited real image as its
limit along the whole initial physical pocket. -/
theorem tendsto_own_stage_of_surviving_approach {B : Chart}
    {W : ℝ → ℝ} (hW : Continuous W) {T x : ℝ} (hT : 0 ≤ T)
    {a : ℝ → ℂ} (hSurvives : QuantumZipper.IsForwardSol W x T a) {p : ℂ}
    (hInitial : Tendsto B.1 (𝓝[(B.dom : Set ℂ)] p) (𝓝[H] (x : ℂ))) :
    Tendsto (B.loewner W T).1 (𝓝[(B.dom : Set ℂ)] p) (𝓝 ((a T).re : ℂ)) := by
  have hReal : a T = ((a T).re : ℂ) := Complex.ext rfl
    (by simpa using im_eq_zero_of_isForwardSol_real hW hSurvives ⟨hT, le_rfl⟩)
  have hlim := (tendsto_fwdMap_of_isForwardSol hW hT hSurvives).comp hInitial
  rw [hReal] at hlim
  exact hlim

/-- A finite current landing at a surviving real image is the initial
inverse landing at the same surviving original coordinate. -/
theorem initial_inverse_landing_of_surviving_current {B : Chart}
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T x : ℝ} (hT : 0 ≤ T)
    {a : ℝ → ℂ} (hSurvives : QuantumZipper.IsForwardSol W x T a) {p : ℂ}
    (hCurrent : Tendsto (B.loewner W T).2.1 (𝓝[H] ((a T).re : ℂ)) (𝓝 p)) :
    Tendsto B.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) := by
  have hReal : a T = ((a T).re : ℂ) := Complex.ext rfl
    (by simpa using im_eq_zero_of_isForwardSol_real hW hSurvives ⟨hT, le_rfl⟩)
  have hAlive := ZhanGT4.eventually_not_mem_fwdHull hW hT hSurvives
  have hFwd : Tendsto (fwdMap W T) (𝓝[H] (x : ℂ)) (𝓝[H] ((a T).re : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hlim := tendsto_fwdMap_of_isForwardSol hW hT hSurvives
      rw [hReal] at hlim
      exact hlim
    · exact hAlive.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT hz
  refine (hCurrent.comp hFwd).congr' ?_
  filter_upwards [hAlive] with z hz
  change B.2.1 (fwdMapInv W T (fwdMap W T z)) = B.2.1 z
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT hz]

end InteractingSLE.Sec7.PocketStopSide
