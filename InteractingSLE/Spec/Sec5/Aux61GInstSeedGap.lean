/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstExitWindow

/-! # The free seed collar and the old physical boundary -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData
open WangWu (negInv)

def oldModelBoundary (K : Set ℂ) : Set ℂ := sphere (0 : ℂ) 1 ∪ (fun z => -cayley z) '' K

theorem isCompact_oldModelBoundary {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) :
    IsCompact (oldModelBoundary K) :=
  (isCompact_sphere 0 1).union
    (hK.image_of_continuousOn ((continuousOn_cayley_Hbar.mono hKH).neg))

theorem cayley_notMem_oldModelBoundary {K : Set ℂ} (hKH : K ⊆ Hbar) {p : ℂ}
    (hp : p ∈ H \ negInv '' fillH K) : cayley p ∉ oldModelBoundary K := by
  intro hm
  have hd := retainedModelBoundary_disjoint hKH (empty_subset Hbar) p
  apply hd.le_bot
  refine ⟨?_, p, mem_connectedComponentIn ⟨hp, notMem_empty p⟩, rfl⟩
  simpa only [retainedModelBoundary, oldModelBoundary, image_empty, union_empty] using hm

theorem cayley_mem_oldModelBoundary_of_frontier {K : Set ℂ} (hK : IsCompact K) {p : ℂ}
    (hp : p ∈ frontier (H \ negInv '' fillH K)) : cayley p ∈ oldModelBoundary K := by
  rw [WangWu.H_diff_image_negInv] at hp
  have hn := Sec7.PocketJordan.neg_cayley_mem_frontier (isOpen_H_diff_fillH hK.isBounded) sdiff_subset hp
  rcases frontier_cayley_fill_subset hK hn with hS | ⟨k, hk, he⟩
  · exact Or.inl (by simpa [mem_sphere_zero_iff_norm] using hS)
  · exact Or.inr ⟨k, hk, by simpa using congrArg Neg.neg he⟩

/-- The selected start normalization fixes the inverse extension at zero. -/
theorem boundedInverse_zero_of_restartSpec {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) (hT0 : 0 < T x)
    (heq : EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H)
    (hc : ContinuousOn (boundedInverse (c x)) Hbar) :
    boundedInverse (c x) 0 = cayley (ρ x 0) := by
  have htime : {u : ℝ≥0 | (u : ℝ≥0∞) < T x} ∈ 𝓝 (0 : ℝ≥0) :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (by simpa using hT0)
  have hγ : Tendsto (inPath E c ρ T x) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℂ)) := by
    have hh : Tendsto (inPath E c ρ T x) (𝓝[>] (0 : ℝ≥0))
        (𝓝 (inPath E c ρ T x 0)) :=
      ((hs.continuousOn_inPath hx).continuousAt htime).tendsto.mono_left nhdsWithin_le_nhds
    rwa [hs.inPath_zero hx hT0] at hh
  have hγH : ∀ᶠ u in 𝓝[>] (0 : ℝ≥0), inPath E c ρ T x u ∈ H := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds htime] with u hu huT
    rw [hs.inPath_eq_fwd hx hu huT]
    exact (hs.conf x hx).fwd_mem (hs.inside x hx u hu huT)
  have hl := (hc (0 : ℂ) (by change (0 : ℝ) ≤ 0; exact le_rfl)).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hγ, hγH.mono fun _ h => QuantumZipper.H_subset_Hbar h⟩)
  have hbar : ρ x 0 ∈ Hbar := closure_H ▸ closure_mono (hs.conf x hx).dom_subset (hs.start_mem x hx)
  have hr := ((QuantumZipper.CA.differentiableAt_cayley
    (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hbar)).continuousAt.tendsto.comp
      (hs.contρ x hx).continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ≥0)))
  apply tendsto_nhds_unique hl
  refine hr.congr' ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds htime] with u hu huT
  dsimp only [Function.comp_apply]
  rw [hs.inPath_eq_fwd hx hu huT, heq ((hs.conf x hx).fwd_mem (hs.inside x hx u hu huT))]
  dsimp only [Function.comp_apply]
  rw [(hs.conf x hx).inv_fwd (hs.inside x hx u hu huT)]

end InteractingSLE.Sec5.Aux61GInst
