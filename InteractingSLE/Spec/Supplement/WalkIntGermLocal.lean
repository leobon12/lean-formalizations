/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermImage
import InteractingSLE.Spec.Supplement.WalkIntCanonFamily

/-!
# Local transition intervals give incident domain inclusion

Only a component half-disc must map into the reference chart domain. Real
limits on its diameter suffice for reflection and an image half-disc.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntGerm

/-- Local-domain version of the landed transition reflection lemma. -/
theorem isRealBoundaryConformal_transition_local {c d : Chart}
    (hc : c.IsConformal) (hd : d.IsConformal) {x r : ℝ}
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) r, c.2.1 z ∈ d.dom)
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => d.1 (c.2.1 y)) (𝓝[H] z) (𝓝 v)) :
    R16.IsRealBoundaryConformal (extendFrom H fun y => d.1 (c.2.1 y)) x r := by
  let T : ℂ → ℂ := fun y => d.1 (c.2.1 y)
  have hTd : DifferentiableOn ℂ T (H ∩ ball (x : ℂ) r) :=
    hd.differentiableOn_fwd.comp (hc.1.mono inter_subset_left) hdom
  have hTo : IsOpen (H ∩ ball (x : ℂ) r) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hTi : ∀ z ∈ H ∩ ball (x : ℂ) r,
      Tendsto T (𝓝[H] z) (𝓝 (T z)) := fun z hz =>
    ((hTd z hz).differentiableAt (hTo.mem_nhds hz)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hRT : ∀ z ∈ H ∩ ball (x : ℂ) r, extendFrom H T z = T z :=
    fun z hz => extendFrom_eq (subset_closure hz.1) (hTi z hz)
  have hcl : Hbar ∩ ball (x : ℂ) r ⊆ closure H := fun z hz => by
    rw [closure_H]
    exact hz.1
  refine ⟨hTd.congr (fun z hz => hRT z hz), ?_, ?_, ?_, ?_⟩
  · refine continuousOn_extendFrom hcl fun z hz => ?_
    rcases (show 0 ≤ z.im from hz.1).lt_or_eq with hp | he
    · exact ⟨T z, hTi z ⟨hp, hz.2⟩⟩
    · obtain ⟨v, -, hv⟩ := hlim z hz.2 he.symm
      exact ⟨v, hv⟩
  · intro z hz hz0
    obtain ⟨v, hv0, hv⟩ := hlim z hz hz0
    rw [extendFrom_eq (hcl ⟨hz0.ge, hz⟩) hv]
    exact hv0
  · intro z hz
    rw [hRT z hz]
    exact hd.fwd_mem (hdom z hz)
  · intro z hz w hw he
    rw [hRT z hz, hRT w hw] at he
    apply hc.injOn hz.1 hw.1
    change d.1 (c.2.1 z) = d.1 (c.2.1 w) at he
    rw [← hd.inv_fwd (hdom z hz), ← hd.inv_fwd (hdom w hw), he]

/-- Real transition limits on an interval imply that a full reference
half-disc belongs to the component's incident side. -/
theorem exists_halfdisc_inv_mem_dom {c d : Chart}
    (hc : c.IsConformal) (hd : d.IsConformal) {x r u : ℝ} (hr : 0 < r)
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) r, c.2.1 z ∈ d.dom)
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => d.1 (c.2.1 y)) (𝓝[H] z) (𝓝 v))
    (hu : Tendsto (fun y => d.1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (u : ℂ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ H ∩ ball (u : ℂ) δ, d.2.1 w ∈ c.dom := by
  let T : ℂ → ℂ := fun y => d.1 (c.2.1 y)
  have hTd : DifferentiableOn ℂ T (H ∩ ball (x : ℂ) r) :=
    hd.differentiableOn_fwd.comp (hc.1.mono inter_subset_left) hdom
  have hTo : IsOpen (H ∩ ball (x : ℂ) r) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hRT : ∀ z ∈ H ∩ ball (x : ℂ) r, extendFrom H T z = T z := fun z hz =>
    extendFrom_eq (subset_closure hz.1)
      (((hTd z hz).differentiableAt (hTo.mem_nhds hz)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have hxcl : (x : ℂ) ∈ closure H := by rw [closure_H]; simp [QuantumZipper.Hbar]
  have hbase : extendFrom H T (x : ℂ) = (u : ℂ) := extendFrom_eq hxcl hu
  obtain ⟨δ, hδ, hsub⟩ := exists_halfdisc_subset_image
    (isRealBoundaryConformal_transition_local hc hd hdom hlim) hr
  rw [hbase] at hsub
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  obtain ⟨z, hz, he⟩ := hsub hw
  rw [← he, hRT z hz]
  change d.2.1 (d.1 (c.2.1 z)) ∈ c.dom
  rw [hd.inv_fwd (hdom z hz)]
  exact hc.inv_mem_dom hz.1

end InteractingSLE.Theorem14.WalkIntGerm
