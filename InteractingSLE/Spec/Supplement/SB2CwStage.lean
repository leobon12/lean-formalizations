/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwChain
import InteractingSLE.Spec.Supplement.SB2NqChain
import InteractingSLE.Spec.Supplement.SBLuChart

/-!
# B's stage chart against the retained union (deterministic)

Packet PROVE-SB2-CANON, round 4 ((P4)). The three stage-chart inputs of `chainFor_canon`, for B's stage chart `cℓ`, a
domain chart of `ℍ ∖ fill B` (`B` B's prefix, inside the retained union `Y`), B's stage trace `β'` and physical piece
`p = bdVal cℓ ∘ β'`:

* **`mem_diff_of_notMem_fillH_stageRetained`** (`hcℓ`): the inverse chart maps the unfilled stage complement into
  `ℍ ∖ fill Y`;
* **`mem_joint_of_mem_fillH_stage`** (`hin`): B's stage hull reads into the joint fill `fill (Y ∪ p[0, s])`: the
unbounded
  component of `ℍ ∖ closure (Y ∪ p[0, s])` around a point `x` maps under `cℓ` to an unbounded preconnected set off
  `β'[0, s]` containing `cℓ x` (the chart moves points by a bounded amount);
* **`piece_of_mem_diff`** (`hpiece`): a physical point of the piece off `fill Y` in `ℍ` is the inverse image of the
stage
  point, which is in `ℍ` (boundary values at real points land on `closure B` or `ℝ`, `Nq.lim_mem_closure_or_real`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Cz

variable {cℓ : Chart} {B Y : Set ℂ}

/-- **`hcℓ`**: the inverse stage chart maps the unfilled stage complement into `ℍ ∖ fill Y`. -/
theorem mem_diff_of_notMem_fillH_stageRetained (hc : cℓ.IsConformal) {z : ℂ}
    (hz : z ∈ H \ fillH (Mn.stageRetained cℓ Y)) : cℓ.2.1 z ∈ H \ fillH Y := by
  refine ⟨hc.2.1 hz.1, fun hY => hz.2 ?_⟩
  exact Qx.self_inter_H_subset_fillH _ ⟨⟨hz.1, hY⟩, hz.1⟩

/-- **`hin`**: B's stage hull reads into the joint fill of the retained union and B's physical piece. -/
theorem mem_joint_of_mem_fillH_stage (hD : IsDomainChart (H \ fillH B) cℓ) {M : ℝ}
    (hM : ∀ v ∈ H, ‖cℓ.2.1 v - v‖ ≤ M) (hBY : B ⊆ Y) {p β' : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hβc : ContinuousOn β' (Icc 0 s)) (hpβ : ∀ r ≤ s, β' r ∈ H → p r = cℓ.2.1 (β' r)) {z : ℂ}
    (hz : z ∈ fillH (β' '' Icc 0 s)) : cℓ.2.1 z ∈ fillH (Y ∪ p '' Icc 0 s) := by
  have hzH : z ∈ H := hz.1
  set x := cℓ.2.1 z with hxdef
  have hxD : x ∈ H \ fillH B := hD.inv_mem hzH
  by_contra hxJ
  set J := Y ∪ p '' Icc 0 s with hJ
  have hxcl : x ∉ closure J := fun h => hxJ ⟨hxD.1, Or.inl h⟩
  set C := connectedComponentIn (H \ closure J) x with hCdef
  have hxC : x ∈ C := mem_connectedComponentIn ⟨hxD.1, hxcl⟩
  have hCsub : C ⊆ H \ closure J := connectedComponentIn_subset _ _
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCub : ¬ IsBounded C := fun hb => hxJ ⟨hxD.1, Or.inr hb⟩
  -- the component avoids `fill B`, so it lies in the chart's domain
  have hCD : C ⊆ H \ fillH B := by
    intro w hw
    have hwJ := hCsub hw
    refine ⟨hwJ.1, ?_⟩
    have hsub : C ⊆ H \ closure B := fun v hv =>
      ⟨(hCsub hv).1, fun h => (hCsub hv).2 (closure_mono (subset_union_left.trans (union_subset_union_left _ hBY)) h)⟩
    exact FinRel.notMem_fillH_of_isPreconnected hw hCpre hsub hCub
  -- its chart image
  set S := cℓ.1 '' C with hSdef
  have hfc : ContinuousOn cℓ.1 (H \ fillH B) := hD.differentiableOn_fwd.continuousOn
  have hSpre : IsPreconnected S := hCpre.image _ (hfc.mono hCD)
  have hzS : z ∈ S := ⟨x, hxC, hD.fwd_inv hzH⟩
  have hSH : S ⊆ H \ closure (β' '' Icc 0 s) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwD := hCD hw
    refine ⟨hD.fwd_mem hwD, fun hcl => ?_⟩
    have hcomp : IsCompact (β' '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hβc
    rw [hcomp.isClosed.closure_eq] at hcl
    obtain ⟨r, hr, hrw⟩ := hcl
    have hrH : β' r ∈ H := by rw [hrw]; exact hD.fwd_mem hwD
    have hpr : p r = w := by rw [hpβ r hr.2 hrH, hrw, hD.inv_fwd hwD]
    exact (hCsub hw).2 (subset_closure (Or.inr ⟨r, hr, hpr⟩))
  have hSub : ¬ IsBounded S := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    refine hCub ((isBounded_closedBall (x := (0 : ℂ)) (r := R + |M|)).subset fun w hw => ?_)
    have hwD := hCD hw
    have h1 := hR ⟨w, hw, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h1 ⊢
    have h2 := hM _ (hD.fwd_mem hwD)
    rw [hD.inv_fwd hwD] at h2
    calc ‖w‖ = ‖cℓ.1 w - (cℓ.1 w - w)‖ := by ring_nf
      _ ≤ ‖cℓ.1 w‖ + ‖cℓ.1 w - w‖ := norm_sub_le _ _
      _ ≤ R + |M| := by
        have : ‖cℓ.1 w - w‖ = ‖w - cℓ.1 w‖ := norm_sub_rev _ _
        rw [this]; linarith [le_abs_self M]
  exact FinRel.notMem_fillH_of_isPreconnected hzS hSpre hSH hSub hz

/-- **`hpiece`**: a physical point of the piece off `fill Y` in `ℍ` is the inverse image of its stage point, which is in
`ℍ`. -/
theorem piece_of_mem_diff (hD : IsDomainChart (H \ fillH B) cℓ) (hBY : B ⊆ Y) (hYc : IsClosed Y)
    (hbl : ∀ x : ℝ, ∃ y : ℂ, Tendsto cℓ.2.1 (𝓝[H] (x : ℂ)) (𝓝 y)) {w : ℂ} (hw0 : 0 ≤ w.im)
    (hp : LuM.bdVal cℓ w ∈ H \ fillH Y) : w ∈ H ∧ cℓ.2.1 w = LuM.bdVal cℓ w := by
  have hcH : ContinuousOn cℓ.2.1 H := hD.isConformal.1.continuousOn
  by_cases hwH : w ∈ H
  · exact ⟨hwH, (LuM.bdVal_eq_of_mem_H hcH hwH).symm⟩
  · exfalso
    have hw0' : w.im = 0 := le_antisymm (not_lt.1 hwH) hw0
    obtain ⟨y, hy⟩ := hbl w.re
    have hwre : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hw0'])
    rw [hwre] at hy
    have hb := LuM.bdVal_eq_of_tendsto hw0 hy
    have hmem := Nq.lim_mem_closure_or_real hD (x := w.re) (by rw [hwre]; exact hy)
    rw [← hb] at hmem
    rcases hmem with hcl | hre
    · exact hp.2 (Qx.self_inter_H_subset_fillH Y ⟨hYc.closure_subset_iff.2 hBY hcl, hp.1⟩)
    · exact (show (LuM.bdVal cℓ w).im ≠ 0 from ne_of_gt hp.1) hre

end InteractingSLE.Theorem14.SB.Cz
