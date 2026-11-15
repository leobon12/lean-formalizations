/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutCollarGeom

/-!
# The relative component frontier lies on the ambient prefix

The erasure argument giving ambient hull membership also gives membership
in the ambient range at the left fibre end. This locates the frontier
without identifying the relative component with the entire ambient domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open Sec6 PocketTraversal Lemma71C PocketStopMarked PocketStopMarked.Outer
  PocketStopWallsFin PocketUnionPt

section Bounded

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- A pocket point on the relative prefix occurs on the ambient prefix ending
at the left stop, including when the erasure fibre is nontrivial. -/
theorem mem_trace_of_mem_trav_prefix (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    {q : ℝ} {y : ℂ} (hyC : y ∈ C)
    (hy : ψ y ∈ trav η C τ σ ψ '' Icc 0 (capInv (trav η C τ σ ψ) q)) :
    y ∈ η '' Icc 0 (ambTime0 η C τ σ ψ q) := by
  rw [image_relCurve_Icc _ hP.erase.clock_σ_pos (capInv_nonneg _ _)] at hy
  set u := clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q)
  have hu : u ∈ Ico 0 (pocketClock η C τ σ σ) :=
    clockOf_mem_Ico hP.erase.clock_σ_pos (capInv_nonneg _ _)
  obtain ⟨v, hv, hvy⟩ := hy
  have hvI : v ∈ Ico 0 (pocketClock η C τ σ σ) := ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hyx : y ∈ closure C \ {x₀} :=
    ⟨subset_closure hyC, fun h => hP.erase.notMem_x (h ▸ hyC)⟩
  have he : erasedPath η C τ σ v = y := hP.jordan.2.1 (hP.erase.erasedPath_mem hvI) hyx hvy
  have hmem : y ∈ erasedPath η C τ σ '' Icc 0 u ∩ C := ⟨⟨v, hv, he⟩, hyC⟩
  rw [hP.erase.erasedPath_image_inter ⟨hu.1, hu.2.le⟩] at hmem
  obtain ⟨⟨t, ht, rfl⟩, htC⟩ := hmem
  refine ⟨t, ⟨ht.1, ?_⟩, rfl⟩
  by_contra hlt
  exact HOuter.notMem_of_mem_Ioc_fibre' hP.erase hu ⟨not_le.1 hlt, ht.2⟩ htC

/-- Inside the pocket, the current relative frontier is on the ambient trace
before the left stop. -/
theorem frontier_relDomain_subset_trace (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (trav η C τ σ ψ)) :
    frontier (H \ HOuter.relHull C ψ (trav η C τ σ ψ) q) ∩ C ⊆
      η '' Icc 0 (ambTime0 η C τ σ ψ q) := by
  have hψc : ContinuousOn ψ C := hP.jordan.1.mono fun y hy =>
    ⟨subset_closure hy, fun h => hP.erase.notMem_x (h ▸ hy)⟩
  have hcompact := isCompact_Icc.image_of_continuousOn
    (hP.driven.continuousOn.mono (show Icc 0 (capInv (trav η C τ σ ψ) q) ⊆ Ici 0 from
      Icc_subset_Ici_self))
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav η C τ σ ψ) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  rw [HOuter.H_diff_relHull hP.subset_H,
    hP.driven.fwdHull_segDriver q.coe_nonneg hq']
  rintro y ⟨hyfr, hyC⟩
  have hy := mem_frontier_of_mem_frontier_inter_preimage hP.erase.isOpen hψc
    (isOpen_H_diff_fillH hcompact.isBounded) hyC hyfr
  have hytrace : ψ y ∈ trav η C τ σ ψ '' Icc 0 (capInv (trav η C τ σ ψ) q) := by
    rcases frontier_H_diff_fillH_subset hcompact.isBounded hy with hyreal | hytrace
    · exact False.elim ((ne_of_gt (hP.jordan.2.2.2.1.2.mapsTo hyC)) hyreal)
    · rwa [hcompact.isClosed.closure_eq] at hytrace
  exact mem_trace_of_mem_trav_prefix hP hyC hytrace

end Bounded

section Inf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- The ambient prefix range statement for a seed-opening erasure pocket. -/
theorem mem_trace_of_mem_travInf_prefix (hP : IsOuterPocketInf W η C y₀ τ ψ)
    {q : ℝ} {y : ℂ} (hyC : y ∈ C)
    (hy : ψ y ∈ travInf η C τ ψ '' Icc 0 (capInv (travInf η C τ ψ) q)) :
    y ∈ η '' Icc 0 (ambTime0Inf η C τ ψ q) := by
  rw [image_relCurve_Icc _ hP.erase.clockEnd_pos (capInv_nonneg _ _)] at hy
  set u := clockOf (clockEnd η C τ) (capInv (travInf η C τ ψ) q)
  have hu : u ∈ Ico 0 (clockEnd η C τ) :=
    clockOf_mem_Ico hP.erase.clockEnd_pos (capInv_nonneg _ _)
  obtain ⟨v, hv, hvy⟩ := hy
  have hvI : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv.1, hv.2.trans_lt hu.2⟩
  have he : erasedPathInf η C τ v = y :=
    hP.jordan.2.1 (hP.erase.erasedPath_mem hvI) (subset_closure hyC) hvy
  have hmem : y ∈ erasedPathInf η C τ '' Icc 0 u ∩ C := ⟨⟨v, hv, he⟩, hyC⟩
  rw [hP.erase.erasedPath_image_inter hu] at hmem
  obtain ⟨⟨t, ht, rfl⟩, htC⟩ := hmem
  refine ⟨t, ⟨ht.1, ?_⟩, rfl⟩
  by_contra hlt
  exact HOuter.notMem_of_mem_Ioc_fibreInf' hP.erase hu ⟨not_le.1 hlt, ht.2⟩ htC

/-- The current relative frontier inside a seed-opening pocket is on the
ambient prefix at the left stop. -/
theorem frontier_relDomainInf_subset_trace (hP : IsOuterPocketInf W η C y₀ τ ψ)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travInf η C τ ψ)) :
    frontier (H \ HOuter.relHull C ψ (travInf η C τ ψ) q) ∩ C ⊆
      η '' Icc 0 (ambTime0Inf η C τ ψ q) := by
  have hψc : ContinuousOn ψ C := hP.jordan.1.mono subset_closure
  have hcompact := isCompact_Icc.image_of_continuousOn
    (hP.driven.continuousOn.mono (show Icc 0 (capInv (travInf η C τ ψ) q) ⊆ Ici 0 from
      Icc_subset_Ici_self))
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf η C τ ψ) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  rw [HOuter.H_diff_relHull hP.subset_H,
    hP.driven.fwdHull_segDriver q.coe_nonneg hq']
  rintro y ⟨hyfr, hyC⟩
  have hy := mem_frontier_of_mem_frontier_inter_preimage hP.erase.isOpen hψc
    (isOpen_H_diff_fillH hcompact.isBounded) hyC hyfr
  have hytrace : ψ y ∈ travInf η C τ ψ '' Icc 0 (capInv (travInf η C τ ψ) q) := by
    rcases frontier_H_diff_fillH_subset hcompact.isBounded hy with hyreal | hytrace
    · exact False.elim ((ne_of_gt (hP.jordan.2.2.2.1.2.mapsTo hyC)) hyreal)
    · rwa [hcompact.isClosed.closure_eq] at hytrace
  exact mem_trace_of_mem_travInf_prefix hP hyC hytrace

end Inf

end InteractingSLE.Sec7.R5Out
