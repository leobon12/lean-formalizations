/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoArc

/-!
# R.6: free witnesses on the shared wall in the seed-opening shapes

PROVE-R6-TWO. The finite inner target is accessible in the seed-opening
outer current domain. When both targets are infinite, the common right
wall tends to infinity in both initial Jordan coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal PocketStopMarked Lemma71C PocketJordan PocketWordAssembly PocketSeedOpen

/-- The actual shared right-wall witness for a seed-opening outer pocket
and a bounded inner pocket, after current-domain inclusion. -/
theorem exists_shared_wall_isFreeAt_twoInf {W : ℝ → ℝ} {η : ℝ → ℂ}
    {R L ML : ℝ≥0 → ℂ} {r s : ℝ≥0} {ψ φ : ℂ → ℂ} {BV : Chart}
    (hcfgC : HOuter.IsOuterCfgInf R L r W η) (hcfgV : HOuter.IsOuterCfg R ML s W η)
    (hJC : IsCfJordanInf R L r ψ) (hJV : IsCfJordan R ML s φ)
    (hVC : cfPocket R ML s ⊆ cfPocket R L r)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = cfPocket R ML s)
    (hBVfwd : EqOn BV.1 φ (cfPocket R ML s))
    {q qV : ℝ≥0} (hqV : (qV : ℝ≥0∞) < capLife (cfTraversal R ML s η φ))
    (hT : pocketFibreInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))
      (clockOf (clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))
        (capInv (cfTraversalInf R L r η ψ) q)) < firstHit η (cfArcR R ML s 0))
    (hIncl : ((BV.loewner (fun t : ℝ => segDriver (cfTraversal R ML s η φ) t.toNNReal) qV).dom : Set ℂ) ⊆
      cfPocket R L r ∩ ψ ⁻¹' (H \ fillH
        (cfTraversalInf R L r η ψ '' Icc 0 (capInv (cfTraversalInf R L r η ψ) q)))) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      HalfPlaneSep.IsFreeAt (cfTraversalInf R L r η ψ '' Icc 0 (capInv (cfTraversalInf R L r η ψ) q))
        (ψ (cfArcR R ML s u)) ∧
      HalfPlaneSep.IsFreeAt (cfTraversal R ML s η φ '' Icc 0 (capInv (cfTraversal R ML s η φ) qV))
        (φ (cfArcR R ML s u)) := by
  let hC := hcfgC.toPocketInf hJC
  let hV := hcfgV.toPocket hJV
  have hP := hcfgV.conf.isCfPocket
    (PocketMarks.zero_notMem_closure_of_rightLo_pos hcfgV.conf hcfgV.bounded)
  have hGc : IsCompact (cfTraversal R ML s η φ '' Icc 0 (capInv (cfTraversal R ML s η φ) qV)) :=
    isCompact_Icc.image_of_continuousOn (hV.driven.continuousOn.mono fun _ hu => hu.1)
  have haV : MapsTo (cfArcR R ML s) (Icc 0 1) (closure (cfPocket R ML s)) := by
    intro u hu
    exact frontier_subset_closure (hP.frontier_eq ▸ Or.inl ⟨u, hu, rfl⟩)
  have hxV := haV ⟨le_rfl, zero_le_one⟩
  exact exists_arc_point_isFreeAt hV.jordan hGc.isClosed hGc.isBounded
    hP.cont₁ hP.inj₁ rfl haV ((hC.jordan.1 _ (closure_mono hVC hxV)).mono (closure_mono hVC))
    (isFreeAt_outerInf_inner_target hC hV hBV hBVdom hBVfwd hqV hT hIncl)

/-- For two infinite targets, any shared arc tending to infinity supplies
a point free in both initial coordinates for bounded relative traces. -/
theorem exists_arc_point_isFreeAt_infinity {C V F G : Set ℂ} {yC yV : ℂ}
    {ψ φ : ℂ → ℂ} {a : ℝ → ℂ}
    (hC : IsJordanCoordInf C yC ψ) (hV : IsJordanCoordInf V yV φ) (hVC : V ⊆ C)
    (hFc : IsClosed F) (hFb : IsBounded F) (hGc : IsClosed G) (hGb : IsBounded G)
    (ha : Tendsto (fun u => ‖a u‖) atTop atTop) (haV : MapsTo a (Ici 0) (closure V)) :
    ∃ u ∈ Ioi (0 : ℝ), HalfPlaneSep.IsFreeAt F (ψ (a u)) ∧
      HalfPlaneSep.IsFreeAt G (φ (a u)) := by
  have haInf : Tendsto a atTop (cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 ha
  have hψlim := hC.2.2.2.2.2.2.comp (tendsto_inf.2 ⟨haInf,
    tendsto_principal.2 ((eventually_ge_atTop (0 : ℝ)).mono fun _ h => closure_mono hVC (haV h))⟩)
  have hφlim := hV.2.2.2.2.2.2.comp (tendsto_inf.2 ⟨haInf,
    tendsto_principal.2 ((eventually_ge_atTop (0 : ℝ)).mono fun _ h => haV h)⟩)
  obtain ⟨u, hu, hFu, hGu⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((eventually_isFreeAt_of_tendsto_norm_atTop hFc hFb
      (tendsto_norm_atTop_iff_cobounded.2 hψlim)).and
      (eventually_isFreeAt_of_tendsto_norm_atTop hGc hGb
        (tendsto_norm_atTop_iff_cobounded.2 hφlim)))).exists
  exact ⟨u, hu, hFu, hGu⟩

/-- An actual unvisited shared-wall point for two seed-opening outer
pockets. The infinite right wall lies beyond both compact relative traces. -/
theorem exists_shared_wall_isFreeAt_twoInfInf {W : ℝ → ℝ} {η : ℝ → ℂ}
    {R L ML : ℝ≥0 → ℂ} {r s : ℝ≥0} {ψ φ : ℂ → ℂ}
    (hcfgC : HOuter.IsOuterCfgInf R L r W η) (hcfgV : HOuter.IsOuterCfgInf R ML s W η)
    (hJC : IsCfJordanInf R L r ψ) (hJV : IsCfJordanInf R ML s φ)
    (hVC : cfPocket R ML s ⊆ cfPocket R L r) (q qV : ℝ≥0) :
    ∃ u ∈ Ioi (0 : ℝ),
      HalfPlaneSep.IsFreeAt (cfTraversalInf R L r η ψ '' Icc 0 (capInv (cfTraversalInf R L r η ψ) q))
        (ψ (cfArcRInf R ML s u)) ∧
      HalfPlaneSep.IsFreeAt (cfTraversalInf R ML s η φ '' Icc 0 (capInv (cfTraversalInf R ML s η φ) qV))
        (φ (cfArcRInf R ML s u)) := by
  let hC := hcfgC.toPocketInf hJC
  let hV := hcfgV.toPocketInf hJV
  have hP := hcfgV.conf.isCfPocketInf hcfgV.seed
  have hFc : IsCompact (cfTraversalInf R L r η ψ '' Icc 0 (capInv (cfTraversalInf R L r η ψ) q)) :=
    isCompact_Icc.image_of_continuousOn (hC.driven.continuousOn.mono fun _ hu => hu.1)
  have hGc : IsCompact (cfTraversalInf R ML s η φ '' Icc 0 (capInv (cfTraversalInf R ML s η φ) qV)) :=
    isCompact_Icc.image_of_continuousOn (hV.driven.continuousOn.mono fun _ hu => hu.1)
  exact exists_arc_point_isFreeAt_infinity hC.jordan hV.jordan hVC
    hFc.isClosed hFc.isBounded hGc.isClosed hGc.isBounded hP.tendsto₁
    (fun u hu => frontier_subset_closure (hP.frontier_eq ▸ Or.inl ⟨u, hu, rfl⟩))

end InteractingSLE.Sec7.R6Two
