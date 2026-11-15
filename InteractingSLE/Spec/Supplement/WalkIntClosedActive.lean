/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedFamily
import InteractingSLE.Spec.Supplement.WalkIntEnvelopeRetained
import InteractingSLE.Spec.Supplement.WalkIntExtendRetained

/-!
# Active component containment for closed-time retained pairs

The new completed endpoints retain the same physical filling and bounded
support properties. The existing continuation theorem therefore applies
to them. Selecting a later common exit in a bounded component is still
the explicitly named physical tail-separation input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry WalkMean

theorem ClosedPrefix.raw_isBounded {s : ExplState} (R : ClosedPrefix s) :
    Bornology.IsBounded R.raw := by
  apply R.model.isHull.2.1.subset
  intro z hz
  rw [R.filled]
  exact mem_fillH_of_mem_closure (R.raw_subset_H hz) (subset_closure hz)

theorem ClosedPrefix.raw_subset_range {s : ExplState} (R : ClosedPrefix s)
    {α : ℝ≥0 → ℂ} {w : ExplSpec} (hRange : range α = physOf w s) : R.raw ⊆ range α := by
  rw [hRange]
  intro z hz
  exact ((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H w s) z).2 (R.raw_subset hz)).1

/-- The completed prefix models also give the joint proper boundary
extension by the existing filled-union theorem. -/
theorem ClosedPair.hasProperBdryExt {sR sL : ExplState} (J : ClosedPair sR sL) :
    GW1P.HasProperBdryExt J.chart := by
  have hM : J.model.hull = fillH (J.right.model.hull ∪ J.left.model.hull) := by
    rw [J.filled, J.right.filled, J.left.filled]
    exact (WalkIntFill.fillH_union_filled J.right.raw_subset_H J.left.raw_subset_H
      (J.right.filled ▸ J.right.model.isHull)
      (J.left.filled ▸ J.left.model.isHull)).symm
  exact WalkIntExtend.hasProperBdryExt_of_filled_union J.right.model J.left.model J.model
    J.right.normalized.conformal J.left.normalized.conformal J.right.proper J.left.proper
    J.normalized.conformal J.normalized.inverse_bound hM

/-- The unbounded component is active for every actual closed-time pair. -/
theorem active_closedPair_of_unbounded {sR sL : ExplState} (J : ClosedPair sR sL)
    {wR wL : ExplSpec} {C : Set ℂ}
    (hC : C ∈ betweenComponents (physOf wR sR) (physOf wL sL)) (hCo : IsOpen C)
    (hCu : ¬ Bornology.IsBounded C) : C ⊆ H \ fillH J.raw := by
  obtain ⟨z, _, _, _, hCeq⟩ := hC
  have hCp : IsPreconnected C := by rw [hCeq]; exact isPreconnected_connectedComponentIn
  have hCsub : C ⊆ H \ (physOf wR sR ∪ physOf wL sL) := by
    rw [hCeq]
    exact connectedComponentIn_subset _ _
  have hraw : J.raw ⊆ physOf wR sR ∪ physOf wL sL := by
    intro p hp
    rcases J.raw_subset hp with hp | hp
    · exact Or.inl (((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H wR sR) p).2 hp).1)
    · exact Or.inr (((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H wL sL) p).2 hp).1)
  have hdis : Disjoint C J.raw := Set.disjoint_left.2
    (fun p hp hr => (hCsub hp).2 (hraw hr))
  have hdisCl := hdis.closure_right hCo
  exact subset_H_diff_fillH_of_isPreconnected
    (J.right.raw_isBounded.union J.left.raw_isBounded) hCp
    (fun p hp => ⟨(hCsub hp).1, fun hr => Set.disjoint_left.1 hdisCl hp hr⟩) hCu

/-- Named remaining bounded geometry: a positive later common contact
whose two proper tails miss the closed raw prefixes. Enclosing cutoffs
and active component containment are then conclusions. -/
theorem active_closedPair_of_tail_separation {sR sL : ExplState} (J : ClosedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    (hTail : ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
      Disjoint (closure J.right.raw) (α '' Ici s) ∧
      Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure C) :
    C ⊆ H \ fillH J.raw := by
  obtain ⟨s, t, hs, ht, hmeet, hsepR, hsepL, hcl⟩ := hTail
  obtain ⟨a, has, ha⟩ := WalkIntEnvelope.exists_cutoff_before_of_disjoint_tail
    hα J.right.raw_isBounded (J.right.raw_subset_range hR) hs hsepR
  obtain ⟨b, hbt, hb⟩ := WalkIntEnvelope.exists_cutoff_before_of_disjoint_tail
    hβ J.left.raw_isBounded (J.left.raw_subset_range hL) ht hsepL
  exact WalkIntActive.active_of_later_common_contact hα hβ horder hC
    (union_subset_union (subset_closure.trans ha) (subset_closure.trans hb)) has hbt hmeet hcl

end InteractingSLE.Theorem14.WalkIntClosed
