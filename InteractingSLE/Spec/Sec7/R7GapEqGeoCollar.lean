/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinOuter

/-!
# Outer collars from a compactified incoming arm

PROVE-R7-GAPEQ. Omitted tails of the full disc crosscut are compact. A neighborhood of an
interior clipped point misses those tails, so the exterior side of the full arm has local
frontier in the closed pocket. This uses the arm's own exterior side, which global side order
places inside the certified forbidden side; no certified-frontier segment assumption is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GapEqGeo

open WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEq R7GapEqFin

/-- A local frontier bound in the counterflow chart from a clipped disc crosscut. Compact
omitted tails also cover a clip whose closing endpoint is the original flow target. -/
theorem local_frontier_of_disc_clip {α : ℝ → ℂ} {C F : Set ℂ} {a b t : ℝ} {p : ℂ}
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (ha : 0 ≤ a) (hb : b ≤ 1) (ht : t ∈ Ioo a b)
    (hp : -cayley p = α t) (hpH : p ∈ H)
    (hfr : ∀ z ∈ frontier F, z ∈ H → -cayley z ∈ α '' Icc 0 1)
    (hseg : cfPt '' (α '' Ioo a b) ⊆ closure C) :
    ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C := by
  let T := α '' (Icc (0 : ℝ) 1 ∩ (Ioo a b)ᶜ)
  have hTc : IsClosed T := (isCompact_Icc.inter_right isOpen_Ioo.isClosed_compl).image_of_continuousOn
    (hαc.mono inter_subset_left) |>.isClosed
  have hpT : -cayley p ∉ T := by
    rintro ⟨s, hs, he⟩
    have hst := hαi hs.1 ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩ (he.trans hp)
    exact hs.2 (hst ▸ ht)
  have hc := (continuousAt_neg_cayley (H_subset_Hbar hpH)).preimage_mem_nhds
    (hTc.isOpen_compl.mem_nhds hpT)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem hc (QuantumZipper.isOpen_H.mem_nhds hpH))
  refine ⟨ε, hε, fun z hz => ?_⟩
  obtain ⟨s, hs, he⟩ := hfr z hz.1 (hball hz.2).2
  have hsI : s ∈ Ioo a b := by
    by_contra hn
    exact (hball hz.2).1 ⟨s, ⟨hs, hn⟩, he⟩
  have h := hseg ⟨α s, ⟨s, hsI, rfl⟩, rfl⟩
  rwa [he, cfPt_neg_cayley (H_subset_Hbar (hball hz.2).2)] at h

/-- An upper-half-plane boundary point of an inverted side lies on the full disc wall. -/
theorem disc_mem_of_negInv_mem_range {R : ℝ≥0 → ℂ} {z : ℂ}
    (hzH : z ∈ H) (hzR : negInv z ∈ range R) :
    -cayley z ∈ toDisc (realPath R) '' Icc 0 1 := by
  obtain ⟨s, hs⟩ := hzR
  refine ⟨discTime s, discTime_mem_Icc s, ?_⟩
  rw [toDisc_realPath_discTime, hs,
    cayley_negInv (H_subset_Hbar hzH) (WangWu.ne_zero_of_mem_H hzH)]

/-- The local frontier premise for the exterior of the right wall follows from the clip
itself, with no assumption about the certified frontier between the two corners. -/
theorem local_frontier_right_clip {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {C : Set ℂ} {a b t : ℝ} {p : ℂ} (ha : 0 ≤ a) (hb : b ≤ 1) (ht : t ∈ Ioo a b)
    (hp : -cayley p = toDisc (realPath R) t) (hpH : p ∈ H)
    (hseg : cfPt '' (toDisc (realPath R) '' Ioo a b) ⊆ closure C) :
    ∃ ε > 0, frontier (negInv '' rightSideOf (range R)) ∩ ball p ε ⊆ closure C := by
  have hα := hR.isProperArc.isDiscCrosscut_toDisc
  exact local_frontier_of_disc_clip hα.cont hα.inj ha hb ht hp hpH
    (fun z hz hzH => disc_mem_of_negInv_mem_range hzH ((forbidden_right hR).2 z hz hzH)) hseg

/-- Reflected local frontier premise for the exterior of the left wall. -/
theorem local_frontier_left_clip {L : ℝ≥0 → ℂ} (hL : IsSimpleProper L)
    {C : Set ℂ} {a b t : ℝ} {p : ℂ} (ha : 0 ≤ a) (hb : b ≤ 1) (ht : t ∈ Ioo a b)
    (hp : -cayley p = toDisc (realPath L) t) (hpH : p ∈ H)
    (hseg : cfPt '' (toDisc (realPath L) '' Ioo a b) ⊆ closure C) :
    ∃ ε > 0, frontier (negInv '' leftSideOf (range L)) ∩ ball p ε ⊆ closure C := by
  have hα := hL.isProperArc.isDiscCrosscut_toDisc
  exact local_frontier_of_disc_clip hα.cont hα.inj ha hb ht hp hpH
    (fun z hz hzH => disc_mem_of_negInv_mem_range hzH ((forbidden_left hL).2 z hz hzH)) hseg

end InteractingSLE.Sec7.R7GapEqGeo
