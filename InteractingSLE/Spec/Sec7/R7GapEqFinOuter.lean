/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinBoundary
import InteractingSLE.Spec.Sec7.R7OuterOrder
import InteractingSLE.WangWu.Prop419Proof

/-!
# Exterior incidence and clipping from the global wall order

PROVE-R7-GAPEQ continuation. The exterior-incidence premise of the Jordan collar follows
from the actual global sides of the outer wall, by the landed nesting and closure theorems.
The local forbidden-frontier premise follows from clipping a proper certified frontier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology
open QuantumZipper (H)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GapEqFin

open WangWu Lemma71I PocketJordan R7GapEq R7StopIn

/-- Any open exterior side disjoint from the pocket supplies approach outside its closure. -/
theorem exterior_incidence_of_openSide {C F S : Set ℂ} {p : ℂ}
    (hSo : IsOpen S) (hCS : Disjoint C S) (hSF : S ⊆ F) (hpS : p ∈ closure S) :
    p ∈ closure (F \ closure C) := by
  apply closure_mono (s := S) (t := F \ closure C) _ hpS
  intro z hz
  exact ⟨hSF hz, fun hzc => Set.disjoint_left.1 (hCS.closure_left hSo) hzc hz⟩

/-- Exterior incidence transports through the counterflow chart `m(z)=-1/z`. Only continuity
at upper-half-plane points and the involution identity are used. -/
theorem exterior_incidence_negInv {C F : Set ℂ} (hFH : F ⊆ H) {p : ℂ} (hpH : p ∈ H)
    (hp : p ∈ closure (F \ closure C)) :
    negInv p ∈ closure (negInv '' F \ closure (negInv '' C)) := by
  have hc : ContinuousAt negInv p := continuousOn_negInv.continuousAt
    (QuantumZipper.isOpen_H.mem_nhds hpH)
  apply closure_mono (s := negInv '' (F \ closure C)) _ (hc.continuousWithinAt.mem_closure_image hp)
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨⟨z, hz.1, rfl⟩, fun hcl => hz.2 ?_⟩
  have hcinv : ContinuousAt negInv (negInv z) := continuousOn_negInv.continuousAt
    (QuantumZipper.isOpen_H.mem_nhds (negInv_mem_H (hFH hz.1)))
  have h := hcinv.continuousWithinAt.mem_closure_image hcl
  rw [negInv_negInv, image_image,
    show (fun w => negInv (negInv w)) = id from funext negInv_negInv, image_id] at h
  exact h

/-- **The right outer wall's exterior incidence**, from global side order. Thus the incidence
part of the collar is not an additional random-tip or prime-end assumption. -/
theorem rightWall_exterior_incidence {R M : ℝ≥0 → ℂ} {C : Set ℂ}
    (hR : IsSimpleProper R) (hM : IsSimpleProper M)
    (hCl : C ⊆ leftSideOf (range R))
    (hMR : Disjoint (range M) (rightSideOf (range R))) {p : ℂ}
    (hpR : p ∈ range R) (hpH : p ∈ H) :
    negInv p ∈ closure (negInv '' rightSideOf (range M) \ closure (negInv '' C)) := by
  have hnest : rightSideOf (range R) ⊆ rightSideOf (range M) := by
    have hMR' : Disjoint (arcRange (realPath M)) (rightSideOf (arcRange (realPath R))) := by
      rwa [arcRange_realPath, arcRange_realPath]
    have h := SeedField.rightSideOf_subset_of_disjoint hR.isProperArc hM.isProperArc hMR'
    simpa only [arcRange_realPath] using h
  have hRc : IsClosed (range R) := by
    have h := hR.isProperArc.isClosed_arcRange
    rwa [arcRange_realPath] at h
  have hSo : IsOpen (rightSideOf (range R)) := Theorem14.SB.isOpen_rightSideOf
    (fun z hz => hRc.closure_eq ▸ hz.1)
  have hCS : Disjoint C (rightSideOf (range R)) := by
    have h := hR.isProperArc.disjoint_leftSideOf_rightSideOf
    rw [arcRange_realPath] at h
    exact h.mono_left hCl
  have hpS := R7Outer.range_subset_closure_rightSideOf_self hR hpR
  have hinc := exterior_incidence_of_openSide hSo hCS hnest hpS
  apply exterior_incidence_negInv (fun z hz => hz.1.1) hpH hinc

/-- The reflected incidence statement for the left outer wall, reusing the landed nesting of
left sides. -/
theorem leftWall_exterior_incidence {L M : ℝ≥0 → ℂ} {C : Set ℂ}
    (hL : IsSimpleProper L) (hM : IsSimpleProper M)
    (hCr : C ⊆ rightSideOf (range L))
    (hLM : Disjoint (range L) (rightSideOf (range M))) {p : ℂ}
    (hpL : p ∈ range L) (hpH : p ∈ H) :
    negInv p ∈ closure (negInv '' leftSideOf (range M) \ closure (negInv '' C)) := by
  have hnest : leftSideOf (range L) ⊆ leftSideOf (range M) := by
    have hLM' : Disjoint (arcRange (realPath L)) (rightSideOf (arcRange (realPath M))) := by
      rwa [arcRange_realPath, arcRange_realPath]
    have h := IsProperArc.leftSideOf_subset_of_disjoint hM.isProperArc hL.isProperArc hLM'
    simpa only [arcRange_realPath] using h
  have hLc : IsClosed (range L) := by
    have h := hL.isProperArc.isClosed_arcRange
    rwa [arcRange_realPath] at h
  have hSo : IsOpen (leftSideOf (range L)) := Theorem14.SB.isOpen_leftSideOf
    (fun z hz => hLc.closure_eq ▸ hz.1)
  have hCS : Disjoint C (leftSideOf (range L)) := by
    have h := hL.isProperArc.disjoint_leftSideOf_rightSideOf
    rw [arcRange_realPath] at h
    exact h.symm.mono_left hCr
  have hpS := R7Outer.range_subset_closure_leftSideOf_self hL hpL
  have hinc := exterior_incidence_of_openSide hSo hCS hnest hpS
  apply exterior_incidence_negInv (fun z hz => hz.1.1) hpH hinc

/-- **The local frontier inclusion from a clipped certified proper arm.** At an interior
parameter of a portion lying in the closed pocket, a ball avoids the two closed omitted tails.
Every forbidden-frontier point in that ball is therefore in the retained portion. -/
theorem exists_local_frontier_subset_of_clipped_arc
    {α : ℝ → ℂ} {C F : Set ℂ} {a b t : ℝ}
    (hα : IsProperArc α) (ht : t ∈ Ioo a b) (ht0 : 0 < t)
    (hfr : frontier F ∩ H ⊆ arcRange α)
    (hseg : α '' Ioo a b ⊆ closure C) :
    ∃ ε > 0, frontier F ∩ ball (α t) ε ⊆ closure C := by
  let T := α '' (Ici (0 : ℝ) ∩ (Ioo a b)ᶜ)
  have hTc : IsClosed T := hα.isClosed_image
    (isClosed_Ici.inter isOpen_Ioo.isClosed_compl) inter_subset_left
  have hpT : α t ∉ T := by
    rintro ⟨s, hs, hst⟩
    exact hs.2 (hα.inj hs.1 (mem_Ici.2 ht0.le) hst ▸ ht)
  have hpH : α t ∈ H := hα.mem_H t ht0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
    (QuantumZipper.isOpen_H.inter hTc.isOpen_compl) (α t) ⟨hpH, hpT⟩
  refine ⟨ε, hε, fun z hz => ?_⟩
  obtain ⟨s, hs, hsz⟩ := hfr ⟨hz.1, (hball hz.2).1⟩
  have hsI : s ∈ Ioo a b := by
    by_contra hn
    exact (hball hz.2).2 ⟨s, ⟨hs, hn⟩, hsz⟩
  exact hseg ⟨s, hsI, hsz⟩

end InteractingSLE.Sec7.R7GapEqFin
