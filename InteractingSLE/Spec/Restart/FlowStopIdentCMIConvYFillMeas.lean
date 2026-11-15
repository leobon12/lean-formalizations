/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYHull
import InteractingSLE.Spec.Restart.RetPlumbProofFilled

/-! # A hitting-measurable reader for the filling of a bounded set -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
open LocalSets

/-- Compact avoidance by the Euclidean closure, including points on the real
boundary, is determined by open hits inside the half-plane. -/
theorem measurableSet_disjoint_closure_interH {C : Set ℂ} (hC : IsCompact C) :
    MeasurableSet[hittingSigma] {A : Set ℂ | Disjoint C (closure (A ∩ H))} := by
  have he : {A : Set ℂ | Disjoint C (closure (A ∩ H))} =
      ⋃ n : ℕ, {A : Set ℂ | (A ∩ (thickening (1 / ((n : ℝ) + 1)) C ∩ H)).Nonempty}ᶜ := by
    ext A
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff]
    constructor
    · intro hd
      have hsub : C ⊆ (closure (A ∩ H))ᶜ := Set.disjoint_left.1 hd
      obtain ⟨δ, hδ, hδC⟩ := hC.exists_thickening_subset_open isClosed_closure.isOpen_compl hsub
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      refine ⟨n, ?_⟩
      rintro ⟨z, hzA, hzC, hzH⟩
      exact hδC (thickening_mono hn.le C hzC) (subset_closure ⟨hzA, hzH⟩)
    · rintro ⟨n, hn⟩
      refine Set.disjoint_left.2 fun z hzC hz => ?_
      have hz' := self_subset_thickening (by positivity : 0 < 1 / ((n : ℝ) + 1)) C hzC
      obtain ⟨w, hwC, hw⟩ := mem_closure_iff.1 hz _ isOpen_thickening hz'
      exact hn ⟨w, hw.1, hwC, hw.2⟩
  rw [he]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_hitting (isOpen_thickening.inter QuantumZipper.isOpen_H) inter_subset_right).compl

/-- Compact caps of the closure of the part visible inside `ℍ`. -/
def hullCompactCap (n : ℕ) (A : Set ℂ) : Set ℂ :=
  closure (A ∩ H) ∩ closedBall 0 (n : ℝ)

theorem isCompact_hullCompactCap (n : ℕ) (A : Set ℂ) : IsCompact (hullCompactCap n A) := by
  simpa only [hullCompactCap, inter_comm] using
    (isCompact_closedBall (0 : ℂ) (n : ℝ)).inter_right (isClosed_closure (s := A ∩ H))

/-- The compact caps have measurable closed-square hits, so the landed dyadic
filling theorem applies directly. -/
theorem isDyadicHitMeasurable_hullCompactCap (n : ℕ) :
    @IsDyadicHitMeasurable (Set ℂ) hittingSigma (hullCompactCap n) := by
  intro j k
  let C : Set ℂ := dyadicSquare j k ∩ closedBall 0 (n : ℝ)
  have hC : IsCompact C := (isCompact_dyadicSquare j k).inter_right isClosed_closedBall
  have hm := (measurableSet_disjoint_closure_interH hC).compl
  convert hm using 1
  ext A
  simp only [mem_ofPred_eq, mem_compl_iff, not_disjoint_iff_nonempty_inter]
  have he : dyadicSquare j k ∩ hullCompactCap n A = C ∩ closure (A ∩ H) := by
    ext z
    simp only [hullCompactCap, C, mem_inter_iff]
    tauto
  rw [he]

/-- This reader is defined on every set. On bounded subsets of `ℍ` it agrees
with filling; on other inputs it still gives an actual measurable enlargement. -/
def hullFillReader (A : Set ℂ) : Set ℂ :=
  A ∪ ⋃ n : ℕ, fillH (hullCompactCap n A)

theorem measurable_hullFillReader : Measurable[hittingSigma, hittingSigma] hullFillReader := by
  let : MeasurableSpace (Set ℂ) := hittingSigma
  refine measurable_union_hitting measurable_id (measurable_iUnion_hitting fun n => ?_)
  exact @RetAux79.measurable_fillH_of_dyadic (Set ℂ) hittingSigma (hullCompactCap n)
    (isDyadicHitMeasurable_hullCompactCap n) (isCompact_hullCompactCap n)

theorem subset_hullFillReader (A : Set ℂ) : A ⊆ hullFillReader A := subset_union_left

/-- The reader recovers the usual filling of every bounded subset of `ℍ`. -/
theorem hullFillReader_eq_fillH {A : Set ℂ} (hAH : A ⊆ H) (hAb : Bornology.IsBounded A) :
    hullFillReader A = fillH A := by
  have hAH' : A ∩ H = A := inter_eq_left.2 hAH
  have hcl : fillH (closure A) = fillH A := fillH_congr (by rw [closure_closure])
  refine Subset.antisymm (union_subset ?_ (iUnion_subset fun n => ?_)) ?_
  · exact fun z hz => mem_fillH_of_mem_closure (hAH hz) (subset_closure hz)
  · have hsub : hullCompactCap n A ⊆ closure A := by
      simp only [hullCompactCap, hAH']
      exact inter_subset_left
    exact (fillH_mono hsub).trans hcl.subset
  · obtain ⟨R, hR⟩ := hAb.closure.subset_closedBall (0 : ℂ)
    obtain ⟨n, hn⟩ := exists_nat_ge R
    have hcap : hullCompactCap n A = closure A := by
      simp only [hullCompactCap, hAH']
      exact inter_eq_left.2 (hR.trans (closedBall_subset_closedBall hn))
    intro z hz
    exact Or.inr (mem_iUnion.2 ⟨n, by rwa [hcap, hcl]⟩)

end InteractingSLE.Restart.FlowStopIdentCMI
