/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActVisit
import InteractingSLE.Spec.Sec7.PocketStopMarkedPathInf

/-!
# The actual left and right stops at an original interior visit

PROVE-POCKET-SIDEIN. Both erasure-fibre endpoints equal the original time
at an interior visit. Composing with the actual capacity clock therefore
identifies both stopped hulls with the same ambient original-time hull.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Sec6 PocketTraversal Lemma71C PocketStopMarked PocketStopWallsFin PocketUnionPt

/-- At an interior visit the left endpoint also equals the original time. -/
theorem pocketFibreLeft_clock_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ t : ℝ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ) (ht : t ∈ visitSet η C τ σ) :
    pocketFibreLeft η C τ σ (pocketClock η C τ σ t) = t := by
  have hv : pocketClock η C τ σ t ∈ Ico 0 (pocketClock η C τ σ σ) :=
    ⟨hP.clock_nonneg ht.1.1.le, hP.clock_lt_of_mem_visitSet ht ht.1.2⟩
  have hright := hP.fibre_clock_of_mem ht
  have hle := pocketFibreLeft_le hP ⟨hv.1, hv.2.le⟩
  rw [hright] at hle
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  exact notMem_of_mem_Ioc_fibre hP hv ⟨hlt, hright.ge⟩ ht.2

/-- The actual right ambient stop of the capacity reached at a visit is the
original visit time, rather than a possibly later erased excursion endpoint. -/
theorem ambTime_relCap_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) (ht : t ∈ visitSet η C τ σ) :
    ambTime η C τ σ ψ (relCap η C τ σ ψ t) = t := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  change pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ)
    (capInv (trav η C τ σ ψ) (capClock (trav η C τ σ ψ) (relTime η C τ σ t)))) = t
  rw [hγ.capInv_eq (relTime_nonneg hP hAC ⟨ht.1.1.le, ht.1.2⟩),
    clockOf_relTime hP hAC ⟨ht.1.1.le, ht.1.2⟩, hP.fibre_clock_of_mem ht]

/-- The optional left ambient stop has exactly the same original time. -/
theorem ambTime0_relCap_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) (ht : t ∈ visitSet η C τ σ) :
    ambTime0 η C τ σ ψ (relCap η C τ σ ψ t) = t := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  change pocketFibreLeft η C τ σ (clockOf (pocketClock η C τ σ σ)
    (capInv (trav η C τ σ ψ) (capClock (trav η C τ σ ψ) (relTime η C τ σ t)))) = t
  rw [hγ.capInv_eq (relTime_nonneg hP hAC ⟨ht.1.1.le, ht.1.2⟩),
    clockOf_relTime hP hAC ⟨ht.1.1.le, ht.1.2⟩, pocketFibreLeft_clock_of_visit hP ht]

/-- Left fibre identity for a pocket whose opening is at the seed. -/
theorem pocketFibreLeftInf_clock_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ t : ℝ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ) (ht : t ∈ visitSetInf η C τ) :
    pocketFibreLeftInf η C τ (pocketClockInf η C τ t) = t := by
  have hv : pocketClockInf η C τ t ∈ Ico 0 (clockEnd η C τ) :=
    ⟨hP.clock_nonneg ht.1.le, hP.clock_lt_clockEnd_of_mem ht⟩
  have hright := hP.fibre_clock_of_mem ht
  have hle := pocketFibreLeftInf_le hP hv
  rw [hright] at hle
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  exact notMem_of_mem_Ioc_fibreInf hP hv ⟨hlt, hright.ge⟩ ht.2

/-- The right ambient stop is the original visit time for the seed opening. -/
theorem ambTimeInf_relCapInf_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) (ht : t ∈ visitSetInf η C τ) :
    ambTimeInf η C τ ψ (relCapInf η C τ ψ t) = t := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  change pocketFibreInf η C τ (clockOf (clockEnd η C τ)
    (capInv (travInf η C τ ψ) (capClock (travInf η C τ ψ) (relTimeInf η C τ t)))) = t
  rw [hγ.capInv_eq (relTimeInf_nonneg hP hAC ht.1.le),
    clockOf_relTimeInf hP hAC ht.1.le, hP.fibre_clock_of_mem ht]

/-- The optional left stop also equals the original time for the seed opening. -/
theorem ambTime0Inf_relCapInf_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) (ht : t ∈ visitSetInf η C τ) :
    ambTime0Inf η C τ ψ (relCapInf η C τ ψ t) = t := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  change pocketFibreLeftInf η C τ (clockOf (clockEnd η C τ)
    (capInv (travInf η C τ ψ) (capClock (travInf η C τ ψ) (relTimeInf η C τ t)))) = t
  rw [hγ.capInv_eq (relTimeInf_nonneg hP hAC ht.1.le),
    clockOf_relTimeInf hP hAC ht.1.le, pocketFibreLeftInf_clock_of_visit hP ht]

/-- The seed-opening erasure clock is positive at an actual interior visit. -/
theorem pocketClockInf_pos_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ t : ℝ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ) (ht : t ∈ visitSetInf η C τ) :
    0 < pocketClockInf η C τ t := by
  have htt : τ < t := ht.1
  obtain ⟨e, he, hb⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t ht
  let d := min (e / 2) ((t - τ) / 2)
  have hd : 0 < d := lt_min (by positivity) (by linarith only [htt])
  have hd₁ : d ≤ e / 2 := min_le_left _ _
  have hd₂ : d ≤ (t - τ) / 2 := min_le_right _ _
  have hu : t - d ∈ visitSetInf η C τ := hb (by
    rw [mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
    linarith only [hd₁, he])
  have hlt := hP.clock_lt_of_mem (a := τ) (b := t) (t := t - d)
    (by linarith only [hd₂, htt]) (by linarith only [hd]) hu
  rwa [IsReversePocketInf.clock_τ] at hlt

/-- Its actual relative capacity is positive and live at that visit. -/
theorem relCapInf_pos_lt_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) (ht : t ∈ visitSetInf η C τ) :
    0 < relCapInf η C τ ψ t ∧
      ENNReal.ofReal (relCapInf η C τ ψ t) < capLife (travInf η C τ ψ) := by
  have hu : 0 < relTimeInf η C τ t :=
    div_pos (pocketClockInf_pos_of_visit hP ht) (sub_pos.2 (hP.clock_lt_clockEnd hAC ht.1.le))
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  have hc : 0 < capClock (travInf η C τ ψ) (relTimeInf η C τ t) := by
    rw [← hγ.capClock_zero]
    exact hγ.strictMonoOn_capClock self_mem_Ici hu.le hu
  exact ⟨hc, hγ.ofReal_capClock_lt hu.le⟩

end InteractingSLE.Sec7.PocketStopSide
