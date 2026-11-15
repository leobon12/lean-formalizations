/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInErase
import InteractingSLE.Spec.Sec7.R7StopInEraseInf
import InteractingSLE.Spec.Sec7.PocketStopMarkedPathInf

/-!
# Live relative capacities at interior visits of an erasure pocket

PROVE-SIDE-VISITS. For the erasure pockets of the mixed and outer R.7
configurations (supplement §5.4, `R7StopIn.IsErasurePocket(Inf)`), an
interior original visit `t` has a positive erasure clock, hence a positive
relative capacity strictly before the lifetime of the erased traversal,
whenever that traversal is a driven curve. These are the erasure counterparts
of the reverse-pocket clock bounds `PocketStopSide.relCap_pos_lt_of_visit`
and `relCapInf_pos_lt_of_visit`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideVis

open Sec6 PocketTraversal Lemma71C PocketStopMarked R7StopIn

variable {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ t : ℝ} {ψ : ℂ → ℂ}

/-- The erasure clock is positive at an interior visit. -/
theorem erasure_clock_pos_of_visit (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (ht : t ∈ visitSet η C τ σ) : 0 < pocketClock η C τ σ t := by
  have htt : τ < t := ht.1.1
  obtain ⟨e, he, hb⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t ht
  let d := min (e / 2) ((t - τ) / 2)
  have hd : 0 < d := lt_min (by positivity) (by linarith only [htt])
  have hd₁ : d ≤ e / 2 := min_le_left _ _
  have hd₂ : d ≤ (t - τ) / 2 := min_le_right _ _
  have hu : t - d ∈ visitSet η C τ σ := hb (by
    rw [mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
    linarith only [hd₁, he])
  have hlt := hP.clock_lt_of_mem (a := τ) (b := t) (t := t - d)
    (by linarith only [hd₂, htt]) (by linarith only [hd]) hu
  rwa [IsErasurePocket.clock_τ] at hlt

/-- **At an interior visit of an erasure pocket the relative capacity is
positive and live** (strictly before the lifetime of the erased traversal). -/
theorem erasure_relCap_pos_lt_of_visit (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hγ : IsDrivenCurve (relTrav η C τ σ ψ)) (ht : t ∈ visitSet η C τ σ) :
    0 < relCap η C τ σ ψ t ∧
      ENNReal.ofReal (relCap η C τ σ ψ t) < capLife (relTrav η C τ σ ψ) := by
  have hu : 0 < relTime η C τ σ t :=
    div_pos (erasure_clock_pos_of_visit hP ht)
      (sub_pos.2 (hP.clock_lt_clock_σ ⟨ht.1.1.le, ht.1.2⟩))
  have hc : 0 < capClock (relTrav η C τ σ ψ) (relTime η C τ σ t) := by
    rw [← hγ.capClock_zero]
    exact hγ.strictMonoOn_capClock self_mem_Ici hu.le hu
  exact ⟨hc, hγ.ofReal_capClock_lt hu.le⟩

/-- The seed-opening erasure clock is positive at an interior visit. -/
theorem erasureInf_clock_pos_of_visit (hP : IsErasurePocketInf η C y₀ τ)
    (ht : t ∈ visitSetInf η C τ) : 0 < pocketClockInf η C τ t := by
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
  rwa [IsErasurePocketInf.clock_τ] at hlt

/-- **At an interior visit of a seed-opening erasure pocket the relative
capacity is positive and live.** -/
theorem erasureInf_relCap_pos_lt_of_visit (hP : IsErasurePocketInf η C y₀ τ)
    (hγ : IsDrivenCurve (travInf η C τ ψ)) (ht : t ∈ visitSetInf η C τ) :
    0 < relCapInf η C τ ψ t ∧
      ENNReal.ofReal (relCapInf η C τ ψ t) < capLife (travInf η C τ ψ) := by
  have hu : 0 < relTimeInf η C τ t :=
    div_pos (erasureInf_clock_pos_of_visit hP ht)
      (sub_pos.2 (hP.clock_lt_clockEnd ht.1.le))
  have hc : 0 < capClock (travInf η C τ ψ) (relTimeInf η C τ t) := by
    rw [← hγ.capClock_zero]
    exact hγ.strictMonoOn_capClock self_mem_Ici hu.le hu
  exact ⟨hc, hγ.ofReal_capClock_lt hu.le⟩

end InteractingSLE.Sec7.SideVis
