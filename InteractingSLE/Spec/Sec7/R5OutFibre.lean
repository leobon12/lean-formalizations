/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutFrontier

/-! # Boundary points of the erased prefix occur before the left stop -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open Sec6 PocketTraversal Lemma71C PocketStopMarked PocketStopMarked.Outer
  PocketStopWallsFin PocketUnionPt

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- GC1 identifies both physical ends even when an erasure fibre lies on the wall. -/
theorem erasedPath_eq_left (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (pocketClock η C τ σ σ)) :
    erasedPath η C τ σ u = η (pocketFibreLeft η C τ σ u) := by
  have ha := pocketFibreLeft_mem' hP u
  have hb := hP.erase.fibre_mem u
  have hab : pocketFibreLeft η C τ σ u ≤ pocketFibre η C τ σ u :=
    fibreLeft_le_fibreRight hP.erase.continuous_clock hP.erase.lt.le (by
      rw [R7StopIn.IsErasurePocket.clock_τ]; exact ⟨hu.1, hu.2.le⟩)
  rcases hab.eq_or_lt with he | hlt
  · change η (pocketFibre η C τ σ u) = _
    rw [he]
  · symm
    exact hP.erase.gc1 hb.2 (hP.erase.clock_lt_of_fibre ⟨hu.1, hu.2.le⟩)
      _ ⟨ha.1, hab⟩ _ ⟨hb.1, le_rfl⟩ hlt
      (by rw [clock_pocketFibreLeft' hP ⟨hu.1, hu.2.le⟩, hP.erase.clock_fibre ⟨hu.1, hu.2.le⟩])
      (fun t ht he => ⟨fibreLeft_le ⟨ht.1, ht.2.trans hb.2⟩ (by
        rw [he, clock_pocketFibreLeft' hP ⟨hu.1, hu.2.le⟩]; exact min_le_left _ _), ht.2⟩)

/-- The entire erased prefix, including its wall points, is on the ambient prefix at the left stop. -/
theorem erasedPath_prefix_subset_left (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (pocketClock η C τ σ σ)) :
    erasedPath η C τ σ '' Icc 0 u ⊆ η '' Icc 0 (pocketFibreLeft η C τ σ u) := by
  rintro y ⟨v, hv, rfl⟩
  rcases hv.2.lt_or_eq with hvu | rfl
  · refine ⟨pocketFibre η C τ σ v, ⟨hP.erase.nonneg.trans (hP.erase.fibre_mem v).1, ?_⟩, rfl⟩
    exact le_of_not_gt fun h => (not_lt_of_ge (hP.erase.monotone_clock h.le)) (by
      rw [clock_pocketFibreLeft' hP ⟨hu.1, hu.2.le⟩,
        hP.erase.clock_fibre ⟨hv.1, hv.2.trans hu.2.le⟩]; exact hvu)
  · exact ⟨_, ⟨hP.erase.nonneg.trans (pocketFibreLeft_mem' hP v).1, le_rfl⟩,
      (erasedPath_eq_left hP hu).symm⟩

/-- GC1 at the two ends of a seed-opening erasure fibre. -/
theorem erasedPathInf_eq_left (hP : IsOuterPocketInf W η C y₀ τ ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    erasedPathInf η C τ u = η (pocketFibreLeftInf η C τ u) := by
  obtain ⟨ha, -, hab⟩ := HOuter.pocketFibreLeftInf_props hP.erase hu
  have hb := hP.erase.fibre_mem hu
  rcases hab.eq_or_lt with he | hlt
  · change η (pocketFibreInf η C τ u) = _
    rw [he]
  · symm
    exact hP.erase.gc1 (hP.erase.clock_lt_of_fibre hu) _ ⟨ha, hab⟩ _ ⟨hb, le_rfl⟩ hlt
      (by rw [clock_pocketFibreLeftInf' hP hu, hP.erase.clock_fibre hu])
      (fun t ht he => ⟨csInf_le (show BddBelow {t | τ ≤ t ∧ u ≤ pocketClockInf η C τ t} from
        ⟨τ, fun _ ht => ht.1⟩) ⟨ht.1, by rw [he, clock_pocketFibreLeftInf' hP hu]⟩, ht.2⟩)

/-- The entire seed-opening erased prefix occurs before the left stop. -/
theorem erasedPathInf_prefix_subset_left (hP : IsOuterPocketInf W η C y₀ τ ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    erasedPathInf η C τ '' Icc 0 u ⊆ η '' Icc 0 (pocketFibreLeftInf η C τ u) := by
  rintro y ⟨v, hv, rfl⟩
  rcases hv.2.lt_or_eq with hvu | rfl
  · have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv.1, hv.2.trans_lt hu.2⟩
    refine ⟨pocketFibreInf η C τ v, ⟨hP.erase.nonneg.trans (hP.erase.fibre_mem hv'), ?_⟩, rfl⟩
    exact le_of_not_gt fun h => (not_lt_of_ge (hP.erase.monotone_clock h.le)) (by
      rw [clock_pocketFibreLeftInf' hP hu, hP.erase.clock_fibre hv']; exact hvu)
  · exact ⟨_, ⟨hP.erase.nonneg.trans (HOuter.pocketFibreLeftInf_props hP.erase hu).1, le_rfl⟩,
      (erasedPathInf_eq_left hP hu).symm⟩

end InteractingSLE.Sec7.R5Out
