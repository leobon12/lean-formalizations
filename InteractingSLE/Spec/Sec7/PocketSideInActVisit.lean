/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRefJoint
import InteractingSLE.Spec.Sec7.PocketStopMarkedPath

/-!
# Original rational visits with actual relative capacity clocks

PROVE-POCKET-SIDEIN. For a retained reverse pocket, openness and strict growth
of its erasure clock give rational original visits. Their actual relative
capacity is positive and before the traversal lifetime. Countable pockets are
intersected before any realized pocket or visit is selected. The R.6 shared
face and exclusion of certified frontiers are not consequences asserted here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Sec6 PocketTraversal Lemma71C PocketStopMarked

/-- At an actual interior visit, the erased clock has already increased. -/
theorem pocketClock_pos_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ t : ℝ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ) (ht : t ∈ visitSet η C τ σ) :
    0 < pocketClock η C τ σ t := by
  obtain ⟨e, he, hb⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t ht
  let d := min (e / 2) ((t - τ) / 2)
  have hd : 0 < d := lt_min (by positivity) (by linarith [ht.1.1])
  have hd₁ : d ≤ e / 2 := min_le_left _ _
  have hd₂ : d ≤ (t - τ) / 2 := min_le_right _ _
  have hu : t - d ∈ visitSet η C τ σ := hb (by
    rw [mem_ball, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hd]
    linarith only [hd₁, he])
  have hlt := hP.clock_lt_of_mem (a := τ) (b := t) (t := t - d)
    (by linarith only [hd₂, ht.1.1]) (by linarith only [hd]) hu
  rwa [IsReversePocket.clock_τ] at hlt

/-- The actual original-to-relative capacity clock at a visit is positive
and lies strictly before the lifetime of the erased traversal. -/
theorem relCap_pos_lt_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {t : ℝ}
    (ht : t ∈ visitSet η C τ σ) :
    0 < relCap η C τ σ ψ t ∧
      ENNReal.ofReal (relCap η C τ σ ψ t) < capLife (trav η C τ σ ψ) := by
  have htI : t ∈ Ico τ σ := ⟨ht.1.1.le, ht.1.2⟩
  have hu : 0 < relTime η C τ σ t :=
    div_pos (pocketClock_pos_of_visit hP ht) (sub_pos.2 (hP.clock_lt_clock_σ hAC htI))
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have hc : 0 < capClock (trav η C τ σ ψ) (relTime η C τ σ t) := by
    rw [← hγ.capClock_zero]
    exact hγ.strictMonoOn_capClock self_mem_Ici hu.le hu
  exact ⟨hc, hγ.ofReal_capClock_lt hu.le⟩

/-- A reverse pocket supplies a rational original visit with a genuine live
relative capacity. No abstract candidate-clock bounds are assumed. -/
theorem exists_rat_live_pocket_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    ∃ r : ℚ, (r : ℝ) ∈ visitSet η C τ σ ∧
      0 < (relCap η C τ σ ψ r).toNNReal ∧
      ((relCap η C τ σ ψ r).toNNReal : ℝ≥0∞) < capLife (trav η C τ σ ψ) := by
  have hclock : pocketClock η C τ σ τ ≠ pocketClock η C τ σ σ := by
    rw [IsReversePocket.clock_τ]
    exact (hP.clock_σ_pos hAC).ne
  obtain ⟨t, _, ht⟩ := hP.exists_mem_of_clock_lt hP.τ_lt_σ hclock
  obtain ⟨r, hr⟩ := Rat.denseRange_cast.exists_mem_open hP.isOpen_visitSet ⟨t, ht⟩
  obtain ⟨hpos, hlive⟩ := relCap_pos_lt_of_visit hP hAC hψ hr
  exact ⟨r, hr, Real.toNNReal_pos.2 hpos, hlive⟩

/-- The actual rational-visit construction is simultaneous over a countable
family. A pathwise nested reference can be selected after this event is fixed. -/
theorem ae_all_exists_rat_live_pocket_visit {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] {P : Measure Ω} {A : ι → Set Ω} {η : Ω → ℝ → ℂ}
    {w : Ω → ℝ → ℝ} {C : ι → Ω → Set ℂ} {α₁ α₂ β : ι → Ω → ℝ → ℂ}
    {τ σ : ι → Ω → ℝ} {ψ : ι → Ω → ℂ → ℂ}
    (hP : ∀ i, ∀ᵐ ω ∂P, ω ∈ A i →
      IsReversePocket (w ω) (η ω) (C i ω) (α₁ i ω) (α₂ i ω) (β i ω) (τ i ω) (σ i ω))
    (hAC : ∀ i, ∀ᵐ ω ∂P, ω ∈ A i →
      AttachmentConstancy (η ω) (C i ω) (α₁ i ω) (α₂ i ω) (τ i ω) (σ i ω))
    (hψ : ∀ i, ∀ᵐ ω ∂P, ω ∈ A i →
      IsJordanCoord (C i ω) (α₁ i ω 0) (α₁ i ω 1) (ψ i ω)) :
    ∀ᵐ ω ∂P, ∀ i, ω ∈ A i → ∃ r : ℚ,
      (r : ℝ) ∈ visitSet (η ω) (C i ω) (τ i ω) (σ i ω) ∧
      0 < (relCap (η ω) (C i ω) (τ i ω) (σ i ω) (ψ i ω) r).toNNReal ∧
      ((relCap (η ω) (C i ω) (τ i ω) (σ i ω) (ψ i ω) r).toNNReal : ℝ≥0∞) <
        capLife (trav (η ω) (C i ω) (τ i ω) (σ i ω) (ψ i ω)) := by
  filter_upwards [ae_all_iff.2 hP, ae_all_iff.2 hAC, ae_all_iff.2 hψ]
    with ω hp hac hchart i hi
  exact exists_rat_live_pocket_visit (hp i hi) (hac i hi) (hchart i hi)

end InteractingSLE.Sec7.PocketStopSide
