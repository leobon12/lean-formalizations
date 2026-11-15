/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvF2a
import InteractingSLE.Spec.Supplement.SB2MdLift
import InteractingSLE.Spec.Supplement.SB2XxPhys

/-!
# SB2(2)'s joint stage induction (D29): the fill identity along the lockstep, without `tail`

Packet PROVE-SB2-LIFTSET (round 19, D29: LIFTSET owns the joint stage-by-stage induction for `StageRelP` at relative
stages `j ≥ 2`). The relative facts at a stage need the **physical domain identity**: the relative run chart, read in
physical coordinates, is a domain chart of `ℍ ∖ fill (A ∪ B_prefix)`. SB2LIFT's landed route goes through the full
prefix identity `prefix₂ = liftImage prefix₁` (`prefix_lift_of_steps`), which takes `tail`, false in general
(SB2LIFT §R29.1). The domain identity only sees the fills, and fills only see points of `ℍ`:

* `liftImage_real_inter_H`: the lift image of real points has no point in `ℍ` (`lift_mem_H_iff`);
* **`inter_H_eq_of_accCorr`**: along the lockstep with history (`AccCorr`, pieces paired by `LiftRel`), the relative
  physical set's points in `ℍ` are the lift image's points in `ℍ` once they are at the start — connectors are real on
  both sides, so no `tail` is used;
* **`fillH_eq_of_accCorr`**: hence the fills agree;
* **`isDomainChart_phys_of_accCorr`**: the physical domain identity at the stage (SB2LIFT's
  `isDomainChart_phys_of_lift` with the relative hull replaced by the lift image of B's prefix).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The lift image of real points has no point in `ℍ`.** -/
theorem liftImage_real_inter_H (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcM : ∀ w ∈ H, c.2.1 w ∈ H) (hoff : BdryOff c) (a : Set ℝ) :
    liftImage β₀ tL γ (((↑) : ℝ → ℂ) '' a) ∩ H = ∅ := by
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨s, ⟨x, -, hx⟩, rfl⟩ hzH
  have hl := lift_mem_H_iff hγ hcH hc1 hoff s
  have hγm : γ s - (m : ℂ) ∈ H := by
    show 0 < (γ s - (m : ℂ)).im
    simpa using (show (0 : ℝ) < (γ s).im from hzH)
  obtain ⟨w, hw, hwe⟩ := hl.1.2 hγm
  have hβH : β₀ (tL + s) ∈ H := by
    rw [← hwe]
    exact hcM w hw
  rw [← hx] at hβH
  have h0 : (0 : ℝ) < ((x : ℂ)).im := hβH
  simp at h0

/-- **The points in `ℍ` along the lockstep with history** (no `tail`): if the relative and actual states correspond
with history from a start where the points in `ℍ` already agree, they agree at the end. -/
theorem inter_H_eq_of_accCorr (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcM : ∀ w ∈ H, c.2.1 w ∈ H) (hoff : BdryOff c) {ι : ℝ → ℝ} {p : ℝ}
    {t₁ t₂ s₁ s₂ : ExplState} (hacc : AccCorr ι p (LiftRel β₀ tL γ) t₁ t₂ s₁ s₂)
    (hstart : statePhysicalSet 0 t₂ ∩ H = liftImage β₀ tL γ (statePhysicalSet 0 t₁) ∩ H) :
    statePhysicalSet 0 s₂ ∩ H = liftImage β₀ tL γ (statePhysicalSet 0 s₁) ∩ H := by
  obtain ⟨-, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hacc
  have hreal : ∀ (Z : List (Set ℝ)), (⋃ a ∈ Z, ((↑) : ℝ → ℂ) '' a) ∩ H = ∅ := fun Z => by
    ext z
    simp only [mem_inter_iff, mem_iUnion, mem_image, mem_empty_iff_false, iff_false, not_and, exists_prop]
    rintro ⟨a, -, x, -, rfl⟩ hz
    exact lt_irrefl (0 : ℝ) (by simpa using (show (0 : ℝ) < ((x : ℂ)).im from hz))
  have hlreal : liftImage β₀ tL γ (⋃ a ∈ X, ((↑) : ℝ → ℂ) '' a) ∩ H = ∅ := by
    rw [liftImage_biUnion, iUnion₂_inter]
    exact subset_empty_iff.1 (iUnion₂_subset fun a _ => (liftImage_real_inter_H hγ hcH hc1 hcM hoff a).subset)
  rw [statePhysicalSet_append hY₂ hX₂, statePhysicalSet_append hY₁ hX₁, liftImage_union, liftImage_union,
    liftImage_biUnion, ← biUnion_eq_of_forall₂ hY, union_inter_distrib_right, union_inter_distrib_right,
    union_inter_distrib_right, union_inter_distrib_right, hreal, hlreal, union_empty, union_empty, hstart]

/-- **The fills along the lockstep with history** (no `tail`). -/
theorem fillH_eq_of_accCorr (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcM : ∀ w ∈ H, c.2.1 w ∈ H) (hoff : BdryOff c) {ι : ℝ → ℝ} {p : ℝ}
    {t₁ t₂ s₁ s₂ : ExplState} (hacc : AccCorr ι p (LiftRel β₀ tL γ) t₁ t₂ s₁ s₂)
    (hstart : statePhysicalSet 0 t₂ ∩ H = liftImage β₀ tL γ (statePhysicalSet 0 t₁) ∩ H) :
    fillH (statePhysicalSet 0 s₂) = fillH (liftImage β₀ tL γ (statePhysicalSet 0 s₁)) := by
  rw [← Lw.fillH_inter_H' (statePhysicalSet 0 s₂), inter_H_eq_of_accCorr hγ hcH hc1 hcM hoff hacc hstart,
    Lw.fillH_inter_H']

/-- The tail times of a compact set on a proper curve form a compact set. -/
theorem isCompact_tailTimes {B : Set ℂ} (hβ : Supp9B.IsProperCurve β₀) (hB : IsCompact B) :
    IsCompact {s : ℝ≥0 | β₀ (tL + s) ∈ B} := by
  have hpre := (isClosedEmbedding_of_isProperCurve hβ).isCompact_preimage hB
  obtain ⟨M, hM⟩ := hpre.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded (hB.isClosed.preimage (hβ.1.comp (continuous_const.add
    continuous_id))) ((Metric.isBounded_closedBall (x := (0 : ℝ≥0)) (r := M)).subset fun s hs => ?_)
  have h1 := hM (show tL + s ∈ β₀ ⁻¹' B from hs)
  rw [Metric.mem_closedBall, NNReal.dist_eq, NNReal.coe_zero, sub_zero] at h1 ⊢
  have h2 : (s : ℝ) ≤ ((tL + s : ℝ≥0) : ℝ) := by simp
  rw [abs_of_nonneg (NNReal.coe_nonneg s)]
  exact h2.trans ((le_abs_self _).trans h1)

/-- **The physical domain identity at a lockstep stage** (no `tail`): with the relative run chart a domain chart of the
complement of its prefix's fill, and the fills agreeing along the lockstep, the relative chart in physical coordinates
is a domain chart of `ℍ ∖ fill (A ∪ B)`, `B` the actual prefix. -/
theorem isDomainChart_phys_of_fill {c₁ : Chart} {A B P₂ : Set ℂ} {ĝ : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c) (h₁ : IsDomainChart (H \ fillH P₂) c₁) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀)
    (hfill : fillH P₂ = fillH (liftImage β₀ tL γ B)) (hB : IsCompact B) (hBr : B ⊆ range β₀)
    (hhead : β₀ '' Icc 0 tL ⊆ hullK A) :
    IsDomainChart (H \ fillH (A ∪ B)) (Mo.physRelChart c c₁ m) := by
  have hT := isCompact_tailTimes (tL := tL) hβ hB
  have hRel : IsCompact (liftImage β₀ tL γ B) := hT.image hγ.2.1.1
  have hRelH : liftImage β₀ tL γ B ⊆ Hbar := by
    rintro _ ⟨s, -, rfl⟩; exact hγ.2.1.2.2.1 s
  have hcl : IsClosed (β₀ '' Ici tL) := (isClosedEmbedding_of_isProperCurve hβ).isClosedMap _ isClosed_Ici
  have h₁' : IsDomainChart (H \ fillH (liftImage β₀ tL γ B)) c₁ := by rw [← hfill]; exact h₁
  exact Mn.isDomainChart_phys_of_lift hc h₁' hA hĝ hC hRel hRelH hγ hβ.1 rfl hB hBr hhead hcl

end InteractingSLE.Theorem14.SB.Lk
