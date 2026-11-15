/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceLocal

/-!
# The single surviving end of the actual unbounded pocket

PROVE-R7-GAPEQ. Local connectivity of the disc pocket at its opening corner gives
preconnected physical neighborhoods arbitrarily far towards infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- The infinite end has preconnected relative neighborhoods outside every bounded
ball, containing every sufficiently distant point of the pocket. -/
theorem exists_preconnected_far_neighborhood {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) (ρ : ℝ) :
    ∃ S : Set ℂ, S ⊆ cfPocket R L r ∩ {z | ρ < ‖z‖} ∧ IsPreconnected S ∧
      ∃ T : ℝ, ∀ z ∈ cfPocket R L r, T ≤ ‖z‖ → z ∈ S := by
  let E := cayley '' changePocket R L r
  have hp : (-1 : ℂ) ∈ closure E := (h.openPt_eq_neg_one_iff.2 h0) ▸
    frontier_subset_closure h.openPt_mem_frontier
  have hEne : ∀ w ∈ E, w ≠ -1 := by
    intro w hw he
    have := h.cayleyChange_props.2.1 hw
    rw [he, mem_ball_zero_iff, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  obtain ⟨ε, hε, hερ⟩ := Metric.mem_nhdsWithin_iff.1
    (tendsto_norm_cfPt.eventually (eventually_gt_atTop ρ))
  obtain ⟨U, hU, hUc, hUN⟩ := isLocConnWithin_discPocket h hp ε hε
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhdsWithin_iff.1 hUN
  have hlim : Tendsto (fun z : ℂ => -cayley z) (cobounded ℂ) (𝓝 (-1)) :=
    QuantumZipper.CA.tendsto_cayley_cobounded.neg
  obtain ⟨T, -, hT⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1
    (hlim.eventually (Metric.ball_mem_nhds (-1) hδ))
  refine ⟨cfPt '' U, ?_, hUc.image _ (continuousOn_cfPt.mono fun w hw => hEne w (hU hw).1),
    T, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    constructor
    · rw [cfPocket, image_negInv_eq h.changePocket_subset_H]
      exact mem_image_of_mem cfPt (hU hw).1
    · exact hερ ⟨(hU hw).2, hEne w (hU hw).1⟩
  · intro z hz hzT
    have hzE : -cayley z ∈ E := by
      dsimp only [E]
      rw [← image_neg_cayley_image_negInv h.changePocket_subset_H]
      exact mem_image_of_mem _ hz
    exact ⟨-cayley z, hδU ⟨hT hzT, hzE⟩,
      cfPt_neg_cayley (H_subset_Hbar' (PocketJordan.image_negInv_subset_H h.changePocket_subset_H hz))⟩

/-- An unbounded subset of a normed plane has a point beyond every given radius. -/
theorem exists_norm_gt_of_not_isBounded {S : Set ℂ} (hS : ¬ IsBounded S) (T : ℝ) :
    ∃ z ∈ S, T < ‖z‖ := by
  by_contra hn
  push Not at hn
  exact hS (isBounded_closedBall.subset fun z hz => mem_closedBall_zero_iff.2 (hn z hz))

/-- Deleting a bounded set from the actual infinite-end pocket leaves at most one
unbounded component. This does not assert that all surviving components are unbounded. -/
theorem component_eq_of_unbounded {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {D : Set ℂ} {p q : ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hfar : ∃ ρ : ℝ, ∀ z ∈ cfPocket R L r, ρ < ‖z‖ → z ∈ D)
    (hp : ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ D) p))
    (hq : ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ D) q)) :
    connectedComponentIn (cfPocket R L r ∩ D) p =
      connectedComponentIn (cfPocket R L r ∩ D) q := by
  obtain ⟨ρ, hρ⟩ := hfar
  obtain ⟨S, hS, hSc, T, hT⟩ := exists_preconnected_far_neighborhood h h0 ρ
  obtain ⟨p', hp'P, hp'T⟩ := exists_norm_gt_of_not_isBounded hp T
  obtain ⟨q', hq'Q, hq'T⟩ := exists_norm_gt_of_not_isBounded hq T
  have hp'C := (connectedComponentIn_subset _ _ hp'P).1
  have hq'C := (connectedComponentIn_subset _ _ hq'Q).1
  have hp'S := hT p' hp'C hp'T.le
  have hq'S := hT q' hq'C hq'T.le
  have hSsub : S ⊆ cfPocket R L r ∩ D := fun _ hz => ⟨(hS hz).1, hρ _ (hS hz).1 (hS hz).2⟩
  have hq'P : q' ∈ connectedComponentIn (cfPocket R L r ∩ D) p := by
    rw [connectedComponentIn_eq hp'P]
    exact hSc.subset_connectedComponentIn hp'S hSsub hq'S
  exact (connectedComponentIn_eq hq'P).trans (connectedComponentIn_eq hq'Q).symm

end InteractingSLE.Sec7.R7EndFace
