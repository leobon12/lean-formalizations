/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeGap
import InteractingSLE.Spec.Sec7.R7GateBridgeWire

/-!
# The actual finite mixed physical gaps with one remaining planar input

PROVE-R7-GAPEQ. First-hit times and freshness follow from visits of the contained wall.
The actual outer collars prove outer attachment constancy. The earlier proper arm and the
contained side's order are reused, so only central-face selection and contained germs remain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6 WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEq R7GapEqCorner

/-- Aux. 42 excludes every positive trace interval on the two-arc pocket frontier. -/
theorem no_interval_frontier {η A₁ A₂ : ℝ → ℂ} {C : Set ℂ} (hC : IsCfPocket C A₁ A₂)
    (hη : ContinuousOn η (Ici 0))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ frontier C := by
  rw [hC.frontier_eq]
  exact not_image_subset_union_of_noSimpleArc hη h42
    ⟨_, hC.cont₁, hC.inj₁, rfl⟩ ⟨_, hC.cont₂, hC.inj₂, rfl⟩

/-- **The finite left-outer / right-contained pocket.** All old-corner, first-hit, proper-arm
and outer-attachment premises of the previous reductions are discharged. `hAC` is the named
contained germ input; `hfaces` is the exact remaining central-side geometry. -/
theorem pocketGapEq_leftOuter_of_faces {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} {η : ℝ → ℂ} {B : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hrev : IsWallReverseVisit R η) (hvis : IsWallVisited R η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hCr : changePocket R L r ⊆ rightSideOf (range L))
    (hside : negInv '' leftSideOf (range L) ⊆ B)
    (hfaces : ∀ s : ℝ, firstHit η (cfArcR R L r 1) ≤ s → s < firstHit η (cfArcR R L r 0) →
      ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    PocketGapEq η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  have hC := h.isCfPocket h0
  obtain ⟨-, hh, huh, -⟩ := h.changeCorner_props
  have hu0 := h.rightLo_pos h0
  have hxvis : ∃ t, cfArcR R L r 0 ∈ η '' Icc 0 t := by
    simpa only [cfArcR, zero_mul, add_zero] using
      wall_visited hη.1 h.right hvis ⟨hu0, huh.le.trans hh.2⟩
  have hyvis : ∃ t, cfArcR R L r 1 ∈ η '' Icc 0 t := by
    simpa only [cfArcR, one_mul, add_sub_cancel] using
      wall_visited hη.1 h.right hvis ⟨hu0.trans huh, hh.2⟩
  obtain ⟨hτ0, hτ, hyf⟩ := firstHit_spec hη.2.1 hyvis
  obtain ⟨-, hσ, hxf⟩ := firstHit_spec hη.2.1 hxvis
  have hτf : η (firstHit η (cfArcR R L r 1)) ∉ η '' Ico 0 (firstHit η (cfArcR R L r 1)) := by
    rw [hτ]; exact hyf
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 (firstHit η (cfArcR R L r 0)) := by
    rw [hC.junction]; exact hxf
  have houter : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasExteriorCollar (cfPocket R L r) B (frontier (cfPocket R L r)) (cfArcL R L r v) :=
    fun _ hv => R7GapEqGeo.hasExteriorCollar_cfArcL h h0 hCr hside Subset.rfl hv
  have h42' := no_interval_frontier hC hη.2.1 h42
  have hAC₂ := barrierAttachConst_of_outerCollars hη.2.1 hC.cont₂ hτ0
    (hτ.trans hC.seed.symm) hxf₂ h42' havoid houter
  exact pocketGapEq_of_selected_faces hC hη hW hW0 hηH hτ0 hτ hτf hσ hxf
    (cfArcR_rev h h0 hη.1 hrev) hAC hAC₂ h42' havoid houter hfaces
    (hasProperEarlierArm_right h h0 hη.1 hrev hxf)

/-- **The reflected finite right-outer / left-contained pocket.** The face input is stated
with the contained left arm first; this is just the same central curve with exchanged labels. -/
theorem pocketGapEq_rightOuter_of_faces {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} {η : ℝ → ℂ} {B : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hrev : IsWallReverseVisit L η) (hvis : IsWallVisited L η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hCl : changePocket R L r ⊆ leftSideOf (range R))
    (hside : negInv '' rightSideOf (range R) ⊆ B)
    (hfaces : ∀ s : ℝ, firstHit η (cfArcR R L r 1) ≤ s → s < firstHit η (cfArcR R L r 0) →
      ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcL R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcR R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    PocketGapEq η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  have hC := h.isCfPocket h0
  obtain ⟨-, -, -, -, hh, huh, hLa, hLb⟩ := h.changeCorner_props
  have hu0 := h.leftLo_pos h0
  have hxvis : ∃ t, cfArcR R L r 0 ∈ η '' Icc 0 t := by
    rw [← hC.junction]
    simpa only [cfArcL, zero_mul, add_zero] using
      wall_visited hη.1 h.left hvis ⟨hu0, huh.le.trans hh.2⟩
  have hyvis : ∃ t, cfArcR R L r 1 ∈ η '' Icc 0 t := by
    rw [← hC.seed]
    simpa only [cfArcL, one_mul, add_sub_cancel] using
      wall_visited hη.1 h.left hvis ⟨hu0.trans huh, hh.2⟩
  obtain ⟨hτ0, hτ, hyf⟩ := firstHit_spec hη.2.1 hyvis
  obtain ⟨-, hσ, hxf⟩ := firstHit_spec hη.2.1 hxvis
  have hτf : η (firstHit η (cfArcR R L r 1)) ∉ η '' Ico 0 (firstHit η (cfArcR R L r 1)) := by
    rw [hτ]; exact hyf
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 (firstHit η (cfArcR R L r 0)) := by
    rw [hC.junction]; exact hxf
  have houter : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasExteriorCollar (cfPocket R L r) B (frontier (cfPocket R L r)) (cfArcR R L r v) :=
    fun _ hv => R7GapEqGeo.hasExteriorCollar_cfArcR h h0 hCl hside Subset.rfl hv
  have h42' := no_interval_frontier hC hη.2.1 h42
  have hAC₁ := barrierAttachConst_of_outerCollars hη.2.1 hC.cont₁ hτ0 hτ hxf h42' havoid houter
  exact pocketGapEq_of_selected_faces (cfPocket_swap hC) hη hW hW0 hηH hτ0
    (hτ.trans hC.seed.symm) hτf (hσ.trans hC.junction.symm) hxf₂
    (cfArcL_rev h h0 hη.1 hrev) hAC hAC₁ h42' havoid houter hfaces
    ((hasProperEarlierArm_left h h0 hη.1 hrev hxf).symm hC.junction.symm)

end InteractingSLE.Sec7.R7GateBridge
