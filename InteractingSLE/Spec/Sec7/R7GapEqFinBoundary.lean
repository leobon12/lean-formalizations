/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinJordan

/-!
# The outer-side collar for the two-arc pocket

PROVE-R7-GAPEQ continuation. The forbidden exterior may overlap the pocket between an outer
arm and its certified frontier. The collar proof therefore uses exterior incidence
`p ∈ closure (F ∖ closure C)`, rather than disjointness of `F` and `C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7GapEq R7StopIn PocketJordan

/-- The two-arc pocket topology already supplied by the change-pocket construction gives its
Jordan boundary, without reverse visits or a counterflow coupling. -/
theorem isJordanCurve_frontier_of_isCfPocket {C : Set ℂ} {B A : ℝ → ℂ}
    (hC : IsCfPocket C B A) : LQGMetric.JordanMap.IsJordanCurve (frontier C) := by
  rw [hC.frontier_eq]
  apply isJordanCurve_image_union hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hC.junction.symm hC.seed.symm
  rintro z ⟨⟨v, hv, rfl⟩, ⟨w, hw, h⟩⟩
  by_cases hv0 : v = 0
  · exact Or.inl (congrArg B hv0)
  by_cases hv1 : v = 1
  · exact Or.inr (congrArg B hv1)
  have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), lt_of_le_of_ne hv.2 hv1⟩
  have hw0 : w ≠ 0 := fun hw0 => hv0 (hC.inj₁ hv ⟨le_rfl, zero_le_one⟩
    (h.symm.trans (by rw [hw0, hC.junction])))
  have hw1 : w ≠ 1 := fun hw1 => hv1 (hC.inj₁ hv ⟨zero_le_one, le_rfl⟩
    (h.symm.trans (by rw [hw1, hC.seed])))
  exact False.elim (hC.sides v hv' w
    ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0), lt_of_le_of_ne hw.2 hw1⟩ h.symm)

/-- The Jordan exterior collar allows `F ∩ C ≠ ∅`. Its inputs describe only the incidence of
the exterior side and the local position of its frontier. -/
theorem hasExteriorCollar_of_exterior_incidence {C F K : Set ℂ} {p : ℂ}
    (hCo : IsOpen C) (hCc : IsConnected C) (hCb : IsBounded C)
    (hCJ : LQGMetric.JordanMap.IsJordanCurve (frontier C)) (hp : p ∈ frontier C)
    (hFo : IsOpen F) (hfrK : frontier C ⊆ K)
    (hinc : p ∈ closure (F \ closure C))
    (hfr : ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C) :
    HasExteriorCollar C F K p := by
  have hFo' : IsOpen (F \ closure C) := hFo.sdiff isClosed_closure
  have hdisj : Disjoint C (F \ closure C) :=
    Set.disjoint_left.2 fun z hz hzF => hzF.2 (subset_closure hz)
  have hfr' : ∃ ε > 0, frontier (F \ closure C) ∩ ball p ε ⊆ closure C := by
    obtain ⟨ε, hε, hεfr⟩ := hfr
    refine ⟨ε, hε, fun z hz => ?_⟩
    rcases frontier_inter_subset F (closure C)ᶜ hz.1 with ⟨hzF, _⟩ | ⟨_, hzC⟩
    · exact hεfr ⟨hzF, hz.2⟩
    · rw [frontier_compl] at hzC
      exact frontier_subset_closure (frontier_closure_subset hzC)
  obtain ⟨U, hU, hpU, hcov⟩ := hasExteriorCollar_of_jordan hCo hCc hCb hCJ hp
    hFo' hdisj hfrK hinc hfr'
  refine ⟨U, hU, hpU, fun z hz => ?_⟩
  rcases hcov hz with (hzC | hzF) | hzK
  · exact Or.inl (Or.inl hzC)
  · exact Or.inl (Or.inr hzF.1)
  · exact Or.inr hzK

/-- **Finite mixed gap equality from exterior incidence.** The generic collar input of the
landed reduction is now discharged by Jordan topology. The remaining inputs are the displayed
local exterior incidence/frontier data, the corner's allowed cover, and Aux. 37 along `B`. -/
theorem pocketGapEq_of_exterior_incidence {W : ℝ → ℝ} {η B A : ℝ → ℂ} {C F : Set ℂ} {τ σ : ℝ}
    (hC : IsCfPocket C B A) (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (h42 : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ frontier C)
    (hFo : IsOpen F) (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hinc : ∀ p ∈ A '' Icc 0 1, p ∉ B '' Icc 0 1 → p ∈ closure (F \ closure C))
    (hfr : ∀ p ∈ A '' Icc 0 1, p ∉ B '' Icc 0 1 →
      ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C)
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hAC : BarrierAttachConst η C B τ σ)
    (hcorner : ∀ t ∈ Ioo τ σ, firstVisit (fun s => η '' Icc 0 s) B t < 1 →
      η t = B 1 → HasOldAllowedCover η C F (frontier C) (η t) t) :
    PocketGapEq η C τ σ := by
  have hfrC : frontier C ⊆ B '' Icc 0 1 ∪ A '' Icc 0 1 := hC.frontier_eq.le
  have hA : IsClosed (A '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hC.cont₂).isClosed
  have hdisj : ∀ v ∈ Ioo (0 : ℝ) 1, B v ∉ A '' Icc 0 1 := by
    rintro v hv ⟨w, hw, hwv⟩
    have hw0 : w ≠ 0 := fun hw0 => hv.1.ne' (hC.inj₁ ⟨hv.1.le, hv.2.le⟩
      ⟨le_rfl, zero_le_one⟩ (hwv.symm.trans (by rw [hw0, hC.junction])))
    have hw1 : w ≠ 1 := fun hw1 => hv.2.ne (hC.inj₁ ⟨hv.1.le, hv.2.le⟩
      ⟨zero_le_one, le_rfl⟩ (hwv.symm.trans (by rw [hw1, hC.seed])))
    exact hC.sides v hv w ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0), lt_of_le_of_ne hw.2 hw1⟩ hwv.symm
  apply pocketGapEq_of_cornerCover hη hW hW0 hC.isOpen h42 Subset.rfl havoid hA hfrC hdisj
    (fun p hp hpB => ?_) hC.cont₁ hC.inj₁ hrev hτ0 hτ hτf hAC hcorner
  apply hasExteriorCollar_of_exterior_incidence hC.isOpen hC.isConnected hC.isBounded
    (isJordanCurve_frontier_of_isCfPocket hC) (hC.frontier_eq.symm ▸ Or.inr hp)
    hFo Subset.rfl (hinc p hp hpB) (hfr p hp hpB)

end InteractingSLE.Sec7.R7GapEqFin
