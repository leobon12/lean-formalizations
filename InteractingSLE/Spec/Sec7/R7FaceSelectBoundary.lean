/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectExterior

/-!
# No unvisited outer suffix enters the central face

PROVE-R7-GAPEQ. A contained suffix has already been visited. The outer side lies in the
closure of its untouched exterior, whose lift is outside the face. This discharges the
boundary-avoidance field of `HasGateFace` without assuming that the outer suffix is swallowed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7FaceSelect

open Sec6 PocketJordan R7GapEqCorner R7GateBridge

/-- The half-plane part of the gate boundary maps to the physical pocket frontier. -/
theorem gate_boundary_mem_frontier {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ}
    {C : Set ℂ} {r q₁ q₂ : ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hC : IsCfPocket C A₁ A₂)
    (hu₁ : firstVisit (fun t => η '' Icc 0 t) A₁ r ≤ 1)
    (hu₂ : firstVisit (fun t => η '' Icc 0 t) A₂ r ≤ 1)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ r), A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ r), A₂ v ∈ H \ fwdHull W r)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂) :
    ∀ w ∈ a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂),
      w ∈ H → trMap W 0 r w ∈ frontier C := by
  have harm : ∀ {A a : ℝ → ℂ} {q : ℝ},
      firstVisit (fun t => η '' Icc 0 t) A r ≤ 1 →
      (∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A r), A v ∈ H \ fwdHull W r) →
      IsFirstVisitArm W η A r q a → A '' Icc 0 1 ⊆ frontier C →
      ∀ w ∈ a '' Icc 0 1, w ∈ H → trMap W 0 r w ∈ frontier C := by
    intro A a q hu hD ha hf w hw hwH
    rcases eq_or_mem_open_arm ha.2.2.1 hw with he | hi
    · rw [he] at hwH
      simp [QuantumZipper.H] at hwH
    · rw [ha.2.2.2.2.2.2] at hi
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hi
      rw [trMap_zero_fwdMap hW hW0 hr (hD v hv)]
      exact hf ⟨v, ⟨hv.1, hv.2.le.trans hu⟩, rfl⟩
  rintro w ((hw | hw) | ⟨x, -, rfl⟩) hwH
  · exact harm hu₁ hD₁ ha₁ (hC.frontier_eq.symm ▸ subset_union_left) w hw hwH
  · exact harm hu₂ hD₂ ha₂ (hC.frontier_eq.symm ▸ subset_union_right) w hw hwH
  · simp [QuantumZipper.H] at hwH

/-- **The boundary-avoidance field of a mixed gate face.** All outer points are adherent to
an unbounded preconnected exterior missing the pocket frontier and the trace. Only the first
side is reverse visited; the second side may have a surviving suffix. -/
theorem gate_face_avoids_frontier_of_exterior
    {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ} {C E : Set ℂ} {τ σ r q₁ q₂ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hC : IsCfPocket C A₁ A₂) (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (hrev : R16.IsReverseVisitOrder A₁ fun t => η '' Icc 0 t)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 r)) (hEfr : Disjoint E (frontier C))
    (houter : A₂ '' Icc 0 1 ⊆ closure E) :
    ∀ w ∈ innerSide
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)),
      trMap W 0 r w ∉ frontier C := by
  have hr := hτ0.trans hτr
  obtain ⟨-, hu₁, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτr hrσ hτ hσ hxf
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨-, hu₂, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₂ hC.mem_H₂
    hτ0 hτr hrσ (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
  obtain ⟨hΓ, hΓH⟩ := firstVisit_face_jordan hW hr hC hu₁ hu₂ hD₁ hD₂ ha₁ ha₂
  have hbd := gate_boundary_mem_frontier hW hW0 hr hC hu₁ hu₂ hD₁ hD₂ ha₁ ha₂
  obtain ⟨-, hEO⟩ := lift_exterior_subset_outerSide hη hW hW0 hr hΓ hΓH hE hEH hEb havoid
    (fun w hw hwH hzE => Set.disjoint_left.1 hEfr hzE (hbd w hw hwH))
  have hcl := trMap_inner_not_mem_closure_exterior hW hW0 hr hΓ hΓH hEO
  have hm := firstVisit_mem (R := fun t => η '' Icc 0 t) hC.cont₁
    (isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun _ ht => ht.1)).isClosed
    ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτr⟩, hτ⟩
  intro w hw hfr
  have hwH := innerSide_subset_H hΓ hΓH hw
  have hzD := trMap_zero_mem_domain hW hW0 hr hwH
  rw [hC.frontier_eq] at hfr
  rcases hfr with ⟨v, hv, hvz⟩ | hz
  · by_cases hvu : v < firstVisit (fun t => η '' Icc 0 t) A₁ r
    · have hg : fwdMap W r (A₁ v) ∈ a₁ '' Ioc 0 1 :=
        ha₁.2.2.2.2.2.2 ▸ ⟨A₁ v, ⟨v, ⟨hv.1, hvu⟩, rfl⟩, rfl⟩
      rw [hvz, fwdMap_trMap_zero hW hW0 hr hwH] at hg
      exact innerSide_subset_compl hw (Or.inl (Or.inl (image_mono Ioc_subset_Icc_self hg)))
    · have hvis := hrev r _ hm.1 v hv (le_of_not_gt hvu) hm.2
      exact notMem_domain_of_mem_trace hη hr hvis (hvz ▸ hzD)
  · exact hcl w hw (houter hz)

end InteractingSLE.Sec7.R7FaceSelect
