/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeFace

/-!
# One central-face input supplies the finite mixed relative driver

PROVE-R7-GAPEQ. The previous proper-arm, old-access and separate target-face inputs are
discharged. The actual change pocket needs only its erasure facts, the attachment inputs
(contained germs remain separate), one reverse-visited wall and the central-side selection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6 WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEqCorner

/-- For a two-arc pocket, central-side selection for its first-visit arms supplies the target
face at each nonterminal physical time. The target access is a conclusion. -/
theorem hasTargetFace_of_gate_faces {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C B : Set ℂ} {τ σ r : ℝ} (hC : IsCfPocket C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ) (hτ : η τ = A₁ 1)
    (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (hfaces : ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η A₁ r q₁ a₁ → IsFirstVisitArm W η A₂ r q₂ a₂ →
      HasGateFace W C B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) r) :
    HasTargetFace W C B (A₁ 0) r := by
  have hτ₂ : η τ = A₂ 1 := hτ.trans hC.seed.symm
  have hσ₂ : η σ = A₂ 0 := hσ.trans hC.junction.symm
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := by rw [hC.junction]; exact hxf
  obtain ⟨hu₁, hu₁1, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁ hτ0 hτr hrσ hτ hσ hxf
  obtain ⟨-, hu₂1, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₂ hC.mem_H₂ hτ0 hτr hrσ hτ₂ hσ₂ hxf₂
  obtain ⟨q₁, a₁, ha₁⟩ := exists_firstVisit_arm hη hW hW0 hC.cont₁ hC.inj₁ hC.mem_H₁ hτ0 hτr hrσ hτ hσ hxf
  obtain ⟨q₂, a₂, ha₂⟩ := exists_firstVisit_arm hη hW hW0 hC.cont₂ hC.inj₂ hC.mem_H₂ hτ0 hτr hrσ hτ₂ hσ₂ hxf₂
  exact hasTargetFace_of_firstVisit_arms hW hW0 (hτ0.trans hτr) hC hu₁ hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
    (hfaces q₁ q₂ a₁ a₂ ha₁ ha₂)

/-- **The actual finite mixed pocket's mapped gaps.** One wall's reverse visits construct
the earlier proper arm. The selected-face input and attachment constancy then prove the old
case; the landed erasure reduction supplies the nonold case. -/
theorem mapped_gaps_of_change_faces {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} {η : ℝ → ℂ} {B : Set ℂ} {τ σ : ℝ}
    (hP : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hrev : IsWallReverseVisit R η ∨ IsWallReverseVisit L η)
    (hAC₁ : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r) τ σ)
    (hAC₂ : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) τ σ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hfaces : ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ cfPocket R L r) →
      a ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r} →
      b ∈ closure {t | a < t ∧ η t ∈ cfPocket R L r} → trMap W s a 0 = trMap W s b 0 := by
  have hC := h.isCfPocket h0
  have hproper := hasProperEarlierArm_of_one_reverse_wall h h0 hη.1 hrev hP.fresh_x
  apply R7GapEqGeo.mapped_gap_eq_of_old_access hP hη hW hW0 hηH
  intro s hs a b hsa hab hbσ hgap ha hb hold
  have hold' : η a ∈ η '' Ico 0 a := image_mono
    (show Icc (0 : ℝ) s ⊆ Ico 0 a from fun _ ht => ⟨ht.1, ht.2.trans_lt hsa⟩) hold
  exact (gap_eq_at_old_start hη hW hW0 hC.isOpen hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hC.mem_H₁ hC.mem_H₂
    hP.nonneg hs.1 hsa hab hbσ hP.first_y (hP.first_y.trans hC.seed.symm)
    hP.first_x (hP.first_x.trans hC.junction.symm) hP.fresh_x
    (fun _ hv _ hw => cfPocket_arms_eq hC hv hw)
    (hC.frontier_eq.symm ▸ subset_union_left) (hC.frontier_eq.symm ▸ subset_union_right)
    hAC₁ hAC₂ havoid hfaces hproper hgap ha hb hold').1

/-- **Relative Loewner evolution with one remaining planar input.** The former independent
target-face, old-access and proper-arm hypotheses are absent. The erased physical pocket
and its central-face selection remain explicit; no source theorem is replaced. -/
theorem relLoewner_of_change_gate_faces {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} {η : ℝ → ℂ} {B : Set ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hψ : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ)
    (hrev : IsWallReverseVisit R η ∨ IsWallReverseVisit L η)
    (hAC₁ : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r) τ σ)
    (hAC₂ : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) τ σ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hfaces : ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    RelLoewner (fun v => ψ (erasedPath η (cfPocket R L r) τ σ v))
      (pocketClock η (cfPocket R L r) τ σ σ) := by
  apply relLoewner_of_face_boundaries hP hη hW hW0
    (PocketJordan.image_negInv_subset_H h.changePocket_subset_H) hψ havoid
    (mapped_gaps_of_change_faces h h0 hP hη hW hW0 hηH hrev hAC₁ hAC₂ havoid hfaces)
  intro u hu
  exact hasTargetFace_of_gate_faces (h.isCfPocket h0) hη hW hW0 hP.nonneg
    (hP.fibre_mem u).1 (hP.fibre_lt_σ hu) hP.first_y hP.first_x hP.fresh_x
    (hfaces _ (hP.fibre_mem u).1 (hP.fibre_lt_σ hu))

end InteractingSLE.Sec7.R7GateBridge
