/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeFresh

/-!
# The finite mixed physical gap from central-side selection

PROVE-R7-GAPEQ. A fresh boundary contact is on the contained side by the outer collars and
has gate zero. Old starts use the landed earlier-chart theorem. Neither endpoint needs an
old corner cover. The central-face hypothesis remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6 PocketJordan R7StopIn R7GapEq R7GapEqCorner

/-- The two-arc pocket topology is symmetric in the labeled sides. -/
theorem cfPocket_swap {C : Set ℂ} {A₁ A₂ : ℝ → ℂ} (hC : IsCfPocket C A₁ A₂) :
    IsCfPocket C A₂ A₁ := by
  refine ⟨hC.isOpen, hC.isConnected, hC.isBounded, ?_, hC.cont₂, hC.cont₁, hC.inj₂, hC.inj₁,
    hC.junction.symm, hC.seed.symm, ?_, hC.mem_H₂, hC.mem_H₁, ?_⟩
  · rw [hC.frontier_eq, union_comm]
  · exact fun v hv w hw he => hC.sides w hw v hv he.symm
  · rw [hC.seed]; exact hC.mem_y

/-- **Fresh start on the contained side**, including the original seed at time zero.
All current arms and the zero gate are constructed. The source germ comparisons enter only
through attachment constancy, and selected-face geometry remains the named planar input. -/
theorem gap_eq_at_fresh_start {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C B : Set ℂ} {τ σ s a b : ℝ} (hC : IsCfPocket C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hτ0 : 0 ≤ τ) (hτa : τ ≤ a)
    (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a < b) (hbσ : b < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (hrev : R16.IsReverseVisitOrder A₁ fun t => η '' Icc 0 t)
    (hAC₁ : BarrierAttachConst η C A₁ τ σ) (hAC₂ : BarrierAttachConst η C A₂ τ σ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hfaces : ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η A₁ a q₁ a₁ → IsFirstVisitArm W η A₂ a q₂ a₂ →
      HasGateFace W C B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) a)
    (hproper : HasProperEarlierArm η A₁ A₂ σ)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hb : b ∈ closure {t | a < t ∧ η t ∈ C})
    (hfresh : η a ∉ η '' Ico 0 a) (hcontact : η a ∈ A₁ '' Icc 0 1) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have ha0 := hτ0.trans hτa
  have haσ := hab.trans hbσ
  have hτ₂ := hτ.trans hC.seed.symm
  have hσ₂ := hσ.trans hC.junction.symm
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := by rw [hC.junction]; exact hxf
  obtain ⟨hu₁, hu₁1, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁ hτ0 hτa haσ hτ hσ hxf
  obtain ⟨hu₂, hu₂1, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₂ hC.mem_H₂ hτ0 hτa haσ hτ₂ hσ₂ hxf₂
  obtain ⟨q₁, a₁, ha₁⟩ := exists_firstVisit_arm hη hW hW0 hC.cont₁ hC.inj₁ hC.mem_H₁ hτ0 hτa haσ hτ hσ hxf
  obtain ⟨q₂, a₂, ha₂⟩ := exists_firstVisit_arm hη hW hW0 hC.cont₂ hC.inj₂ hC.mem_H₂ hτ0 hτa haσ hτ₂ hσ₂ hxf₂
  have ha₁' : IsFirstVisitArm W η A₁ a q₁ a₁ := ha₁
  have ha₂' : IsFirstVisitArm W η A₂ a q₂ a₂ := ha₂
  obtain ⟨v, hv, hvη⟩ := hcontact
  have hq₁ := firstVisit_gate_zero hη hW hW0 hηH ha0 hC.inj₁ hrev hv hvη.symm hfresh ha₁'
  have hface := hfaces q₁ q₂ a₁ a₂ ha₁' ha₂'
  have havoid' : ∀ t, a ≤ t → η t ∉ B := fun t ht => havoid t (ha0.trans ht)
  rcases le_total q₁ q₂ with hq | hq
  · rw [min_eq_left hq, max_eq_right hq] at hface
    exact gap_eq_of_ordered_firstVisit_arms_of_gate hη hW hW0 hC hτ0 hτa hs hsa hab hbσ hq
      hAC₁ hAC₂ hu₁ hu₁1 hu₂1 hD₁ hD₂ ha₁' ha₂' havoid' hface (fun _ => hproper)
      (Or.inl hq₁) hgap hb
  · rw [min_eq_right hq, max_eq_left hq, union_comm (a₁ '' Icc 0 1) (a₂ '' Icc 0 1)] at hface
    exact gap_eq_of_ordered_firstVisit_arms_of_gate hη hW hW0 (cfPocket_swap hC) hτ0 hτa hs hsa hab hbσ hq
      hAC₂ hAC₁ hu₂ hu₂1 hu₁1 hD₂ hD₁ ha₂' ha₁' havoid' hface
      (fun _ => hproper.symm hC.junction.symm) (Or.inr hq₁) hgap hb

/-- **The full finite mixed physical gap reduction.** Exterior collars exclude the outer
side at a fresh start, while reverse visit order identifies its contained attachment. The
old-start theorem handles old contacts, including the shared entrance corner. The remaining
new planar input is exactly `hfaces`; there is no old-corner-cover hypothesis. -/
theorem pocketGapEq_of_selected_faces {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C B : Set ℂ} {τ σ : ℝ} (hC : IsCfPocket C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hτ0 : 0 ≤ τ) (hτ : η τ = A₁ 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (hrev : R16.IsReverseVisitOrder A₁ fun t => η '' Icc 0 t)
    (hAC₁ : BarrierAttachConst η C A₁ τ σ) (hAC₂ : BarrierAttachConst η C A₂ τ σ)
    (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ frontier C)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (houter : ∀ v ∈ Ioo (0 : ℝ) 1, HasExteriorCollar C B (frontier C) (A₂ v))
    (hfaces : ∀ r : ℝ, τ ≤ r → r < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η A₁ r q₁ a₁ → IsFirstVisitArm W η A₂ r q₂ a₂ →
      HasGateFace W C B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) r)
    (hproper : HasProperEarlierArm η A₁ A₂ σ) : PocketGapEq η C τ σ := by
  intro a b hτa hab hbσ hgap hb ha
  have ha0 := hτ0.trans hτa
  have haσ := hab.trans hbσ
  by_cases hold : η a ∈ η '' Ico 0 a
  · have haτ : a ≠ τ := fun he => hτf (he ▸ hold)
    have hτa' : τ < a := lt_of_le_of_ne hτa haτ.symm
    have ha' := ha.resolve_left haτ
    exact (gap_eq_at_old_start hη hW hW0 hC.isOpen hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hC.mem_H₁ hC.mem_H₂
      hτ0 le_rfl hτa' hab hbσ hτ (hτ.trans hC.seed.symm) hσ (hσ.trans hC.junction.symm) hxf
      (fun _ hv _ hw => cfPocket_arms_eq hC hv hw)
      (hC.frontier_eq.symm ▸ subset_union_left) (hC.frontier_eq.symm ▸ subset_union_right)
      hAC₁ hAC₂ havoid hfaces hproper hgap ha' hb hold).2
  · have hacl : η a ∈ closure C := by
      rcases ha with he | ha'
      · rw [he, hτ]
        exact frontier_subset_closure (hC.frontier_eq.symm ▸ Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
      · exact mem_closure_of_visits hη.2.1 hτ0 ha'
    have hafr : η a ∈ frontier C := by
      rw [hC.isOpen.frontier_eq]
      exact ⟨hacl, hgap a ⟨le_rfl, hab.le⟩⟩
    have hcontact : η a ∈ A₁ '' Icc 0 1 := by
      by_contra hn
      obtain ⟨v, hv, he⟩ := (hC.frontier_eq ▸ hafr).resolve_left hn
      have hv0 : v ≠ 0 := by
        intro he0
        apply hn
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, (he0 ▸ he).symm.trans hC.junction |>.symm⟩
      have hv1 : v ≠ 1 := by
        intro he1
        apply hn
        exact ⟨1, ⟨zero_le_one, le_rfl⟩, hC.seed.symm.trans (he1 ▸ he)⟩
      obtain ⟨U, hU, hpU, hcov⟩ := houter v
        ⟨lt_of_le_of_ne hv.1 hv0.symm, lt_of_le_of_ne hv.2 hv1⟩
      rw [he] at hpU
      exact not_mem_collar_at_gap hη.2.1 h42 havoid ha0 hab hgap ⟨le_rfl, hab.le⟩ hU hcov hpU
    exact (gap_eq_at_fresh_start hC hη hW hW0 hηH hτ0 hτa hτ0 hτa hab hbσ hτ hσ hxf
      hrev hAC₁ hAC₂ havoid (hfaces a hτa haσ) hproper hgap hb hold hcontact).2

end InteractingSLE.Sec7.R7GateBridge
