/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapFaces

/-!
# Infinite mixed gap endpoints from selected compact faces

PROVE-R7-GAPEQ. Old starts use an earlier chart after both attained maxima.
Fresh starts lie on the contained arm and have its current gate zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 PocketJordan R7StopIn R7GapEq R7InfinityChart

variable {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ} {C F K : Set ℂ} {τ : ℝ}
variable (hC : IsCfPocketInf C A₁ A₂)
variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
variable (hτ0 : 0 ≤ τ) (hτ : η τ = A₁ 0)
variable (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
variable (hAC : BarrierAttachConstInf η C A₁ τ)
variable (h42 : ∀ c d : ℝ, 0 ≤ c → c < d → ¬ η '' Icc c d ⊆ K)
variable (havoid : ∀ t, 0 ≤ t → η t ∉ F)
variable (houter : ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar C F K (A₂ v))
variable (hfaces : ∀ r, τ ≤ r → ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
  IsLastVisitArm W η A₁ r p q₁ b₁ → IsLastVisitArm W η A₂ r p q₂ b₂ → p < min q₁ q₂ →
  LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
  compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
  MapsTo (fun ζ => trMap W 0 r (psiMapInv p ζ))
    (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) C ∧
  ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
    psiMap p (trMap W r t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)))

include hC hη hW hW0 hτ0 hτ hrev hAC h42 havoid houter hfaces

/-- Every gap starting strictly after an earlier chart has equal mapped and
physical endpoint values. The start may be an old shared entrance corner. -/
theorem gap_eq_of_selected_faces {s a b : ℝ} (hτs : τ ≤ s) (hsa : s < a) (hab : a < b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (ha : a ∈ closure {t | τ < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hτa := hτs.trans_lt hsa
  have hs := hτ0.trans hτs
  have hAC₂ := outer_attachConstInf_of_collars hη.2.1 hC.cont₂ hC.tendsto₂ hτ0
    (hτ.trans hC.seed.symm) h42 havoid houter
  by_cases hold : η a ∈ η '' Ico 0 a
  · obtain ⟨r, hτr, hsr, hra, he₁, he₂⟩ := exists_earlier_chart_lastVisits hη.2.1
      hC.cont₁ hC.cont₂ hC.tendsto₁ hC.tendsto₂ hτ0 hτa hsa hτ
      (hτ.trans hC.seed.symm) hold
    exact gap_eq_of_current_arms hC hη hW hW0 hτ0 hτr hs hsr hra.le hab hτ hrev
      hAC hAC₂ he₁ he₂ (hfaces r hτr) hgap
      (Or.inl (R7GapEqGeo.mem_closure_visits_after hra ha))
      (R7GapEqGeo.mem_closure_visits_after (hra.trans hab) hb)
  · have hcontact := gap_contact_on_contained hC hη.2.1 h42 havoid houter
      (hτ0.trans hτa.le) hab hgap ⟨le_rfl, hab.le⟩
      (mem_closure_of_visits hη.2.1 hτ0 ha)
    exact gap_eq_of_current_arms hC hη hW hW0 hτ0 hτa.le hs hsa.le le_rfl hab hτ hrev
      hAC hAC₂ rfl rfl (hfaces a hτa.le) hgap (Or.inr ⟨rfl, hold, hcontact⟩) hb

/-- The actual physical infinite-gap predicate follows from the same selected
faces and the contained attachment comparison. No old-cover premise remains. -/
theorem pocketGapEqInf_of_selected_faces (hτf : η τ ∉ η '' Ico 0 τ) : PocketGapEqInf η C τ := by
  intro a b hτa hab hgap hb ha
  rcases eq_or_lt_of_le hτa with hτa | hτa
  · subst a
    have hAC₂ := outer_attachConstInf_of_collars hη.2.1 hC.cont₂ hC.tendsto₂ hτ0
      (hτ.trans hC.seed.symm) h42 havoid houter
    exact (gap_eq_of_current_arms hC hη hW hW0 hτ0 le_rfl hτ0 le_rfl le_rfl hab hτ hrev
      hAC hAC₂ rfl rfl (hfaces τ le_rfl) hgap
      (Or.inr ⟨rfl, hτf, 0, self_mem_Ici, hτ.symm⟩) hb).2
  · exact (gap_eq_of_selected_faces hC hη hW hW0 hτ0 hτ hrev hAC h42 havoid houter hfaces
      le_rfl hτa hab hgap (ha.resolve_left hτa.ne') hb).2

end InteractingSLE.Sec7.R7InfinityGap
