/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapMapped
import InteractingSLE.Spec.Sec7.R7InfinityGapFresh

/-!
# Gap equality from the two current proper arms

PROVE-R7-GAPEQ. Choose a pole outside the compact mapped gap path. The selected
face and attachment constancy give both mapped and physical endpoint equality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 PocketJordan R7StopIn R7InfinityChart

/-- Both attachment parameters agree with their gap-start values. The selected
compact face then proves equality, for an old visit limit or a fresh contained gate. -/
theorem gap_eq_of_current_arms {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C : Set ℂ} {τ s r a b : ℝ} (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r ≤ a) (hab : a < b) (hτ : η τ = A₁ 0)
    (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hAC₁ : BarrierAttachConstInf η C A₁ τ) (hAC₂ : BarrierAttachConstInf η C A₂ τ)
    (he₁ : lastVisit (fun t => η '' Icc 0 t) A₁ r = lastVisit (fun t => η '' Icc 0 t) A₁ a)
    (he₂ : lastVisit (fun t => η '' Icc 0 t) A₂ r = lastVisit (fun t => η '' Icc 0 t) A₂ a)
    (hfaces : ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
      IsLastVisitArm W η A₁ r p q₁ b₁ → IsLastVisitArm W η A₂ r p q₂ b₂ → p < min q₁ q₂ →
      LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
      compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
      MapsTo (fun ζ => trMap W 0 r (psiMapInv p ζ))
        (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) C ∧
      ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
        psiMap p (trMap W r t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)))
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C} ∨
      (r = a ∧ η a ∉ η '' Ico 0 a ∧ η a ∈ A₁ '' Ici 0))
    (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr := hτ0.trans hτr
  obtain ⟨q₁, q₂, harcs⟩ := exists_pocket_compact_arms hC hη hW hW0 hτ0 hτr hτ
  have hδc : ContinuousOn (fun t => trMap W r t 0) (Icc a b) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr).mono fun _ ht => hra.trans ht.1
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hδc).isBounded.exists_norm_le
  let p := min (min q₁ q₂) (-|B|) - 1
  have hp : p < min q₁ q₂ := (sub_one_lt _).trans_le (min_le_left _ _)
  have hδp : ∀ t ∈ Icc a b, trMap W r t 0 ≠ p := by
    intro t ht he
    have hsmall := hB _ ⟨t, ht, rfl⟩
    change ‖trMap W r t 0‖ ≤ B at hsmall
    rw [he, norm_real, Real.norm_eq_abs] at hsmall
    have hple : p ≤ -|B| - 1 := sub_le_sub_right (min_le_right _ _) 1
    have hpneg : p < 0 := by linarith only [hple, abs_nonneg B]
    rw [abs_of_neg hpneg] at hsmall
    linarith only [hsmall, hple, le_abs_self B]
  obtain ⟨b₁, b₂, hb₁, hb₂, hdisj⟩ := harcs p hp
  have hpq₁ := hp.trans_le (min_le_left _ _)
  have hpq₂ := hp.trans_le (min_le_right _ _)
  obtain ⟨hΓ, hΓH⟩ := compactBoundary_jordan
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hpq₁)))
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hpq₂)))
    hb₁.1 hb₂.1 hb₁.2.1 hb₂.2.1 hb₁.2.2.1 hb₂.2.2.1
    hb₁.2.2.2.1 hb₂.2.2.2.1 hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hdisj
  obtain ⟨hFC, h11⟩ := hfaces p q₁ q₂ b₁ b₂ hb₁ hb₂ hp hΓ hΓH
  have hy₁ : A₁ 0 ∈ η '' Icc 0 r := ⟨τ, ⟨hτ0, hτr⟩, hτ⟩
  have hy₂ : A₂ 0 ∈ η '' Icc 0 r := hC.seed ▸ hy₁
  obtain ⟨hu₁, -, hD₁⟩ := lastVisit_tail_domain hη hr hC.cont₁ hC.tendsto₁ hC.mem_H₁ hy₁
  obtain ⟨hu₂, -, hD₂⟩ := lastVisit_tail_domain hη hr hC.cont₂ hC.tendsto₂ hC.mem_H₂ hy₂
  have hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₁ r),
      η t ≠ A₁ v := fun t ht v hv => avoid_tail_of_attachment_const hη.2.1 hC.tendsto₁
        hAC₁ (hτr.trans hra) he₁ hgap t ht (hr.trans (hra.trans ht.1)) v (hu₁.trans hv.le) hv
  have hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₂ r),
      η t ≠ A₂ v := fun t ht v hv => avoid_tail_of_attachment_const hη.2.1 hC.tendsto₂
        hAC₂ (hτr.trans hra) he₂ hgap t ht (hr.trans (hra.trans ht.1)) v (hu₂.trans hv.le) hv
  have hstart : (trMap W r a 0 = q₁ ∨ trMap W r a 0 = q₂) ∨
      a ∈ closure {t | r < t ∧ η t ∈ C} := by
    rcases ha with ha | ⟨he, hfresh, v, hv, hpv⟩
    · exact Or.inr ha
    · subst r
      have hq := lastVisit_gate_zero_of_pocket hC hη hW hW0 hr hrev hv hpv.symm hfresh hb₁
      exact Or.inl (Or.inl (by rw [hq, ofReal_zero]; exact YuanSimpleApprox.trMap_self hW a zero_mem_Hbar))
  have heq := ownFuture_gap_eq_of_compact_face hη hW hW0 hr hC.isOpen hra hab hb₁ hb₂ hp
    hdisj hD₁ hD₂ hFC h11 hδp hgap hunv₁ hunv₂ hstart hb
  exact ownFuture_and_trace_eq hη hW hW0 hs hsr hra (hra.trans hab.le) heq

end InteractingSLE.Sec7.R7InfinityGap
