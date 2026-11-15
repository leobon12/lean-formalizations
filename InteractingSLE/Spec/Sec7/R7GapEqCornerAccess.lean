/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerEq
import InteractingSLE.Spec.Sec7.R7GapEqCornerTarget

/-!
# The old-start gap, including an old shared entrance corner

PROVE-R7-GAPEQ. Choose a chart after both earlier attachment visits, build the two current
incoming arms, order their real gates and apply the gate reduction. The remaining geometric
inputs are central-side selection and the earlier proper arm; the germ input is precisely
the existing `BarrierAttachConst` for each contained side.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn

/-- Changing the order of the two sides preserves the earlier-arm input. -/
theorem HasProperEarlierArm.symm {η A₁ A₂ : ℝ → ℂ} {σ : ℝ}
    (h : HasProperEarlierArm η A₁ A₂ σ) (hj : A₁ 0 = A₂ 0) :
    HasProperEarlierArm η A₂ A₁ σ := by
  obtain ⟨β, hc, hi, h0, hH, ht, hf, h13, h23⟩ := h
  exact ⟨β, hc, hi, h0.trans hj, hH, ht, hf,
    fun v hv w hw he => (h23 v hv w hw he).trans hj,
    fun v hv w hw he => (h13 v hv w hw he).trans hj⟩

/-- **The old-start part of the R.7 gap equality, and the old-access mapped input.** The two
arms may be contained or outer. No corner cover, physical endpoint equality, reverse visit
order, or singleton-tip statement is assumed. The named geometric hypotheses select the
central face of their lifts and supply the earlier proper arm.

For the previous `hOld` input, `η a ∈ η '' Icc 0 s` with `s < a` implies `hold` here, and the
first projection supplies exactly its mapped equality. The second projection handles the
old shared entrance corner in the physical gap argument. -/
theorem gap_eq_at_old_start {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C B : Set ℂ} {τ σ s a b : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hC : IsOpen C)
    (hA₁c : ContinuousOn A₁ (Icc 0 1)) (hA₂c : ContinuousOn A₂ (Icc 0 1))
    (hA₁i : InjOn A₁ (Icc 0 1)) (hA₂i : InjOn A₂ (Icc 0 1))
    (hA₁H : ∀ v ∈ Ico (0 : ℝ) 1, A₁ v ∈ H) (hA₂H : ∀ v ∈ Ico (0 : ℝ) 1, A₂ v ∈ H)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hsa : s < a) (hab : a < b) (hbσ : b < σ)
    (hτ₁ : η τ = A₁ 1) (hτ₂ : η τ = A₂ 1)
    (hσ₁ : η σ = A₁ 0) (hσ₂ : η σ = A₂ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (h12 : ∀ v ∈ Ico (0 : ℝ) 1, ∀ w ∈ Ico (0 : ℝ) 1, A₁ v = A₂ w → A₁ v = A₁ 0)
    (hf₁ : A₁ '' Icc 0 1 ⊆ frontier C) (hf₂ : A₂ '' Icc 0 1 ⊆ frontier C)
    (hAC₁ : BarrierAttachConst η C A₁ τ σ) (hAC₂ : BarrierAttachConst η C A₂ τ σ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hfaces : ∀ r : ℝ, τ ≤ r → r < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η A₁ r q₁ a₁ → IsFirstVisitArm W η A₂ r q₂ a₂ →
      HasGateFace W C B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) r)
    (hproper : HasProperEarlierArm η A₁ A₂ σ)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (ha : a ∈ closure {t | s < t ∧ η t ∈ C}) (hb : b ∈ closure {t | a < t ∧ η t ∈ C})
    (hold : η a ∈ η '' Ico 0 a) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hj : A₁ 0 = A₂ 0 := hσ₁.symm.trans hσ₂
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := hj ▸ hxf
  obtain ⟨r, hτr, hsr, hra, he₁, he₂⟩ := exists_earlier_chart_firstVisits hη.2.1
    hA₁c hA₂c hτ0 (hτs.trans_lt hsa) hsa hτ₁ hτ₂ hold
  have hrσ := hra.trans (hab.trans hbσ)
  obtain ⟨hu₁, hu₁1, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hA₁c hA₁H hτ0 hτr hrσ hτ₁ hσ₁ hxf
  obtain ⟨hu₂, hu₂1, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hA₂c hA₂H hτ0 hτr hrσ hτ₂ hσ₂ hxf₂
  obtain ⟨q₁, a₁, ha₁⟩ := exists_firstVisit_arm hη hW hW0 hA₁c hA₁i hA₁H hτ0 hτr hrσ hτ₁ hσ₁ hxf
  obtain ⟨q₂, a₂, ha₂⟩ := exists_firstVisit_arm hη hW hW0 hA₂c hA₂i hA₂H hτ0 hτr hrσ hτ₂ hσ₂ hxf₂
  have ha₁' : IsFirstVisitArm W η A₁ r q₁ a₁ := ha₁
  have ha₂' : IsFirstVisitArm W η A₂ r q₂ a₂ := ha₂
  have hface := hfaces r hτr hrσ q₁ q₂ a₁ a₂ ha₁' ha₂'
  have har := R7GapEqGeo.mem_closure_visits_after hra ha
  have hbr := R7GapEqGeo.mem_closure_visits_after (hra.trans hab) hb
  have havoid' : ∀ t, r ≤ t → η t ∉ B := fun t ht => havoid t (hτ0.trans (hτr.trans ht))
  rcases le_total q₁ q₂ with hq | hq
  · rw [min_eq_left hq, max_eq_right hq] at hface
    exact gap_eq_of_ordered_firstVisit_arms hη hW hW0 hC hτ0 hτr (hτ0.trans hτs) hsr
      hra hab hbσ hq hAC₁ hAC₂ he₁ he₂ hu₁ hu₁1 hu₂1 hD₁ hD₂ ha₁' ha₂' hj h12 hf₁ hf₂
      havoid' hface (fun _ => hproper) hgap har hbr
  · rw [min_eq_right hq, max_eq_left hq, union_comm (a₁ '' Icc 0 1) (a₂ '' Icc 0 1)] at hface
    have h21 : ∀ v ∈ Ico (0 : ℝ) 1, ∀ w ∈ Ico (0 : ℝ) 1, A₂ v = A₁ w → A₂ v = A₂ 0 := by
      intro v hv w hw he
      exact he.trans ((h12 w hw v hv he.symm).trans hj)
    exact gap_eq_of_ordered_firstVisit_arms hη hW hW0 hC hτ0 hτr (hτ0.trans hτs) hsr
      hra hab hbσ hq hAC₂ hAC₁ he₂ he₁ hu₂ hu₂1 hu₁1 hD₂ hD₁ ha₂' ha₁' hj.symm h21 hf₂ hf₁
      havoid' hface (fun _ => hproper.symm hj) hgap har hbr

end InteractingSLE.Sec7.R7GapEqCorner
