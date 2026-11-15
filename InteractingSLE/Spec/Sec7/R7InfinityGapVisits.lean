/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessConfinement

/-!
# Last-visit attachments at old and fresh gap starts

PROVE-R7-GAPEQ. An old start admits an earlier chart after both proper-arm maxima
were attained. Attachment constancy excludes all later proper tails on the gap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 R7StopIn R7InfinityChart

/-- An attained proper-arm attachment was already visited before an old start. -/
theorem lastVisit_attained_before_old_start {η A : ℝ → ℂ} {τ a : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hAc : ContinuousOn A (Ici 0))
    (hAt : Tendsto (fun v => ‖A v‖) atTop atTop)
    (hτ0 : 0 ≤ τ) (hτa : τ ≤ a) (hτ : η τ = A 0)
    (hold : η a ∈ η '' Ico 0 a) :
    ∃ t ∈ Ico (0 : ℝ) a, η t = A (lastVisit (fun s => η '' Icc 0 s) A a) := by
  obtain ⟨t, ht, he⟩ := (lastVisit_mem (R := fun s => η '' Icc 0 s) hAc hAt
    (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1))
    ⟨0, self_mem_Ici, τ, ⟨hτ0, hτa⟩, hτ⟩).2
  rcases eq_or_lt_of_le ht.2 with hta | hta
  · obtain ⟨t', ht', he'⟩ := hold
    exact ⟨t', ht', he'.trans (hta ▸ he)⟩
  · exact ⟨t, ⟨ht.1, hta⟩, he⟩

/-- A common earlier chart preserves both proper-arm maxima. No reverse visit
order is required for the outer arm. -/
theorem exists_earlier_chart_lastVisits {η A₁ A₂ : ℝ → ℂ} {τ s a : ℝ}
    (hη : ContinuousOn η (Ici 0))
    (hA₁ : ContinuousOn A₁ (Ici 0)) (hA₂ : ContinuousOn A₂ (Ici 0))
    (hAt₁ : Tendsto (fun v => ‖A₁ v‖) atTop atTop)
    (hAt₂ : Tendsto (fun v => ‖A₂ v‖) atTop atTop)
    (hτ0 : 0 ≤ τ) (hτa : τ < a) (hsa : s < a)
    (hτ₁ : η τ = A₁ 0) (hτ₂ : η τ = A₂ 0) (hold : η a ∈ η '' Ico 0 a) :
    ∃ r : ℝ, τ ≤ r ∧ s ≤ r ∧ r < a ∧
      lastVisit (fun t => η '' Icc 0 t) A₁ r = lastVisit (fun t => η '' Icc 0 t) A₁ a ∧
      lastVisit (fun t => η '' Icc 0 t) A₂ r = lastVisit (fun t => η '' Icc 0 t) A₂ a := by
  obtain ⟨t₁, ht₁, he₁⟩ := lastVisit_attained_before_old_start hη hA₁ hAt₁ hτ0 hτa.le hτ₁ hold
  obtain ⟨t₂, ht₂, he₂⟩ := lastVisit_attained_before_old_start hη hA₂ hAt₂ hτ0 hτa.le hτ₂ hold
  let M := max (max τ s) (max t₁ t₂)
  obtain ⟨r, hMr, hra⟩ := exists_between (max_lt (max_lt hτa hsa) (max_lt ht₁.2 ht₂.2))
  have hτr : τ ≤ r := ((le_max_left _ _).trans (le_max_left _ _)).trans hMr.le
  have hsr : s ≤ r := ((le_max_right _ _).trans (le_max_left _ _)).trans hMr.le
  have ht₁r : t₁ ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hMr.le
  have ht₂r : t₂ ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hMr.le
  have hcpt := fun t => isCompact_Icc.image_of_continuousOn
    (hη.mono (show Icc (0 : ℝ) t ⊆ Ici 0 from fun _ ht => ht.1))
  exact ⟨r, hτr, hsr, hra,
    lastVisit_eq_of_visited hA₁ hAt₁ monotone_image_Icc hra.le (hcpt a) (hcpt r).isBounded
      ⟨0, self_mem_Ici, τ, ⟨hτ0, hτa.le⟩, hτ₁⟩ ⟨t₁, ⟨ht₁.1, ht₁r⟩, he₁⟩,
    lastVisit_eq_of_visited hA₂ hAt₂ monotone_image_Icc hra.le (hcpt a) (hcpt r).isBounded
      ⟨0, self_mem_Ici, τ, ⟨hτ0, hτa.le⟩, hτ₂⟩ ⟨t₂, ⟨ht₂.1, ht₂r⟩, he₂⟩⟩

/-- Constant last-visit parameters exclude every point beyond the chart-time
attachment throughout a gap. -/
theorem avoid_tail_of_attachment_const {η A : ℝ → ℂ} {C : Set ℂ} {τ r a b : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hAt : Tendsto (fun v => ‖A v‖) atTop atTop)
    (hAC : BarrierAttachConstInf η C A τ) (hτa : τ ≤ a)
    (heq : lastVisit (fun t => η '' Icc 0 t) A r = lastVisit (fun t => η '' Icc 0 t) A a)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) :
    ∀ t ∈ Icc a b, 0 ≤ t → ∀ v ∈ Ici (0 : ℝ),
      lastVisit (fun t => η '' Icc 0 t) A r < v → η t ≠ A v := by
  intro t ht ht0 v hv huv he
  have hc := hAC a t hτa ht.1 (fun u hu => hgap u ⟨hu.1, hu.2.trans ht.2⟩)
  have hl := le_lastVisit (R := fun t => η '' Icc 0 t) hAt
    (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hu => hu.1)).isBounded hv
    ⟨t, ⟨ht0, le_rfl⟩, he⟩
  rw [hc, ← heq] at hl
  exact (not_le.2 huv) hl

/-- A fresh contact of the reverse-visited contained proper arm has gate zero,
including a possible entrance at time zero. -/
theorem lastVisit_gate_zero {W : ℝ → ℝ} {η A b : ℝ → ℂ} {a p q v : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (ha : 0 ≤ a)
    (hAc : ContinuousOn A (Ici 0)) (hAi : InjOn A (Ici 0))
    (hAt : Tendsto (fun v => ‖A v‖) atTop atTop)
    (hrev : IsReverseVisitOrderInf A fun t => η '' Icc 0 t)
    (hv : v ∈ Ici (0 : ℝ)) (hp : η a = A v) (hfresh : η a ∉ η '' Ico 0 a)
    (hb : IsLastVisitArm W η A a p q b) : q = 0 := by
  have hu := lastVisit_eq_of_fresh hAc hAi hAt hη.2.1 hrev ha hv hp hfresh
  have hq : trMap W 0 a q = η a := hb.2.2.2.2.2.2.trans ((congrArg A hu).trans hp.symm)
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, YuanSimpleApprox.trMap_self hW 0 (ofReal_mem_Hbar q), hη.1] at hq
    exact ofReal_eq_zero.1 hq
  · exact fresh_tip_fibre hη hW hW0 ha0 (hηH a ha0) hfresh hq

end InteractingSLE.Sec7.R7InfinityGap
