/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerFace

/-!
# An earlier chart after both old attachment visits

PROVE-R7-GAPEQ. Oldness of the physical gap start makes each attained attachment an
earlier visit, even for an outer arm. A common intermediate chart preserves both minima.
Attachment constancy then excludes its lifted incoming prefixes throughout the gap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn

/-- At an old start, the attained attachment has itself been visited strictly earlier.
No reverse order, attachment continuity or simplicity is needed. -/
theorem firstVisit_attained_before_old_start {η A : ℝ → ℂ} {τ a : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hAc : ContinuousOn A (Icc 0 1))
    (hτ0 : 0 ≤ τ) (hτa : τ ≤ a) (hτ : η τ = A 1)
    (hold : η a ∈ η '' Ico 0 a) :
    ∃ t ∈ Ico (0 : ℝ) a, η t = A (firstVisit (fun s => η '' Icc 0 s) A a) := by
  obtain ⟨t, ht, he⟩ := (firstVisit_mem (R := fun s => η '' Icc 0 s) hAc
    (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1)).isClosed
    ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτa⟩, hτ⟩).2
  rcases eq_or_lt_of_le ht.2 with hta | hta
  · obtain ⟨t', ht', he'⟩ := hold
    exact ⟨t', ht', he'.trans (hta ▸ he)⟩
  · exact ⟨t, ⟨ht.1, hta⟩, he⟩

/-- Choose one earlier chart after the visits of both attachment minima. This applies equally
to contained and outer arms and supplies the old-start chart used by the gate lemma. -/
theorem exists_earlier_chart_firstVisits {η A₁ A₂ : ℝ → ℂ} {τ s a : ℝ}
    (hη : ContinuousOn η (Ici 0))
    (hA₁ : ContinuousOn A₁ (Icc 0 1)) (hA₂ : ContinuousOn A₂ (Icc 0 1))
    (hτ0 : 0 ≤ τ) (hτa : τ < a) (hsa : s < a)
    (hτ₁ : η τ = A₁ 1) (hτ₂ : η τ = A₂ 1) (hold : η a ∈ η '' Ico 0 a) :
    ∃ r : ℝ, τ ≤ r ∧ s ≤ r ∧ r < a ∧
      firstVisit (fun t => η '' Icc 0 t) A₁ r = firstVisit (fun t => η '' Icc 0 t) A₁ a ∧
      firstVisit (fun t => η '' Icc 0 t) A₂ r = firstVisit (fun t => η '' Icc 0 t) A₂ a := by
  obtain ⟨t₁, ht₁, he₁⟩ := firstVisit_attained_before_old_start hη hA₁ hτ0 hτa.le hτ₁ hold
  obtain ⟨t₂, ht₂, he₂⟩ := firstVisit_attained_before_old_start hη hA₂ hτ0 hτa.le hτ₂ hold
  let M := max (max τ s) (max t₁ t₂)
  let r := (M + a) / 2
  have hMa : M < a := max_lt (max_lt hτa hsa) (max_lt ht₁.2 ht₂.2)
  have hMr : M ≤ r := by dsimp [r]; linarith
  have hra : r < a := by dsimp [r]; linarith
  have hτr : τ ≤ r := ((le_max_left _ _).trans (le_max_left _ _)).trans hMr
  have hsr : s ≤ r := ((le_max_right _ _).trans (le_max_left _ _)).trans hMr
  have ht₁r : t₁ ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hMr
  have ht₂r : t₂ ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hMr
  have heq : ∀ {A : ℝ → ℂ}, ContinuousOn A (Icc 0 1) → η τ = A 1 →
      ∀ {t : ℝ}, t ∈ Ico (0 : ℝ) a → t ≤ r →
      η t = A (firstVisit (fun v => η '' Icc 0 v) A a) →
      firstVisit (fun v => η '' Icc 0 v) A r = firstVisit (fun v => η '' Icc 0 v) A a := by
    intro A hAc hτ t ht htr he
    exact firstVisit_eq_of_visited hAc monotone_image_Icc hra.le
      (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1)).isClosed
      ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτa.le⟩, hτ⟩ ⟨t, ⟨ht.1, htr⟩, he⟩
  exact ⟨r, hτr, hsr, hra, heq hA₁ hτ₁ ht₁ ht₁r he₁, heq hA₂ hτ₂ ht₂ ht₂r he₂⟩

/-- A fixed-chart incoming arm whose minimum agrees with the gap-start minimum is avoided
throughout the gap. Only the physical minimum and inverse-map identity are used. -/
theorem ownFuture_avoids_firstVisit_arm {W : ℝ → ℝ} {η A α : ℝ → ℂ}
    {C : Set ℂ} {τ σ r a b : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hra : r ≤ a) (hbσ : b < σ)
    (hAC : BarrierAttachConst η C A τ σ)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (heq : firstVisit (fun t => η '' Icc 0 t) A r = firstVisit (fun t => η '' Icc 0 t) A a)
    (hu1 : firstVisit (fun t => η '' Icc 0 t) A r ≤ 1)
    (hD : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A r),
      A v ∈ H \ fwdHull W r)
    (himage : α '' Ioc 0 1 = fwdMap W r ''
      (A '' Ico 0 (firstVisit (fun t => η '' Icc 0 t) A r))) :
    ∀ t ∈ Icc a b, trMap W r t 0 ∉ α '' Ioc 0 1 := by
  intro t ht
  rw [himage]
  apply ownFuture_notMem_lift hη hW hW0 (hτ0.trans hτr) (hra.trans ht.1) hD
  intro v hv
  apply avoid_prefix_of_attachment_const hAC (hτr.trans hra) hbσ hgap t ht v
    ⟨hv.1, hv.2.le.trans hu1⟩
  · exact heq ▸ hv.2
  · exact hτ0.trans (hτr.trans (hra.trans ht.1))

end InteractingSLE.Sec7.R7GapEqCorner
