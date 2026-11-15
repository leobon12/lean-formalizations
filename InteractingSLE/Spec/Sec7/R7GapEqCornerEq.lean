/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerGate

/-!
# Gap equality from first-visit arms and central-side selection

PROVE-R7-GAPEQ. Both real-gate cases use the landed gate theorem. All incoming-tree
avoidance and the face-boundary exclusion are proved here. The only new planar inputs are
`HasGateFace` and, for distinct gates, `HasProperEarlierArm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn

/-- Exact first-exit arm data, supplied by `exists_firstVisit_arm`. The gate may be any real
boundary access to the attained minimum; it is not asserted to be the current driver. -/
def IsFirstVisitArm (W : ℝ → ℝ) (η A : ℝ → ℂ) (r q : ℝ) (α : ℝ → ℂ) : Prop :=
  ContinuousOn α (Icc 0 1) ∧ InjOn α (Icc 0 1) ∧ α 0 = q ∧
    α 1 = fwdMap W r (A 0) ∧ (∀ v ∈ Ioc (0 : ℝ) 1, α v ∈ H) ∧
    trMap W 0 r q = A (firstVisit (fun t => η '' Icc 0 t) A r) ∧
    α '' Ioc 0 1 = fwdMap W r '' (A '' Ico 0 (firstVisit (fun t => η '' Icc 0 t) A r))

/-- A lifted incoming arm and a lifted proper earlier arm meet only at their physical
junction. A real gate cannot lie on the latter, which is entirely in `ℍ`. -/
theorem lifted_arm_third_inter {W : ℝ → ℝ} {r u q : ℝ} {A α β : ℝ → ℂ} {x : ℂ}
    (hW : Continuous W) (hr : 0 ≤ r) (hα0 : α 0 = q)
    (hD : ∀ v ∈ Ico (0 : ℝ) u, A v ∈ H \ fwdHull W r)
    (hβD : ∀ v ∈ Ici (0 : ℝ), β v ∈ H \ fwdHull W r)
    (hi : α '' Ioc 0 1 = fwdMap W r '' (A '' Ico 0 u))
    (hAβ : ∀ v ∈ Ico (0 : ℝ) u, ∀ w ∈ Ici (0 : ℝ), A v = β w → A v = x) :
    α '' Icc 0 1 ∩ (fun t => fwdMap W r (β t)) '' Ici 0 ⊆ {fwdMap W r x} := by
  intro w hw
  have hwβ : w ∈ fwdMap W r '' (β '' Ici 0) := by
    obtain ⟨t, ht, rfl⟩ := hw.2
    exact ⟨β t, ⟨t, ht, rfl⟩, rfl⟩
  rcases eq_or_mem_open_arm hα0 hw.1 with he | hi'
  · obtain ⟨t, ht, htw⟩ := hw.2
    have hH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hβD t ht)
    change fwdMap W r (β t) = w at htw
    rw [htw, he] at hH
    simp [QuantumZipper.H] at hH
  · exact lift_inter_eq hW hr hD hβD hAβ (hi ▸ hi') hwβ

/-- **Old-access gate reduction.** In a chart after both attachment visits, the two incoming
prefixes stay unvisited on the gap. The face selection and proper earlier arm suffice for
both mapped and physical equality, including the shared entrance corner and equal gates.
There is no physical gap-equality premise and no old-boundary-cover premise. -/
theorem gap_eq_of_ordered_firstVisit_arms {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ}
    {C B : Set ℂ} {τ σ s r a b q₁ q₂ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hC : IsOpen C)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r)
    (hra : r < a) (hab : a < b) (hbσ : b < σ) (hq : q₁ ≤ q₂)
    (hAC₁ : BarrierAttachConst η C A₁ τ σ) (hAC₂ : BarrierAttachConst η C A₂ τ σ)
    (he₁ : firstVisit (fun t => η '' Icc 0 t) A₁ r = firstVisit (fun t => η '' Icc 0 t) A₁ a)
    (he₂ : firstVisit (fun t => η '' Icc 0 t) A₂ r = firstVisit (fun t => η '' Icc 0 t) A₂ a)
    (hu₁ : 0 < firstVisit (fun t => η '' Icc 0 t) A₁ r)
    (hu₁1 : firstVisit (fun t => η '' Icc 0 t) A₁ r ≤ 1)
    (hu₂1 : firstVisit (fun t => η '' Icc 0 t) A₂ r ≤ 1)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ r), A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ r), A₂ v ∈ H \ fwdHull W r)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hj : A₁ 0 = A₂ 0)
    (h12 : ∀ v ∈ Ico (0 : ℝ) 1, ∀ w ∈ Ico (0 : ℝ) 1, A₁ v = A₂ w → A₁ v = A₁ 0)
    (hf₁ : A₁ '' Icc 0 1 ⊆ frontier C) (hf₂ : A₂ '' Icc 0 1 ⊆ frontier C)
    (havoid : ∀ t, r ≤ t → η t ∉ B)
    (hface : HasGateFace W C B (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) r)
    (hproper : q₁ < q₂ → HasProperEarlierArm η A₁ A₂ σ)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (ha : a ∈ closure {t | r < t ∧ η t ∈ C}) (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  obtain ⟨hc₁, hi₁, hz₁, hez₁, hH₁, -, himg₁⟩ := ha₁
  obtain ⟨hc₂, hi₂, hz₂, hez₂, hH₂, -, himg₂⟩ := ha₂
  have hr : 0 ≤ r := hτ0.trans hτr
  have hez₂' : a₂ 1 = fwdMap W r (A₁ 0) := by rw [hez₂, ← hj]
  have hinter := lifted_arms_inter hW hr hz₁ hz₂ hH₁ hD₁ hD₂ himg₁ himg₂
    (fun v hv w hw => h12 v ⟨hv.1, hv.2.trans_le hu₁1⟩ w ⟨hw.1, hw.2.trans_le hu₂1⟩)
  have hbd := gate_boundary_avoids_pocket hW hW0 hr hC hz₁ hz₂ hD₁ hD₂ himg₁ himg₂
    ((image_mono (show Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ r) ⊆ Icc 0 1
      from fun _ hv => ⟨hv.1, hv.2.le.trans hu₁1⟩)).trans hf₁)
    ((image_mono (show Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ r) ⊆ Icc 0 1
      from fun _ hv => ⟨hv.1, hv.2.le.trans hu₂1⟩)).trans hf₂)
  have hav₁ := ownFuture_avoids_firstVisit_arm hη hW hW0 hτ0 hτr hra.le hbσ hAC₁ hgap he₁ hu₁1 hD₁ himg₁
  have hav₂ := ownFuture_avoids_firstVisit_arm hη hW hW0 hτ0 hτr hra.le hbσ hAC₂ hgap he₂ hu₂1 hD₂ himg₂
  rcases lt_or_eq_of_le hq with hq' | hq'
  · have hinter' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {fwdMap W r (A₁ 0)} := by
      intro w hw
      rcases hinter hw with he | he
      · have hreal : w.im = 0 := by rw [he]; simp
        have hEq : (q₁ : ℂ) = q₂ := he.symm.trans (arm_real hz₂ hH₂ hw.2 hreal)
        exact False.elim (hq'.ne (Complex.ofReal_injective hEq))
      · exact he
    obtain ⟨hΓ, hΓH⟩ := isJordanCurve_faceBoundary hq' hc₁ hc₂ hi₁ hi₂ hz₁ hz₂ hez₁ hez₂' hH₁ hH₂ hinter'
    obtain ⟨hfr, ⟨p, hp, hpC⟩, hbulge⟩ := hface
    obtain ⟨hFC, -⟩ := image_innerSide_eq_component hη hW hW0 hr hC hΓ hΓH hfr hbd hp hpC
    have h11 := ownFuture_mem_face_of_forbidden_bulges hη hW hW0 hr havoid hbulge
    obtain ⟨β, hβc, hβi, hβ0, hβH, hβt, hβfresh, h13, h23⟩ := hproper hq'
    have hβD := proper_prefix_domain hη hr hβc hβH
      (fun t ht => hβfresh t ht.1 (ht.2.trans_lt (hra.trans (hab.trans hbσ))))
      (hβ0 ▸ hD₁ 0 ⟨le_rfl, hu₁⟩)
    obtain ⟨hβgc, hβgi, hβgH, hβgt⟩ := thirdArm_props hW hW0 hr hβc hβi hβD hβt
    have h13' := lifted_arm_third_inter hW hr hz₁ hD₁ hβD himg₁
      (fun v hv => h13 v ⟨hv.1, hv.2.le.trans hu₁1⟩)
    have h23' := lifted_arm_third_inter hW hr hz₂ hD₂ hβD himg₂
      (fun v hv => h23 v ⟨hv.1, hv.2.le.trans hu₂1⟩)
    apply ownFuture_gap_eq_of_face hη hW hW0 hC hq' hc₁ hc₂ hi₁ hi₂ hz₁ hz₂ hez₁ hez₂'
      hH₁ hH₂ hinter' hβgc hβgi (by rw [hβ0]) hβgH hβgt h13' h23' hs hsr hra hab
      h11 (by rintro _ ⟨w, hw, rfl⟩; exact hFC hw) hgap ?_ ha hb
    intro t ht htree
    rcases htree with (ht₁ | ht₂) | ht₃
    · exact hav₁ t ht ht₁
    · exact hav₂ t ht ht₂
    · have ht₃' : trMap W r t 0 ∈ fwdMap W r '' (β '' Ici 0) := by
        obtain ⟨v, hv, he⟩ := ht₃
        exact ⟨β v, ⟨v, hv, rfl⟩, he⟩
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.le.trans ht.1) hβD
        (hβfresh t (hr.trans (hra.le.trans ht.1)) (ht.2.trans_lt hbσ)) ht₃'
  · have hΓeq : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂ =
        a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 := by
      apply union_eq_left.2
      rintro _ ⟨x, hx, rfl⟩
      have hxq : x = q₁ := le_antisymm (hq' ▸ hx.2) hx.1
      exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hz₁.trans (congrArg ofReal hxq.symm)⟩
    have hz₂' : a₂ 0 = q₁ := by rw [hz₂, ← hq']
    have hΓ : LQGMetric.JordanMap.IsJordanCurve (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) :=
      Sec7.isJordanCurve_image_union hc₁ hc₂ hi₁ hi₂ (hz₁.trans hz₂'.symm)
        (hez₁.trans hez₂'.symm) (by rw [hz₁, hez₁]; exact hinter)
    have hΓH := union_subset (image_arm_subset_Hbar hz₁ hH₁) (image_arm_subset_Hbar hz₂ hH₂)
    rw [hΓeq] at hface hbd
    obtain ⟨hfr, ⟨p, hp, hpC⟩, hbulge⟩ := hface
    obtain ⟨hFC, -⟩ := image_innerSide_eq_component hη hW hW0 hr hC hΓ hΓH hfr hbd hp hpC
    apply ownFuture_gap_eq_of_face_eq hη hW hW0 hC (isCompact_of_isJordanCurve hΓ).isClosed
      hz₁ hz₂' hs hsr hra.le (hra.trans hab).le
      (ownFuture_mem_face_of_forbidden_bulges hη hW hW0 hr havoid hbulge)
      (by rintro _ ⟨w, hw, rfl⟩; exact hFC hw) (hgap a ⟨le_rfl, hab.le⟩)
      (hgap b ⟨hab.le, le_rfl⟩) ?_ ha hb
    intro t ht htree
    have ht' : t ∈ Icc a b := by
      rcases Set.mem_insert_iff.1 ht with rfl | ht
      · exact ⟨le_rfl, hab.le⟩
      · have he : t = b := Set.mem_singleton_iff.1 ht
        subst t
        exact ⟨hab.le, le_rfl⟩
    exact htree.elim (hav₁ t ht') (hav₂ t ht')

end InteractingSLE.Sec7.R7GapEqCorner
