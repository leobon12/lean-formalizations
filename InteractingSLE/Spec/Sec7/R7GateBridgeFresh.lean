/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeFreshGate

/-!
# Fresh gap equality for the two current incoming arms

PROVE-R7-GAPEQ. Attachment constancy excludes all incoming prefixes, the earlier proper
arm excludes the third branch, and central-face selection supplies the two face conditions.
A fresh contact on a reverse-visited contained side has gate zero, including time zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6 PocketJordan R7StopIn R7GapEqCorner

/-- A fresh contact with a reverse-visited side has gate zero in every first-visit lift.
At time zero this is the identity map; at positive times it is the landed fresh-tip theorem. -/
theorem firstVisit_gate_zero {W : ℝ → ℝ} {η A α : ℝ → ℂ} {a q v : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (ha : 0 ≤ a) (hAi : InjOn A (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder A fun t => η '' Icc 0 t)
    (hv : v ∈ Icc (0 : ℝ) 1) (hp : η a = A v) (hfresh : η a ∉ η '' Ico 0 a)
    (hα : IsFirstVisitArm W η A a q α) : q = 0 := by
  have hu : firstVisit (fun t => η '' Icc 0 t) A a = v :=
    R16.firstVisitParam_eq_of_fresh hAi hrev ha hv hp hfresh
  have hq : trMap W 0 a q = η a := hα.2.2.2.2.2.1.trans ((congrArg A hu).trans hp.symm)
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, YuanSimpleApprox.trMap_self hW 0 (ofReal_mem_Hbar q), hη.1] at hq
    exact ofReal_eq_zero.1 hq
  · exact fresh_tip_fibre hη hW hW0 ha0 (hηH a ha0) hfresh hq

/-- **Fresh gap equality in the current chart**, with either ordered gate equal to zero.
The other arm may be outer and its suffix need not be swallowed. -/
theorem gap_eq_of_ordered_firstVisit_arms_of_gate {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ}
    {C B : Set ℂ} {τ σ s a b q₁ q₂ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hC : IsCfPocket C A₁ A₂)
    (hτ0 : 0 ≤ τ) (hτa : τ ≤ a) (hs : 0 ≤ s) (hsa : s ≤ a)
    (hab : a < b) (hbσ : b < σ) (hq : q₁ ≤ q₂)
    (hAC₁ : BarrierAttachConst η C A₁ τ σ) (hAC₂ : BarrierAttachConst η C A₂ τ σ)
    (hu₁ : 0 < firstVisit (fun t => η '' Icc 0 t) A₁ a)
    (hu₁1 : firstVisit (fun t => η '' Icc 0 t) A₁ a ≤ 1)
    (hu₂1 : firstVisit (fun t => η '' Icc 0 t) A₂ a ≤ 1)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ a), A₁ v ∈ H \ fwdHull W a)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ a), A₂ v ∈ H \ fwdHull W a)
    (ha₁ : IsFirstVisitArm W η A₁ a q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ a q₂ a₂)
    (havoid : ∀ t, a ≤ t → η t ∉ B)
    (hface : HasGateFace W C B (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) a)
    (hproper : q₁ < q₂ → HasProperEarlierArm η A₁ A₂ σ)
    (hgate : q₁ = 0 ∨ q₂ = 0) (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have ha0 := hτ0.trans hτa
  obtain ⟨hΓ, hΓH⟩ := firstVisit_face_jordan hW ha0 hC hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
  rw [min_eq_left hq, max_eq_right hq] at hΓ hΓH
  obtain ⟨hc₁, hi₁, hz₁, hez₁, hH₁, -, himg₁⟩ := ha₁
  obtain ⟨hc₂, hi₂, hz₂, hez₂, hH₂, -, himg₂⟩ := ha₂
  have hez₂' : a₂ 1 = fwdMap W a (A₁ 0) := by rw [hez₂, hC.junction]
  have hinter := lifted_arms_inter hW ha0 hz₁ hz₂ hH₁ hD₁ hD₂ himg₁ himg₂
    (fun v hv w hw => cfPocket_arms_eq hC ⟨hv.1, hv.2.trans_le hu₁1⟩ ⟨hw.1, hw.2.trans_le hu₂1⟩)
  have hbd := gate_boundary_avoids_pocket hW hW0 ha0 hC.isOpen hz₁ hz₂ hD₁ hD₂ himg₁ himg₂
    ((image_mono (show Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ a) ⊆ Icc 0 1
      from fun _ hv => ⟨hv.1, hv.2.le.trans hu₁1⟩)).trans (hC.frontier_eq.symm ▸ subset_union_left))
    ((image_mono (show Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ a) ⊆ Icc 0 1
      from fun _ hv => ⟨hv.1, hv.2.le.trans hu₂1⟩)).trans (hC.frontier_eq.symm ▸ subset_union_right))
  obtain ⟨hfr, ⟨p, hp, hpC⟩, hbulge⟩ := hface
  obtain ⟨hFC, -⟩ := image_innerSide_eq_component hη hW hW0 ha0 hC.isOpen hΓ hΓH hfr hbd hp hpC
  have h11 := ownFuture_mem_face_of_forbidden_bulges hη hW hW0 ha0 havoid hbulge
  have hav₁ := ownFuture_avoids_firstVisit_arm hη hW hW0 hτ0 hτa le_rfl hbσ hAC₁ hgap rfl hu₁1 hD₁ himg₁
  have hav₂ := ownFuture_avoids_firstVisit_arm hη hW hW0 hτ0 hτa le_rfl hbσ hAC₂ hgap rfl hu₂1 hD₂ himg₂
  rcases lt_or_eq_of_le hq with hq' | hq'
  · have hinter' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {fwdMap W a (A₁ 0)} := by
      intro w hw
      rcases hinter hw with he | he
      · have hreal : w.im = 0 := by rw [he]; simp
        exact False.elim (hq'.ne (ofReal_injective (he.symm.trans (arm_real hz₂ hH₂ hw.2 hreal))))
      · exact he
    obtain ⟨β, hβc, hβi, hβ0, hβH, hβt, hβfresh, h13, h23⟩ := hproper hq'
    have hβD := proper_prefix_domain hη ha0 hβc hβH
      (fun t ht => hβfresh t ht.1 (ht.2.trans_lt (hab.trans hbσ)))
      (hβ0 ▸ hD₁ 0 ⟨le_rfl, hu₁⟩)
    obtain ⟨hβgc, hβgi, hβgH, hβgt⟩ := thirdArm_props hW hW0 ha0 hβc hβi hβD hβt
    have h13' := lifted_arm_third_inter hW ha0 hz₁ hD₁ hβD himg₁
      (fun v hv => h13 v ⟨hv.1, hv.2.le.trans hu₁1⟩)
    have h23' := lifted_arm_third_inter hW ha0 hz₂ hD₂ hβD himg₂
      (fun v hv => h23 v ⟨hv.1, hv.2.le.trans hu₂1⟩)
    apply ownFuture_gap_eq_of_face_of_gate hη hW hW0 hC.isOpen hq' hc₁ hc₂ hi₁ hi₂ hz₁ hz₂ hez₁ hez₂'
      hH₁ hH₂ hinter' hβgc hβgi (by rw [hβ0]) hβgH hβgt h13' h23' hs hsa hab h11
      (by rintro _ ⟨w, hw, rfl⟩; exact hFC hw) hgate hgap ?_ hb
    intro t ht htree
    rcases htree with (ht₁ | ht₂) | ht₃
    · exact hav₁ t ht ht₁
    · exact hav₂ t ht ht₂
    · have ht₃' : trMap W a t 0 ∈ fwdMap W a '' (β '' Ici 0) := by
        obtain ⟨v, hv, he⟩ := ht₃
        exact ⟨β v, ⟨v, hv, rfl⟩, he⟩
      exact ownFuture_notMem_lift hη hW hW0 ha0 ht.1 hβD
        (hβfresh t (ha0.trans ht.1) (ht.2.trans_lt hbσ)) ht₃'
  · have hq0 : q₁ = 0 := hgate.elim id (fun he => hq'.trans he)
    have hq20 : q₂ = 0 := hq'.symm.trans hq0
    have hΓeq : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂ =
        a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 := by
      apply union_eq_left.2
      rintro _ ⟨x, hx, rfl⟩
      have hxq : x = q₁ := le_antisymm (hq' ▸ hx.2) hx.1
      exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hz₁.trans (congrArg ofReal hxq.symm)⟩
    rw [hΓeq] at hΓ h11 hFC
    apply ownFuture_gap_eq_of_face_eq_of_gate hη hW hW0 hC.isOpen (isCompact_of_isJordanCurve hΓ).isClosed
      (hz₁.trans (congrArg ofReal hq0)) (hz₂.trans (congrArg ofReal hq20)) hs hsa hab.le h11
      (by rintro _ ⟨w, hw, rfl⟩; exact hFC hw) (hgap b ⟨hab.le, le_rfl⟩) ?_ hb
    exact fun he => he.elim (hav₁ b ⟨hab.le, le_rfl⟩) (hav₂ b ⟨hab.le, le_rfl⟩)

end InteractingSLE.Sec7.R7GateBridge
