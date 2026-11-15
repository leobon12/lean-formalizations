/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeProper

/-!
# The gate face automatically has the required target access

PROVE-R7-GAPEQ. The same two first-visit arms used for gap separation form a Jordan curve
after ordering their real gates. Their common interior endpoint lands at the target. Thus
`HasGateFace` supplies `HasTargetFace`; an independent target-face hypothesis is unnecessary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6 PocketJordan R7GapEqCorner

/-- The half-open side intersection property from the landed two-arc pocket topology.
The entrance at parameter one is deliberately excluded. -/
theorem cfPocket_arms_eq {C : Set ℂ} {A₁ A₂ : ℝ → ℂ} (hC : IsCfPocket C A₁ A₂)
    {v w : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) (hw : w ∈ Ico (0 : ℝ) 1)
    (he : A₁ v = A₂ w) : A₁ v = A₁ 0 := by
  rcases eq_or_lt_of_le hv.1 with h0 | h0
  · rw [← h0]
  rcases eq_or_lt_of_le hw.1 with h0' | h0'
  · rw [he, ← h0', hC.junction]
  exact False.elim (hC.sides v ⟨h0, hv.2⟩ w ⟨h0', hw.2⟩ he)

/-- The two first-visit arms form a Jordan face in `Hbar`, with gates ordered by `min/max`.
This uses only the prefix domains and two-side topology, allowing unvisited outer suffixes. -/
theorem firstVisit_face_jordan {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ}
    {C : Set ℂ} {r q₁ q₂ : ℝ} (hW : Continuous W) (hr : 0 ≤ r)
    (hC : IsCfPocket C A₁ A₂)
    (hu₁1 : firstVisit (fun t => η '' Icc 0 t) A₁ r ≤ 1)
    (hu₂1 : firstVisit (fun t => η '' Icc 0 t) A₂ r ≤ 1)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ r), A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ r), A₂ v ∈ H \ fwdHull W r)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂) :
    LQGMetric.JordanMap.IsJordanCurve
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) ∧
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂) ⊆ Hbar := by
  obtain ⟨hc₁, hi₁, hz₁, hez₁, hH₁, -, himg₁⟩ := ha₁
  obtain ⟨hc₂, hi₂, hz₂, hez₂, hH₂, -, himg₂⟩ := ha₂
  have hez₂' : a₂ 1 = fwdMap W r (A₁ 0) := by rw [hez₂, hC.junction]
  have hinter := lifted_arms_inter hW hr hz₁ hz₂ hH₁ hD₁ hD₂ himg₁ himg₂
    (fun v hv w hw => cfPocket_arms_eq hC ⟨hv.1, hv.2.trans_le hu₁1⟩ ⟨hw.1, hw.2.trans_le hu₂1⟩)
  have hinter' : q₁ ≠ q₂ → a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {fwdMap W r (A₁ 0)} := by
    intro hq w hw
    rcases hinter hw with he | he
    · have hreal : w.im = 0 := by rw [he]; simp
      exact False.elim (hq (ofReal_injective (he.symm.trans (arm_real hz₂ hH₂ hw.2 hreal))))
    · exact he
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · simpa only [min_eq_left hq.le, max_eq_right hq.le] using
      isJordanCurve_faceBoundary hq hc₁ hc₂ hi₁ hi₂ hz₁ hz₂ hez₁ hez₂' hH₁ hH₂ (hinter' hq.ne)
  · have hΓeq : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂) =
        a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 := by
      rw [← hq, min_self, max_self]
      apply union_eq_left.2
      rintro _ ⟨x, hx, rfl⟩
      have hxq : x = q₁ := le_antisymm hx.2 hx.1
      exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hz₁.trans (congrArg ofReal hxq.symm)⟩
    rw [hΓeq]
    exact ⟨Sec7.isJordanCurve_image_union hc₁ hc₂ hi₁ hi₂
      (by rw [hz₁, hz₂, hq]) (hez₁.trans hez₂'.symm) (by rw [hz₁, hez₁]; exact hinter),
      union_subset (image_arm_subset_Hbar hz₁ hH₁) (image_arm_subset_Hbar hz₂ hH₂)⟩
  · have h12 : a₂ '' Icc 0 1 ∩ a₁ '' Icc 0 1 ⊆ {fwdMap W r (A₁ 0)} :=
      fun _ hw => hinter' hq.ne.symm ⟨hw.2, hw.1⟩
    have hJ := isJordanCurve_faceBoundary hq hc₂ hc₁ hi₂ hi₁ hz₂ hz₁ hez₂' hez₁ hH₂ hH₁ h12
    rwa [min_eq_right hq.le, max_eq_left hq.le,
      union_comm (a₁ '' Icc 0 1) (a₂ '' Icc 0 1)]

/-- A selected gate face is already a target face. Its boundary maps outside the pocket by
the landed prefix argument, and its common lifted junction gives the required target access. -/
theorem hasTargetFace_of_firstVisit_arms {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ}
    {C B : Set ℂ} {r q₁ q₂ : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hC : IsCfPocket C A₁ A₂)
    (hu₁ : 0 < firstVisit (fun t => η '' Icc 0 t) A₁ r)
    (hu₁1 : firstVisit (fun t => η '' Icc 0 t) A₁ r ≤ 1)
    (hu₂1 : firstVisit (fun t => η '' Icc 0 t) A₂ r ≤ 1)
    (hD₁ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ r), A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ r), A₂ v ∈ H \ fwdHull W r)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hface : HasGateFace W C B
      (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) r) :
    HasTargetFace W C B (A₁ 0) r := by
  obtain ⟨hΓ, hΓH⟩ := firstVisit_face_jordan hW hr hC hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
  obtain ⟨-, -, hz₁, hez₁, hH₁, -, himg₁⟩ := ha₁
  obtain ⟨-, -, hz₂, -, -, -, himg₂⟩ := ha₂
  have hf₁ : A₁ '' Icc 0 1 ⊆ frontier C := hC.frontier_eq.symm ▸ subset_union_left
  have hf₂ : A₂ '' Icc 0 1 ⊆ frontier C := hC.frontier_eq.symm ▸ subset_union_right
  have hbd := gate_boundary_avoids_pocket hW hW0 hr hC.isOpen hz₁ hz₂ hD₁ hD₂ himg₁ himg₂
    ((image_mono (show Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₁ r) ⊆ Icc 0 1
      from fun _ hv => ⟨hv.1, hv.2.le.trans hu₁1⟩)).trans hf₁)
    ((image_mono (show Ico (0 : ℝ) (firstVisit (fun t => η '' Icc 0 t) A₂ r) ⊆ Icc 0 1
      from fun _ hv => ⟨hv.1, hv.2.le.trans hu₂1⟩)).trans hf₂)
  obtain ⟨hfr, ⟨p, hp, hpC⟩, hbulge⟩ := hface
  refine ⟨_, p, a₁ 1, hΓ, hΓH, hp, hpC, hfr, ?_,
    Or.inl (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩), hH₁ 1 ⟨zero_lt_one, le_rfl⟩, ?_, hbulge⟩
  · rintro w (hw | ⟨x, -, rfl⟩) hwH
    · exact hbd w (Or.inl hw) hwH
    · simp [QuantumZipper.H] at hwH
  · rw [hez₁, trMap_zero_fwdMap hW hW0 hr (hD₁ 0 ⟨le_rfl, hu₁⟩)]

end InteractingSLE.Sec7.R7GateBridge
