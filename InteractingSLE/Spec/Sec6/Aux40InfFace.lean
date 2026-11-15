/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40InfErase
import InteractingSLE.Spec.Sec6.Aux40InfJordan

/-!
# The central face of the pocket at infinity

Specification §6.2, **Aux.** lemma 36, geometric part ((RG3), `source/spec/p193-240.md` L57: "If
`x₀` is the original target, its image is instead on the real circle. Use the Jordan-face
description directly. When `q₁ ≠ q₂`, the two arcs together with the real-circle interval between
`q₁, q₂` which avoids that target form a Jordan boundary. When `q₁ = q₂`, the two arcs themselves
form a Jordan boundary"), for the pocket of `IsReversePocketInf`.

In the chart at `s ≥ τ` the unvisited prefixes lift to proper arcs from the gates `q_i` to `∞`.
After the real Möbius map `ψ_p` (`p` left of both gates) they become the compact arcs of
`Aux39InfArm`, and the face `F_s = {w ∈ ℍ : f̄_s(w) ∈ C}` is `ψ_p⁻¹(innerSide Γ)` for a Jordan curve
`Γ ⊆ ℍ̄` (`Aux39InfPocket`'s identifications).

## Main results (namespace `IsReversePocketInf`)

* `exists_face`: the face at infinity in the `ψ_p`-picture;
* `isConformalBijection_face`: `f̄_s ∘ ψ_p⁻¹` maps the inner side of `Γ` conformally onto
  `C ∩ D_s`;
* `isPreconnected_inter_domain`, `not_isBounded_inter_domain`: `C ∩ D_s` is preconnected and
  unbounded.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec6

namespace IsReversePocketInf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}

/-- **The central face at infinity at `s ≥ τ`** (Aux. lemma 36, geometric part; (RG3)): for every
real `p` to the left of both gates, `ζ ∈ ℍ` is mapped by `f̄_s ∘ ψ_p⁻¹` into `C` iff it is on the
inner side of a Jordan curve `Γ ⊆ ℍ̄` (the two compactified lifted prefixes, and for distinct gates
the real segment between their images). -/
theorem exists_face (hP : IsReversePocketInf W η C α₁ α₂ τ) {s : ℝ} (hτs : τ ≤ s) :
    ∃ P : ℝ, ∀ p < P, ∃ Γ : Set ℂ, LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧
      ∀ ζ ∈ H, (trMap W 0 s (psiMapInv p ζ) ∈ C ↔ ζ ∈ innerSide Γ) := by
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  obtain ⟨hu₁, -, hK₁, hD₁⟩ := hP.chart hτs (Or.inl rfl)
  obtain ⟨hu₂, -, hK₂, hD₂⟩ := hP.chart hτs (Or.inr rfl)
  obtain ⟨q₁, -, hlim₁⟩ := exists_tendsto_lift_right hη hW hW0 hs0
    (hP.cont₁.mono fun t ht => hu₁.trans ht.1) (fun t ht => hD₁ t ht.1) (hK₁ _ ⟨hu₁, le_rfl⟩)
  obtain ⟨q₂, -, hlim₂⟩ := exists_tendsto_lift_right hη hW hW0 hs0
    (hP.cont₂.mono fun t ht => hu₂.trans ht.1) (fun t ht => hD₂ t ht.1) (hK₂ _ ⟨hu₂, le_rfl⟩)
  refine ⟨min q₁ q₂, fun p hp => ?_⟩
  have hpq₁ : p < q₁ := hp.trans_le (min_le_left _ _)
  have hpq₂ : p < q₂ := hp.trans_le (min_le_right _ _)
  obtain ⟨b₁, hb₁c, hb₁i, hb₁0, hb₁1, hb₁H, hb₁img⟩ := exists_psiArm hW hW0 hs0
    (hP.cont₁.mono (Ici_subset_Ici.2 hu₁)) (hP.inj₁.mono (Ici_subset_Ici.2 hu₁)) hD₁ hP.tendsto₁
    hlim₁ hpq₁
  obtain ⟨b₂, hb₂c, hb₂i, hb₂0, hb₂1, hb₂H, hb₂img⟩ := exists_psiArm hW hW0 hs0
    (hP.cont₂.mono (Ici_subset_Ici.2 hu₂)) (hP.inj₂.mono (Ici_subset_Ici.2 hu₂)) hD₂ hP.tendsto₂
    hlim₂ hpq₂
  have h12 := hP.disjoint_prefixes hu₁ hu₂
  have hdisj : ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1 := by
    intro w hw₁ hw₂
    rw [hb₁img] at hw₁; rw [hb₂img] at hw₂
    obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hw₁
    obtain ⟨_, ⟨_, ⟨v', hv', rfl⟩, rfl⟩, he⟩ := hw₂
    have h1 := QuantumZipper.FwdHolo.injOn_fwdMap hW hs0 (hD₂ v' hv') (hD₁ v hv)
      (psiMap_injective he)
    exact h12 v hv v' hv' h1.symm
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · obtain ⟨hlt, hneg⟩ := psiMap_ofReal_lt hpq₁ hq
    have h : IsArcPairInf (-(q₁ - p)⁻¹) (-(q₂ - p)⁻¹) b₁ b₂ :=
      ⟨hlt, hneg, hb₁c, hb₂c, hb₁i, hb₂i, hb₁0, hb₂0, hb₁1, hb₂1, hb₁H, hb₂H, fun w hw => by
        rcases psiArms_inter hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hdisj hw.1 hw.2 with h' | ⟨h1, h2⟩
        · exact h'
        · exact absurd (ofReal_injective (h1.symm.trans h2)) hlt.ne⟩
    exact ⟨_, h.isJordanCurve_face.1, h.isJordanCurve_face.2, fun ζ hζ =>
      trMap_psiMapInv_mem_iff hη hW hW0 hs0 hP.isOpen hP.farReal hu₁ hu₂ hP.frontier_eq hD₁ hD₂
        hK₁ hK₂ h hpq₂ rfl hb₁img hb₂img hζ⟩
  · subst hq
    have hx0 : -(q₁ - p)⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 (by linarith))
    have hinter : b₁ '' Icc 0 1 ∩ b₂ '' Icc 0 1 ⊆ {((-(q₁ - p)⁻¹ : ℝ) : ℂ), 0} := fun w hw => by
      rcases psiArms_inter hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hdisj hw.1 hw.2 with h' | ⟨h1, -⟩
      · exact Or.inr h'
      · exact Or.inl h1
    refine ⟨b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1, Sec7.isJordanCurve_image_union hb₁c hb₂c hb₁i hb₂i
      (by rw [hb₁0, hb₂0]) (by rw [hb₁1, hb₂1]) (by rw [hb₁0, hb₁1]; exact hinter),
      union_subset (image_arcInf_subset_Hbar hb₁0 hb₁1 hb₁H)
        (image_arcInf_subset_Hbar hb₂0 hb₂1 hb₂H), fun ζ hζ => ?_⟩
    exact trMap_psiMapInv_mem_iff_eq hη hW hW0 hs0 hP.isOpen hP.farReal hu₁ hu₂ hP.frontier_eq
      hD₁ hD₂ hK₁ hK₂ hx0 hb₁c hb₂c hb₁i hb₂i hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hinter hpq₁ rfl
      hb₁img hb₂img hζ
  · obtain ⟨hlt, hneg⟩ := psiMap_ofReal_lt hpq₂ hq
    have h : IsArcPairInf (-(q₂ - p)⁻¹) (-(q₁ - p)⁻¹) b₂ b₁ :=
      ⟨hlt, hneg, hb₂c, hb₁c, hb₂i, hb₁i, hb₂0, hb₁0, hb₂1, hb₁1, hb₂H, hb₁H, fun w hw => by
        rcases psiArms_inter hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hdisj hw.2 hw.1 with h' | ⟨h1, h2⟩
        · exact h'
        · exact absurd (ofReal_injective (h2.symm.trans h1)) hlt.ne⟩
    exact ⟨_, h.isJordanCurve_face.1, h.isJordanCurve_face.2, fun ζ hζ =>
      trMap_psiMapInv_mem_iff hη hW hW0 hs0 hP.isOpen hP.farReal hu₂ hu₁
        (by rw [hP.frontier_eq, union_comm]) hD₂ hD₁ hK₂ hK₁ h hpq₁ rfl hb₂img hb₁img hζ⟩

/-- `f̄_s ∘ ψ_p⁻¹` maps the inner side `F` of the face curve conformally onto `C ∩ D_s`. -/
theorem isConformalBijection_face (hP : IsReversePocketInf W η C α₁ α₂ τ) {s : ℝ} (hs0 : 0 ≤ s)
    {p : ℝ} {Γ : Set ℂ} (hΓJ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hiff : ∀ ζ ∈ H, (trMap W 0 s (psiMapInv p ζ) ∈ C ↔ ζ ∈ innerSide Γ)) :
    IsConformalBijection (fun ζ => trMap W 0 s (psiMapInv p ζ)) (innerSide Γ)
      (C ∩ (H \ fwdHull W s)) := by
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have hFH : innerSide Γ ⊆ H := innerSide_subset_H hΓJ hΓH
  have hfeq : ∀ w ∈ H, trMap W 0 s w = fwdMapInv W s w := fun w hw => by
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs0 hw, YuanSimpleApprox.shiftDrive_zero_eq hW0,
      sub_zero]
  have himgH := trMap_zero_image_H hW hW0 hs0
  have hψH : ∀ ζ ∈ H, psiMapInv p ζ ∈ H := fun ζ hζ => psiMapInv_mem_H hζ
  refine ⟨fun ζ hζ => ?_, fun ζ hζ => ⟨(hiff ζ (hFH hζ)).2 hζ, himgH ▸ ⟨_, hψH ζ (hFH hζ), rfl⟩⟩,
    fun ζ hζ ζ' hζ' h => ?_, fun z hz => ?_⟩
  · have hζ0 : ζ ≠ 0 := fun h => by
      have := hFH hζ; rw [h] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    have hd : DifferentiableAt ℂ (psiMapInv p) ζ :=
      (differentiableAt_const _).sub (differentiableAt_id.inv hζ0)
    have hd2 : DifferentiableWithinAt ℂ (fwdMapInv W s) H (psiMapInv p ζ) :=
      QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hs0 _ (hψH ζ (hFH hζ))
    have hd3 : DifferentiableWithinAt ℂ (fun ζ => fwdMapInv W s (psiMapInv p ζ)) (innerSide Γ)
        ζ := hd2.comp ζ hd.differentiableWithinAt fun ζ' hζ' => hψH ζ' (hFH hζ')
    exact hd3.congr (fun ζ' hζ' => hfeq _ (hψH ζ' (hFH hζ'))) (hfeq _ (hψH ζ (hFH hζ)))
  · simp only at h
    rw [hfeq _ (hψH ζ (hFH hζ)), hfeq _ (hψH ζ' (hFH hζ'))] at h
    have h1 := QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hs0 (hψH ζ (hFH hζ))
      (hψH ζ' (hFH hζ')) h
    have h2 := congrArg (psiMap p) h1
    rwa [psiMap_psiMapInv, psiMap_psiMapInv] at h2
  · have hzD := hz.2
    rw [← himgH] at hzD
    obtain ⟨w, hw, rfl⟩ := hzD
    have hwp : w ≠ p := fun h => by rw [h] at hw; exact not_mem_H_ofReal p hw
    refine ⟨psiMap p w, (hiff _ ((psiMap_mem_H_iff hwp).2 hw)).1 ?_, ?_⟩
    · rw [psiMapInv_psiMap]; exact hz.1
    · simp only [psiMapInv_psiMap]

/-- The domain part `C ∩ D_s` of the pocket at `s ≥ τ` is preconnected (the image of the face). -/
theorem isPreconnected_inter_domain (hP : IsReversePocketInf W η C α₁ α₂ τ) {s : ℝ}
    (hτs : τ ≤ s) : IsPreconnected (C ∩ (H \ fwdHull W s)) := by
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  obtain ⟨P, hP'⟩ := hP.exists_face hτs
  obtain ⟨Γ, hΓJ, hΓH, hiff⟩ := hP' (P - 1) (by linarith)
  obtain ⟨-, -, -, -, -, -, -, hpre, -⟩ := jordan_sides hΓJ hΓH
  have hf := hP.isConformalBijection_face hs0 hΓJ hΓH hiff
  rw [← hf.2.image_eq]
  exact hpre.image _ hf.1.continuousOn

/-- The domain part `C ∩ D_s` of the pocket is unbounded. -/
theorem not_isBounded_inter_domain (hP : IsReversePocketInf W η C α₁ α₂ τ) {s : ℝ}
    (hs0 : 0 ≤ s) : ¬ IsBounded (C ∩ (H \ fwdHull W s)) := by
  have hRc : IsCompact (η '' Icc 0 s) := hP.isCompact_range s
  obtain ⟨ρ, hρ, hρR⟩ := exists_closure_subset_ball hRc.isBounded
  have hK : fwdHull W s ⊆ ball 0 ρ := by
    rw [hP.trace.2.2 s hs0]; exact fillH_subset_ball hρ hρR
  intro hb
  refine hP.not_isBounded ((hb.union (isBounded_ball (x := (0 : ℂ)) (r := ρ))).subset ?_)
  intro z hz
  by_cases hzb : z ∈ ball (0 : ℂ) ρ
  · exact Or.inr hzb
  · exact Or.inl ⟨hz, hP.subset_H hz, fun h => hzb (hK h)⟩

end IsReversePocketInf

end InteractingSLE.Sec6
