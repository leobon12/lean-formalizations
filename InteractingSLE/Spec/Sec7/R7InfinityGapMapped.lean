/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapTopology

/-!
# Mapped gaps in a selected compact current face

PROVE-R7-GAPEQ. Physical face inclusion and future confinement replace the old
two-swallowed-prefix input of the contained-pocket theorem at infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 R7InfinityChart

/-- A selected compact face gives mapped gap equality from tail avoidance and
either an old visit limit or a gate at the initial endpoint. -/
theorem ownFuture_gap_eq_of_compact_face {W : ℝ → ℝ} {η A₁ A₂ b₁ b₂ : ℝ → ℂ}
    {C : Set ℂ} {r p q₁ q₂ a b : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hCo : IsOpen C) (hra : r ≤ a) (hab : a < b)
    (hb₁ : IsLastVisitArm W η A₁ r p q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ r p q₂ b₂)
    (hp : p < min q₁ q₂)
    (hdisj : ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1)
    (hD₁ : ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₁ r), A₁ v ∈ H \ fwdHull W r)
    (hD₂ : ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₂ r), A₂ v ∈ H \ fwdHull W r)
    (hFC : MapsTo (fun ζ => trMap W 0 r (psiMapInv p ζ))
      (innerSide (compactBoundary b₁ b₂ (-(q₁ - p)⁻¹) (-(q₂ - p)⁻¹))) C)
    (h11 : ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
      psiMap p (trMap W r t 0) ∈
        innerSide (compactBoundary b₁ b₂ (-(q₁ - p)⁻¹) (-(q₂ - p)⁻¹)))
    (hδp : ∀ t ∈ Icc a b, trMap W r t 0 ≠ p)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C)
    (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₁ r), η t ≠ A₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) A₂ r), η t ≠ A₂ v)
    (ha : (trMap W r a 0 = q₁ ∨ trMap W r a 0 = q₂) ∨
      a ∈ closure {t | r < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) : trMap W r a 0 = trMap W r b 0 := by
  let Γ := compactBoundary b₁ b₂ (-(q₁ - p)⁻¹) (-(q₂ - p)⁻¹)
  let δ : ℝ → ℂ := fun t => trMap W r t 0
  let δ' : ℝ → ℂ := fun t => psiMap p (δ t)
  have hpq₁ := hp.trans_le (min_le_left _ _)
  have hpq₂ := hp.trans_le (min_le_right _ _)
  have hGδ : ∀ t, r ≤ t → trMap W 0 r (psiMapInv p (δ' t)) = η t := by
    intro t hrt
    dsimp only [δ', δ]
    rw [psiMapInv_psiMap, traceMapOut_trMap_zero hη hW hW0 hr hrt]
  have hδc : ContinuousOn δ (Icc a b) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr).mono fun _ ht => hra.trans ht.1
  have h11' : ∀ t, r ≤ t → η t ∈ C → δ t ∈ H → δ t ∈ psiMap p ⁻¹' innerSide Γ := h11
  have hcl : ∀ t ∈ Icc a b, t ∈ closure {t | r < t ∧ η t ∈ C} → δ' t ∈ closure (innerSide Γ) := by
    intro t ht htcl
    have hm := ownFuture_mem_closure_face hη hW hW0 hCo hr h11' htcl
    have hc : ContinuousAt (psiMap p) (δ t) := continuousOn_psiMap.continuousAt
      (isOpen_compl_singleton.mem_nhds (hδp t ht))
    exact closure_mono (image_preimage_subset _ _) (hc.continuousWithinAt.mem_closure_image hm)
  have ha' : δ' a = ((-(q₁ - p)⁻¹ : ℝ) : ℂ) ∨ δ' a = ((-(q₂ - p)⁻¹ : ℝ) : ℂ) ∨
      δ' a ∈ closure (innerSide Γ) := by
    rcases ha with (ha | ha) | ha
    · exact Or.inl (by dsimp [δ', δ]; rw [ha, psiMap_ofReal])
    · exact Or.inr (Or.inl (by dsimp [δ', δ]; rw [ha, psiMap_ofReal]))
    · exact Or.inr (Or.inr (hcl a ⟨le_rfl, hab.le⟩ ha))
  have hgate := compact_gate_eq
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hpq₁)))
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hpq₂)))
    hb₁.1 hb₂.1 hb₁.2.1 hb₂.2.1 hb₁.2.2.1 hb₂.2.2.1
    hb₁.2.2.2.1 hb₂.2.2.2.1 hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hdisj hab
    (continuousOn_psiMap.comp hδc fun t ht => hδp t ht)
    (fun t ht => psiMap_mem_Hbar (YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 hr
      (hra.trans ht.1)))
    (fun t ht hF => hgap t ht (hGδ t (hra.trans ht.1) ▸ hFC hF))
    (fun t ht hB => by
      rw [hb₁.2.2.2.2.2.1] at hB
      obtain ⟨w, hw, he⟩ := hB
      rw [psiMap_injective he] at hw
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.trans ht.1) hD₁ (hunv₁ t ht) hw)
    (fun t ht hB => by
      rw [hb₂.2.2.2.2.2.1] at hB
      obtain ⟨w, hw, he⟩ := hB
      rw [psiMap_injective he] at hw
      exact ownFuture_notMem_lift hη hW hW0 hr (hra.trans ht.1) hD₂ (hunv₂ t ht) hw)
    (fun t ht h0 => hδp t ht (psiMap_eq_zero_iff.1 h0))
    (fun c d hac hcd hdb => by
      obtain ⟨t, ht, htH⟩ := ownFuture_not_forall_real hη hW hW0 hr (hra.trans hac) hcd
      exact ⟨t, ht, (psiMap_mem_H_iff (hδp t ⟨hac.trans ht.1, ht.2.trans hdb⟩)).2 htH⟩)
    ha' (hcl b ⟨hab.le, le_rfl⟩ hb)
  exact psiMap_injective hgate

end InteractingSLE.Sec7.R7InfinityGap
