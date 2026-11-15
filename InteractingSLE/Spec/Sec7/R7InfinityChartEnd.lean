/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceChart
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# A compact face incident to zero has an unbounded physical image

PROVE-R7-GAPEQ. The inverse compactifying map tends to infinity at zero. Bounded
Loewner displacement transfers this to the physical image of the Jordan inner side.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open InteractingSLE.YuanSimpleApprox (trMap)
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6

/-- The inverse compactifying map tends to infinity at its puncture. -/
theorem tendsto_norm_psiMapInv_zero (a : ℝ) :
    Tendsto (fun ζ : ℂ => ‖psiMapInv a ζ‖) (𝓝[≠] 0) atTop := by
  apply tendsto_atTop_mono _ (tendsto_atTop_add_const_right _ (-|a|)
    (tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ)))
  intro ζ
  have hn := norm_sub_norm_le (ζ⁻¹) (a : ℂ)
  rw [norm_real, Real.norm_eq_abs, norm_sub_rev] at hn
  exact hn

/-- A Jordan face incident to the compactified end has an unbounded inverse image. -/
theorem not_isBounded_inverse_innerSide {Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (h0 : (0 : ℂ) ∈ Γ) (a : ℝ) : ¬ IsBounded (psiMapInv a '' innerSide Γ) := by
  have hfront := (jordan_sides hΓ hΓH).2.2.1
  have hcl : (0 : ℂ) ∈ closure (innerSide Γ) := frontier_subset_closure (hfront.symm ▸ h0)
  have : (𝓝[innerSide Γ] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hne : innerSide Γ ⊆ {(0 : ℂ)}ᶜ := by
    intro ζ hζ he
    have hh := innerSide_subset_H hΓ hΓH hζ
    rw [show ζ = 0 from he] at hh
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hh)
  have hlim := tendsto_norm_atTop_iff_cobounded.1
    ((tendsto_norm_psiMapInv_zero a).mono_left (nhdsWithin_mono 0 hne))
  intro hb
  obtain ⟨ζ, hζout, hζin⟩ := Filter.nonempty_of_mem
    (inter_mem (hlim.eventually_mem hb) self_mem_nhdsWithin)
  exact hζout (mem_image_of_mem (psiMapInv a) hζin)

/-- The physical Loewner image is unbounded as well. No side selection, witness, or
component identity is needed for this conclusion. -/
theorem not_isBounded_physical_innerSide {W : ℝ → ℝ} {s a : ℝ} {Γ : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar) (h0 : (0 : ℂ) ∈ Γ) :
    ¬ IsBounded ((fun ζ => trMap W 0 s (psiMapInv a ζ)) '' innerSide Γ) := by
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le hW hW0 hs
  have hu := not_isBounded_image_of_norm_sub_le (not_isBounded_inverse_innerSide hΓ hΓH h0 a)
    (f := trMap W 0 s) (fun z hz => by
      obtain ⟨ζ, hζ, rfl⟩ := hz
      exact hK _ (psiMapInv_mem_H (innerSide_subset_H hΓ hΓH hζ)))
  rwa [image_image] at hu

end InteractingSLE.Sec7.R7InfinityChart
