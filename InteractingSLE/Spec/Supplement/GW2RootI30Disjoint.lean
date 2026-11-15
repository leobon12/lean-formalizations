/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Connector
import InteractingSLE.Spec.Supplement.GW2RootI30Mobius
import InteractingSLE.Spec.Supplement.GB6Disjoint

/-!
# Closed-hull separation at the low-arc roots

Packet PROVE-T14-GW2ROOT2. The zero-based connector has the same filling
as the translated flow trace. GB6's two-sided no-entry theorem therefore
proves closed-hull separation from the cover's original trace separation.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open Supp8.GB6 Supp8.GB6.CoordB Sec5.CrossRestart ConformalImageFull

/-- Real translation of the entire generating set preserves the filling. -/
theorem isFilling_image_add_full {K A : Set ℂ} (hK : IsHPHull K) (x : ℝ)
    (hfill : IsFilling K A) :
    IsFilling ((fun z : ℂ => z + x) '' K) ((fun z : ℂ => z + x) '' A) := by
  apply (isFilling_congr_inter_H (A := (fun z : ℂ => z + x) '' A)
    (B := (fun z : ℂ => z + x) '' (A ∩ H)) ?_).2
    (isFilling_image_add hK x hfill)
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    have hwH : w ∈ H := by
      change 0 < (w + (x : ℂ)).im at hz
      change 0 < w.im
      simpa only [add_im, ofReal_im, add_zero] using hz
    exact ⟨⟨w, ⟨hw, hwH⟩, rfl⟩, hz⟩
  · rintro ⟨⟨w, ⟨hw, _⟩, rfl⟩, hz⟩
    exact ⟨⟨w, hw, rfl⟩, hz⟩

/-- The closed inverted translated hull misses the retained hull before
trace contact, whenever the cover's real connector is untouched. -/
theorem disjoint_closure_translated_hull {wα w : ℝ≥0 → ℝ} {α γ : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace wα ⊤ α) (hwα : Continuous wα) (hwα0 : wα 0 = 0)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    {s v : ℝ≥0} (hv : 0 < v) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => γ t + x) '' Icc 0 v \ {0}))) :
    Disjoint (closure (fwdHull (Ito.rpath wα) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun t => Ito.rpath w t + x) v)) := by
  have hγc : ContinuousOn γ (Icc 0 v) :=
    hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
  have hγH : MapsTo (fun t => γ t + x) (Icc 0 v) Hbar := by
    intro t _
    have ht := Sec7.IsGeneratingTrace.mem_Hbar hγ hw.continuousOn hw0
      (t := t) le_top
    change 0 ≤ (γ t).im at ht
    change 0 ≤ (γ t + x).im
    simpa only [add_im, ofReal_im, add_zero] using ht
  obtain ⟨δ, hδc, hδ0, hδH, hδeq, hδsep⟩ := exists_zero_carrier
    (γ := fun t => γ t + x) hx hv
    (hγc.add continuousOn_const) (by rw [hγ.1, zero_add]) hγH harc hsep
  obtain ⟨hAk, hAH, hAu, hKA⟩ := rangeData_of_isGeneratingTrace hα
    hwα.continuousOn hwα0 (s := s) ENNReal.coe_lt_top
  have hBk := isCompact_Icc.image_of_continuousOn hδc
  have hBu : ∀ c ∈ (fun z : ℂ => -z⁻¹) '' (δ '' Icc 0 1 \ {0}),
      ∃ P ⊆ (fun z : ℂ => -z⁻¹) '' (δ '' Icc 0 1 \ {0}),
        IsPreconnected P ∧ c ∈ P ∧ ¬ Bornology.IsBounded P := by
    rintro _ ⟨_, ⟨⟨t, ht, rfl⟩, hn⟩, rfl⟩
    exact exists_unbounded_inv_image hδc hδ0 ht hn
  have hK : IsHPHull (fwdHull (Ito.rpath w) v) :=
    isHPHull_fwdHull (hw.comp continuous_real_toNNReal) v.coe_nonneg
  have hfill := isFilling_image_add_full hK x (hγ.2.2 v ENNReal.coe_lt_top)
  rw [← fwdHull_add_const, image_image] at hfill
  have hfillδ : IsFilling (fwdHull (fun t => Ito.rpath w t + x) v) (δ '' Icc 0 1) :=
    (isFilling_congr_inter_H hδeq).2 hfill
  have hKB := fwdHull_eq_fillH_of_isFilling hBk hfillδ
  change fwdHull (Ito.rpath wα) s = fillH (α '' Icc 0 s) at hKA
  rw [hKA, hKB]
  exact disjoint_closure_fillH_inv_image hAk hBk hAH
    (by rintro _ ⟨t, ht, rfl⟩; exact hδH ht) hAu hBu hδsep

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
