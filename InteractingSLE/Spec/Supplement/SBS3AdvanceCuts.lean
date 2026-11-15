/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.W0bSelect
import InteractingSLE.Spec.Supplement.OwnHistoryPath

/-!
# Lemma S3: rational compact common arcs in the physical half-plane

Packet PROVE-T14-S3, continuation. A generating trace cannot traverse an open
real interval. Every hypothetical common time interval therefore contains a
compact common interval in the physical half-plane, with rational endpoints
strictly after entrance and strictly before lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- Select a compact common arc in `H` at rational own times, strictly inside
the original interval. This also treats an interval ending at lifetime. -/
theorem exists_rational_compact_common_arc {w : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ}
    {ζ τ : ℝ≥0∞} (hβ : IsGeneratingTrace w ζ β)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {A : Set ℂ} {s₁ s₂ : ℝ≥0} (hτ : τ ≤ s₁) (hs : s₁ < s₂)
    (hsζ : (s₂ : ℝ≥0∞) ≤ ζ) (hA : β '' Ioo s₁ s₂ ⊆ A) :
    ∃ q₁ q₂ : ℚ, τ < ((q₁ : ℝ).toNNReal : ℝ≥0∞) ∧
      (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal ∧
      ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ ∧
      β '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ A ∩ H := by
  obtain ⟨t, ht, htH⟩ := Restart.IsGeneratingTrace.exists_mem_H hβ hw hw0 hs hsζ
  have hcont : ContinuousOn β (Ioo s₁ s₂) := hβ.2.1.mono fun r hr =>
    (ENNReal.coe_le_coe.2 hr.2.le).trans hsζ
  have hev : ∀ᶠ r in 𝓝 t, r ∈ Ioo s₁ s₂ ∧ β r ∈ H := by
    filter_upwards [isOpen_Ioo.mem_nhds ht,
      (hcont.continuousAt (isOpen_Ioo.mem_nhds ht)).preimage_mem_nhds
        (QuantumZipper.isOpen_H.mem_nhds htH)] with r hr hrH using ⟨hr, hrH⟩
  obtain ⟨a, b, htab, hab⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨s₁, ht.1⟩ (exists_gt t)).1 hev
  obtain ⟨q₁, haq₁, hq₁t⟩ := Supp9.W0b.exists_rat_btwn_nnreal htab.1
  obtain ⟨q₂, htq₂, hq₂b⟩ := Supp9.W0b.exists_rat_btwn_nnreal htab.2
  have hq₁q₂ : (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal := hq₁t.trans htq₂
  have hI : Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ Ioo a b := fun r hr =>
    ⟨haq₁.trans_le hr.1, hr.2.trans_lt hq₂b⟩
  have hq₁ := (hab (hI (left_mem_Icc.2 hq₁q₂.le))).1
  have hq₂ := (hab (hI (right_mem_Icc.2 hq₁q₂.le))).1
  refine ⟨q₁, q₂, hτ.trans_lt (ENNReal.coe_lt_coe.2 hq₁.1), hq₁q₂,
    (ENNReal.coe_lt_coe.2 hq₂.2).trans_le hsζ, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨hA ⟨r, (hab (hI hr)).1, rfl⟩, (hab (hI hr)).2⟩

/-- Countable rational compact arcs suffice for the full pathwise conclusion
of S3, including entrance equality and finite terminal times. -/
theorem no_common_arc_of_rational_compact {w : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ}
    {ζ τ : ℝ≥0∞} (hβ : IsGeneratingTrace w ζ β)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {A : Set ℂ}
    (hQ : ∀ q₁ q₂ : ℚ, τ < ((q₁ : ℝ).toNNReal : ℝ≥0∞) →
      (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
      ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ →
      ¬ β '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ A ∩ H) :
    ∀ s₁ s₂ : ℝ≥0, τ ≤ s₁ → s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ ζ →
      ¬ β '' Ioo s₁ s₂ ⊆ A := by
  intro s₁ s₂ hτ hs hsζ hA
  obtain ⟨q₁, q₂, hτq, hqq, hqζ, hQA⟩ :=
    exists_rational_compact_common_arc hβ hw hw0 hτ hs hsζ hA
  exact hQ q₁ q₂ hτq hqq hqζ hQA

end InteractingSLE.Theorem14.SB.S3
