/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PathReduce
import InteractingSLE.Spec.Supplement.GW4LeafClock
import InteractingSLE.Spec.Supplement.GW4IdentHull
import InteractingSLE.Spec.Sec7.SideHeightGeom

/-!
# Uniqueness of deterministic retargeting

Packet PROVE-GW1-DET. Two retargetings cover the same original time interval.
At equal original times their tips agree. Their initial trace ranges are therefore
nested, and so are their fillings. Equal half-plane capacity then identifies the
hulls and drivers. This argument uses no probability or conformal filling rule.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1Det

open GW1Path

/-- Recentring translates every finite physical tip by the recentring amount. -/
theorem tipAt_recenter_infinity_iff {U : ℝ≥0 → ℝ} {v : ℝ} {r : ℝ≥0} {z : ℂ} :
    ((Chart.id.recenter v).trans infinitySourceChart).tipAt U r z ↔
      infinitySourceChart.tipAt U r (z - v) := by
  constructor
  · intro h
    have h' := h.sub_const (v : ℂ)
    simpa only [Chart.tipAt, Chart.trans, Chart.recenter, Chart.id, infinitySourceChart,
      add_sub_cancel_right] using h'
  · intro h
    have h' := h.add_const (v : ℂ)
    simpa only [Chart.tipAt, Chart.trans, Chart.recenter, Chart.id, infinitySourceChart,
      sub_add_cancel] using h'

/-- A translated inversion tip relation determines the generating trace value,
including the case where the inversion has no finite tip. -/
theorem trace_eq_of_tipAt_iff {U₁ U₂ : ℝ≥0 → ℝ} {γ₁ γ₂ : ℝ≥0 → ℂ}
    (hγ₁ : IsGeneratingTrace U₁ ⊤ γ₁) (hγ₂ : IsGeneratingTrace U₂ ⊤ γ₂)
    (hU₁ : Continuous U₁) (hU₂ : Continuous U₂) {v : ℝ} {r₁ r₂ : ℝ≥0}
    (h : ∀ z : ℂ, ((Chart.id.recenter v).trans infinitySourceChart).tipAt U₁ r₁ z ↔
      ((Chart.id.recenter v).trans infinitySourceChart).tipAt U₂ r₂ z) :
    γ₁ r₁ = γ₂ r₂ := by
  have h0₁ := Sec7.SideHeight.w_zero_of_isGeneratingTrace hγ₁ (by simp)
  have h0₂ := Sec7.SideHeight.w_zero_of_isGeneratingTrace hγ₂ (by simp)
  have hi : ∀ z : ℂ, (γ₁ r₁ ≠ 0 ∧ z = -(γ₁ r₁)⁻¹) ↔
      (γ₂ r₂ ≠ 0 ∧ z = -(γ₂ r₂)⁻¹) := by
    intro z
    have hz := h (z + v)
    simp only [tipAt_recenter_infinity_iff, add_sub_cancel_right,
      GW4Leaf.tipAt_infinitySourceChart_iff hγ₁ hU₁ h0₁,
      GW4Leaf.tipAt_infinitySourceChart_iff hγ₂ hU₂ h0₂] at hz
    exact hz
  by_cases h₁ : γ₁ r₁ = 0
  · have h₂ : γ₂ r₂ = 0 := by
      by_contra h₂
      exact ((hi (-(γ₂ r₂)⁻¹)).2 ⟨h₂, rfl⟩).1 h₁
    exact h₁.trans h₂.symm
  · have he := ((hi (-(γ₁ r₁)⁻¹)).1 ⟨h₁, rfl⟩).2
    exact inv_injective (neg_injective he)

/-- If two increasing clocks cover the same interval, their initial trace ranges
are nested in the order of their terminal clock values. -/
theorem traceRange_subset_of_clock_le {γ₁ γ₂ : ℝ≥0 → ℂ} {ℓ₁ ℓ₂ : ℝ≥0 → ℝ≥0}
    (hℓ₁ : Monotone ℓ₁) (hℓ₂ : StrictMono ℓ₂) (hrange : range ℓ₁ = range ℓ₂)
    (heq : ∀ r₁ r₂, ℓ₁ r₁ = ℓ₂ r₂ → γ₁ r₁ = γ₂ r₂)
    {s₁ s₂ : ℝ≥0} (hs : ℓ₁ s₁ ≤ ℓ₂ s₂) :
    γ₁ '' Icc 0 s₁ ⊆ γ₂ '' Icc 0 s₂ := by
  rintro _ ⟨r₁, hr₁, rfl⟩
  have hm : ℓ₁ r₁ ∈ range ℓ₂ := hrange ▸ mem_range_self r₁
  obtain ⟨r₂, hr₂⟩ := hm
  refine ⟨r₂, ⟨zero_le, ?_⟩, (heq r₁ r₂ hr₂.symm).symm⟩
  exact hℓ₂.le_iff_le.1 (hr₂ ▸ (hℓ₁ hr₁.2).trans hs)

/-- **Uniqueness when retargeting exists.** This is the uniqueness assertion in
`GW1Path.DetRetargetStatement`, with its original retargeting relation unchanged. -/
theorem isRetargetOf_unique {U₁ U₂ Q : ℝ≥0 → ℝ} {v : ℝ}
    (hU₁ : Continuous U₁) (hU₂ : Continuous U₂)
    (h₁ : IsRetargetOf U₁ Q v) (h₂ : IsRetargetOf U₂ Q v) : U₁ = U₂ := by
  obtain ⟨⟨γ₁, hγ₁, -⟩, ℓ₁, -, hm₁, hr₁, ht₁⟩ := h₁
  obtain ⟨⟨γ₂, hγ₂, -⟩, ℓ₂, -, hm₂, hr₂, ht₂⟩ := h₂
  have hrange : range ℓ₁ = range ℓ₂ := hr₁.trans hr₂.symm
  have heq : ∀ r₁ r₂, ℓ₁ r₁ = ℓ₂ r₂ → γ₁ r₁ = γ₂ r₂ := by
    intro r₁ r₂ hr
    apply trace_eq_of_tipAt_iff hγ₁ hγ₂ hU₁ hU₂ (v := v)
    intro z
    rw [ht₁, ht₂, hr]
  have hhull : ∀ s : ℝ≥0,
      QuantumZipper.fwdHull (fun r : ℝ => U₁ r.toNNReal) s =
        QuantumZipper.fwdHull (fun r : ℝ => U₂ r.toNNReal) s := by
    intro s
    rcases le_total (ℓ₁ s) (ℓ₂ s) with hs | hs
    · apply GW4Ident.fwdHull_eq_of_subset (hU₁.comp continuous_real_toNNReal)
        (hU₂.comp continuous_real_toNNReal) s.coe_nonneg
      change QuantumZipper.fwdHull (fun r : ℝ => U₁ r.toNNReal) s ⊆
        QuantumZipper.fwdHull (fun r : ℝ => U₂ r.toNNReal) s
      rw [Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ₁ ENNReal.coe_lt_top,
        Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ₂ ENNReal.coe_lt_top]
      exact fillH_mono (traceRange_subset_of_clock_le hm₁.monotone hm₂ hrange heq hs)
    · symm
      apply GW4Ident.fwdHull_eq_of_subset (hU₂.comp continuous_real_toNNReal)
        (hU₁.comp continuous_real_toNNReal) s.coe_nonneg
      change QuantumZipper.fwdHull (fun r : ℝ => U₂ r.toNNReal) s ⊆
        QuantumZipper.fwdHull (fun r : ℝ => U₁ r.toNNReal) s
      rw [Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ₂ ENNReal.coe_lt_top,
        Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ₁ ENNReal.coe_lt_top]
      exact fillH_mono (traceRange_subset_of_clock_le hm₂.monotone hm₁ hrange.symm
        (fun r₂ r₁ hr => (heq r₁ r₂ hr.symm).symm) hs)
  exact GW4Ident.eq_of_forall_fwdHull_eq hU₁ hU₂
    (Sec7.SideHeight.w_zero_of_isGeneratingTrace hγ₁ (by simp)) hhull

end InteractingSLE.Theorem14.GW1Det
