/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1Det
import InteractingSLE.Spec.Supplement.GW1LaunchClockCompose

/-!
# Uniqueness of the retargeting clock

Continuation of PROVE-GW1-DET. A fixed pair of drivers admits at most one
prefix clock. Equality of the source trace prefixes gives equality of their
fillings, and half-plane capacity recovers the source times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1Det

/-- A strictly increasing clock covering an initial time interval starts at zero. -/
theorem clock_zero_of_range {ℓ : ℝ≥0 → ℝ≥0} {S : ℝ≥0∞}
    (hm : StrictMono ℓ) (hr : range ℓ = {t : ℝ≥0 | (t : ℝ≥0∞) < S}) : ℓ 0 = 0 := by
  have hS : (0 : ℝ≥0∞) < S := by
    have h := mem_range_self (f := ℓ) 0
    rw [hr] at h
    exact lt_of_le_of_lt bot_le h
  obtain ⟨r, he⟩ := (show (0 : ℝ≥0) ∈ range ℓ by rw [hr]; exact hS)
  exact le_antisymm ((hm.monotone (show 0 ≤ r from zero_le)).trans he.le) zero_le

/-- The source generating trace and its capacity parametrization determine any
clock giving the same tips through a fixed chart. No injectivity of the trace
or boundary extension is assumed. -/
theorem prefixClock_unique {c : Chart} {U Q : ℝ≥0 → ℝ} {A : Set ℂ}
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace Q ⊤ γ) (hQ : Continuous Q)
    {ℓ₁ ℓ₂ : ℝ≥0 → ℝ≥0}
    (h₁ : GW1LaunchClock.IsPrefixClock c Q U A ℓ₁)
    (h₂ : GW1LaunchClock.IsPrefixClock c Q U A ℓ₂) : ℓ₁ = ℓ₂ := by
  have heq : ∀ r, γ (ℓ₁ r) = γ (ℓ₂ r) := by
    intro r
    apply trace_eq_of_tipAt_iff hγ hγ hQ hQ (v := 0)
    intro z
    simpa only [tipAt_recenter_infinity_iff, Complex.ofReal_zero, sub_zero] using
      (h₁.2.2.2 r z).symm.trans (h₂.2.2.2 r z)
  have h0₁ := clock_zero_of_range h₁.2.1 h₁.2.2.1
  have h0₂ := clock_zero_of_range h₂.2.1 h₂.2.2.1
  have himg₁ (r : ℝ≥0) : ℓ₁ '' Icc 0 r = Icc 0 (ℓ₁ r) := by
    rw [h₁.1.continuousOn.image_Icc_of_monotoneOn zero_le (h₁.2.1.monotone.monotoneOn _), h0₁]
  have himg₂ (r : ℝ≥0) : ℓ₂ '' Icc 0 r = Icc 0 (ℓ₂ r) := by
    rw [h₂.1.continuousOn.image_Icc_of_monotoneOn zero_le (h₂.2.1.monotone.monotoneOn _), h0₂]
  have hQc := hQ.comp continuous_real_toNNReal
  funext r
  have htrace : γ '' Icc 0 (ℓ₁ r) = γ '' Icc 0 (ℓ₂ r) := by
    rw [← himg₁, ← himg₂, image_image, image_image]
    exact congrArg (fun f : ℝ≥0 → ℂ => f '' Icc 0 r) (funext heq)
  have hhull : QuantumZipper.fwdHull (fun s : ℝ => Q s.toNNReal) (ℓ₁ r) =
      QuantumZipper.fwdHull (fun s : ℝ => Q s.toNNReal) (ℓ₂ r) := by
    rw [Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ ENNReal.coe_lt_top,
      Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ ENNReal.coe_lt_top, htrace]
  have hcap := HPHull.hcap_congr
    (A := ⟨_, isHPHull_fwdHull hQc (ℓ₁ r).coe_nonneg⟩)
    (B := ⟨_, isHPHull_fwdHull hQc (ℓ₂ r).coe_nonneg⟩) hhull
  rw [GW4Ident.hcap_fwdHull_eq hQc (ℓ₁ r).coe_nonneg,
    GW4Ident.hcap_fwdHull_eq hQc (ℓ₂ r).coe_nonneg] at hcap
  exact NNReal.coe_injective (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hcap)

end InteractingSLE.Theorem14.GW1Det
