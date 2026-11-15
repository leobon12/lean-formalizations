/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Monotone

/-!
# A comparison principle for integrated equations with monotone drift

Packet PROVE-BESSEL. Deterministic input for the Bessel processes of the specification
(pp. 19–21, (2.1)–(2.3)).

`InteractingSLE.Bessel.le_of_sub_eq_integral`: let `X, Y` be continuous on `[0, T]` with
`X t - Y t = X 0 - Y 0 + ∫₀ᵗ (f - h)`, `X 0 ≤ Y 0`, and suppose that for almost every `s ∈ [0, T]`,
`Y s < X s` implies `f s ≤ h s`. Then `X ≤ Y` on `[0, T]`.

Proof: if `X t₁ > Y t₁`, let `t₀` be the last time in `[0, t₁]` with `X ≤ Y`. On `(t₀, t₁]` one has
`X > Y`, so `f ≤ h` almost everywhere there and `(X - Y) t₁ ≤ (X - Y) t₀ ≤ 0`, a contradiction.

This is the whole of pathwise uniqueness and comparison for `X = x + w + ∫ c / X` with `c > 0`
(the drift `x ↦ c / x` is decreasing on `(0, ∞)`), and the monotonicity in the regularization
parameter of the regularized equations.
-/

open MeasureTheory Set

namespace InteractingSLE

namespace Bessel

/-- **Comparison principle.** If `X - Y = (X 0 - Y 0) + ∫₀ᵗ (f - h)` on `[0, T]`, `X 0 ≤ Y 0`, and
almost everywhere on `[0, T]` the inequality `Y s < X s` forces `f s ≤ h s`, then `X ≤ Y` on
`[0, T]`. -/
theorem le_of_sub_eq_integral {X Y f h : ℝ → ℝ} {T : ℝ} (hX : ContinuousOn X (Icc 0 T))
    (hY : ContinuousOn Y (Icc 0 T)) (hf : IntervalIntegrable f volume 0 T)
    (hh : IntervalIntegrable h volume 0 T) (h0 : X 0 ≤ Y 0)
    (heq : ∀ t ∈ Icc (0 : ℝ) T, X t - Y t = X 0 - Y 0 + ∫ s in (0 : ℝ)..t, (f s - h s))
    (hmono : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) T → Y s < X s → f s ≤ h s) :
    ∀ t ∈ Icc (0 : ℝ) T, X t ≤ Y t := by
  intro t₁ ht₁
  by_contra hcon
  push Not at hcon
  set S : Set ℝ := Icc 0 t₁ ∩ {s | X s ≤ Y s} with hS
  have hsub : Icc (0 : ℝ) t₁ ⊆ Icc 0 T := Icc_subset_Icc_right ht₁.2
  have hSclosed : IsClosed S := by
    have hc : ContinuousOn (fun s => X s - Y s) (Icc 0 t₁) := (hX.mono hsub).sub (hY.mono hsub)
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
    convert this using 1
    ext s
    simp only [hS, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic, sub_nonpos]
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht₁.1⟩, h0⟩
  have hbdd : BddAbove S := ⟨t₁, fun s hs => hs.1.2⟩
  set t₀ := sSup S with ht₀
  have ht₀S : t₀ ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hbdd
  have ht₀le : t₀ ≤ t₁ := ht₀S.1.2
  have ht₀0 : 0 ≤ t₀ := ht₀S.1.1
  have hgt : ∀ s ∈ Ioc t₀ t₁, Y s < X s := by
    intro s hs
    by_contra hns
    push Not at hns
    have : s ∈ S := ⟨⟨ht₀0.trans hs.1.le, hs.2⟩, hns⟩
    exact absurd (le_csSup hbdd this) (not_le.2 hs.1)
  -- integrability of `f - h` on the relevant intervals
  have hfh : IntervalIntegrable (fun s => f s - h s) volume 0 T := hf.sub hh
  have hint : ∀ u ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun s => f s - h s) volume 0 u :=
    fun u hu => hfh.mono_set (by
      rw [uIcc_of_le hu.1, uIcc_of_le (hu.1.trans hu.2)]
      exact Icc_subset_Icc_right hu.2)
  have ht₀T : t₀ ∈ Icc (0 : ℝ) T := hsub ht₀S.1
  have hdiff : (X t₁ - Y t₁) - (X t₀ - Y t₀) = ∫ s in t₀..t₁, (f s - h s) := by
    rw [heq t₁ ht₁, heq t₀ ht₀T]
    rw [add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hint t₁ ht₁) (hint t₀ ht₀T)
  have hnonpos : ∫ s in t₀..t₁, (f s - h s) ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht₀le]
    refine integral_nonpos_of_ae ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hmono] with s hs hsI
    have hsT : s ∈ Icc (0 : ℝ) T := hsub ⟨ht₀0.trans hsI.1.le, hsI.2⟩
    simpa using sub_nonpos.2 (hs hsT (hgt s hsI))
  have ht₀XY : X t₀ ≤ Y t₀ := ht₀S.2
  have : X t₁ - Y t₁ ≤ 0 := by linarith
  linarith

end Bessel

end InteractingSLE
