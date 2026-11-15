/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteMap

/-!
# Separated-source scales and concrete original-flow data

Packet PROVE-ZHAN-GT4-A22. Positive lower and finite upper bounds give
one exponential scale. The data constructor fixes the other-source
coordinate and derivative to the actual original Loewner flow.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (fwdMap)

/-- Put a positive compact range of absolute values in one exponential scale. -/
theorem exists_inScale_of_abs_bounds {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ, c ≤ |u| → |u| ≤ C → InScale L u := by
  refine ⟨|Real.log c| + |Real.log C|, by positivity, ?_⟩
  intro u hu hu'
  constructor
  · apply le_trans ?_ hu
    calc Real.exp (-(|Real.log c| + |Real.log C|)) ≤ Real.exp (Real.log c) :=
        Real.exp_le_exp.2 (by linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log C)])
      _ = c := Real.exp_log hc
  · apply hu'.trans
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ ≤ Real.exp (|Real.log c| + |Real.log C|) :=
        Real.exp_le_exp.2 ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))

/-- Uniform bounds for two separated gaps give uniform bounds for their ratio. -/
theorem abs_div_bounds {a b cn cd C : ℝ} (hcn : 0 < cn) (hcd : 0 < cd) (hC : 0 < C)
    (ha : cn ≤ |a| ∧ |a| ≤ C) (hb : cd ≤ |b| ∧ |b| ≤ C) :
    cn / C ≤ |a / b| ∧ |a / b| ≤ C / cd := by
  have hb0 : 0 < |b| := hcd.trans_le hb.1
  rw [abs_div]
  constructor
  · rw [div_le_div_iff₀ hC hb0]
    exact (mul_le_mul_of_nonneg_left hb.2 hcn.le).trans
      (mul_le_mul_of_nonneg_right ha.1 hC.le)
  · rw [div_le_div_iff₀ hb0 hcd]
    exact (mul_le_mul_of_nonneg_right ha.2 hcd.le).trans
      (mul_le_mul_of_nonneg_left hb.1 hC.le)

namespace SeedData

/-- Seeded data whose other-source coordinate and derivative are those of
the original flow at the fixed other starting point `p`. -/
def fromSource {n : ℕ} (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (κ : ℝ)
    (rr : Fin n → ℝ) (ζ₀ p : ℝ) (V : Fin n → ℝ → ℝ) : SeedData n where
  W := W
  W' := W'
  a := a
  φ := φ
  κ := κ
  r := rr
  ζ₀ := ζ₀
  V₀ := fun t => (fwdMap W t p).re + W t
  G₀ := fun t => (deriv (fwdMap W t) p).re
  V := V

end SeedData

end InteractingSLE.ZhanGT4
