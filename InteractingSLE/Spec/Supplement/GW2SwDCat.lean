/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProb

/-!
# Associativity of driver concatenation

Packet PROVE-GW2-SWITCH (round 4). J31's joined record reads Proposition 5.13's back-nested
concatenation (`joinedDriver`: piece `j` followed by the concatenation of the later pieces), while
`Swc.joinDrv` is front-nested (the concatenation of the earlier pieces followed by piece `k`). The two
agree because `catPath` is associative when the middle driver starts at `0`:

* **`catPath_assoc`**: `catPath (catPath w₀ a w₁) (a + b) w₂ = catPath w₀ a (catPath w₁ b w₂)`.
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.SwD

open Sec7.StripSideHeightProb

/-- **Concatenation of drivers is associative** (the middle driver starts at `0`). -/
theorem catPath_assoc {w₀ w₁ w₂ : ℝ≥0 → ℝ} (h10 : w₁ 0 = 0) (a b : ℝ≥0) :
    catPath (catPath w₀ a w₁) (a + b) w₂ = catPath w₀ a (catPath w₁ b w₂) := by
  funext t
  by_cases hta : t ≤ a
  · have htab : t ≤ a + b := hta.trans le_self_add
    simp only [catPath, hta, htab, ↓reduceIte]
  · by_cases htab : t ≤ a + b
    · have hb : t - a ≤ b := tsub_le_iff_left.2 htab
      simp only [catPath, hta, htab, hb, ↓reduceIte]
    · have hb : ¬ t - a ≤ b := fun h => htab (tsub_le_iff_left.1 h)
      simp only [catPath, hta, htab, hb, ↓reduceIte]
      rw [tsub_tsub]
      split_ifs with h
      · have hb0 : b = 0 := le_antisymm (by simpa using h) bot_le
        subst hb0
        rw [add_zero, h10, zero_add]
      · rw [add_tsub_cancel_left]
        ring

end InteractingSLE.Theorem14.GW2TipSystem.SwD
