import HigherDimLQGMetric.LfppTight.CrossGeom

/-! Crossing inequalities transport through two-sided multiplicative bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_supPairs_le_of_pointwise {d : ℕ}
    (D E : Rd d × Rd d → ℝ) (A : Set (Rd d)) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ p, D p ≤ a * E p) :
    supPairs D A ≤ ENNReal.ofReal a * supPairs E A := by
  rw [← l6a_supPairs_mul E A ha]
  unfold supPairs
  apply iSup_mono
  intro u
  apply iSup_mono
  intro hu
  apply iSup_mono
  intro v
  apply iSup_mono
  intro hv
  exact ENNReal.ofReal_le_ofReal (h (u, v))

theorem l6a_infPairs_le_of_pointwise {d : ℕ}
    (D E : Rd d × Rd d → ℝ) (A B : Set (Rd d)) {a : ℝ} (ha : 0 < a)
    (h : ∀ p, D p ≤ a * E p) :
    infPairs D A B ≤ ENNReal.ofReal a * infPairs E A B := by
  rw [← l6a_infPairs_mul E A B ha]
  unfold infPairs
  apply iInf_mono
  intro u
  apply iInf_mono
  intro hu
  apply iInf_mono
  intro v
  apply iInf_mono
  intro hv
  exact ENNReal.ofReal_le_ofReal (h (u, v))

theorem l6a_cross_of_biBound {d : ℕ}
    (D E : Rd d × Rd d → ℝ) (A B C : Set (Rd d))
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hDE : ∀ p, D p ≤ a * E p)
    (hED : ∀ p, E p ≤ b * D p)
    (hcross : supPairs E A ≤ ENNReal.ofReal c * infPairs E B C) :
    supPairs D A ≤ ENNReal.ofReal (a * b * c) * infPairs D B C := by
  have hs := l6a_supPairs_le_of_pointwise D E A ha.le hDE
  have hi := l6a_infPairs_le_of_pointwise E D B C hb hED
  calc
    supPairs D A ≤ ENNReal.ofReal a * supPairs E A := hs
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal c * infPairs E B C) := by gcongr
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal c *
        (ENNReal.ofReal b * infPairs D B C)) := by gcongr
    _ = ENNReal.ofReal (a * b * c) * infPairs D B C := by
      simp only [ENNReal.ofReal_mul (mul_nonneg ha.le hb.le),
        ENNReal.ofReal_mul ha.le]
      ac_rfl

theorem l6a_cross_of_perturb_normalized {d : ℕ}
    (D B G : Rd d × Rd d → ℝ) (A S T : Set (Rd d))
    {a t C : ℝ} (ha : 0 < a) (ht : 0 < t) (hC : 0 < C)
    (hDB : ∀ p, D p ≤ a * B p)
    (hBD : ∀ p, B p ≤ a * D p)
    (hBG : B = fun p => t * G p)
    (hcross : supPairs G A ≤
      ENNReal.ofReal (C * a ^ 2)⁻¹ * infPairs G S T) :
    supPairs D A ≤ ENNReal.ofReal C⁻¹ * infPairs D S T := by
  have hcrossB : supPairs B A ≤
      ENNReal.ofReal (C * a ^ 2)⁻¹ * infPairs B S T := by
    rw [hBG]
    exact (l6a_cross_iff_mul G A S T ht).2 hcross
  have h := l6a_cross_of_biBound D B A S T ha ha hDB hBD hcrossB
  have heq : a * a * (C * a ^ 2)⁻¹ = C⁻¹ := by
    field_simp [ha.ne', hC.ne']
  simpa only [heq] using h

end HigherDimLQGMetric
