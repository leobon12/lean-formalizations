/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Order
import InteractingSLE.Spec.Sec7.SideAncOrient

/-!
# Source-wall landings and the counterflow marks in the same coordinate

PROVE-SIDE-COLLAR2. Retain the actual disc times of boundary landings.
The marked counterflow coordinate is the negative inverse of the real
flow boundary value, so its position comparisons follow from arc order.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open scoped NNReal

namespace InteractingSLE.Sec7.SideC15

open WangWu PocketCoord PocketJordan Aux119Bdry Lemma71I Lemma71O SideAnc

/-- Every negative flow coordinate lands at a point of the open left
arc, with its actual disc time and its exact uniformizer value. -/
theorem exists_left_flowArc_landing {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : ξ < 0) :
    ∃ t ∈ Ioo (leftLo R L r) (leftHi R L r),
      land c ξ = L (arcTime t).toNNReal ∧ Ψ (toDisc (realPath L) t) = (ξ : ℂ) := by
  have h := hF.config
  have hξH : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨z, hz, hΨz, _⟩ := hF.exists_tendsto hξH
  rcases mem_open_arcs h hF.unif hz (by rw [hΨz]; simp) (by rw [hΨz]; exact_mod_cast hξ.ne) with
    ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · have hp := hF.orient Ψ hF.unif s hs
    rw [hΨz, Complex.ofReal_re] at hp
    exact (not_lt_of_gt hξ hp).elim
  · refine ⟨t, ht, ?_, hΨz⟩
    rw [hF.land_eq hξH hz hΨz]
    exact cayleyInv_toDisc h.left (ht.2.trans_le h.changeCorner_props.2.2.2.2.1.2)

/-- The corresponding exact landing on the open right arc. -/
theorem exists_right_flowArc_landing {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ t ∈ Ioo (rightLo R L r) (rightHi R L r),
      land c ξ = R (arcTime t).toNNReal ∧ Ψ (toDisc (realPath R) t) = (ξ : ℂ) := by
  have h := hF.config
  have hξH : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨z, hz, hΨz, _⟩ := hF.exists_tendsto hξH
  rcases mem_open_arcs h hF.unif hz (by rw [hΨz]; simp) (by rw [hΨz]; exact_mod_cast hξ.ne') with
    ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · refine ⟨s, hs, ?_, hΨz⟩
    rw [hF.land_eq hξH hz hΨz]
    exact cayleyInv_toDisc h.right (hs.2.trans_le h.changeCorner_props.2.1.2)
  · have hn := h.re_neg_left_of_re_pos hF.unif (hF.orient Ψ hF.unif) t ht
    rw [hΨz, Complex.ofReal_re] at hn
    exact (not_lt_of_gt hξ hn).elim

/-- Read a counterflow boundary mark directly in the flow coordinate.
The statement is algebraic and retains the original Jordan chart. -/
theorem counterflow_mark_eq_neg_inv {p w : ℂ} {ψ : ℂ → ℂ}
    (hwp : w ≠ p) (him : (jordanUnif p ψ w).im = 0) :
    (ψ (cfPt w)).re = -((jordanUnif p ψ w).re)⁻¹ := by
  have hψ : ψ (cfPt w) = negInv (jordanUnif p ψ w) := by
    rw [jordanUnif_of_ne hwp, negInv_negInv]
  have he : jordanUnif p ψ w = ((jordanUnif p ψ w).re : ℂ) := by
    apply Complex.ext
    · exact (Complex.ofReal_re _).symm
    · rw [Complex.ofReal_im]
      exact him
  rw [hψ, he]
  simp only [negInv, ← Complex.ofReal_inv, ← Complex.ofReal_neg, Complex.ofReal_re]

/-- The negative inverse preserves order within the negative half-line. -/
theorem neg_inv_le_neg_inv_iff_of_neg {x y : ℝ} (hx : x < 0) (hy : y < 0) :
    -x⁻¹ ≤ -y⁻¹ ↔ x ≤ y := by
  rw [neg_le_neg_iff, inv_le_inv_of_neg hy hx]

/-- The same order identity in the positive half-line. -/
theorem neg_inv_lt_neg_inv_iff_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    -x⁻¹ < -y⁻¹ ↔ x < y := by
  rw [neg_lt_neg_iff, inv_lt_inv₀ hy hx]

end InteractingSLE.Sec7.SideC15
