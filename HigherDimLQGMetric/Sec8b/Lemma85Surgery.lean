import HigherDimLQGMetric.Sec8b.StartDrop
import HigherDimLQGMetric.Sec8b.FiniteSets

/-! Deterministic finite shortcut estimate for [S] Lemma 8.5. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- An arbitrary finite collection of disjoint shortcut windows yields the
real-valued inequality used to count very-good centres. -/
theorem s7b_many_shortcuts_real {ι : Type*} [DecidableEq ι]
    (D E : ContMetric d) (P : ℝ → Rd d)
    (Z : Finset ι) (win : ι → ℝ × ℝ) (L : ι → ℝ)
    (C c' total : ℝ)
    (hdisj : (Z : Set ι).PairwiseDisjoint
      (fun z => Ioo (win z).1 (win z).2))
    (hvalid : ∀ z ∈ Z, (win z).1 < (win z).2)
    (hL : ∀ z ∈ Z, 0 ≤ L z)
    (hC : 0 ≤ C) (hc' : 0 ≤ c') (htotal : 0 ≤ total)
    (hlocal : ∀ z ∈ Z,
      ENNReal.ofReal (C * L z) ≤ D.len P (win z).1 (win z).2)
    (hshort : ∀ z ∈ Z,
      E.1 (P (win z).1, P (win z).2) ≤ c' * L z)
    (hlen : ∀ a b : ℝ, a ≤ b → E.len P a b ≤ D.len P a b)
    (hwin : ∀ z ∈ Z, 0 ≤ (win z).1 ∧ (win z).2 ≤ 1)
    (htot : D.len P 0 1 = ENNReal.ofReal total) :
    E.1 (P 0, P 1) + C * ∑ z ∈ Z, L z ≤
      total + c' * ∑ z ∈ Z, L z := by
  have hdrop := s7b_many_window_drop D E P Z win
    (fun z => C * L z) (fun z => c' * L z)
    hdisj hvalid hlocal (fun z hz =>
      ENNReal.ofReal_le_ofReal (hshort z hz)) hlen
    0 1 hwin zero_le_one
  have hLC : ∀ z ∈ Z, 0 ≤ C * L z := fun z hz =>
    mul_nonneg hC (hL z hz)
  have hLc : ∀ z ∈ Z, 0 ≤ c' * L z := fun z hz =>
    mul_nonneg hc' (hL z hz)
  have hsumC : (∑ z ∈ Z, ENNReal.ofReal (C * L z)) =
      ENNReal.ofReal (C * ∑ z ∈ Z, L z) := by
    rw [← ENNReal.ofReal_sum_of_nonneg hLC, Finset.mul_sum]
  have hsumc : (∑ z ∈ Z, ENNReal.ofReal (c' * L z)) =
      ENNReal.ofReal (c' * ∑ z ∈ Z, L z) := by
    rw [← ENNReal.ofReal_sum_of_nonneg hLc, Finset.mul_sum]
  have hsumL : 0 ≤ ∑ z ∈ Z, L z := Finset.sum_nonneg hL
  rw [hsumC, hsumc, htot] at hdrop
  have hreal : E.1 (P 0, P 1) + C * ∑ z ∈ Z, L z ≤
      total + c' * ∑ z ∈ Z, L z := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg htotal (mul_nonneg hc' hsumL))).mp
    rw [ENNReal.ofReal_add (E.nonneg _ _) (mul_nonneg hC hsumL),
      ENNReal.ofReal_add htotal (mul_nonneg hc' hsumL)]
    exact hdrop
  exact hreal

/-- The shortcut inequality and the occupation estimate bound the number
of disjoint very-good centres. -/
theorem s7b_shortcut_card_bound {ι : Type*}
    (Z : Finset ι) (L : ι → ℝ)
    {C c' c H qS k Dbase Ebase total : ℝ}
    (hc' : c' < C) (hqS : 0 < qS)
    (hL : ∀ z ∈ Z, c * qS ≤ L z)
    (hnear : C * Dbase - qS ≤ Ebase)
    (hocc : total ≤ C * Dbase + 2 * C * H * k * qS)
    (hsurgery : Ebase + C * ∑ z ∈ Z, L z ≤
      total + c' * ∑ z ∈ Z, L z) :
    (C - c') * c * (Z.card : ℝ) ≤ 2 * C * H * k + 1 := by
  have hsum : c * qS * (Z.card : ℝ) ≤ ∑ z ∈ Z, L z := by
    have hh := Finset.sum_le_sum (fun z hz => hL z hz)
    simpa only [Finset.sum_const_zero, Finset.sum_const,
      nsmul_eq_mul, mul_comm] using hh
  have hgap : 0 < C - c' := sub_pos.mpr hc'
  have hmain : (C - c') * ∑ z ∈ Z, L z ≤
      (2 * C * H * k + 1) * qS := by
    nlinarith only [hnear, hocc, hsurgery]
  have hmul := mul_le_mul_of_nonneg_left hsum hgap.le
  have hbound : ((C - c') * c * (Z.card : ℝ)) * qS ≤
      (2 * C * H * k + 1) * qS := by
    nlinarith only [hmul, hmain]
  exact le_of_mul_le_mul_right hbound hqS

end HigherDimLQGMetric
