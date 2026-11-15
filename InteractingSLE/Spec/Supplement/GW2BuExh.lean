/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuGood

/-!
# The caps exhaust every value below the stage life

Packet PROVE-GW2-BUF (round 18; deterministic, one sample). The root-`x` clock `a` is `0` at `0`, continuous and
strictly increasing before the contact `T_c`, and bounded there. Its supremum is the relative life `L`. Decision
D27's exhaustion says the caps exhaust every clock value below the death clock `d`.

* **`clock_lt_life`**: before the contact the clock is strictly below `L`;
* **`exhausts_below_min`**: the caps exhaust every value below `min (L, d)` (an intermediate clock value between the
  value and `d`, when the clock passes `d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

variable {a : ℝ≥0 → ℝ} {Tc : ℝ≥0∞}

/-- **Before the contact the clock is strictly below its supremum.** -/
theorem clock_lt_life (hsm : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc}) {M : ℝ}
    (hM : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t ≤ M) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Tc) :
    a t < sSup (a '' {t | (t : ℝ≥0∞) < Tc}) := by
  have hAbdd : BddAbove (a '' {t | (t : ℝ≥0∞) < Tc}) := ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM t ht⟩
  obtain ⟨t', htt', ht'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  exact (hsm ht ht' (ENNReal.coe_lt_coe.1 htt')).trans_le (le_csSup hAbdd ⟨t', ht', rfl⟩)

/-- **The caps exhaust every value below `min (L, d)`.** -/
theorem exhausts_below_min (ha0 : a 0 = 0) (hTc : 0 < Tc) (hac : ContinuousOn a {t | (t : ℝ≥0∞) < Tc})
    {M : ℝ} (hM : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t ≤ M) {d : ℝ≥0∞} {V : ℕ → ℝ≥0∞}
    (hD : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ENNReal.ofReal (a t) < d → ∀ᶠ n in atTop, ENNReal.ofReal (a t) < V n) :
    ∀ q : ℝ≥0∞, q < min (ENNReal.ofReal (sSup (a '' {t | (t : ℝ≥0∞) < Tc}))) d →
      ∀ᶠ n in atTop, q < V n := by
  intro q hq
  set A := a '' {t | (t : ℝ≥0∞) < Tc} with hAdef
  have hAne : A.Nonempty := ⟨a 0, 0, show ((0 : ℝ≥0) : ℝ≥0∞) < Tc by rw [ENNReal.coe_zero]; exact hTc, rfl⟩
  have hqL : q < ENNReal.ofReal (sSup A) := hq.trans_le (min_le_left _ _)
  have hqd : q < d := hq.trans_le (min_le_right _ _)
  have hqfin : q ≠ ⊤ := ne_top_of_lt hqL
  have hqr : q.toReal < sSup A := by
    have h := (ENNReal.lt_ofReal_iff_toReal_lt hqfin).1 hqL
    exact h
  obtain ⟨_, ⟨t₁, ht₁, rfl⟩, hq₁⟩ := exists_lt_of_lt_csSup hAne hqr
  have hq₁' : q < ENNReal.ofReal (a t₁) := (ENNReal.lt_ofReal_iff_toReal_lt hqfin).2 hq₁
  by_cases hd₁ : ENNReal.ofReal (a t₁) < d
  · filter_upwards [hD t₁ ht₁ hd₁] with n hn
    exact hq₁'.trans hn
  · rw [not_lt] at hd₁
    have hdfin : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd₁
    set v : ℝ := (q.toReal + d.toReal) / 2 with hv
    have hqd' : q.toReal < d.toReal := (ENNReal.toReal_lt_toReal hqfin hdfin).2 hqd
    have hv1 : q.toReal < v := by rw [hv]; linarith
    have hv2 : v < d.toReal := by rw [hv]; linarith
    have ha₁ : 0 ≤ a t₁ := le_trans ENNReal.toReal_nonneg hq₁.le
    have hdle : d.toReal ≤ a t₁ := ENNReal.toReal_le_of_le_ofReal ha₁ hd₁
    have hv0 : 0 ≤ v := le_trans ENNReal.toReal_nonneg hv1.le
    have hcont : ContinuousOn a (Icc 0 t₁) :=
      hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₁
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₁) hcont
      ⟨by rw [ha0]; exact hv0, (hv2.trans_le hdle).le⟩
    have htT : (t : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₁
    have hvd : ENNReal.ofReal (a t) < d := by
      rw [hteq]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hv0 hdfin).2 hv2
    have hqv : q < ENNReal.ofReal (a t) := by
      rw [hteq]
      exact (ENNReal.lt_ofReal_iff_toReal_lt hqfin).2 hv1
    filter_upwards [hD t htT hvd] with n hn
    exact hqv.trans hn

end InteractingSLE.Theorem14.GW2Bh
