/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VcCongr

/-!
# SB2(1)'s version half: the relative clock of a lift

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The relative clock at the absolute
physical time `t` of the upper flow, for a lift `γ` after the entrance `t_L` and the lifetime `ζ`:

  `clockOf γ t_L ζ t = sup {capClock γ s | t_L + s ≤ t, t_L + s < ζ}`

(`0` up to `t_L`; the capacity of the lift up to `t − t_L` before the lifetime; constant after the lifetime, equal to
the relative lifetime).

* `clockOf_eq_zero_of_lt` and `clockOf_eq_zero_of_le` (with `capClock γ 0 = 0`): the clock vanishes up to `t_L`;
* **`clockOf_eq`**: for `t_L ≤ t < ζ`, `clockOf … t = capClock γ (t − t_L)` when the capacity clock is monotone on
  `[0, t − t_L]`. These are the clock clauses of `Tc.IsSB2LineChainAt` (with a record's chain:
  `capClock γ 0 = 0` and strict monotonicity on `[0, S₀]`);
* `monotone_clockOf`: the clock is monotone at every sample.

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vc

/-- **The relative clock of a lift** at the absolute physical time `t`. -/
def clockOf (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (ζ : ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : tL + s ≤ t) (_ : ((tL + s : ℝ≥0) : ℝ≥0∞) < ζ),
    ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s)

/-- **The clock is monotone** (at every sample). -/
theorem monotone_clockOf (γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (ζ : ℝ≥0∞) : Monotone (clockOf γ tL ζ) := by
  intro t t' htt'
  exact iSup₂_mono' fun s hs => ⟨s, hs.trans htt', le_rfl⟩

/-- Before the entrance the clock vanishes. -/
theorem clockOf_eq_zero_of_lt {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : t < tL) :
    clockOf γ tL ζ t = 0 := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) zero_le
  exact absurd (lt_of_le_of_lt le_self_add (lt_of_le_of_lt hs ht)) (lt_irrefl _)

/-- **Up to the entrance the clock vanishes** (the capacity clock vanishes at `0`). -/
theorem clockOf_eq_zero_of_le {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : t ≤ tL)
    (h0 : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0 = 0) : clockOf γ tL ζ t = 0 := by
  refine le_antisymm (iSup₂_le fun s hs => iSup_le fun _ => ?_) zero_le
  have hs0 : s = 0 := by
    have : tL + s ≤ tL + 0 := by rw [add_zero]; exact hs.trans ht
    exact le_antisymm (le_of_add_le_add_left this) zero_le
  subst hs0
  rw [NNReal.coe_zero, h0, ENNReal.ofReal_zero]

/-- **Before the lifetime the clock is the capacity clock of the lift at `t − t_L`** (capacity clock monotone on
`[0, t − t_L]`). -/
theorem clockOf_eq {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ζ : ℝ≥0∞} {t : ℝ≥0} (htL : tL ≤ t) (htζ : (t : ℝ≥0∞) < ζ)
    (hmono : MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => γ r.toNNReal) (Icc 0 ((t : ℝ) - tL))) :
    clockOf γ tL ζ t = ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) ((t : ℝ) - tL)) := by
  have hd : tL + (t - tL) = t := add_tsub_cancel_of_le htL
  have hdr : ((t - tL : ℝ≥0) : ℝ) = (t : ℝ) - tL := NNReal.coe_sub htL
  refine le_antisymm (iSup₂_le fun s hs => iSup_le fun _ => ?_) ?_
  · have hs' : (s : ℝ) ≤ (t : ℝ) - tL := by
      have := NNReal.coe_le_coe.2 hs
      rw [NNReal.coe_add] at this
      linarith
    have hnn : (0 : ℝ) ≤ (t : ℝ) - tL := by rw [← hdr]; exact NNReal.coe_nonneg _
    exact ENNReal.ofReal_le_ofReal (hmono ⟨s.2, hs'⟩ ⟨hnn, le_rfl⟩ hs')
  · have h1 : tL + (t - tL) ≤ t := hd.le
    have h2 : ((tL + (t - tL) : ℝ≥0) : ℝ≥0∞) < ζ := by rw [hd]; exact htζ
    have := le_iSup₂ (f := fun (s : ℝ≥0) (_ : tL + s ≤ t) => ⨆ (_ : ((tL + s : ℝ≥0) : ℝ≥0∞) < ζ),
      ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s)) (t - tL) h1
    refine le_trans ?_ this
    rw [hdr]
    exact le_iSup (fun _ : ((tL + (t - tL) : ℝ≥0) : ℝ≥0∞) < ζ =>
      ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) ((t : ℝ) - tL))) h2

end InteractingSLE.Theorem14.SB.Vc
