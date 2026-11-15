/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BlCmp
import InteractingSLE.Spec.Sec2.MartingaleFinalImage

/-!
# The contact clause, isolated (decision D17 pending), and its deterministic consequence

Packet PROVE-GW2-BUF (round 9). D12's "exit before contact" needs one input about the relative chart at the relative
life `L` (the first contact): the gap of a tail junction label gets arbitrarily small as the relative time approaches
`L`. This file states it as one predicate, which every option of D17 proves:

* `GapVanishes U x L`: for every `ε > 0` and every `c₀ < L` some `c ∈ (c₀, L)` has `rightImg U x c − U c < ε`
  (`liminf_{c ↑ L}` of the gap is `0`).
  * Options (A) (Pommerenke) and (B) (the law route) give the relative trace continuous on `[0, L]` and real at `L`.
    NOJUMP's `SB.Vo.rightImg_eq_iff_real_tip` then collides the junction at `L`, and the gap tends to `0`.
  * Option (C) (a Beurling-type estimate) gives it directly.

The deterministic consequence:

* **`exists_gap_eq_before`**: if the gap at the stage start `S < L` is above a level `g > 0`, it equals `g` at some
  relative time strictly between `S` and `L`;
* **`exists_cmp_gap_eq_before`**: the comparison gap (restarted at `S`, scaled by `b > 0`) then equals any level
  `g' > 0` it starts above, at a comparison time `b² u` with `0 < u` and `S + u < L`. A buffer requiring gap `> g'`
  is left there, strictly before contact.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Sec5.Prop59NodeTree Sec5.CrossCond.StagedRepLater

/-- **The contact clause**: the gap of the label `x` gets arbitrarily small as the relative time approaches `L`. -/
def GapVanishes (U : ℝ → ℝ) (x L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ c₀ : ℝ, c₀ < L → ∃ c : ℝ, c₀ < c ∧ c < L ∧ rightImg U x c - U c < ε

variable {U : ℝ → ℝ}

/-- **Before the relative life the gap crosses every level it starts above.** -/
theorem exists_gap_eq_before (hU : Continuous U) {x L S g : ℝ} (hvan : GapVanishes U x L) (hS : 0 ≤ S)
    (hSL : S < L) (hg : 0 < g) (h0 : g < rightImg U x S - U S) :
    ∃ c, S < c ∧ c < L ∧ rightImg U x c - U c = g := by
  have hc : ContinuousOn (fun t => rightImg U x t - U t) (Ici 0) :=
    (continuousOn_rightImg hU x).sub hU.continuousOn
  obtain ⟨c₀, hSc₀, hc₀L, hc₀⟩ := hvan g hg S hSL
  obtain ⟨c, hc', hcg⟩ := intermediate_value_Icc' hSc₀.le (hc.mono fun t ht => le_trans hS ht.1)
    (show g ∈ Icc (rightImg U x c₀ - U c₀) (rightImg U x S - U S) from ⟨hc₀.le, h0.le⟩)
  refine ⟨c, lt_of_le_of_ne hc'.1 fun h => ?_, hc'.2.trans_lt hc₀L, hcg⟩
  rw [← h] at hcg
  exact (lt_irrefl g) (hcg ▸ h0)

/-- **The comparison gap reaches every buffer level before contact**, under the contact clause. -/
theorem exists_cmp_gap_eq_before (hU : Continuous U) {x L S : ℝ} (hvan : GapVanishes U x L) (hS : 0 ≤ S)
    (hSL : S < L) {b : ℝ} (hb : 0 < b) {g' : ℝ} (hg' : 0 < g')
    (h0 : g' < rightImg (scD b (shiftDrv U S)) (b * (rightImg U x S - U S)) (b ^ 2 * 0) -
      scD b (shiftDrv U S) (b ^ 2 * 0)) :
    ∃ u : ℝ, 0 < u ∧ S + u < L ∧
      rightImg (scD b (shiftDrv U S)) (b * (rightImg U x S - U S)) (b ^ 2 * u) -
        scD b (shiftDrv U S) (b ^ 2 * u) = g' := by
  have h0' : g' / b < rightImg U x S - U S := by
    rw [gap_cmp_eq hU hS hb x le_rfl, add_zero] at h0
    rw [div_lt_iff₀ hb, mul_comm]
    exact h0
  obtain ⟨c, hSc, hcL, hcg⟩ := exists_gap_eq_before hU hvan hS hSL (div_pos hg' hb) h0'
  refine ⟨c - S, by linarith, by linarith, ?_⟩
  rw [gap_cmp_eq hU hS hb x (by linarith), add_sub_cancel, hcg, mul_div_cancel₀ _ hb.ne']

end InteractingSLE.Theorem14.GW2Bh
