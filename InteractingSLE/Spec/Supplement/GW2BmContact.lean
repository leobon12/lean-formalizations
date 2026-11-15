/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BlContact
import InteractingSLE.Spec.Supplement.SB2VoCol
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# The contact clause by the law route (decision D17 (B), provisional): its deterministic core

Packet PROVE-GW2-BUF (round 10). D17 (B): on `[0, L)` (`L` the relative life, the first contact) the relative driver
`D` equals a canonical stage flow-line driver `Wc` (the stage law, an input owned by STAGEMEAN/RELDET). Theorem 1.3
makes `Wc`'s trace continuous up to its own lifetime `≥ L`. Then:

* **`gapVanishes_of_canonical`**: if the canonical trace at `L` is a real point at or right of the label `x ≥ 0`
  (nonzero, with the zero gap of `Wc` open before `L`), the gap of `x` along `D` vanishes as the relative time
  approaches `L` (`GapVanishes D x L`, the isolated contact clause). The proof:
  * NOJUMP's `SB.Vo.rightImg_eq_iff_real_tip` collides `x` with `Wc` at `L`;
  * the gap of `Wc` is continuous;
  * `D` and `Wc` have the same gaps before `L` (`GB6.rightImg_congr`).

  NOJUMP's `SB.Vn.tendsto_of_eqOn_canonical` is not needed here, since the gap is read along `Wc` itself.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow

/-- **The contact clause from a canonical driver whose trace reaches a real point beyond the label.** -/
theorem gapVanishes_of_canonical {D Wc : ℝ → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {L : ℝ} (hL : 0 < L)
    (hagree : ∀ r ∈ Ico 0 L, D r = Wc r) {ηc : ℝ → ℂ} (hη : IsLoewnerTraceLT Wc L ηc)
    (hc : ContinuousOn ηc (Icc 0 L)) (hsep : ∀ t ∈ Ioo 0 L, Wc t < rightImg Wc 0 t) (hne : ηc L ≠ 0)
    (him : (ηc L).im = 0) {x : ℝ} (hx : 0 ≤ x) (hxle : x ≤ (ηc L).re) : GapVanishes D x L := by
  have hcol : rightImg Wc x L = Wc L :=
    (SB.Vo.rightImg_eq_iff_real_tip hWc hWc0 hL hη hc hsep hne hx).2 ⟨him, hxle⟩
  have hG : ContinuousOn (fun t => rightImg Wc x t - Wc t) (Ici 0) :=
    (continuousOn_rightImg hWc x).sub hWc.continuousOn
  intro ε hε c₀ hc₀
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hG L (show (0 : ℝ) ≤ L from hL.le)) ε hε
  set d := min (min ((L - c₀) / 2) (δ / 2)) (L / 2) with hd
  have hd0 : 0 < d := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hd1 : d ≤ (L - c₀) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : d ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ L / 2 := min_le_right _ _
  refine ⟨L - d, by linarith, by linarith, ?_⟩
  have hmem : L - d ∈ Ici (0 : ℝ) := show (0 : ℝ) ≤ L - d by linarith
  have hdist : dist (L - d) L < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    linarith
  have h1 := hball hmem hdist
  rw [Real.dist_eq, hcol, sub_self, sub_zero] at h1
  have hcongr : rightImg D x (L - d) = rightImg Wc x (L - d) :=
    Supp8.GB6.rightImg_congr hWc (by linarith) fun r hr => hagree r ⟨hr.1, by linarith [hr.2]⟩
  rw [hcongr, hagree (L - d) ⟨by linarith, by linarith⟩]
  exact lt_of_abs_lt h1

end InteractingSLE.Theorem14.GW2Bh
