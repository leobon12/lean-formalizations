/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WzChart
import InteractingSLE.Spec.Supplement.SB2LkDom

/-!
# SB2(1)'s late (S) line mean, part 10: the lift is interior where the tip is in the chart domain

Packet PROVE-T14-SB2DRV (round 11), the input `hγH : γ (t − T_L) ∈ ℍ` of `FinRel.isRelConfigJK_of_s2_liftOn` from the
named hypothesis `SB2JxTipStatement` (`η t ∈ (I.chart ω).dom`):

* **`lift_mem_H_of_mem_image`** (generic): for a conformal chart with a boundary map `g` (continuous on `ℍ̄`, the
  inverse on `ℍ`), a point `y ∈ ℍ̄` with `g y` in the chart image of `ℍ` lies in `ℍ` (`Lk.ext_notMem_image`);
* **`lift_mem_H_of_tip`**: for the components of the per-time chain record (the shifted launch chart
  `Lw.shiftChart c u m`, its boundary map `g`, the S2 lift `γ` with `g (γ s) = β' (t_L + s)`, and `β' t = η t − u`), if
  the tip `η t` is in `c.2.1 '' ℍ` and `t_L ≤ t`, then `γ (t − t_L) ∈ ℍ`.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lv

/-- **A point of `ℍ̄` whose boundary-map image is in the chart image of `ℍ` lies in `ℍ`.** -/
theorem lift_mem_H_of_mem_image {c : Chart} (hc : c.IsConformal) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {y : ℂ} (hy : 0 ≤ y.im)
    (hmem : g y ∈ c.2.1 '' H) : y ∈ H := by
  by_contra hyH
  have hinj : InjOn c.2.1 H := fun a ha a' ha' e => by rw [← hc.2.2 a ha, e, hc.2.2 a' ha']
  exact Lk.ext_notMem_image hc.1 hinj hgc hgi hy hyH hmem

/-- **The S2 lift at the line time is interior when the tip is in the launch chart's image.** -/
theorem lift_mem_H_of_tip {c : Chart} {u m : ℝ} (hc : (Lw.shiftChart c u m).IsConformal) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (Lw.shiftChart c u m).2.1 H) {β' γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) {tL t : ℝ≥0} (hlift : ∀ s, g (γ s) = β' (tL + s)) {η : ℝ≥0 → ℂ}
    (hβt : β' t = η t - u) (htip : η t ∈ c.2.1 '' H) (htL : tL ≤ t) : γ (t - tL) ∈ H := by
  refine lift_mem_H_of_mem_image hc hgc hgi (hγ.2.2.1 _) ?_
  rw [hlift, add_tsub_cancel_of_le htL, hβt]
  obtain ⟨w, hw, hwη⟩ := htip
  refine ⟨w - m, ?_, ?_⟩
  · show 0 < (w - (m : ℂ)).im
    have : 0 < w.im := hw
    simpa using this
  · show c.2.1 (w - m + m) - u = η t - u
    rw [sub_add_cancel, hwη]

end InteractingSLE.Theorem14.SB.Lv
