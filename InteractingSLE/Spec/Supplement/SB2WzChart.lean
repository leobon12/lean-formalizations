/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WzBack

/-!
# SB2(1)'s late (S) line mean, part 9: FIN's chart is the seed-shifted launch chart

Packet PROVE-T14-SB2DRV (round 10). FIN's union mean needs a chart that is conformal at EVERY sample (`hc`, `hcinv`,
`hlift` are pointwise). The launch chart record `I.chart ω` is conformal at every sample, so FIN's chart is taken to be
`Lw.shiftChart (I.chart ω) u 0`:

* **`isConformal_lw_shiftChart`**: `Lw.shiftChart c u m` is conformal whenever `c` is;
* **`shiftChart_recenter`**: `Lw.shiftChart (c.recenter m) u 0 = Lw.shiftChart c u m` — on the launch event
  (`I.chart = launchChart.recenter (launchEntry)`) FIN's chart is the chain record's shifted launch chart;
* **`exists_measurableSet_subset_of_ae`**, **`measurable_fwdHull_switch`**: FIN's hull map `ω ↦ fwdHull (w ω) (t ω)`
  is hitting-measurable as soon as it equals a measurable version on a measurable set and is empty off it.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.SB.Lv

/-- **The seed-shifted chart of a conformal chart is conformal.** -/
theorem isConformal_lw_shiftChart {c : Chart} (hc : c.IsConformal) (u m : ℝ) : (Lw.shiftChart c u m).IsConformal := by
  have hm : MapsTo (fun y : ℂ => y + (m : ℂ)) H H := fun y hy =>
    show 0 < (y + (m : ℂ)).im by have : 0 < y.im := hy; simpa using this
  refine ⟨(hc.1.comp (differentiableOn_id.add_const _) hm).sub_const _, fun y hy => ?_, fun y hy => ?_⟩
  · show 0 < (c.2.1 (y + m) - (u : ℂ)).im
    have : 0 < (c.2.1 (y + m)).im := hc.2.1 (hm hy)
    simpa using this
  · show c.1 (c.2.1 (y + m) - u + u) - m = y
    rw [sub_add_cancel, hc.2.2 _ (hm hy), add_sub_cancel_right]

/-- **The seed-shifted recentred chart is the seed-shifted chart.** -/
theorem shiftChart_recenter (c : Chart) (u m : ℝ) : Lw.shiftChart (c.recenter m) u 0 = Lw.shiftChart c u m := by
  obtain ⟨f, g, l⟩ := c
  simp only [Lw.shiftChart, Chart.recenter, Complex.ofReal_zero, sub_zero, add_zero]

/-- A measurable co-null set inside an almost sure event. -/
theorem exists_measurableSet_subset_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂P, p ω) : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, p ω := by
  refine ⟨(toMeasurable P {ω | ¬ p ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hp
  · by_contra hn
    exact hω (subset_toMeasurable _ _ hn)

/-- **FIN's literal hull map is measurable** once it equals a measurable version on a measurable set and is empty off
it. -/
theorem measurable_fwdHull_switch {Ω : Type*} [mΩ : MeasurableSpace Ω] {G : Set Ω} (hG : MeasurableSet G)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K) {w : Ω → ℝ → ℝ} {t : Ω → ℝ}
    (hon : ∀ ω ∈ G, fwdHull (w ω) (t ω) = K ω) (hoff : ∀ ω ∉ G, fwdHull (w ω) (t ω) = ∅) :
    Measurable[mΩ, hittingSigma] fun ω => fwdHull (w ω) (t ω) := by
  classical
  have e : (fun ω => fwdHull (w ω) (t ω)) = fun ω => if ω ∈ G then K ω else ∅ := by
    funext ω
    by_cases hω : ω ∈ G
    · rw [ite_eq_left hω, hon ω hω]
    · rw [ite_eq_right hω, hoff ω hω]
  rw [e]
  exact Measurable.ite hG hKm measurable_const

end InteractingSLE.Theorem14.SB.Lv
