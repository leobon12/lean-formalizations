/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Bdry

/-!
# Aux. lemma 119: the own heights become the heights (PW13.1) of the flow chart

Packet PROVE-STRIPSYS22. Specification §7.4, the proof of Aux. lemma 119 (`source/spec/p385-432.md` L33, L50,
pp. 386–387):

> Hence the own height `λ − θ_Lχ` on a right side of the left path, and `−λ − θ_Rχ` on a left side of the right path,
> become exactly the two heights in (PW13.1) in the final chart. […] On every compact selected open side, nested
> local-set boundary comparison makes the mean `h_A` agree at the boundary with its single-path own mean. […] In the
> `φ` coordinate they are (PW13.1).

The coordinate mean of a field mean `v` in a chart `c` with lift `ℓ` is `v ∘ c⁻¹ + u₀ ∘ c⁻¹ + χ ℓ ∘ c⁻¹` (the coordinate
rule (1.4) applied to the mean). At a real chart point `ξ` whose landing point is a wall point `w`, the boundary value
of the shifted lift `ℓ + 2πn` is the own derivative argument of the wall's prefix (Aux. lemma 119's common lift,
`Lemma71N.IsPocketBranch`), so any own height of the wall at `w`, transferred to `v` by the nested comparison, is the
boundary value of the coordinate mean at `ξ` (`tendsto_chartMean_of_own`). For the change pocket's flow chart this
gives (PW13.1) at every real point but `0`, with the actual heights of the wall pieces at the landing points
(`IsFlowChart.tendsto_chartMean_neg`, `IsFlowChart.tendsto_chartMean_pos`).

The own heights (Proposition 6.1/Aux. lemma 70 for the wall pieces, at genuine own stopping times) and the nested
comparisons (Proposition 3.8) are hypotheses here, stated along the pocket approach `𝓝[C] w`; the identification of
the mean as the bounded Poisson extension (Aux. lemmas 27–28: no singular term at the finitely many exceptional points)
is not part of this file.

## Main results

* `tendsto_comp_land`: the chart inverse carries the approach to `ξ` from `ℍ` into the pocket approach to its landing
  point;
* **`tendsto_chartMean_of_own`** (one chart point, abstract filters);
* **`IsFlowChart.tendsto_chartMean_neg`**, **`IsFlowChart.tendsto_chartMean_pos`**: (PW13.1) on `ℝ₋` along the left
  wall and on `ℝ₊` along the right wall.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar logDerivFwd)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux119Own

open Lemma71O (land)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketJordan PocketMarks Aux119Bdry

/-- **The coordinate mean at one chart point from an own height** (Aux. lemma 119: "Hence the own height […] become[s]
exactly the two heights in (PW13.1) in the final chart"): if the shifted lift `ℓ + 2πn` has the boundary value of an own
derivative argument at `ξ`, the chart inverse carries the approach to `ξ` into a filter `F`, and along `F` the mean `v`
agrees with an own mean `v_q` (`v − v_q → 0`, nested comparison) whose own coordinate mean tends to `h`, then the
coordinate mean of `v` in the chart tends to `h` at `ξ`. -/
theorem tendsto_chartMean_of_own {c : Chart} {n : ℤ} {W : ℝ≥0 → ℝ} {q : ℝ≥0} {ξ : ℝ} {F : Filter ℂ}
    (hbr : Tendsto (fun y => c.2.2 (c.2.1 y) + 2 * π * n -
      (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 0))
    (hland : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) F) {v vq u₀ : ℂ → ℝ} {χ h : ℝ}
    (hcmp : Tendsto (fun z => v z - vq z) F (𝓝 0))
    (hown : Tendsto (fun z => vq z + u₀ z + χ * (logDerivFwd (fun r : ℝ => W r.toNNReal) q z).im) F (𝓝 h)) :
    Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ)) (𝓝 h) := by
  have h1 := hcmp.comp hland
  have h2 := hown.comp hland
  have h3 := hbr.const_mul χ
  have hsum := (h1.add h2).add h3
  rw [zero_add, mul_zero, add_zero] at hsum
  refine hsum.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

/-- **The chart inverse carries the approach to `ξ` into the pocket approach to the landing point.** -/
theorem tendsto_comp_land {c : Chart} {C : Set ℂ} (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) {ξ : ℂ}
    {w : ℂ} (hl : Tendsto c.2.1 (𝓝[H] ξ) (𝓝 w)) : Tendsto c.2.1 (𝓝[H] ξ) (𝓝[C] w) :=
  tendsto_nhdsWithin_iff.2 ⟨hl, eventually_nhdsWithin_of_forall fun y hy => by
    rw [← hdom]; exact hc.inv_mem_dom hy⟩

namespace IsFlowChart

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

/-- **(PW13.1) on `ℝ₋`** (the left incoming arc): for the common lift's integer `n` of the change pocket's flow chart,
if at every point `L s` of the open left arc, for some own time `q > s`, the mean `v` agrees along the pocket approach
with the own mean `vL q` of the left wall's prefix (nested comparison) and that own mean has the own height `hL s` in
the own chart, then at every negative chart point the coordinate mean of `v` tends to the height of its landing
point. -/
theorem tendsto_chartMean_neg (hF : IsFlowChart R L r Ψ c) {n : ℤ} (hn : IsPocketBranch L R c n)
    {WL WR : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L) (htrR : IsGeneratingTrace WR ⊤ R)
    {v u₀ : ℂ → ℝ} {vL : ℝ≥0 → ℂ → ℝ} {χ : ℝ} {hL : ℝ≥0 → ℝ}
    (hown : ∀ s : ℝ≥0, L s ∉ range R → ∃ q : ℝ≥0, s < q ∧
      Tendsto (fun z => v z - vL q z) (𝓝[changePocket R L r] (L s)) (𝓝 0) ∧
      Tendsto (fun z => vL q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WL t.toNNReal) q z).im)
        (𝓝[changePocket R L r] (L s)) (𝓝 (hL s))) {ξ : ℝ} (hξ : ξ < 0) :
    ∃ s : ℝ≥0, L s ∉ range R ∧ land c ξ = L s ∧
      Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ))
        (𝓝 (hL s)) := by
  have hT := hF.isTwoArcFrame
  obtain ⟨s, hsR, hs⟩ := hT.neg ξ hξ
  have hl : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (L s)) := hs ▸ hT.tendsto_land (mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨q, hsq, hcmp, hown⟩ := hown s hsR
  have hbr := (hn WL WR htrL htrR ξ s q hsq).1 hξ hl
  exact ⟨s, hsR, hs, tendsto_chartMean_of_own hbr (tendsto_comp_land hF.conf hF.dom hl) hcmp hown⟩

/-- **(PW13.1) on `ℝ₊`** (the right incoming arc), as `tendsto_chartMean_neg` with the right wall. -/
theorem tendsto_chartMean_pos (hF : IsFlowChart R L r Ψ c) {n : ℤ} (hn : IsPocketBranch L R c n)
    {WL WR : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L) (htrR : IsGeneratingTrace WR ⊤ R)
    {v u₀ : ℂ → ℝ} {vR : ℝ≥0 → ℂ → ℝ} {χ : ℝ} {hR : ℝ≥0 → ℝ}
    (hown : ∀ s : ℝ≥0, R s ∉ range L → ∃ q : ℝ≥0, s < q ∧
      Tendsto (fun z => v z - vR q z) (𝓝[changePocket R L r] (R s)) (𝓝 0) ∧
      Tendsto (fun z => vR q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WR t.toNNReal) q z).im)
        (𝓝[changePocket R L r] (R s)) (𝓝 (hR s))) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ s : ℝ≥0, R s ∉ range L ∧ land c ξ = R s ∧
      Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ))
        (𝓝 (hR s)) := by
  have hT := hF.isTwoArcFrame
  obtain ⟨s, hsL, hs⟩ := hT.pos ξ hξ
  have hl : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (R s)) := hs ▸ hT.tendsto_land (mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨q, hsq, hcmp, hown⟩ := hown s hsL
  have hbr := (hn WL WR htrL htrR ξ s q hsq).2 hξ hl
  exact ⟨s, hsL, hs, tendsto_chartMean_of_own hbr (tendsto_comp_land hF.conf hF.dom hl) hcmp hown⟩

end IsFlowChart

end InteractingSLE.Sec7.Aux119Own
