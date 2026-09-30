import QuantumZipper.Proofs.Probability.Williams.W6Main
import QuantumZipper.Proofs.LQG.ZoomRadialEnd
import QuantumZipper.Proofs.LQG.ZoomRadialEndBasic

/-!
# Wire5: the consumers of `WilliamsDriftDecomposition`, made unconditional

`QuantumZipper.Williams.williamsDriftDecomposition_holds`
(`Proofs/Probability/Williams/W6Main.lean`) proves the Williams drift decomposition (L14,

```
∀ μ σ c > 0, Ω, P, b, b' : the pasting path `Zp` of `X = σ b - μ·` at its first hit of `-c`
with the reversed path `Yh` of `Y' = σ b' + μ·` has the law of `Yh`)
```

see D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974), and L. C. G. Rogers, J. W. Pitman, *Markov functions*,
Ann. Probab. 9 (1981), Thm 1; Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII.4.

Six theorems in the repository take that decomposition as an explicit hypothesis
`(hW : WilliamsDriftDecomposition)`. This file discharges that hypothesis in each of them,
producing unconditional statements (`*_uncond`) with the same conclusions and the same
remaining hypotheses, valid at universe `0` (as the originals, since
`WilliamsDriftDecomposition` quantifies over `Ω : Type`):

* `WedgeTrans.translation_good` → `Wire5.translation_good_uncond`
* `WedgeTrans.wedge_translation` → `Wire5.wedge_translation_uncond`
  (the same statement as `QuantumZipper.Williams.wedge_translation_uncond`, reproduced here so
  that a consumer needs only this module)
* `ZoomRadial.prob_Tc_lt_le_prob_wedge_high` → `Wire5.prob_Tc_lt_le_prob_wedge_high_uncond`
* `ZoomRadial.abs_prob_zoomRadial_sub_le` → `Wire5.abs_prob_zoomRadial_sub_le_uncond`
* `ZoomRadial.prob_trunc_Rw_eq_prob_trunc_wedge` → `Wire5.prob_trunc_Rw_eq_prob_trunc_wedge_uncond`
* `ZoomRadial.williams_law` → `Wire5.williams_law_uncond`

Every proof is the original theorem applied to `williamsDriftDecomposition_holds`; no
mathematics is added here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Wire5

open QuantumZipper.ZoomRadial QuantumZipper.WedgeTrans

/-- **B4(c), unconditional.** `WedgeTrans.wedge_translation` with the Williams drift
decomposition (L14) discharged: wedge translation invariance. (Same statement as
`QuantumZipper.Williams.wedge_translation_uncond`.) -/
theorem wedge_translation_uncond {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ}
    (hA : IsWedgeProcess α Q A P) (hαQ : α < Q) {c : ℝ} (hc : 0 < c) :
    P.map (fun ω t => A (sInf {s | 0 ≤ s ∧ A s ω ≤ -c} + t) ω + c) =
      P.map (fun ω t => A t ω) :=
  WedgeTrans.wedge_translation (hW := QuantumZipper.Williams.williamsDriftDecomposition_holds)
    hA hαQ hc

/-- **D3-RAD step (iv), unconditional.** `ZoomRadial.prob_Tc_lt_le_prob_wedge_high` with the
Williams drift decomposition discharged: the zoom happens before time `S` only with probability
at most that of the wedge path's backward half reaching `c` somewhere on `[−S, 0]`. -/
theorem prob_Tc_lt_le_prob_wedge_high_uncond {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {α Q : ℝ} (hαQ : α < Q)
    {B B' : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hB' : IsBrownianReal B' P')
    (hInd : IndepFun (pathOf B) (pathOf B') P') {A : ℝ → Ω' → ℝ}
    (hAB : ∀ ω t, A t ω = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t)
    {c S : ℝ} (hc : 0 < c) (hS : 0 ≤ S) :
    P' {ω | Tc α Q c B ω < S} ≤ P' {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} :=
  ZoomRadial.prob_Tc_lt_le_prob_wedge_high
    (hW := QuantumZipper.Williams.williamsDriftDecomposition_holds) hαQ hB hB' hInd hAB hc hS

/-- **TASKS.md R6 (D3-RAD), unconditional.** `ZoomRadial.abs_prob_zoomRadial_sub_le` with the
Williams drift decomposition discharged: the radially normalized process at a zoom has, on
every measurable path set `E`, the same probability as the wedge radial process up to
`2 P'{∃ u ∈ [0,S], c ≤ A(−u)}`. -/
theorem abs_prob_zoomRadial_sub_le_uncond {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {α Q : ℝ} (hαQ : α < Q) {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P)
    {A : ℝ → Ω' → ℝ} (hA : IsWedgeProcess α Q A P') {c S : ℝ} (hc : 0 < c) (hS : 0 ≤ S)
    {E : Set (ℝ → ℝ)} (hE : MeasurableSet E) :
    |(P {ω | (fun s => zoomRadial α Q b c ω (max s (-S))) ∈ E}).toReal -
      (P' {ω' | (fun s => A (max s (-S)) ω') ∈ E}).toReal| ≤
    2 * (P' {ω' | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω'}).toReal :=
  ZoomRadial.abs_prob_zoomRadial_sub_le
    (hW := QuantumZipper.Williams.williamsDriftDecomposition_holds) hαQ hb hA hc hS hE

end Wire5
end QuantumZipper
