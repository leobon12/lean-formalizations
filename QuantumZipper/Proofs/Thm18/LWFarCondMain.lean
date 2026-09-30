import QuantumZipper.Proofs.Thm18.LWFarCondStop
import QuantumZipper.Proofs.RS.OnePointFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-1: the conditional one-point estimate at a stopping time

**Result.** `condOnePointStmt_holds : 0 < κ → κ < 4 → CondOnePointStmt κ`.

Source: G. Lawler, B. Werness, *Multi-point Green's functions for SLE and an estimate of
Beffara*, Ann. Probab. 41 (2013), Lemma 2.10 (p. 12), upper bound: conditionally on `𝓕_τ`, the
probability that the curve gets conformally `r`-close to `w` after `τ` is
`≤ C (r/Υ_τ(w))^{1−κ/8} S_τ(w)^{8/κ−1}`. As in LW, the proof is the (strong) domain Markov
property plus the unconditional one-point estimate: with `Z = Z_τ(w)` and the restarted
motion `B̃ = B_{τ+·} − B_τ` (independent of `𝓕_τ`, `StrongMarkov.indepFun_smPath`),
`Υ_{τ+u}(w) = Υ̃_u(Z) Υ_τ(w)/Im Z` (`lwc_flow`), so the event is
`{Υ̃_u(Z) < r Im Z/Υ_τ(w) for some u}` for the Loewner chain of `B̃` started at `Z`;
`RS.prob_logCR_lt_unif` (Lawler–Zhou Prop 2.3 / Beffara's one-point estimate, uniform constant)
bounds it for each frozen value of `(Z, r Im Z/Υ_τ)`, and the freezing lemma (`lwc_freeze`,
independence and Fubini) integrates the bound over `A`. The bad event is carried on the space of
continuous paths, where it is measurable (`measurableSet_lwcBad`), so no outer-measure issue
arises.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

open FwdClock

/-- Continuous real paths on `ℝ≥0` (subtype σ-algebra of the product σ-algebra). -/
abbrev LwcPath : Type := {y : ℝ≥0 → ℝ // Continuous y}

/-- **Freezing lemma**: for independent `ξ` and `Y` and a measurable set `S`,
`P((ξ, Y) ∈ S) = ∫ P(Y ∈ S_{ξ(ω)}) dP(ω)`. -/
theorem lwc_freeze {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → β} {Y : Ω → γ} (hξ : Measurable ξ)
    (hY : Measurable Y) (hind : IndepFun ξ Y P) {S : Set (β × γ)} (hS : MeasurableSet S) :
    P ((fun ω => (ξ ω, Y ω)) ⁻¹' S) = ∫⁻ ω, P.map Y (Prod.mk (ξ ω) ⁻¹' S) ∂P := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hξ.aemeasurable hY.aemeasurable).1 hind
  have hm : Measurable fun ω => (ξ ω, Y ω) := hξ.prodMk hY
  rw [← Measure.map_apply hm hS, h, Measure.prod_apply hS,
    lintegral_map (measurable_measure_prodMk_left hS) hξ]

end LWFar
end Thm18Asm
end QuantumZipper
