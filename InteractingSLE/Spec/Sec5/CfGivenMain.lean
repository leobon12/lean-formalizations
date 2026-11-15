/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfGivenChart

/-!
# Lemma 4.7's conditional law at a switch time from its fixed-time chart form

Packet PROVE-CFGIVEN. The named input of PROVE-SWITCHED, `RestartSw.CounterflowGivenPrefixStatement` (the counterflow
given a stopped flow-line prefix, under the regular conditional law given the prefix's record), is reduced here to
`CfGivenChartStatement`: the **unconditional** statement on the given space, with the coupling clause of the image
counterflow in the chart form at fixed times — the form in which the cross-conditioning chain proves it
(`Sec5.Lemma47Angle.isChartCouplingCharFunConst_q_angle` on the glued space,
`Sec7.Lemma71D.IsChartCouplingCharFunConst`).

With `R = recOf t₀ D` (the record of the flow prefix) and `𝒢 = σ(R)`, the statement asks for a raw filtration
`𝓐 ⊇ 𝒢`, a word type `(nL, nR, ρL, ρR)` with `𝒢`-measurable ordered positions `(xL, xR)` (almost surely a flow-type
word at `16/κ`), a globally continuous `𝓐`-adapted driver `W″` from `0` with almost surely infinite continuation
threshold, and a family `η″`, such that

* (chart clause) the field `−h` read in the image charts `cfChart R = (recChart R).trans R` with `(a, k) = (−πχ, −χ)`
  has, given `𝓐_t` and at every fixed image time `t`, the Gaussian law of the image word's coupling mean
  (Lemma 4.7's coupling in the image chart; spec p. 118, Propositions 3.7–3.8);
* (L) the image hulls are local for the image field (K2's `HasSafeMembers`; `hasSafeMembers_imgField_of_loc` derives
  it from the locality of the physical union of the prefix and the counterflow hull);
* the image field has integrable pairings;
* almost surely `η″` generates `W″` and a continuous increasing clock carries it to the physical counterflow.

## Main results

* `CfGivenChartStatement` (named input);
* **`cfGivenPSideStatement_of_chart`**: `CfGivenChartStatement → CfGivenPSideStatement`
  (`hasSafeLaw_imgField_of_chartConst`);
* **`counterflowGivenPrefixStatement_of_chart`**: `CfGivenChartStatement → RestartSw.CounterflowGivenPrefixStatement`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfGiven

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal
open Exist Exist.Staged Exist.StagedLaw
open WangWu (negInv)

/-- **Named input: Lemma 4.7's conditional law at a deterministic own time, unconditional fixed-time chart form**
(spec p. 118, Lemma 4.7's proof: the conditional law of `η′` given `η([0, τ])` from Propositions 3.7–3.8 and
Theorem 2.4; Lemma 5.7's proof, p. 138). Binders verbatim from `RestartSw.CounterflowGivenPrefixStatement`; the
conclusion is that of `CfGivenPSideStatement` with K2's (S) replaced by the chart coupling clause at fixed times of a
raw filtration `𝓐` (`Sec7.Lemma71D.IsChartCouplingCharFunConst`) for the field `−h` in the image charts
`cfChart (recOf t₀ D)` with `(a, k) = (−πχ, −χ)` and lifetime `⊤`. -/
def CfGivenChartStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (t₀ : ℝ≥0) (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (𝓐 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W'' : ℝ≥0 → Ω → ℝ) (η'' : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧ (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, W'' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W'' t ω) ∧ StronglyAdapted 𝓐 W'' ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR W'' xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W'' (geomLW W'' xL) (geomRW W'' xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf (t₀ : ℝ≥0∞) (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) W'' (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- **The unconditional statement from its fixed-time chart form** (K2's (S) from the chart clause,
`hasSafeLaw_imgField_of_chartConst`). -/
theorem cfGivenPSideStatement_of_chart (hC : CfGivenChartStatement.{u}) : CfGivenPSideStatement.{u} := by
  intro κ b J Ω mΩ hΩ P hP h W' ζ' hκ hκ4 hb hh hcf hζ' hleft hright θ₀ hθ₀ D hDm hDreg hD t₀ η hη
  obtain ⟨𝓐, nL, nR, ρL, ρR, xL, xR, W'', η'', h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hW0, hWc, hWa, hthr, htype,
    hint, hchart, hmem, hpath⟩ := hC κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ' hleft hright θ₀ hθ₀ D hDm hDreg hD t₀ η hη
  exact ⟨𝓐, nL, nR, ρL, ρR, xL, xR, W'', η'', h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hW0, hWc, hWa, hthr, htype,
    hint, hasSafeLaw_imgField_of_chartConst hκ hh.1 h𝒢 hW0 hWc hchart, hmem, hpath⟩

/-- **PROVE-SWITCHED's named input from the fixed-time chart form of Lemma 4.7's conditional law.** -/
theorem counterflowGivenPrefixStatement_of_chart (hC : CfGivenChartStatement.{u}) :
    RestartSw.CounterflowGivenPrefixStatement.{u} :=
  counterflowGivenPrefixStatement_of_pSide (cfGivenPSideStatement_of_chart hC)

end InteractingSLE.Sec5.CfGiven
