/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71DChart
import InteractingSLE.Spec.Sec7.Lemma71CTop

/-!
# Lemma 7.1's pocket curve from the coupling clause at fixed times of the raw filtration

Packet PROVE-LEMMA71D. PROVE-LEMMA71C reduced Lemma 7.1's killed mapped segment to the named input
`Lemma71C.Lemma71PocketCurveStatement`, which asks for a filtration **with the usual conditions** and the chart coupling
clause at **every stopping time** of it ("What remains" B of its handoff). The source obtains the clause from Lemma 6.2's
history locality, available at path-functional times (ruling R37), and Proposition 6.5's time continuity. This file
replaces that named input by `Lemma71PocketCurveConstStatement`, which asks only for

* a raw filtration `𝓐` (e.g. the natural filtration of the revealed outer curves and the mapped middle prefix): no
  right-continuity, no null sets;
* the adaptedness of the filled prefixes and the `𝓐₀`-measurability of the pocket chart for `𝓐`;
* the chart coupling clause **at fixed times**, killed at the terminal capacity time
  (`Lemma71D.IsChartCouplingCharFunConst`).

The usual augmentation `usualAugmentation 𝓐 P` then carries everything (`isChartCouplingCharFun_usualAugmentation`,
`Lemma71DChart.lean`, through Lévy's downward theorem, `Stochastic/Martingale/Backward.lean`).

## Main results

* `Lemma71PocketCurveConstStatement` (**named input**, fixed-time form);
* **`lemma71PocketCurveStatement_of_const`**: `Lemma71PocketCurveConstStatement → Lemma71PocketCurveStatement`;
* `lemma71KilledSegmentStatement_of_pocketCurveConst`, `lemma71TraceReferenceStatement_of_pocketCurveConst`: the
  compositions with PROVE-LEMMA71C, PROVE-LEMMA71B and PROVE-LEMMA71.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.Lemma71D

open MartChar Coupling Lemma71B Lemma71C

/-- **Named input: the three-curve pocket coupling at fixed times** (Specification §7.1, setup pp. 221–222; proof of
Lemma 7.1, pp. 223–225). Fix `0 < κ < 4` and angles `θ₁ < 0 < θ₂`. On the probability space of the three-curve
construction there are a filtration `𝓐` (the raw filtration retaining the complete outer curves and the mapped middle
prefix; no usual conditions required), the mapped pocket segment `γ = ψ(η_C)` (`IsSegCurve`) with `𝓐`-adapted filled
prefixes at capacity times (`IsPrefixAdapted`), the measurable field `h`, the pocket chart `c` (conformal,
`𝓐₀`-measurable, continuous lift), and constants `a`, `k` of the coordinate change (1.4), such that **at every fixed
capacity time `t`**, almost surely on `{t < T}` (`T` the terminal capacity time), conditionally on `𝓐_t` the field on
the remaining chart domain `ψ⁻¹(ℍ ∖ K_t)` is the coupling mean of the mapped driver with the (CPF2) weights, read
back through the chart, plus a zero-boundary GFF there (`IsChartCouplingCharFunConst`; Lemma 6.2, Remark 6.7). -/
def Lemma71PocketCurveConstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓐 : Filtration ℝ≥0 mΩ) (γ : Ω → ℝ → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart) (a k : ℝ),
      (∀ ω, IsSegCurve (γ ω)) ∧ IsPrefixAdapted 𝓐 γ ∧
      Measurable h ∧ (∀ ω, (c ω).IsConformal) ∧
      (∀ z, MeasurableSet[𝓐 0] {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable[𝓐 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable[𝓐 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P 𝓐
        (fun s ω => segDriver (γ ω) s) (geomL (fun s ω => segDriver (γ ω) s) LP.twoSeedXL)
        (geomR (fun s ω => segDriver (γ ω) s) LP.twoSeedXR) (fun ω => capLife (γ ω)) c a k h

/-- **The usual-conditions form of the pocket coupling from its fixed-time form**: pass to the usual augmentation
of `𝓐` (right-continuous, contains the null sets, larger than `𝓐`), and transfer the coupling clause from fixed times
to all its stopping times (`isChartCouplingCharFun_usualAugmentation`; the force points of the mapped driver are
continuous and ordered before the terminal capacity time, `Lemma71C.continuousOn_geomL/R`,
`Lemma71C.geomL_le_le_geomR`). Conditional helper. -/
theorem lemma71PocketCurveStatement_of_const (hpc : Lemma71PocketCurveConstStatement.{v}) :
    Lemma71PocketCurveStatement.{v} := by
  intro κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  obtain ⟨Ω, mΩ, P, hP, 𝓐, γ, h, c, a, k, hγ, hpre, hh, hcc, hdom, hfwd, hliftm, hliftc, hcf⟩ :=
    hpc κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  have hle := Ito.le_usualAugmentation 𝓐 P
  have hc : ∀ ω, ContinuousOn (fun s => segDriver (γ ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ ω)} :=
    fun ω => (hγ ω).segDriver_spec.2.1
  refine ⟨Ω, mΩ, P, hP, usualAugmentation 𝓐 P, Ito.isRightContinuous_usualAugmentation 𝓐 P, γ, h, c, a, k,
    fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0, hγ,
    fun r n j => hle r _ (hpre r n j), hh, hcc, fun z => hle 0 _ (hdom z),
    fun z => (hfwd z).mono (hle 0) le_rfl, fun z => (hliftm z).mono (hle 0) le_rfl, hliftc, ?_⟩
  exact isChartCouplingCharFun_usualAugmentation hh hcc hliftc hc
    (fun i ω => continuousOn_geomL hc LP.twoSeedXL i ω) (fun i ω => continuousOn_geomR hc LP.twoSeedXR i ω)
    (fun ω t ht => geomL_le_le_geomR hc LP.twoSeedXL LP.twoSeedXR ht) hcf

/-- **`Lemma71KilledSegmentStatement` from the fixed-time form of the pocket coupling.** Conditional helper. -/
theorem lemma71KilledSegmentStatement_of_pocketCurveConst (hpc : Lemma71PocketCurveConstStatement.{v}) :
    Lemma71KilledSegmentStatement.{v} :=
  lemma71KilledSegmentStatement_of_pocketCurve (lemma71PocketCurveStatement_of_const hpc)

/-- `Sec7.Lemma71TraceReferenceStatement` from the fixed-time form of the pocket coupling. Conditional helper. -/
theorem lemma71TraceReferenceStatement_of_pocketCurveConst (hpc : Lemma71PocketCurveConstStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} :=
  lemma71TraceReferenceStatement_of_pocketCurve (lemma71PocketCurveStatement_of_const hpc)

end InteractingSLE.Sec7.Lemma71D
