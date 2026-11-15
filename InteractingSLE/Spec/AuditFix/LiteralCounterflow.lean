/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.LiteralCounterflowAngle
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_boundaryWalks_frontiers
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_componentKernels

/-!
# Theorem 1.4 for the paper's literal counterflow line (audit fix, counterflow frame)

Packet PROVE-AF-CFLIT (audit priority 2, audit §3.4, p. 9). The sealed Theorem 1.4
(`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, `.boundaryWalks_frontiers`, `.componentKernels`)
is stated for the centred counterflow `CF_d(h) = CF_lit(h + πχ)` of the flow background `h` (FD11.1, spec p. 12): in
the chart `R(z) = −1/z` with lift `−2 Log z` it is the angle-`0` parameter-`κ′` flow line of
`−h ∘ R + πχ − 2χ arg w` (FD12.5). The paper (arXiv:1201.1496v2, pp. 19–20) defines the counterflow line of a field
through `ψ`, a continuous branch of `arg ψ′` and the field `h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′`; for the same chart, lift and
field representative this gives `−h ∘ R + 2πχ − 2χ arg w` (`IsLiteralCounterflowDriver`). Errata item A2 records why
the paper's figures and Theorem 1.4 need the centred normalization.

## Main results (each a `…Statement : Prop` with its `…_holds` proof)

* `LiteralCounterflowBridgeStatement` (FD11.1): for the same driver `W` and lifetime `ζ`,
  `IsCenteredCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriver κ P ĥ W ζ` whenever `ĥ = h + πχ` (frozen
  `IsTranslateAddConst 0 (πχ)`, for every `ω`: a shift of the fixed field representative, not an equality in law).
* `LiteralCounterflowWordStatement`: the two parameter fields are the same distribution (`g = −hR`), both transports
  exist and are unique, and for every boundary word `b'` the two couplings with the force word induced by `b'` (seed
  marks `0∓`, marks at the genuine jumps of `b'` on the left `y < 0` and right `y > 0`, angle `0`, parameter
  `κ′ = 16/κ`) are equivalent: same boundary data, same word on each side, same driver, same lifetime.
* `LiteralCounterflowParamFieldStatement`: the explicit parameter fields, tested against every transport pair:
  literal (branch `n`) `−h ∘ R + 2π(1 − n)χ − 2χ arg w`, centred `−h ∘ R + πχ − 2χ arg w`.
* `LiteralCounterflowBranchStatement`: for every branch `n` of `arg R′`, `CF_d(h) = CF_lit,n(h + (1 − 2n)πχ)`; the
  literal parameter field of a fixed `h` never equals the centred one (they differ by `(1 − 2n)πχ ≠ 0` for
  `0 < κ < 4`): the half-turn is a frame convention that no branch choice produces. The branch of FD12.1 is `n = 0`;
  the paper's Remark normalization `arg ψ′(ψ⁻¹(i)) ∈ (−π, π]` selects `n = 1`, where `CF_d(h) = CF_lit(h − πχ)`.
* `ShiftedFieldStatement`: `h + s` exists, is unique and measurable in `ω`; `b + s` is finite piecewise-constant data
  with the same finite set iff `b` is, and then has the same genuine jumps; and `h + s` is a GFF with boundary data
  `b + s` iff `h` is a GFF with boundary data `b`.
* `FlowLineAngleShiftStatement` (FD11.3): the angle-`θ` flow line of `h` (data `b`) is the angle-`(θ − π)` flow line of
  `ĥ = h + πχ` (data `b + πχ`), with the same coupling field and force word; so the frontier angles `∓π/2` of the flow
  background are the angles `−3π/2`, `−π/2` of the literal background.
* `LiteralCounterflowLightConeStatement`, `LiteralCounterflowFrontiersStatement`,
  `LiteralCounterflowComponentKernelsStatement`: the three conclusions of Theorem 1.4 for the literal counterflow line
  of `ĥ = h + πχ` (all frozen hypotheses on `h`, `b` and the staged histories of `h` verbatim); in the component
  kernels the component counterflows are also literal counterflows, of the shifted component fields `hC C + πχ`.

## How the frozen hypotheses transfer

The frozen Theorem 1.4 assumes `IsGFFWithBoundaryData P h b jumps` for the flow background `h`, whose staged histories
(flow lines at angles in `[−π/2, π/2]`) build the light cone and the frontier walks. In the corollaries this
hypothesis is kept verbatim, on `h`. The literal counterflow is that of the shifted field `ĥ = h + πχ`, which is a GFF
with boundary data `b + πχ` and the same finite jump set (`ShiftedFieldStatement`). Read in the literal background `ĥ`
(data `b̂`), the frozen theorems describe `CF_lit(ĥ)` through the staged histories of `ĥ − πχ` (data `b̂ − πχ`), i.e.
the flow lines of `ĥ` at the shifted angle labels `θ − π ∈ [−3π/2, −π/2]` (FD11.3: `h + θχ = ĥ + (θ − π)χ`); that
relabelling is not restated with the frozen staged-history vocabulary, which is tied to the background `h` and data `b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.AuditFix

open CFLit

/-! ### The frame bridge -/

/-- **FD11.1, `CF_d(h) = CF_lit(h + πχ)`** (spec p. 12; paper pp. 19–20): for every `κ > 0`, every random field `h`
on `ℍ` and its shift `ĥ = h + πχ` (frozen `IsTranslateAddConst 0 (πχ) (h ω) (ĥ ω)` for every `ω`), a driver `W` with
lifetime `ζ` drives the frozen centred counterflow of `h` iff it drives the paper's literal counterflow line of `ĥ`
(chart `R(z) = −1/z`, FD12.1 lift, field `ĥ ∘ R⁻¹ − χ arg (R⁻¹)′`, coupled with its negative as in Theorem 1.1 at
`κ′ = 16/κ`, angle `0`, induced force word). -/
def LiteralCounterflowBridgeStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (_hĥ : ∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (h ω) (ĥ ω))
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsCenteredCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriver κ P ĥ W ζ

theorem literalCounterflowBridge_holds : LiteralCounterflowBridgeStatement.{u} := by
  intro κ hκ Ω _ P h ĥ hĥ W ζ
  exact isCenteredCounterflowDriver_iff_literal hκ P hĥ W ζ

/-- **The same parameter field, boundary data and force word on each side.** For `κ > 0`:
* the centred transport `g` of a field `h` and the literal transport `hR` of `ĥ = h + πχ` exist and are unique, and
  `g = −hR` (the parameter fields are the same distribution);
* for every random field `h`, its shift `ĥ = h + πχ`, every boundary word `b'` (any function and finite set `jumps'`),
  driver `W` and lifetime `ζ`: `W` drives the angle-`0` parameter-`κ′` flow line, with the force word induced by `b'`,
  of the centred parameter field of `h` iff it drives the one with the same word of the literal parameter field
  `−hR` of `ĥ`. -/
def LiteralCounterflowWordStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ),
    (∀ h : LQGMetric.DistOn upperHalfPlaneOpens, ∃! g : LQGMetric.DistOn upperHalfPlaneOpens,
      IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ))
        h g) ∧
    (∀ ĥ : LQGMetric.DistOn upperHalfPlaneOpens, ∃! hR : LQGMetric.DistOn upperHalfPlaneOpens,
      IsChartTransport infinitySourceChart 1 0 (QuantumZipper.chiC κ) ĥ hR) ∧
    (∀ h ĥ g hR : LQGMetric.DistOn upperHalfPlaneOpens,
      IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) h ĥ →
      IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ))
        h g →
      IsChartTransport infinitySourceChart 1 0 (QuantumZipper.chiC κ) ĥ hR → g = -hR) ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      (∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (h ω) (ĥ ω)) →
      ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        (∃ g : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
            (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
              (QuantumZipper.chiC (16 / κ)) (h ω) (g ω)) ∧
            IsFlowLineDriver (16 / κ) b' jumps' 0 P g W ζ) ↔
          ∃ hR : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
            (∀ ω, IsChartTransport infinitySourceChart 1 0 (QuantumZipper.chiC κ) (ĥ ω) (hR ω)) ∧
            IsFlowLineDriver (16 / κ) b' jumps' 0 P (fun ω => -hR ω) W ζ

theorem literalCounterflowWord_holds : LiteralCounterflowWordStatement.{u} := by
  intro κ hκ
  have hc := Chart.isConformal_infinitySourceChart
  have hℓ := Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift
  refine ⟨fun h => Chart.existsUnique_isChartTransport hc hℓ _ _ _ h,
    fun ĥ => Chart.existsUnique_isChartTransport hc hℓ _ _ _ ĥ,
    fun h ĥ g hR hĥ hg hR' => centred_eq_neg_literal hκ hĥ hg hR', ?_⟩
  intro Ω _ P h ĥ hĥ b' jumps' W ζ
  exact centredWitness_iff_literalWitness hκ P hĥ b' jumps' W ζ

/-- **The explicit parameter fields** (FD12.1–FD12.5; audit §3.4). For `κ > 0`, a field `h` and every transport pair
`(φ, φ')` of the chart `R` (`φ = (φ' ∘ R) |R′|²`, supported in `ℍ`; such a `φ` exists for every `φ'`):
* the literal parameter field of `h` with the branch `n` is `−h ∘ R + 2π(1 − n)χ − 2χ arg w` (`0 < arg w < π`): for
  `n = 0`, `−h ∘ R + 2πχ − 2χ arg w`;
* the centred parameter field of `h` is `−h ∘ R + πχ − 2χ arg w`. -/
def LiteralCounterflowParamFieldStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ),
    (∀ φ' : LQGMetric.TestOn upperHalfPlaneOpens, ∃ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ infinitySourceChart.2.1 '' QuantumZipper.H ∧
      ∀ z ∈ infinitySourceChart.2.1 '' QuantumZipper.H,
        φ z = φ' (infinitySourceChart.1 z) * ‖deriv infinitySourceChart.1 z‖ ^ 2) ∧
    ∀ (h : LQGMetric.DistOn upperHalfPlaneOpens) (φ φ' : LQGMetric.TestOn upperHalfPlaneOpens),
      tsupport φ ⊆ infinitySourceChart.2.1 '' QuantumZipper.H →
      (∀ z ∈ infinitySourceChart.2.1 '' QuantumZipper.H,
        φ z = φ' (infinitySourceChart.1 z) * ‖deriv infinitySourceChart.1 z‖ ^ 2) →
      (∀ (n : ℤ) (hR : LQGMetric.DistOn upperHalfPlaneOpens),
        IsChartTransport (infinitySourceChartAt n) 1 0 (QuantumZipper.chiC κ) h hR →
        (-hR) φ' = -h φ + ∫ w, (2 * Real.pi * (1 - n) * QuantumZipper.chiC κ -
          2 * QuantumZipper.chiC κ * Complex.arg w) * φ' w) ∧
      ∀ g : LQGMetric.DistOn upperHalfPlaneOpens,
        IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
          (QuantumZipper.chiC (16 / κ)) h g →
        g φ' = -h φ + ∫ w, (Real.pi * QuantumZipper.chiC κ - 2 * QuantumZipper.chiC κ * Complex.arg w) * φ' w

theorem literalCounterflowParamField_holds : LiteralCounterflowParamFieldStatement := by
  intro κ hκ
  have hc := Chart.isConformal_infinitySourceChart
  refine ⟨fun φ' => ⟨Chart.pushTest hc φ', ?_, fun z hz => ?_⟩, fun h φ φ' hs hφ => ⟨fun n hR hR' =>
    literalAt_paramField_apply n hR' hs hφ, fun g hg => centred_paramField_apply hκ hg hs hφ⟩⟩
  · rw [← hc.coe_dom]
    exact Chart.tsupport_pushTest_subset hc φ'
  · rw [← hc.coe_dom] at hz
    rw [Chart.pushTest_apply_of_mem hc φ' hz, mul_comm]

/-- **The branch of `arg R′` and the half-turn** (paper p. 19, Remark; spec FD11.2, p. 12: a compatible change of
logarithm branch "cannot replace `c = 0` by `c = −πχ` while leaving `h` fixed"):
* the branch-`n` lift at `R⁻¹(i) = i` is `arg R′(i) = −π + 2πn`, in `(−π, π]` exactly for `n = 1` (the Remark's
  normalization); FD12.1 is `n = 0` (`IsLiteralCounterflowDriver = IsLiteralCounterflowDriverAt 0`);
* for every branch `n`, `CF_d(h) = CF_lit,n(h + (1 − 2n)πχ)` for the same driver and lifetime;
* for `0 < κ < 4`, every branch `n` and every field `h`, the literal parameter field `−hR` of `h` and the centred
  parameter field `g` of the same `h` differ by the constant `(1 − 2n)πχ`, which is nonzero, so `−hR ≠ g`. -/
def LiteralCounterflowBranchStatement : Prop :=
  (∀ n : ℤ, (infinitySourceChartAt n).2.2 ((infinitySourceChartAt n).2.1 Complex.I) =
      -Real.pi + 2 * Real.pi * n ∧
    ((infinitySourceChartAt n).2.2 ((infinitySourceChartAt n).2.1 Complex.I) ∈ Set.Ioc (-Real.pi) Real.pi ↔
      n = 1)) ∧
  (∀ {κ : ℝ} {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
      (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsLiteralCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriverAt 0 κ P h W ζ) ∧
  (∀ {κ : ℝ} (_hκ : 0 < κ) (n : ℤ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    (∀ ω, IsTranslateAddConst 0 ((1 - 2 * n) * (Real.pi * QuantumZipper.chiC κ)) (h ω) (ĥ ω)) →
    ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W ζ ↔ IsLiteralCounterflowDriverAt n κ P ĥ W ζ) ∧
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4) (n : ℤ) (h g hR : LQGMetric.DistOn upperHalfPlaneOpens),
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ))
      h g →
    IsChartTransport (infinitySourceChartAt n) 1 0 (QuantumZipper.chiC κ) h hR →
    (∀ φ' : LQGMetric.TestOn upperHalfPlaneOpens,
        (-hR) φ' = g φ' + (1 - 2 * n) * (Real.pi * QuantumZipper.chiC κ) * ∫ w, φ' w) ∧
      (1 - 2 * (n : ℝ)) * (Real.pi * QuantumZipper.chiC κ) ≠ 0 ∧ -hR ≠ g

theorem literalCounterflowBranch_holds : LiteralCounterflowBranchStatement.{u} := by
  refine ⟨fun n => ⟨infinitySourceChartAt_lift_I n, remarkBranch_iff n⟩, ?_, ?_, ?_⟩
  · intro κ Ω _ P h W ζ
    exact isLiteralCounterflowDriver_iff_at_zero P h W ζ
  · intro κ hκ n Ω _ P h ĥ hĥ W ζ
    exact isCenteredCounterflowDriver_iff_literalAt hκ n P hĥ W ζ
  · intro κ hκ hκ4 n h g hR hg hR'
    exact literalAt_paramField_ne_centred hκ hκ4 n hg hR'

/-- **The shifted field and its boundary data.** For every constant `s`:
* every field `h` has exactly one shift `ĥ = h + s` (frozen `IsTranslateAddConst 0 s h ĥ`), and a measurable random
  field has a measurable random shift;
* `b + s` is finite piecewise-constant boundary data, with the same finite set `jumps`, iff `b` is, and then `b + s`
  has the same genuine jumps (`jumpSet`; its one-sided limits are those of `b` plus `s`);
* for `ĥ = h + s` (every `ω`), `ĥ` is a GFF with boundary data `b + s` iff `h` is a GFF with boundary data `b`: the
  shift acts on the GFF `IsGFFWithBoundaryData` and its boundary data together. -/
def ShiftedFieldStatement : Prop :=
  ∀ s : ℝ,
    (∀ h : LQGMetric.DistOn upperHalfPlaneOpens, ∃! ĥ : LQGMetric.DistOn upperHalfPlaneOpens,
      IsTranslateAddConst 0 s h ĥ) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), Measurable h →
      ∃ ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens, Measurable ĥ ∧ ∀ ω, IsTranslateAddConst 0 s (h ω) (ĥ ω)) ∧
    (∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
      IsPiecewiseConstantBoundaryData (fun x => b x + s) jumps ↔ IsPiecewiseConstantBoundaryData b jumps) ∧
    (∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
      PiecewiseConstantBoundaryData.jumpSet (fun x => b x + s) jumps =
        PiecewiseConstantBoundaryData.jumpSet b jumps) ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      (∀ ω, IsTranslateAddConst 0 s (h ω) (ĥ ω)) → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
        IsGFFWithBoundaryData P ĥ (fun x => b x + s) jumps ↔ IsGFFWithBoundaryData P h b jumps

theorem shiftedField_holds : ShiftedFieldStatement.{u} := by
  intro s
  refine ⟨fun h => ⟨shiftDist s h, isTranslateAddConst_shiftDist s h,
      fun ĥ hĥ => eq_shiftDist_of_isTranslateAddConst hĥ⟩,
    fun h hm => ⟨fun ω => shiftDist s (h ω), (measurable_shiftDist s).comp hm,
      fun ω => isTranslateAddConst_shiftDist s (h ω)⟩,
    fun b jumps => isPiecewiseConstantBoundaryData_add_const_iff b jumps s,
    fun b jumps hb => jumpSet_add_const hb s,
    fun P h ĥ hĥ b jumps => isGFFWithBoundaryData_shift_iff hĥ b _⟩

/-- **FD11.3: angle labels in the literal background** (spec p. 12: with `h = ĥ − πχ` and `θ = θ̂ + π`, "`h + θχ =
ĥ + θ̂χ`. Both actual coupling fields are unchanged. Every boundary height of the flow background is shifted along with
`h`."). For finite piecewise-constant data `b`, a random field `h` and its shift `ĥ = h + πχ` (every `ω`; `ĥ` has the
data `b + πχ`): a driver `W` with lifetime `ζ` drives the angle-`θ` flow line of `h` iff it drives the angle-`(θ − π)`
flow line of `ĥ`, with the same coupling field and the same induced force word. In particular the angle-`∓π/2` flow
lines of the flow background `h` (the frontier walks of Theorem 1.4) are the angle-`−3π/2` and angle-`−π/2` flow lines
of the literal background `ĥ`. -/
def FlowLineAngleShiftStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ (θ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      (∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (h ω) (ĥ ω)) →
      ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsFlowLineDriver κ b jumps θ P h W ζ ↔
          IsFlowLineDriver κ (fun x => b x + Real.pi * QuantumZipper.chiC κ) jumps (θ - Real.pi) P ĥ W ζ

theorem flowLineAngleShift_holds : FlowLineAngleShiftStatement.{u} := by
  intro κ b jumps hb θ Ω _ P h ĥ hĥ W ζ
  exact (isFlowLineDriver_shift_iff (θ := θ) (θ' := θ - Real.pi) hb (by ring) P hĥ W ζ).symm

/-! ### Theorem 1.4 for the literal counterflow line -/

/-- **Theorem 1.4, light cone, for the literal counterflow line of `h + πχ`.** The frozen
`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone` with its counterflow hypothesis replaced by: `W′`
(lifetime `ζ′`) drives the paper's literal counterflow line (FD12.1 branch) of the shifted field `ĥ = h + πχ`. All
other hypotheses (on `κ`, `b`, `h`, `ζ′`, `Θ` and the staged histories of `h`) and the conclusion are verbatim. -/
def LiteralCounterflowLightConeStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    (_hĥ : ∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (h ω) (ĥ ω))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (_hcf : IsLiteralCounterflowDriver κ P ĥ W' ζ') (_hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (Θ : Set ℝ) (_hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (_hΘc : Θ.Countable)
    (_hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ),
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω)

theorem literalCounterflowLightCone_holds : LiteralCounterflowLightConeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h ĥ hh hĥ W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  exact IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone hκ hκ4 b jumps hb hh
    ((isCenteredCounterflowDriver_iff_literal hκ P hĥ W' ζ').2 hcf) hζ' Θ hΘ hΘc hΘd

/-- **Theorem 1.4, frontiers, for the literal counterflow line of `h + πχ`.** The frozen
`IsCenteredCounterflowDriver.boundaryWalks_frontiers` with its counterflow hypothesis replaced by: `W′` (lifetime
`ζ′`) drives the paper's literal counterflow line (FD12.1 branch) of `ĥ = h + πχ`. The right and left walks are the
angle `−π/2` and `+π/2` walks of the flow background `h`; all other hypotheses and the conclusion are verbatim. -/
def LiteralCounterflowFrontiersStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    (_hĥ : ∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (h ω) (ĥ ω))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (_hcf : IsLiteralCounterflowDriver κ P ĥ W' ζ') (_hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (_hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (_hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)),
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤)

theorem literalCounterflowFrontiers_holds : LiteralCounterflowFrontiersStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h ĥ hh hĥ W' ζ' hcf hζ' E hE hreg
  exact IsCenteredCounterflowDriver.boundaryWalks_frontiers hκ hκ4 b jumps hb hh
    ((isCenteredCounterflowDriver_iff_literal hκ P hĥ W' ζ').2 hcf) hζ' E hE hreg

/-- **Theorem 1.4, component kernels, for the literal counterflow line of `h + πχ`.** The frozen
`IsCenteredCounterflowDriver.componentKernels` with both counterflow frames made literal: the hypothesis is that `W′`
(lifetime `ζ′`) drives the literal counterflow line (FD12.1 branch) of `ĥ = h + πχ`, and in the conclusion the actual
counterflow traversal of each component `C` is, through the continuous increasing clock, the literal counterflow line
`WC C` of the shifted component field `ĥC C = hC C + πχ`. All other hypotheses and clauses are verbatim (the component
field `hC C` is `h` written in the component chart with coefficient `χ`; its boundary word is that of GW3.1). -/
def LiteralCounterflowComponentKernelsStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h ĥ : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    (_hĥ : ∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (h ω) (ĥ ω))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (_hcf : IsLiteralCounterflowDriver κ P ĥ W' ζ') (_hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (_hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (_hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec)),
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC ĥC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            (∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (hC C ω) (ĥC C ω)) ∧
            IsLiteralCounterflowDriver κ ν (ĥC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν

theorem literalCounterflowComponentKernels_holds : LiteralCounterflowComponentKernelsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h ĥ hh hĥ W' ζ' hcf hζ' E hE hreg
  have H := IsCenteredCounterflowDriver.componentKernels hκ hκ4 b jumps hb hh
    ((isCenteredCounterflowDriver_iff_literal hκ P hĥ W' ζ').2 hcf) hζ' E hE hreg
  dsimp only at H ⊢
  refine Filter.Eventually.mono H fun ω₀ hω₀ => ⟨hω₀.1, fun cs hcs => ?_⟩
  obtain ⟨ℓ, hC, WC, ζC, hall, hind⟩ := hω₀.2 cs hcs
  refine ⟨ℓ, hC, fun C ω => shiftDist (Real.pi * QuantumZipper.chiC κ) (hC C ω), WC, ζC, fun C hCm => ?_, hind⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hall C hCm
  have hsh : ∀ ω, IsTranslateAddConst 0 (Real.pi * QuantumZipper.chiC κ) (hC C ω)
      (shiftDist (Real.pi * QuantumZipper.chiC κ) (hC C ω)) := fun ω => isTranslateAddConst_shiftDist _ _
  exact ⟨h1, h2, h3, hsh, (isCenteredCounterflowDriver_iff_literal hκ _ hsh _ _).1 h4, h5⟩

end InteractingSLE.AuditFix
