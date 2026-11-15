/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSys
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Theorem15Inputs

/-!
# The strip system's paths: Theorem 1.3 traces of the staged pieces and of the centred counterflow

Packet PROVE-STRIPSYS2, item 2, first step (`planning/handoffs/PROVE-STRIPSYS.md` §5 C.1: "Each piece needs its trace
(Theorem 1.3 at `κ < 4` under the conditional laws of `IsStagedHistory`)"; "The counterflow trace (parameter
`16/κ > 4`, non-boundary word) also needs Theorem 1.3").

Theorem 1.3 is taken as a named hypothesis with exactly the frozen anchor's type
(`Exist.Theorem13Statement`, PROVE-FLOWEXIST; the DRAFT anchor is not imported), or, for the flow-line pieces, its
restriction `Theorem13LowStatement` to parameters `0 < a < 4` (the packet's "Theorem 1.3 at `κ′ < 4`").

* **`IsStagedHistory.ae_ae_exists_trace`**: for every instruction `k`, for `P`-almost every `ω₀` at which `k`
  launches an ordinary piece, the piece's driver has, under the conditional law `condExpKernel P (pastSigma … k) ω₀`,
  almost surely a generating trace on its lifetime, transient when the lifetime is infinite;
* **`IsCenteredCounterflowDriver.ae_exists_trace`**: the driver of the centred counterflow has almost surely a
  generating trace on its lifetime (the curve `R(η')` of the frozen docstring is `−1/η'`), transient when the lifetime
  is infinite; `IsStripSystem.ae_exists_counterflowTrace` for the strip system (lifetime `⊤` almost surely).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripSysPath

/-- **Theorem 1.3 at parameters `0 < a < 4`** (named input; exactly the conclusion of the frozen anchor
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, restricted to `a < 4`). -/
def Theorem13LowStatement : Prop :=
  ∀ {a : ℝ} (_ : 0 < a) (_ : a < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (_ : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (_ : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ),
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

theorem theorem13LowStatement_of_theorem13 (h : Exist.Theorem13Statement.{u}) : Theorem13LowStatement.{u} := by
  intro a ha _ nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact h ha hF hE

/-- The trace conclusion of Theorem 1.3 for one driver path. -/
def HasTrace (W : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace W ζ η ∧ (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

/-- **A flow-line driver has a trace** (Theorem 1.3 at `0 < κ < 4` for the flow-line word, which is ordered). -/
theorem IsFlowLineDriver.ae_hasTrace (h13 : Theorem13LowStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hW : IsFlowLineDriver κ b jumps θ P h W ζ) :
    ∀ᵐ ω ∂P, HasTrace (fun t => W t ω) (ζ ω) := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := hW
  filter_upwards [h13 hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b jumps 0) hC.1] with ω hω
  exact hω.2

/-- **Every launched piece of a staged history has a trace under its conditional law** (Theorem 1.3 at
`0 < κ < 4`, applied under `condExpKernel P (pastSigma … k) ω₀` to the flow-line coupling that `IsStagedHistory`
provides there). -/
theorem IsStagedHistory.ae_ae_hasTrace (h13 : Theorem13LowStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), HasTrace (fun t => (E k ω).1 t) (E k ω).2 := by
  filter_upwards [hE.2.2.2 k] with ω₀ hω₀ c θ hl
  obtain ⟨b', jumps', h', -, -, hW⟩ := hω₀ c θ hl
  exact IsFlowLineDriver.ae_hasTrace h13 hκ hκ4 hW

/-- **The centred counterflow has a trace** (Theorem 1.3 at parameter `16/κ`): the driver `W` of the frozen
`IsCenteredCounterflowDriver` has almost surely a generating trace `η'` on its lifetime, transient when the lifetime
is infinite; the physical counterflow is `−1/η'`. -/
theorem IsCenteredCounterflowDriver.ae_hasTrace (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : IsCenteredCounterflowDriver κ P h W ζ) : ∀ᵐ ω ∂P, HasTrace (fun t => W t ω) (ζ ω) := by
  obtain ⟨b', jumps', h', -, -, ⟨h'', 𝓕, VL, VR, B, -, hC⟩⟩ := hW
  filter_upwards [h13 (div_pos (by norm_num) hκ) (Theorem15.isOrderedForceWord_flowLine b' jumps' 0) hC.1]
    with ω hω
  exact hω.2

/-- **The strip system's counterflow trace**: almost surely the centred counterflow driver has a transient generating
trace on `[0, ∞)`. -/
theorem IsStripSystem.ae_hasTrace_counterflow (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η ∧
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  filter_upwards [IsCenteredCounterflowDriver.ae_hasTrace h13 hS.kappa_pos hS.counterflow, hS.lifetime]
    with ω hω hζ
  obtain ⟨η, hη, htr⟩ := hω
  rw [hζ] at hη htr
  exact ⟨η, hη, htr rfl⟩

/-- **The strip system's staged pieces have traces under their conditional laws** (every boundary-continued
program, every instruction that launches a piece). -/
theorem IsStripSystem.ae_ae_hasTrace (h13 : Theorem13LowStatement.{u}) {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E) {spec : ExplSpec}
    (hspec : IsBoundaryContinuedProgram spec.2.2) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E spec j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀),
        HasTrace (fun t => (E spec k ω).1 t) (E spec k ω).2 :=
  IsStagedHistory.ae_ae_hasTrace h13 hS.kappa_pos hS.kappa_lt_four (hS.staged spec hspec) k

end StripSysPath

end Sec7

end InteractingSLE
