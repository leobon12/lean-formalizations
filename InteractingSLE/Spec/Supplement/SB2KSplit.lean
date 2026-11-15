/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KAmb

/-!
# SB2(1)'s remaining ambient input split into the active word and the driver with its link

Packet PROVE-T14-SB2FIN5. `SB2RelCoreAmbRegSuccStatement` (the input left by `sb2UpperLaunchEntryLAmbStatement_of_succ`)
has three clauses sharing the relative driver `(bc, jc, W, ζr)` only between clauses (1) and (3). Clause (2), SB2(1)'s
active word, concerns the lower walk alone (no upper flow, no S1), so it is stated separately:

* `SB2ActiveWordAmbStatement` (named input): at almost every launch `k + 1` of the lower walk, every witness of the
  launch clause has SB2(1)'s active word on `(launchEntry, 0)` — a statement about the staged conditional word of the
  lower walk in GW1's ambient setting (PROVE-T14-SB2FIN5 handoff §4.1 gives the word invariant that proves it);
* `SB2DriverLinkAmbStatement` (named input): clauses (1) and (3) — K2's conditional flow-line driver in the recentred
  launch chart (its chart and word inputs: `exists_k2ChartInputs_launch_succ`) and the remainder link;
* **`sb2RelCoreAmbRegSuccStatement_of_parts`** and **`sb2UpperLaunchEntryLAmbStatement_of_parts`**: SB2(1) in the
  ambient form SB3 consumes, from the two parts and Theorem 1.3.

Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged

/-- **Named input: SB2(1)'s active word at the launches after the first, in GW1's ambient setting.** -/
def SB2ActiveWordAmbStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u : ℝ), u ≤ 0 →
      ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E (k + 1) ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E (k + 1) u ω₀)

/-- **Named input: SB2(1)'s clauses (1) and (3) at the launches after the first, in GW1's ambient setting** (K2's
conditional flow-line driver in the launch chart recentred at its entry, and the remainder link). -/
def SB2DriverLinkAmbStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    Ly.LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E (k + 1) ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E (k + 1) u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) P (launchSet κ b jumps E (k + 1)) h
        (fun ω => (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀),
          IsRemainderLink (launchChart κ b jumps E (k + 1) ω₀) (η ω) (ζ ω)
            (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E (k + 1) u ω₀) (ζr ω))

/-- **The ambient input from its two parts.** -/
theorem sb2RelCoreAmbRegSuccStatement_of_parts (hw : SB2ActiveWordAmbStatement.{u})
    (hd : SB2DriverLinkAmbStatement.{u}) : SB2RelCoreAmbRegSuccStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k u ψ hu hψ hL hH η ζ hη hS1
  obtain ⟨bc, jc, W, ζr, h1, h3⟩ := hd κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k u ψ hu hψ hL hH η ζ hη hS1
  exact ⟨bc, jc, W, ζr, h1, hw κ hκ hκ4 b jumps hb P h hh hadm E hE hER hreg k u hu, h3⟩

/-- **SB2(1) in the ambient form SB3 consumes** (`Ly.SB2UpperLaunchEntryLAmbStatement`), from Theorem 1.3, the active
word and the driver with its link at the launches after the first. -/
theorem sb2UpperLaunchEntryLAmbStatement_of_parts (h13 : Exist.Theorem13Statement.{u})
    (hw : SB2ActiveWordAmbStatement.{u}) (hd : SB2DriverLinkAmbStatement.{u}) :
    Ly.SB2UpperLaunchEntryLAmbStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_succ h13 (sb2RelCoreAmbRegSuccStatement_of_parts hw hd)

end InteractingSLE.Theorem14.SB.Lv
