/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.Chart
import InteractingSLE.Frozen.Spec.IsChartTransport
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver
import InteractingSLE.Frozen.Spec.counterflowCompletedRange
import InteractingSLE.Frozen.Spec.Instr
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_physSet
import InteractingSLE.Frozen.Spec.ExplState_ordinarySet
import InteractingSLE.Frozen.Spec.pastSigma
import InteractingSLE.Frozen.Spec.IsStagedHistory
import InteractingSLE.Frozen.Spec.boundaryLightConeFamily
import InteractingSLE.Frozen.Spec.IsBoundaryContinuedProgram
import InteractingSLE.Frozen.Spec.boundaryWalkSpec
import InteractingSLE.Frozen.Spec.rightSideOf
import InteractingSLE.Frozen.Spec.leftSideOf
import InteractingSLE.Frozen.Spec.betweenComponents
import InteractingSLE.Frozen.Spec.IsComponentChart
import InteractingSLE.Frozen.Spec.IsComponentBoundaryData
import InteractingSLE.Frozen.Spec.IsComponentTraversal

/-!
# Theorem 1.4: the named inputs (supplement §§13–15, Lemmas GW0–GW6, SB1–SB5)

Packet PROVE-SEC7-D2. The specification proves Theorem 1.4 (pp. 4–5) through its proof interface "GW0, GW2, GW2a,
SB1–SB5, GW6" (light cone) and "GW1, BW3a–BW3, SB1–SB5, GW3–GW4, GW6" (frontiers); §7.4.3 (p. 421): "GW0–GW6,
BW3a–BW3 and SB1–SB5 in the specification supply the general boundary case … GW1 constructs the two extreme
boundary walks … SB1–SB5 prove the joined barriers … Unrestricted exhaustion then identifies the actual frontiers.
GW3–GW4 construct each un-erased component interval, continuous relative driver, exact phase and complete optional
kernel … GW6 proves the nowhere-boundary-filling clause." These supplement lemmas (`source/spec/p577-624.md`
L922–L1100, `p625-671.md` L69–L340) are not yet in Lean. Each is stated here, on the frozen carriers of the Theorem 1.4
surface, as a named `…Statement : Prop`; `Theorem14.lean` derives the four frozen anchors from them.

All statements share the setting of Theorem 1.4 (`0 < κ < 4`, a GFF `h` on `ℍ` with piecewise-constant boundary data
`b`, the centred counterflow `W'` with almost surely infinite lifetime) and quantify over every realization `E` of the
staged histories with angles in `[−π/2, π/2]`.

| Input | Source | Used for |
|---|---|---|
| `GW2LightConeStatement` | Lemma GW2, p. 621 (with GW0, p. 617: no threshold ⇒ all cumulative groups `> −2`) | light cone, first clause |
| `GW2aContainmentStatement` | Lemma GW2a, p. 623 ("Every finite such history … is contained in the counterflow range") | light cone, second clause; walks in the range |
| `SBFrontierStatement` | SB1–SB5, pp. 626–630, with the GW2 exhaustion (p. 421, "the actual frontiers") | frontiers, side exclusion |
| `GW6Statement` | Lemma GW6, p. 639 | frontiers, nowhere-boundary-filling clause |
| `GW3ChartStatement` | Lemma GW3, p. 636 | component kernels, chart existence |
| `GW4KernelStatement` | Theorem GW4, pp. 637–639 (with GW3) | component kernels |
| `StagedHistoryConstructionStatement` | GW1, p. 618; GW2a, p. 623; BW1–BW2 (one prescribed history at a time) | `exists_isStagedHistory` |
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

/-- **Named input: Lemma GW2** (unrestricted boundary-seeded light-cone exhaustion, p. 621), with Lemma GW0 (p. 617)
supplying its hypothesis ("the printed no-threshold hypothesis forces all groups to exceed `−2`", p. 421): there is a
deterministic countable dense schedule set `Q ⊂ (0, ∞)` such that the closed union of the GW2 family and the initial
point is almost surely the completed counterflow range. -/
def GW2LightConeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
          counterflowCompletedRange (fun t => W' t ω)

/-- **Named input: Lemma GW2a, containment** (p. 623): every prescribed finite boundary-continued staged history
from the original target `0` (ordinary angles in `[−π/2, π/2]`, the literal boundary-continuation rule) is almost
surely contained in the completed counterflow range ("Every finite such history is simple, is contained in the
counterflow range in reverse first-visit order"). -/
def GW2aContainmentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ p : List Instr, IsBoundaryContinuedProgram p →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω)

/-- **Named input: the frontier identification** (SB1–SB5, pp. 626–630, with the GW2 exhaustion; p. 421: "SB1–SB5
prove the joined barriers with their mixed middle words, selected prime ends and common lifts. Unrestricted
exhaustion then identifies the actual frontiers"): almost surely the completed counterflow range has no point
strictly on the right of the right walk `R` and no point strictly on the left of the left walk `L`. -/
def SBFrontierStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω ∂P,
        counterflowCompletedRange (fun t => W' t ω) ∩
            rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅ ∧
          counterflowCompletedRange (fun t => W' t ω) ∩
            leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅

/-- **Named input: Lemma GW6** (the nowhere-boundary-filling clause, p. 639): on the event that the counterflow's
intersection with the original boundary has empty relative interior, the first ordinary pieces of both walks never
reach a finite continuation threshold. -/
def GW6Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω ∂P,
        interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
            (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤

/-- **Named input: Lemma GW3, the charts** (p. 636): almost surely every component of `ℍ \ (R ∪ L)` between the
walks has a common-lift chart `(C; x_C, y_C) → (ℍ; 0, ∞)`. -/
def GW3ChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          ∃ c : Chart, IsComponentChart
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C c

/-- **Named input: Theorem GW4** (complete finite-word kernels, pp. 637–639, with Lemma GW3): conditionally on the
labelled walks, for every choice of component charts, the component fields in their common-lift charts are GFFs
with the GW3.1 boundary words, the component traversals are the centred counterflows of these fields with infinite
relative lifetime, and the component field–path pairs are independent. This is the second assertion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, verbatim. -/
def GW4KernelStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
          ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
            (∀ C ∈ betweenComponents R L,
              IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
              (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
                (hC C ω)) ∧
              (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
                IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                  (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
                IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
              IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
              ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
                IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
            iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν

/-- **Named input: the staged-history construction, one history at a time** (GW1, p. 618: "Run the ordinary
angle-`−π/2` flow from `x` … launch the same angle in the current unbounded conditional domain"; GW2a, p. 623: every
prescribed finite boundary-continued history "retains its entire marked conditional precontact pair"; BW1–BW2): for
every prescribed boundary-continued history there is a driver family realizing it as conditional flow lines of `h`. -/
def StagedHistoryConstructionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      ∃ D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, IsStagedHistory κ b jumps P h spec D

end Theorem14

end InteractingSLE
