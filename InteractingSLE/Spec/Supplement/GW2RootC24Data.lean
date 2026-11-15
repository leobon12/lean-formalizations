/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootV7Retained
import InteractingSLE.Spec.Supplement.GW2RootC11Meas
import InteractingSLE.Spec.Supplement.GW2RootS5Claims

/-!
# Data for the conditional assembly of the complete GW2 root test

Packet PROVE-T14-GW2ROOT2. The orchestrator explicitly requests the full
root-test conclusion with precisely named hypotheses for the open items.
`SourceData` contains exactly its source setup. `Construction` contains
the still-to-be-constructed cover and actual experiments, without claiming
their existence or any geometric or retained-law assertion.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC24

open Exist Staged StagedLaw Restart LQGMetric RootK3

/-- The original setup of `GW2RootTestStatement`, with no additional premise. -/
structure SourceData (Ω : Type u) [MeasurableSpace Ω] where
  κ : ℝ
  hκ : 0 < κ
  hκ4 : κ < 4
  h12p : Theorem12ParamStatement.{u}
  βA : BoundaryWord × ℝ × RecData → BoundaryWord
  hβA : IsStopLaw.{u} κ βA
  b : ℝ → ℝ
  jumps : Finset ℝ
  c₀ : BoundaryWord
  hb : IsPiecewiseConstantBoundaryData b jumps
  hc₀J : c₀.jumps = jumps
  hc₀ : ∀ y ∉ jumps, c₀.fn y = b y
  P : Measure Ω
  probability : IsProbabilityMeasure P
  h : Ω → DistOn upperHalfPlaneOpens
  hh : IsGFFWithBoundaryData P h b jumps
  W : ℝ≥0 → Ω → ℝ
  ζ : Ω → ℝ≥0∞
  hcf : IsCenteredCounterflowDriver κ P h W ζ
  hζ : ∀ᵐ ω ∂P, ζ ω = ⊤
  Θ : Set ℝ
  hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2)
  hΘc : Θ.Countable
  hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ
  Q : Set ℝ≥0
  hQc : Q.Countable
  hQd : Dense Q
  hQpos : ∀ q ∈ Q, 0 < q
  α : Ω → ℝ≥0 → ℂ
  hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) ⊤ (α ω)
  s : ℝ≥0

attribute [instance] SourceData.probability

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The exact retained sigma algebra of the source problem and root. -/
abbrev SourceData.sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    List (EntryIdx c.Θ c.Q) → MeasurableSpace Ω :=
  rootSigma c.hκ c.h12p c.βA c.c₀ c.h c.W c.ζ c.s r

/-- Data of an actual experiment, before the remaining geometry and
model identifications are supplied. Sample measurability is explicit. -/
structure Experiment (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  data : StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r)
  sampleMeas : ∀ l a, Measurable (data.sample l a)
  driftBound : ℝ
  Y : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ≥0 → ℝ
  clock : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Ω → ℝ≥0

variable [StandardBorelSpace Ω]

/-- The full retained conditional sample kernel, constructed by the landed
measurable pushforward; no conditional law is assumed at this step. -/
abbrev Experiment.retained {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    (e : Experiment c r) : StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) :=
  RootV7.retainedData c.P e.data e.sampleMeas

/-- Choices still required in each source setup: the initial cover events
and actual experiments for every root. No properties are implicit fields. -/
structure Construction (c : SourceData Ω) where
  G : ScaledRootIdx c.Θ c.Q → Set Ω
  experiment : (r : ScaledRootIdx c.Θ c.Q) → Experiment c r

/-- A family of the required concrete choices over the original source setups.
The assembly accepts this family as data; it does not assert its existence. -/
abbrev ConstructionFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω), Construction c

end InteractingSLE.Theorem14.GW2TipSystem.RootC24
