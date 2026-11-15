/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SsmMeas
import InteractingSLE.Spec.Supplement.GW2SdjLines

/-!
# GW2's open lines: the kernel marks (T1) and their agreement with the instance's marks (T2)

Packet PROVE-GW2-STAGEMEAN, ruling R117(b). `GW2Sdj.OpenLinesMean` (the stage union mean, the no-threshold clause,
the stage-start conditional law and the word map) is proved by conditioning on the EARLIER pieces of the schedule:
under `μ_{ω₀} = condExpKernel P (pastSigma … k) ω₀` (`k` the index of the current piece, the last instruction of
`RootJ31.futureProgram`) the current stage is stage-0-shaped. Two inputs of that route are RELDET's (R106, R117(b)):

* **(T1) `KernelUnionLocal`**: almost surely, at a launch of the current piece in the chart `cL`, under the conditional
  kernel of the earlier pieces, the launch image `cL(B t ∩ dom cL)` of the instance's union `B t = schedUnionS … t` is
  a marked local set, with marks `𝓚 t`, of the field read in `cL` centred by any bounded harmonic function that makes it
  a zero-boundary GFF under the kernel;
* **(T2) `KernelMarksAgree`**: the marks `𝓚 t` are countably generated sub-σ-algebras containing the σ-algebra of the
  earlier pieces that agree with the instance's marks `ℋ t` up to `P`-null sets (R106 (II)).

`𝓚 t` must NOT contain all `P`-null sets: a `P`-null set may carry positive mass under `μ_{ω₀}` (the fibre of
`ω₀`), so a null-complete marks σ-algebra is never marked local under the kernel. Hence (T2) is agreement up to null
sets.

`SchedKernelLinesStatement` bundles (T1)–(T2) with RELDET's existing provisions of `GW2Rd.exists_schedLinesLocal_setsL`
(as consumed by `GW2Sdj.exists_schedChoice_lines`) at root `0`: it is the statement PROVE-GW2-RELDET proves.

Definitions only; no theorem here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Olm

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Sdi GW2Sde GW2Rd WholeField Supp8.RelSafe

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The schedule with the current piece: the history program followed by the candidate piece. -/
abbrev futSpec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : ExplSpec :=
  ⟨rootPt r.1, true, scheduleProgram 0 (futureProgram c r l a)⟩

/-- The canonical (field-determined) staged family of that schedule. -/
abbrev futFam (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  GW2Schedule.canonFam c.hκ c.h12p c.βA c.c₀ (GW2Tip.specAngle (futSpec c r l a))
    (GW2Tip.specDelta (futSpec c r l a)) (futSpec c r l a).1 c.h

/-- The index of the current piece (the last instruction of the future program). -/
abbrev curIdx (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : ℕ :=
  (historyProgram c r l).length

/-- **The σ-algebra of the earlier pieces** (the retained past before the current piece). -/
abbrev pastG (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    MeasurableSpace Ω :=
  pastSigma c.κ c.b c.jumps (futSpec c r l a) (futFam c r l a) (curIdx c r l)

/-- The launch record of the current piece at a sample: `some (chart, angle)` when it is launched. -/
abbrev curLaunch (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω₀ : Ω) :
    Option (Chart × ℝ) :=
  (ExplState.run c.κ c.b c.jumps (futSpec c r l a) (fun j => futFam c r l a j ω₀) (curIdx c r l + 1)).2.2.2.1
    (curIdx c r l)

/-- The launch image of the instance's union in a chart `cL`. -/
def launchUnion (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (cL : Chart)
    (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  cL.1 '' (schedUnionS c r l a t ω ∩ (cL.dom : Set ℂ))

/-- **(T1) Named input (RELDET): the union is marked local under the conditioning on the earlier pieces.** Almost
surely, at a launch of the current piece in the chart `cL`, under `condExpKernel P (pastG …) ω₀`, the launch image of
`B t` is a history-marked local set, with marks `𝓚 t`, of the field `X` read in `cL` (`IsChartTransport cL 1 0 χ`,
the transport of `IsStagedHistory`) centred by any `uL` that makes it a zero-boundary GFF under the kernel. -/
def KernelUnionLocal [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (𝓚 : ℝ≥0 → MeasurableSpace Ω) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), curLaunch c r l a ω₀ = some (cL, θ) →
    ∀ X : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport cL 1 0 (chiC c.κ) (c.h ω) (X ω)) →
    ∀ uL : ℂ → ℝ, LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X uL)
        (condExpKernel c.P (pastG c r l a) ω₀) →
      IsHistoryAvoidanceLocal (𝓚 t) (launchUnion c r l a cL t) (centredField X uL)
        (condExpKernel c.P (pastG c r l a) ω₀)

/-- **(T2) Named input (RELDET): the kernel marks agree with the instance's marks up to null sets** (R106 (II)). The
kernel marks are raw (countably generated, as the comap of a record into a Polish space is) and contain the
σ-algebra of the earlier pieces: conditional expectations given `𝓚 t` are then read under the conditional kernel of the
earlier pieces (`condExpKernel` tower). -/
def KernelMarksAgree (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (𝓚 ℋ : ℝ≥0 → MeasurableSpace Ω) : Prop :=
  ∀ t : ℝ≥0, 𝓚 t ≤ mΩ ∧ @MeasurableSpace.CountablyGenerated Ω (𝓚 t) ∧ pastG c r l a ≤ 𝓚 t ∧
    𝓚 t ⊔ Ito.nullSets c.P = ℋ t ⊔ Ito.nullSets c.P

/-- **The statement PROVE-GW2-RELDET proves (R117(b))**: at root `0`, RELDET's provisions of
`GW2Rd.exists_schedLinesLocal_setsL` for the corrected union (as `GW2Sdj.exists_schedChoice_lines` consumes them:
`u₀` harmonic with a zero-boundary centred field, marks `ℋ` above the stage filtration, below `mΩ`, and the marked
locality of `B t`) together with kernel marks `𝓚` satisfying (T1) and (T2). -/
def SchedKernelLinesStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 →
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      (∀ t, stgFilt (physFilt (measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P) (historyTime c r l)
        (measurable_stageEncRec c r l) t ≤ ℋ t) ∧
      (∀ t, ℋ t ≤ mΩ) ∧
      (∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionS c r l a t) (centredField c.h u₀) c.P) ∧
      ∃ 𝓚 : ℝ≥0 → MeasurableSpace Ω, KernelMarksAgree c r l a 𝓚 ℋ ∧ KernelUnionLocal c r l a 𝓚

end InteractingSLE.Theorem14.GW2Olm
