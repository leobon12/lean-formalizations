/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6PastStep
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas
import InteractingSLE.Spec.Supplement.WalkUnionLawMain

/-!
# Lemma GW2a for every boundary-continued program: the statement, the induction datum and the named inputs

Packet PROVE-GW2AC. Lemma GW2a (supplement p. 623, `source/spec/p577-624.md` L1040–L1056): "Every finite such history
is simple, is contained in the counterflow range in reverse first-visit order […] *Proof.* Use the induction datum of
GW1, without requiring that the current ordinary angle be extreme. […] In the already established complete conditional
counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary piece […] BR6 forces the
entire connector and its reverse first visits, and BR4a gives the actual complete pair targeted at its next seed."

* **`GW2aContainmentRegStatement`**: Theorem 1.4's leaf `Theorem14.GW2aContainmentStatement` with ruling R51's
  hypothesis that every staged family is `StagedPiecesRegular` (the hypothesis of the version-2 Theorem 1.4 anchors;
  every consumer of the leaf has it). The unregularized leaf asks for pathwise containment of pieces that
  `IsStagedHistory` constrains only through their conditional laws (ruling R51, `planning/handoffs/PROVE-T14-GW1P.md`
  §5).
* `arcAt`: the connector recorded by one instruction.
* **`HasStatePair`**: GW1's induction datum after `k` instructions at a sample `ω₀`: if the history is still alive,
  under the regular conditional law given the retained past, every field read in the current chart has a centred
  counterflow with infinite lifetime whose tips, read through the chart and the inversion, lie in the completed range of
  the original counterflow. At a launch this is the landed `GW2Later.HasLaunchPair` (`hasLaunchPair_of_hasStatePair`).
* **`BW1PrefixPairStatement`** (named input): Proposition BW1 (supplement pp. 613–615) for one flow line stopped at its
  own time `t`, at a finite positive stop whose endpoint is not an interior tip (a finite continuation threshold, or a
  real endpoint at the deterministic own time), in the form of the landed `GW2Later.GB6PrefixPairStatement` (GB6's
  interior case).
* **`GW2aConnectorStepStatement`** (named input): GW2a's connector step ("BR6 forces the entire connector and its
  reverse first visits, and BR4a gives the actual complete pair targeted at its next seed", Corollary BW2 at a general
  angle), in the conditional world of the retained past.
* `hasStatePair_zero`: the datum before the first instruction (the original counterflow itself). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

/-! ### The statement under ruling R51 -/

/-- **Lemma GW2a, containment, under ruling R51** (supplement p. 623): the binders of Theorem 1.4's leaf
`Theorem14.GW2aContainmentStatement`, together with the hypothesis of the version-2 Theorem 1.4 anchors that every
staged family is `StagedPiecesRegular` (its launched pieces are continuous curves almost surely). Every prescribed
finite boundary-continued staged history from the original target `0` is almost surely contained in the completed
counterflow range. -/
def GW2aContainmentRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ p : List Instr, IsBoundaryContinuedProgram p →
        ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω)

/-- The unregularized leaf implies the R51 form (it has fewer hypotheses). -/
theorem gw2aContainmentRegStatement_of_leaf (hA : GW2aContainmentStatement.{u}) :
    GW2aContainmentRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh W' ζ' hcf hζ' E hE _ p hp =>
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE p hp

/-! ### The connector recorded by one instruction -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The connector recorded by instruction `k`**: the union of the connectors appended to the state by the `k`-th
step (empty when the step records none). -/
def arcAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) : Set ℝ :=
  ⋃ a ∈ (ExplState.run κ b jumps spec D (k + 1)).2.1.drop (ExplState.run κ b jumps spec D k).2.1.length, a

/-! ### GW1's induction datum after `k` instructions -/

/-- **GW1's induction datum after `k` instructions** (supplement p. 618, item 2; GW2a p. 623: "the already established
complete conditional counterflow pair targeted at the current incoming tip"), at a sample `ω₀` of the retained past. If
the history of `ω₀` is still alive after `k` instructions (neither done nor dead), then under the regular conditional
law given the retained past, every field `h'` that is `h` read in the current chart `c` has a centred counterflow driver
`Wk` with infinite lifetime whose tips, read through `c` and the inversion `z ↦ −1/z`, are physical points of the
completed range of the original counterflow `W'`. -/
def HasStatePair (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω₀ : Ω) : Prop :=
  ¬ IsTerminal (ExplState.run κ b jumps spec (fun j => E j ω₀) k) →
    ∀ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω₀) k).2.2.2.2.1 1 0
        (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      ∃ (Wk : ℝ≥0 → Ω → ℝ) (ζk : Ω → ℝ≥0∞),
        IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' Wk ζk ∧
        (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ζk ω = ⊤) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ∀ (r : ℝ≥0) (z : ℂ),
          ((ExplState.run κ b jumps spec (fun j => E j ω₀) k).2.2.2.2.1.trans infinitySourceChart).tipAt
            (fun s => Wk s ω) r z → z ∈ counterflowCompletedRange (fun t => W' t ω)

/-! ### The named inputs -/

/-- **Named input: Proposition BW1 for one flow line at a real endpoint** (supplement pp. 613–615, `source/spec/
p577-624.md` L830–L865: "Retain its full marked history `A = α[0, σ]` at a finite available own stopping time with
finite continuous endpoint `q ∈ ℝ \ {0}` […] In particular this includes a finite original continuation threshold […]
Conditional on the marked terminal history `A`, the actual prefix `η[0, T]` is the complete counterflow of the
conditional component field in `U`, from `y` to that prime end over `q`. Its relative capacity lifetime is infinite";
GW2a p. 623: "GB6 and BW1 apply to the next ordinary piece"). For a flow line `α` of `h` (angle in `[−π/2, π/2]`,
`0 < κ < 4`) run for its own time `t`, conditioning on (any measurable version of) the record of the stopped prefix:
at almost every sample whose stop `min t ζα` is finite and positive and is either the lifetime (a finite
continuation threshold) or a stop whose endpoint is not an interior tip, the field read in the flow's own chart at the
stop has a centred counterflow with infinite lifetime whose physical tips, read in the original chart, are points of
the completed range of `η`. It is the real-endpoint companion of `GW2Later.GB6PrefixPairStatement` (GB6, interior
tips), stated in the same form. -/
def BW1PrefixPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) →
  ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q h b jumps →
  ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ Q h W ζ → (∀ᵐ ω ∂Q, ζ ω = ⊤) →
  ∀ (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞), IsFlowLineDriver κ b jumps θ Q h Wα ζα →
  ∀ t : ℝ≥0∞, ∀ g : Ω → RecData, Measurable g →
    (∀ᵐ ω ∂Q, g ω = recOf t ((fun s => Wα s ω), ζα ω)) →
    ∀ᵐ ω ∂Q, 0 < min t (ζα ω) → min t (ζα ω) ≠ ⊤ →
      (ζα ω ≤ t ∨ ¬ IsInteriorStop (fun s => Wα s ω) (min t (ζα ω))) →
      ∀ h₂ : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω', IsChartTransport (Chart.id.loewner (stopDrv t ((fun s => Wα s ω), ζα ω))
          (stopTime t ((fun s => Wα s ω), ζα ω))) 1 0 (QuantumZipper.chiC κ) (h ω') (h₂ ω')) →
        ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
          IsCenteredCounterflowDriver κ (condExpKernel Q (MeasurableSpace.comap g inferInstance) ω) h₂ W₂ ζ₂ ∧
          (∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ζ₂ ω' = ⊤) ∧
          ∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
            ((Chart.id.loewner (stopDrv t ((fun s => Wα s ω), ζα ω))
              (stopTime t ((fun s => Wα s ω), ζα ω))).trans infinitySourceChart).tipAt
                (fun s => W₂ s ω') r z →
              z ∈ counterflowCompletedRange (fun s => W s ω')

/-- **Named input: GW2a's connector step in the conditional world of the retained past** (supplement p. 623–624: "For a
right threshold the proposed connector has `H + θχ ≤ −λ ⟹ H ≤ −λ − θχ ≤ −Λ`. Its outward conditional counterflow sums
are consequently at most `d` by the BW2 calculation, while the whole conditional word is admissible. BR6 forces the
entire connector and its reverse first visits, and BR4a gives the actual complete pair targeted at its next seed. […] On
a partial connector the same retargeting applies before a prescribed angle change. A connector has no field reveal";
Corollary BW2, pp. 615–616, at a general angle). For a boundary-continued program from `0` and a staged history with
measurable drivers regular at every sample: at almost every sample `ω₀` at which GW1's datum holds after `k`
instructions and instruction `k` records a connector (the step appends one), almost surely under the regular conditional
law given the retained past, that connector lies in the completed counterflow range and the datum holds after `k + 1`
instructions. -/
def GW2aConnectorStepStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ (p : List Instr), IsBoundaryContinuedProgram p → ∀ E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E → StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E →
      (∀ j ω, IsRegularDriver (E j ω)) → ∀ k : ℕ,
        ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E k ω₀ →
          (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) (k + 1)).2.1 ≠
            (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.1 →
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀),
            ((↑) : ℝ → ℂ) '' arcAt κ b jumps ⟨0, false, p⟩ (fun j => E j ω) k ⊆
                counterflowCompletedRange (fun t => W' t ω) ∧
              HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E (k + 1) ω

/-! ### Basic facts about the datum -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- A launching instruction starts from a living state, in its chart. -/
theorem not_isTerminal_of_launch {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {c : Chart} {θ : ℝ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) :
    ¬ IsTerminal (ExplState.run κ b jumps spec D k) := fun ht => by
  rw [(isTerminal_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D ht k le_rfl).2] at hl
  exact absurd hl (by simp)

/-- **At a launch, GW1's datum is the landed launch datum** (`GW2Later.HasLaunchPair`). -/
theorem hasLaunchPair_of_hasStatePair {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω₀ : Ω}
    (hD : HasStatePair κ b jumps P h W' spec E k ω₀) : HasLaunchPair κ b jumps P h W' spec E k ω₀ := by
  intro c θ hl h' htr
  have hc := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω₀) hl).2.2
  subst hc
  exact hD (not_isTerminal_of_launch hl) h' htr

/-- **The datum before the first instruction**: the original counterflow itself (the conditional law given the empty
past is `P`, and the field read in the root chart `z ↦ z − 0` is `h`). -/
theorem hasStatePair_zero {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {gw : Bool} {p : List Instr} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    HasStatePair κ b jumps P h W' ⟨0, gw, p⟩ E 0 ω₀ := by
  intro _ h' htr
  have hc : (ExplState.run κ b jumps ⟨0, gw, p⟩ (fun j => E j ω₀) 0).2.2.2.2.1 = Chart.id.recenter 0 := rfl
  rw [hc] at htr ⊢
  have hh' : h' = h := funext fun ω => by
    rw [GW2aPiece.eq_flowField_of_isChartTransport (htr ω), Sec7.Prop74B.flowField_zero_zero]
  subst hh'
  have hν : condExpKernel P (pastSigma κ b jumps ⟨0, gw, p⟩ E 0) ω₀ = P := by
    rw [GW1.pastSigma_zero_eq_bot]
    exact GW1.condExpKernel_bot_apply P ω₀
  rw [hν]
  refine ⟨W', ζ', hcf, hζ', Eventually.of_forall fun ω r z hz => ?_⟩
  have h1 : infinitySourceChart.tipAt (fun s => W' s ω) r z := tipAt_recenter_zero_trans.1 hz
  have h2 : z ∈ infinitySourceChart.tipSet (fun s => W' s ω) ⊤ := by
    rw [Chart.tipSet_eq_tipAt]
    exact ⟨r, le_top, h1⟩
  exact mem_union_left _ h2

end GW2aCont

end Theorem14

end InteractingSLE
