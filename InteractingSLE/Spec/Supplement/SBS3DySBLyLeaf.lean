/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyLeaf
import InteractingSLE.Spec.Supplement.SBS3DyInst
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SBLyLeaf` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SBLyLeaf` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `HasConditionalRelativeTailRLe`;
* `hasConditionalActualTailSewing_of_relativeTailRLe`;
* `ScheduleRelativeTailRLe`;
* `scheduleActualTailSewing_of_relativeTailRLe`;
* `SB4DistinctSeedRelTailRLeStatement`;
* `SB4InitialArcRelTailRLeStatement`;
* `sb4DistinctSeedRetainedTailStatement_of_relTailRLe`;
* `sb4InitialArcRetainedTailStatement_of_relTailRLe`;
* `hasConditionalRelativeTail_of_launchRLe`;
* `scheduleRelativeTail_of_launchRLe`;
* `SB4DistinctSeedLaunchTailRLeStatement`;
* `sb4DistinctSeedRelTailRStatement_of_launchRLe`;
* `sb4InitialArcRelTailRStatement_of_launchRLe`;
* `sb4RetainedTailStatements_of_launchRLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ly

open Sec4 Leaf FlowDilate GW2Schedule Exist.StagedLaw
open PiecewiseConstantBoundaryData (rightLim jumpSet)

/-! ### The relative SB3 instance with the premise -/

/-- **The S1-free conditional data at one switch, with the premise** (`Leaf.HasConditionalRelativeTail` with
`IsRelSB3InstanceRLe`). -/
def HasConditionalRelativeTailRLe (κ : ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set Ω) (A S : Ω → Set ℂ) : Prop :=
  ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (a : Ω → ℝ≥0 → ℂ),
    NullMeasurableSet F P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, (∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ F → HasActualTailSewing (A ω) (S ω)) ∨
      ∃ (hQ : Ω → DistOn upperHalfPlaneOpens) (b' : ℝ → ℝ) (jumps' : Finset ℝ)
        (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
        IsRelSB3InstanceRLe κ (condExpKernel P 𝒢.1 ω₀) hQ b' jumps' EL u' ψ η ζ ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ F →
          HasRelTailGeometry (A ω) (S ω) (relWalkSet κ b' jumps' EL ω) u' (η ω) (ζ ω)

/-- **The comparison step of SB4 with the amended SB3.** -/
theorem hasConditionalActualTailSewing_of_relativeTailRLe (hSB3 : SB3InductionGenRLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Set Ω} {A S : Ω → Set ℂ}
    (hrel : HasConditionalRelativeTailRLe κ P F A S) : HasConditionalActualTailSewing P F A S := by
  obtain ⟨𝒢, a, hF, hm, hreg, hcond⟩ := hrel
  refine ⟨𝒢, a, hF, hm, hreg, ?_⟩
  filter_upwards [hcond] with ω₀ hω₀
  rcases hω₀ with hdir | ⟨hQ, b', jumps', EL, u', ψ, η, ζ, hI, hgeo⟩
  · exact hdir
  · filter_upwards [ae_isOneSided_of_relSB3InstanceRLe hSB3 h12 h13 hκ hκ4 hI, hgeo]
      with ω hS1 hg hωF
    exact (hg hωF).hasActualTailSewing (hS1 · · · ·)

/-! ### Schedules and the S1-free leaves -/

/-- `Leaf.ScheduleRelativeTail` with the premise. -/
def ScheduleRelativeTailRLe {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasConditionalRelativeTailRLe κ P
      {ω | (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k ≠ none}
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

/-- SB3 (amended) turns the S1-free switch data into SBSEW's local construction. -/
theorem scheduleActualTailSewing_of_relativeTailRLe (hSB3 : SB3InductionGenRLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ} {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (h : ScheduleRelativeTailRLe κ b jumps P E x l S) :
    ScheduleActualTailSewing κ b jumps P E x l S :=
  fun k hk hprev => hasConditionalActualTailSewing_of_relativeTailRLe hSB3 h12 h13 hκ hκ4 (h k hk hprev)

/-- **S1-free distinct-seed leaf with the premise** (`Leaf.SB4DistinctSeedRelTailStatement` with
`ScheduleRelativeTailRLe`). -/
def SB4DistinctSeedRelTailRLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        ScheduleRelativeTailRLe κ b jumps P E u l (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleRelativeTailRLe κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- **S1-free initial-arc leaf with the premise** (`Leaf.SB4InitialArcRelTailStatement` with
`ScheduleRelativeTailRLe`). -/
def SB4InitialArcRelTailRLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ v : ℝ, 0 < v →
      rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      ScheduleRelativeTailRLe κ b jumps P E v l (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

/-- **The distinct-seed retained-tail leaf from the amended SB3 and the S1-free data.** -/
theorem sb4DistinctSeedRetainedTailStatement_of_relTailRLe (hSB3 : SB3InductionGenRLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4DistinctSeedRelTailRLeStatement.{u}) : SB4DistinctSeedRetainedTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun x hx hθ hL hH =>
      scheduleActualTailSewing_of_relativeTailRLe hSB3 h12 h13 hκ hκ4 (hc.1 x hx hθ hL hH),
    fun x hx hθ hR' hH =>
      scheduleActualTailSewing_of_relativeTailRLe hSB3 h12 h13 hκ hκ4 (hc.2 x hx hθ hR' hH)⟩

/-- **The initial-arc retained-tail leaf from the amended SB3 and the S1-free data.** -/
theorem sb4InitialArcRetainedTailStatement_of_relTailRLe (hSB3 : SB3InductionGenRLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4InitialArcRelTailRLeStatement.{u}) : SB4InitialArcRetainedTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  exact scheduleActualTailSewing_of_relativeTailRLe hSB3 h12 h13 hκ hκ4
    (hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-! ### The launch form -/

/-- **The launch form gives the S1-free switch data with the premise** (`Leaf.hasConditionalRelativeTail_of_launch`
with the premise carried along). -/
theorem hasConditionalRelativeTail_of_launchRLe (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) {k : ℕ} {l : List (ℝ × ℝ≥0)}
    {original : Set ℝ} {A S : Ω → Set ℂ}
    (hangles : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hθl : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∃ q ∈ l, θ = q.1)
    (hL : HasLaunchRelativeTailR κ b jumps P h spec E k l original A S) :
    HasConditionalRelativeTailRLe κ P (launchEvent κ b jumps spec E k) A S := by
  obtain ⟨a, hF, hm, hreg, hcond⟩ := hL
  refine ⟨⟨pastSigma κ b jumps spec E k, hE.2.1 k⟩, a, hF, hm, hreg, ?_⟩
  filter_upwards [hcond, hE.2.2.2 k, hθl] with ω₀ hω₀ hlaunch hθ
  rcases hω₀ with hdir | ⟨c, θ, hcθ, hall⟩
  · exact Or.inl hdir
  · obtain ⟨b', J', hl, hb', hct, hfl⟩ := hlaunch c θ hcθ
    obtain ⟨m, EL, hm0, hadm, hEL, hword, hpos, hgeo⟩ := hall b' J' hl hb' hct hfl
    obtain ⟨q, hq, rfl⟩ := hθ c θ hcθ
    obtain ⟨hpc, hG, hFL⟩ := relFlowLine_of_isFlowLineDriver h13 hκ hb' hfl m
    refine Or.inr ⟨fun ω => affField m one_pos (hl ω), affData 1 m b', affJumps 1 m J', EL, m, q.1,
      fun ω t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) ω t),
      fun ω => (E k ω).2, ⟨⟨?_, hadm⟩, (hangles q hq).2⟩, hgeo⟩
    exact isRelSB3Instance_of_word hκ hκ4 (fun p hp => (hangles p hp).1) hgaps hbridge
      ⟨hpc, hG, hEL, hm0, ⟨q, hq, rfl⟩, hword, hFL, hpos⟩

/-- The launch form gives the chart-free switch data with the premise. -/
theorem scheduleRelativeTail_of_launchRLe (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ} {S : Ω → Set ℂ}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩
      (E ⟨x, true, scheduleProgram 0 l⟩))
    (hangles : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hL : ScheduleLaunchTailR κ b jumps P h E x l original S) :
    ScheduleRelativeTailRLe κ b jumps P E x l S :=
  fun k hk hprev => hasConditionalRelativeTail_of_launchRLe h13 hκ hκ4 hE hangles hgaps hbridge
    (Eventually.of_forall fun _ _ _ hcθ => launch_angle_mem_schedule hcθ)
    (hasLaunchRelativeTail_of_scheduleR hE hk (hL k hk hprev))

/-- **The SB4 distinct-seed leaf `hDS` with R95's premise** (`Leaf.SB4DistinctSeedLaunchTailStatement` with
`ScheduleLaunchTailR` / `ScheduleRelativeTailRLe`: at every switch the relative data also satisfy
`LowerLeftAdmissible`). -/
def SB4DistinctSeedLaunchTailRLeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ l : List (ℝ × ℝ≥0), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) →
      (∀ u ≤ 0, (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
        ScheduleLaunchTailR κ b jumps P h E u l (b '' {x | x ∈ Ioo u 0 ∧ x ∉ jumps}) (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleRelativeTailRLe κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

theorem sb4DistinctSeedRelTailRStatement_of_launchRLe (h13 : Exist.Theorem13Statement.{u})
    (hL : SB4DistinctSeedLaunchTailRLeStatement.{u}) : SB4DistinctSeedRelTailRLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  refine ⟨fun x hx hθ hLx hH => ?_, hc.2⟩
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram
    (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  exact scheduleRelativeTail_of_launchRLe h13 hκ hκ4 (hE _ hprog) hθ h41
    (distinctSeed_bridge hLx hH) (hc.1 x hx hθ hLx hH)

theorem sb4InitialArcRelTailRStatement_of_launchRLe (h13 : Exist.Theorem13Statement.{u})
    (hL : SB4InitialArcLaunchTailRStatement.{u}) : SB4InitialArcRelTailRLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram
    (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  exact scheduleRelativeTail_of_launchRLe h13 hκ hκ4 (hE _ hprog) hθ h41
    (fun _ _ _ hB => absurd hB (notMem_empty _))
    (hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-- **Both SB4 retained-tail leaves of Theorem 1.4's wiring** from the amended SB3, Theorems 1.2–1.3 and the
launch-form switch data with the premise (`Leaf.sb4RetainedTailStatements_of_launch` after R95). -/
theorem sb4RetainedTailStatements_of_launchRLe (hSB3 : SB3InductionGenRLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hDS : SB4DistinctSeedLaunchTailRLeStatement.{u}) (hIA : SB4InitialArcLaunchTailRStatement.{u}) :
    SB4DistinctSeedRetainedTailStatement.{u} ∧ SB4InitialArcRetainedTailStatement.{u} :=
  ⟨sb4DistinctSeedRetainedTailStatement_of_relTailRLe hSB3 h12 h13
      (sb4DistinctSeedRelTailRStatement_of_launchRLe h13 hDS),
    sb4InitialArcRetainedTailStatement_of_relTailRLe hSB3 h12 h13
      (sb4InitialArcRelTailRStatement_of_launchRLe h13 hIA)⟩

/-! ### The new leaves only add the premise -/

end InteractingSLE.Theorem14.SB.Ly
