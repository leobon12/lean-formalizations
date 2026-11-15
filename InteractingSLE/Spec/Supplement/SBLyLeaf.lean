/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyGen
import InteractingSLE.Spec.Supplement.SBLeafLaunchWire

/-!
# SB4's switch step with R95's premise

Packet PROVE-T14-SBLEAVES4. Ruling R95: SB3's induction statement gets the premise that the lower walk's thresholds
are right records (`Ly.SB3InductionGenRStatement`, premise `LowerLeftAdmissible`), and its consumers supply it at each
use. The only consumer in Theorem 1.4's wiring is SB4's switch step (PROVE-T14-SBTAIL's `SBLeafStep`,
`SBLeafAssembly`, `SBLeafLaunch`, `SBLeafLaunchWire`): SB3 is applied to SB2(2)'s relative lower walk in the chart of
the new upper piece. There the premise is a condition on the relative boundary data, supplied by SB2(2)'s word
("All these old groups are admissible ... An ordinary lower piece can therefore terminate only at its retained
original threshold"; spec p. 632).

This file repeats that chain with the premise carried by the relative data (`…R` names; each `…R` definition is its
landed namesake plus the one conjunct `LowerLeftAdmissible` on the relative data):

* `IsRelSB3InstanceR`, `ae_isOneSided_of_relSB3InstanceR`, `HasConditionalRelativeTailR`,
  `hasConditionalActualTailSewing_of_relativeTailR`;
* `ScheduleRelativeTailR`, `SB4DistinctSeedRelTailRStatement`, `SB4InitialArcRelTailRStatement` and the two
  retained-tail leaves from them;
* the launch form: `LaunchRelDataR`, `HasLaunchRelativeTailR`, `HasScheduleLaunchTailR`, `ScheduleLaunchTailR`,
  **`SB4DistinctSeedLaunchTailRStatement`**, **`SB4InitialArcLaunchTailRStatement`** (the SB4 leaves `hDS`, `hIA`
  with the premise), and `sb4RetainedTailStatements_of_launchR`;
* the forgetful maps to the landed leaves (`sb4DistinctSeedLaunchTailStatement_of_R`, …): the new leaves only add the
  premise.
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

/-- **The relative pair is an instance of the amended Lemma SB3**: `Leaf.IsRelSB3Instance` and R95's premise on the
relative data. -/
def IsRelSB3InstanceR (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Ω → DistOn upperHalfPlaneOpens)
    (b' : ℝ → ℝ) (jumps' : Finset ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsRelSB3Instance κ Q hQ b' jumps' EL u' ψ η ζ ∧ LowerLeftAdmissible κ b' jumps'

/-- **A relative counterflow gives the premise** (R96): if the relative field carries a complete centred counterflow
under `Q`, the relative instance is an instance of the amended SB3 (GW1's ambient bound). -/
theorem isRelSB3InstanceR_of_counterflow (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hQ : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {jumps' : Finset ℝ} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u' ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hI : IsRelSB3Instance κ Q hQ b' jumps' EL u' ψ η ζ)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ Q hQ W' ζ')
    (hζ' : ∀ᵐ ω ∂Q, ζ' ω = ⊤) : IsRelSB3InstanceR κ Q hQ b' jumps' EL u' ψ η ζ :=
  ⟨hI, lowerLeftAdmissible_of_counterflow h13₀ hκ hκ4 hI.1 hI.2.1 hcf hζ'⟩

/-- **The amended SB3 applied to a relative instance** (`Leaf.ae_isOneSided_of_relSB3Instance` with the premise). -/
theorem ae_isOneSided_of_relSB3InstanceR (hSB3 : SB3InductionGenRStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {hQ : Ω → DistOn upperHalfPlaneOpens}
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u' ψ : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hI : IsRelSB3InstanceR κ Q hQ b' jumps' EL u' ψ η ζ) :
    ∀ᵐ ω ∂Q, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 →
      range γ = relWalkSet κ b' jumps' EL ω →
      ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u' 0) (η ω) a := by
  classical
  obtain ⟨⟨hb, hh, hL, hu, hψ, hA, hH, hη, hζ⟩, hadm⟩ := hI
  obtain ⟨E₀, hE₀⟩ :=
    Exist.StagedLaw.exists_isStagedHistory_regular_of_thm12_thm13 h12 h13 hκ hκ4 hb hh
  have hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b' jumps' Q hQ spec
          (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL spec) ∧
        StagedPiecesRegular κ b' jumps' Q spec
          (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL spec) := by
    intro spec hspec
    by_cases hs : spec = boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true
    · subst hs
      rw [Function.update_self]
      exact hL hspec
    · rw [Function.update_of_ne hs]
      exact hE₀ spec hspec
  have hS := hSB3 κ hκ hκ4 b' jumps' hb Q hQ hh hadm
    (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL)
    (fun s hs => (hE s hs).1) (fun s hs => (hE s hs).2) u' ψ hu hψ hA hH η ζ hη hζ
  filter_upwards [hS] with ω hω γ hγ hγ0 hr
  exact hω γ hγ hγ0 (by rw [lowerWalkSet_update]; exact hr)

/-- **The S1-free conditional data at one switch, with the premise** (`Leaf.HasConditionalRelativeTail` with
`IsRelSB3InstanceR`). -/
def HasConditionalRelativeTailR (κ : ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set Ω) (A S : Ω → Set ℂ) : Prop :=
  ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (a : Ω → ℝ≥0 → ℂ),
    NullMeasurableSet F P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, (∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ F → HasActualTailSewing (A ω) (S ω)) ∨
      ∃ (hQ : Ω → DistOn upperHalfPlaneOpens) (b' : ℝ → ℝ) (jumps' : Finset ℝ)
        (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
        IsRelSB3InstanceR κ (condExpKernel P 𝒢.1 ω₀) hQ b' jumps' EL u' ψ η ζ ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ F →
          HasRelTailGeometry (A ω) (S ω) (relWalkSet κ b' jumps' EL ω) u' (η ω) (ζ ω)

/-- The amended data forget to the landed data. -/
theorem HasConditionalRelativeTailR.toLanded {κ : ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Set Ω} {A S : Ω → Set ℂ}
    (h : HasConditionalRelativeTailR κ P F A S) : HasConditionalRelativeTail κ P F A S := by
  obtain ⟨𝒢, a, hF, hm, hreg, hcond⟩ := h
  refine ⟨𝒢, a, hF, hm, hreg, ?_⟩
  filter_upwards [hcond] with ω₀ hω₀
  rcases hω₀ with hdir | ⟨hQ, b', jumps', EL, u', ψ, η, ζ, hI, hgeo⟩
  · exact Or.inl hdir
  · exact Or.inr ⟨hQ, b', jumps', EL, u', ψ, η, ζ, hI.1, hgeo⟩

/-- **The comparison step of SB4 with the amended SB3.** -/
theorem hasConditionalActualTailSewing_of_relativeTailR (hSB3 : SB3InductionGenRStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Set Ω} {A S : Ω → Set ℂ}
    (hrel : HasConditionalRelativeTailR κ P F A S) : HasConditionalActualTailSewing P F A S := by
  obtain ⟨𝒢, a, hF, hm, hreg, hcond⟩ := hrel
  refine ⟨𝒢, a, hF, hm, hreg, ?_⟩
  filter_upwards [hcond] with ω₀ hω₀
  rcases hω₀ with hdir | ⟨hQ, b', jumps', EL, u', ψ, η, ζ, hI, hgeo⟩
  · exact hdir
  · filter_upwards [ae_isOneSided_of_relSB3InstanceR hSB3 h12 h13 hκ hκ4 hI, hgeo]
      with ω hS1 hg hωF
    exact (hg hωF).hasActualTailSewing (hS1 · · · ·)

/-! ### Schedules and the S1-free leaves -/

/-- `Leaf.ScheduleRelativeTail` with the premise. -/
def ScheduleRelativeTailR {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasConditionalRelativeTailR κ P
      {ω | (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k ≠ none}
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

theorem ScheduleRelativeTailR.toLanded {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ} {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (h : ScheduleRelativeTailR κ b jumps P E x l S) : ScheduleRelativeTail κ b jumps P E x l S :=
  fun k hk hprev => (h k hk hprev).toLanded

/-- SB3 (amended) turns the S1-free switch data into SBSEW's local construction. -/
theorem scheduleActualTailSewing_of_relativeTailR (hSB3 : SB3InductionGenRStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ} {l : List (ℝ × ℝ≥0)} {S : Ω → Set ℂ}
    (h : ScheduleRelativeTailR κ b jumps P E x l S) :
    ScheduleActualTailSewing κ b jumps P E x l S :=
  fun k hk hprev => hasConditionalActualTailSewing_of_relativeTailR hSB3 h12 h13 hκ hκ4 (h k hk hprev)

/-- **S1-free distinct-seed leaf with the premise** (`Leaf.SB4DistinctSeedRelTailStatement` with
`ScheduleRelativeTailR`). -/
def SB4DistinctSeedRelTailRStatement : Prop :=
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
        ScheduleRelativeTailR κ b jumps P E u l (fun ω =>
          rightSideOf (lowerWalkSet κ b jumps E ω))) ∧
      (∀ v, 0 ≤ v → (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
        (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        (∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
        ScheduleRelativeTailR κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- **S1-free initial-arc leaf with the premise** (`Leaf.SB4InitialArcRelTailStatement` with
`ScheduleRelativeTailR`). -/
def SB4InitialArcRelTailRStatement : Prop :=
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
      ScheduleRelativeTailR κ b jumps P E v l (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

/-- **The distinct-seed retained-tail leaf from the amended SB3 and the S1-free data.** -/
theorem sb4DistinctSeedRetainedTailStatement_of_relTailR (hSB3 : SB3InductionGenRStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4DistinctSeedRelTailRStatement.{u}) : SB4DistinctSeedRetainedTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun x hx hθ hL hH =>
      scheduleActualTailSewing_of_relativeTailR hSB3 h12 h13 hκ hκ4 (hc.1 x hx hθ hL hH),
    fun x hx hθ hR' hH =>
      scheduleActualTailSewing_of_relativeTailR hSB3 h12 h13 hκ hκ4 (hc.2 x hx hθ hR' hH)⟩

/-- **The initial-arc retained-tail leaf from the amended SB3 and the S1-free data.** -/
theorem sb4InitialArcRetainedTailStatement_of_relTailR (hSB3 : SB3InductionGenRStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : SB4InitialArcRelTailRStatement.{u}) : SB4InitialArcRetainedTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  exact scheduleActualTailSewing_of_relativeTailR hSB3 h12 h13 hκ hκ4
    (hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-! ### The launch form -/

/-- **The data at one launched realization, with the premise** (`Leaf.LaunchRelData` with one more conjunct: the
translated relative data satisfy `LowerLeftAdmissible`, SB2(2)'s "All these old groups are admissible"). -/
def LaunchRelDataR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) (l : List (ℝ × ℝ≥0)) (original : Set ℝ) (A S : Ω → Set ℂ) (ω₀ : Ω) (c : Chart)
    (θ : ℝ) : Prop :=
  ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (hl : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hl ω)) →
    IsFlowLineDriver κ b' J' θ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) hl
      (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) →
    ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), m ≤ 0 ∧
      LowerLeftAdmissible κ (affData 1 m b') (affJumps 1 m J') ∧
      (IsBoundaryContinuedProgram
          (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true).2.2 →
        IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
            (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            (fun ω => affField m one_pos (hl ω))
            (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) EL ∧
          StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
            (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) EL) ∧
      (∀ x ∈ Ioo m 0, x ∉ affJumps 1 m J' →
        (∃ p ∈ l, affData 1 m b' x = sleLambda κ - p.1 * chiC κ ∨
            affData 1 m b' x = -sleLambda κ - p.1 * chiC κ) ∨
          affData 1 m b' x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
          affData 1 m b' x ∈ original) ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), 0 < (E k ω).2) ∧
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        ω ∈ launchEvent κ b jumps spec E k →
        HasRelTailGeometry (A ω) (S ω)
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω) m
          (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t)
            (fun ω => (E k ω).2) ω t)) (E k ω).2

theorem LaunchRelDataR.toLanded {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {k : ℕ} {l : List (ℝ × ℝ≥0)} {original : Set ℝ} {A S : Ω → Set ℂ} {ω₀ : Ω} {c : Chart} {θ : ℝ}
    (hD : LaunchRelDataR κ b jumps P h spec E k l original A S ω₀ c θ) :
    LaunchRelData κ b jumps P h spec E k l original A S ω₀ c θ := by
  intro b' J' hl hb' hct hfl
  obtain ⟨m, EL, hm, -, hEL, hword, hpos, hgeo⟩ := hD b' J' hl hb' hct hfl
  exact ⟨m, EL, hm, hEL, hword, hpos, hgeo⟩

/-- `Leaf.HasLaunchRelativeTail` with `LaunchRelDataR`. -/
def HasLaunchRelativeTailR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) (l : List (ℝ × ℝ≥0)) (original : Set ℝ) (A S : Ω → Set ℂ) : Prop :=
  ∃ a : Ω → ℝ≥0 → ℂ,
    NullMeasurableSet (launchEvent κ b jumps spec E k) P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps spec E k →
      Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P,
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        ω ∈ launchEvent κ b jumps spec E k → HasActualTailSewing (A ω) (S ω)) ∨
      ∃ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) ∧
        LaunchRelDataR κ b jumps P h spec E k l original A S ω₀ c θ

/-- **The launch form gives the S1-free switch data with the premise** (`Leaf.hasConditionalRelativeTail_of_launch`
with the premise carried along). -/
theorem hasConditionalRelativeTail_of_launchR (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E) {k : ℕ} {l : List (ℝ × ℝ≥0)}
    {original : Set ℝ} {A S : Ω → Set ℂ}
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hθl : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∃ q ∈ l, θ = q.1)
    (hL : HasLaunchRelativeTailR κ b jumps P h spec E k l original A S) :
    HasConditionalRelativeTailR κ P (launchEvent κ b jumps spec E k) A S := by
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
      fun ω => (E k ω).2, ⟨?_, hadm⟩, hgeo⟩
    exact isRelSB3Instance_of_word hκ hκ4 hangles hgaps hbridge
      ⟨hpc, hG, hEL, hm0, ⟨q, hq, rfl⟩, hword, hFL, hpos⟩

/-- `Leaf.HasScheduleLaunchTail` with `LaunchRelDataR`. -/
def HasScheduleLaunchTailR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (x : ℝ) (l : List (ℝ × ℝ≥0))
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (original : Set ℝ) (A S : Ω → Set ℂ) : Prop :=
  ∃ a : Ω → ℝ≥0 → ℂ,
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
      Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩ (fun j => E j ω₀) (k + 1)).2.2.2.1 k =
        some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
          ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (A ω) (S ω)) ∨
        LaunchRelDataR κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l original A S ω₀ c θ

theorem HasScheduleLaunchTailR.toLanded {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {original : Set ℝ} {A S : Ω → Set ℂ}
    (hL : HasScheduleLaunchTailR κ b jumps P h x l E k original A S) :
    HasScheduleLaunchTail κ b jumps P h x l E k original A S := by
  obtain ⟨a, hm, hreg, hcond⟩ := hL
  refine ⟨a, hm, hreg, ?_⟩
  filter_upwards [hcond] with ω₀ h1 c θ hcθ
  rcases h1 c θ hcθ with hd | hd
  · exact Or.inl hd
  · exact Or.inr hd.toLanded

theorem hasLaunchRelativeTail_of_scheduleR {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {original : Set ℝ} {A S : Ω → Set ℂ}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hk : k < (scheduleProgram 0 l).length)
    (hL : HasScheduleLaunchTailR κ b jumps P h x l E k original A S) :
    HasLaunchRelativeTailR κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l original A S := by
  obtain ⟨a, hm, hreg, hcond⟩ := hL
  have hF := measurableSet_launchEvent_schedule (κ := κ) (b := b) (jumps := jumps) (x := x) E hk
  refine ⟨a, (hE.2.1 k _ hF).nullMeasurableSet, hm, hreg, ?_⟩
  filter_upwards [hcond, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (hE.2.1 k) hF.compl]
    with ω₀ h1 h2
  by_cases hω₀ : ω₀ ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k
  · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hω₀
    rcases h1 c θ hcθ with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨c, θ, hcθ, hd⟩
  · refine Or.inl ?_
    filter_upwards [h2 hω₀] with ω hω hωF
    exact absurd hωF hω

/-- `Leaf.ScheduleLaunchTail` with `HasScheduleLaunchTailR`. -/
def ScheduleLaunchTailR {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ)
    (l : List (ℝ × ℝ≥0)) (original : Set ℝ) (S : Ω → Set ℂ) : Prop :=
  ∀ k < (scheduleProgram 0 l).length,
    (∀ᵐ ω ∂P, prefixPhysSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k ∩ S ω = ∅) →
    HasScheduleLaunchTailR κ b jumps P h x l (E ⟨x, true, scheduleProgram 0 l⟩) k original
      (fun ω => schedulePiece κ b jumps x l
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) S

theorem ScheduleLaunchTailR.toLanded {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ} {S : Ω → Set ℂ}
    (hL : ScheduleLaunchTailR κ b jumps P h E x l original S) :
    ScheduleLaunchTail κ b jumps P h E x l original S :=
  fun k hk hprev => (hL k hk hprev).toLanded

/-- The launch form gives the chart-free switch data with the premise. -/
theorem scheduleRelativeTail_of_launchR (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x : ℝ}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ} {S : Ω → Set ℂ}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩
      (E ⟨x, true, scheduleProgram 0 l⟩))
    (hangles : ∀ p ∈ l, -(Real.pi / 2) < p.1)
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hL : ScheduleLaunchTailR κ b jumps P h E x l original S) :
    ScheduleRelativeTailR κ b jumps P E x l S :=
  fun k hk hprev => hasConditionalRelativeTail_of_launchR h13 hκ hκ4 hE hangles hgaps hbridge
    (Eventually.of_forall fun _ _ _ hcθ => launch_angle_mem_schedule hcθ)
    (hasLaunchRelativeTail_of_scheduleR hE hk (hL k hk hprev))

/-- **The SB4 distinct-seed leaf `hDS` with R95's premise** (`Leaf.SB4DistinctSeedLaunchTailStatement` with
`ScheduleLaunchTailR` / `ScheduleRelativeTailR`: at every switch the relative data also satisfy
`LowerLeftAdmissible`). -/
def SB4DistinctSeedLaunchTailRStatement : Prop :=
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
        ScheduleRelativeTailR κ b jumps P E v l (fun ω =>
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω))))

/-- **The SB4 initial-arc leaf `hIA` with R95's premise** (`Leaf.SB4InitialArcLaunchTailStatement` with
`ScheduleLaunchTailR`). -/
def SB4InitialArcLaunchTailRStatement : Prop :=
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
      ScheduleLaunchTailR κ b jumps P h E v l ∅ (fun ω =>
        rightSideOf (lowerWalkSet κ b jumps E ω))

theorem sb4DistinctSeedRelTailRStatement_of_launchR (h13 : Exist.Theorem13Statement.{u})
    (hL : SB4DistinctSeedLaunchTailRStatement.{u}) : SB4DistinctSeedRelTailRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  refine ⟨fun x hx hθ hLx hH => ?_, hc.2⟩
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram
    (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  exact scheduleRelativeTail_of_launchR h13 hκ hκ4 (hE _ hprog) (fun p hp => (hθ p hp).1) h41
    (distinctSeed_bridge hLx hH) (hc.1 x hx hθ hLx hH)

theorem sb4InitialArcRelTailRStatement_of_launchR (h13 : Exist.Theorem13Statement.{u})
    (hL : SB4InitialArcLaunchTailRStatement.{u}) : SB4InitialArcRelTailRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  have hprog := GW2Sched.isBoundaryContinuedProgram_scheduleProgram
    (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  exact scheduleRelativeTail_of_launchR h13 hκ hκ4 (hE _ hprog) (fun p hp => (hθ p hp).1) h41
    (fun _ _ _ hB => absurd hB (notMem_empty _))
    (hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ)

/-- **Both SB4 retained-tail leaves of Theorem 1.4's wiring** from the amended SB3, Theorems 1.2–1.3 and the
launch-form switch data with the premise (`Leaf.sb4RetainedTailStatements_of_launch` after R95). -/
theorem sb4RetainedTailStatements_of_launchR (hSB3 : SB3InductionGenRStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hDS : SB4DistinctSeedLaunchTailRStatement.{u}) (hIA : SB4InitialArcLaunchTailRStatement.{u}) :
    SB4DistinctSeedRetainedTailStatement.{u} ∧ SB4InitialArcRetainedTailStatement.{u} :=
  ⟨sb4DistinctSeedRetainedTailStatement_of_relTailR hSB3 h12 h13
      (sb4DistinctSeedRelTailRStatement_of_launchR h13 hDS),
    sb4InitialArcRetainedTailStatement_of_relTailR hSB3 h12 h13
      (sb4InitialArcRelTailRStatement_of_launchR h13 hIA)⟩

/-! ### The new leaves only add the premise -/

theorem sb4DistinctSeedLaunchTailStatement_of_R (hL : SB4DistinctSeedLaunchTailRStatement.{u}) :
    SB4DistinctSeedLaunchTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  have hc := hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun x hx hθ hLx hH => (hc.1 x hx hθ hLx hH).toLanded,
    fun x hx hθ hLx hH => (hc.2 x hx hθ hLx hH).toLanded⟩

theorem sb4InitialArcLaunchTailStatement_of_R (hL : SB4InitialArcLaunchTailRStatement.{u}) :
    SB4InitialArcLaunchTailStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ
  exact (hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl h41 hθ).toLanded

end InteractingSLE.Theorem14.SB.Ly
