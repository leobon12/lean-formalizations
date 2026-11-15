/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RArcGeom

/-!
# SB4's initial-arc leaf with R95's premise

Packet PROVE-T14-SB4LEAF. `Ly.SB4InitialArcLaunchTailRStatement`: for a seed `v > 0` on the lower walk's initial
forced arc, every switch of an upper schedule from `v` has the launch-form data against the right side of the
completed lower walk. The source (supplement p. 635): "For a connector seed `v`, retain the lower prefix through `v`.
The remaining lower walk, in its current domain, starts with the remaining low interval up to the next available
mark. [...] Apply the just-proved common-seed assertion in this retained field, then use the same winding gluing to
restore the earlier lower prefix."

The common-seed identification in the retained field is SB2(2) for the retained history `A = arcPrefix` (the schedule
from `v` with the arc `[0, v]`); its two halves are the named inputs

* **`SB2ArcLaunchStatement`**: SB2(2) at the arc seed (R99 form; on the initial arc there are no retained original
  bridge heights, so the active word on `(m, 0)` has only old upper sides and low heights);
* **`SB2ArcTailLiftStatement`**: its pointwise lift (as `Lf.SB2LowerTailLiftStatement`), with the arc on the lower
  walk ("the lower prefix through `v`").

Ruling R104a: the two are combined into **`SB2ArcLaunchLiftStatement`** (an output whose completed lower tail lifts;
`sb2ArcLaunchLiftStatement_of_pair`). From it: `lowerLeftAdmissible_of_arcWord` (R95's premise) and
**`scheduleLaunchTailR_arc_lift`**; `scheduleLaunchTailR_arc` is the round-1 form from the pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule
open PiecewiseConstantBoundaryData (rightLim jumpSet)

section Output

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (v : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
  (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)

/-- **SB2(2)'s output at the arc seed for one witness**: the translation `m ≤ 0` with the right entry value `−m` at
`R = max (A ∩ ℝ)`, the admissible old groups left of the upper tip, the active word on `(m, 0)` (old upper sides or
low heights), and the relative lower walk `EL` of the translated conditional field. -/
def IsArcLaunchOutput : Prop :=
  m ≤ 0 ∧
    (∀ y, y ≤ m → y ∉ affJumps 1 m J' →
      -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ)) ∧
    IsRightEntryValue c (realMax (arcPrefix κ b jumps E v l k ω₀)) (-m) ∧
    (∀ x ∈ Ioo m 0, x ∉ affJumps 1 m J' →
      (∃ p ∈ l, affData 1 m b' x = sleLambda κ - p.1 * chiC κ ∨
          affData 1 m b' x = -sleLambda κ - p.1 * chiC κ) ∨
        affData 1 m b' x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ) ∧
    IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL ∧
    StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀)
      (relLowerSpec b' J' m) EL

end Output

/-- **The setting of SB4's initial-arc case** (the hypotheses of `Ly.SB4InitialArcLaunchTailRStatement` at one switch
`k`, with the retained history on the closed left at the launch samples) for a proposition `C` about each retained
launch and each witness of its conditional launch law. -/
def SB2ArcSetting (C : ℝ → (ℝ → ℝ) → Finset ℝ → ∀ {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
    (ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) → ℝ → List (ℝ × ℝ≥0) → ℕ → Ω → Chart →
    (ℝ → ℝ) → Finset ℝ → (Ω → DistOn upperHalfPlaneOpens) → Prop) : Prop :=
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
    ∀ (v : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), 0 < v →
      rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ →
      (∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) →
      l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k →
        arcPrefix κ b jumps E v l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (sspec v l) (fun j => E (sspec v l) j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
        ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' J' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀)
            h' b' J' →
          C κ b jumps P E v l k ω₀ c b' J' h'

/-- **Named input: SB2(2) at the initial-arc seed** (R99 form): for every witness of the conditional launch law, a
translation `m ≤ 0` and a relative lower walk with `IsArcLaunchOutput`. -/
def SB2ArcLaunchStatement : Prop :=
  SB2ArcSetting.{u} fun κ b jumps _ _ _ P _ E v l k ω₀ c b' J' h' =>
    ∃ (m : ℝ) (EL : ℕ → _ → (ℝ≥0 → ℝ) × ℝ≥0∞), IsArcLaunchOutput κ b jumps P E v l k ω₀ c b' J' h' m EL

/-- **Named input: the pointwise lift at the initial-arc seed** (as `Lf.SB2LowerTailLiftStatement`): for every output
of SB2(2), almost surely under the retained kernel, the arc `[0, v]` is on the lower walk, the lower walk misses a real
point left of `0` and of the retained history, and the tail of every proper parametrization of the lower walk from
`0` after its visit to `R = max (A ∩ ℝ)` is the chart boundary image of the relative walk. -/
def SB2ArcTailLiftStatement : Prop :=
  SB2ArcSetting.{u} fun κ b jumps _ _ _ P _ E v l k ω₀ c b' J' h' =>
    ∀ (m : ℝ) (EL : ℕ → _ → (ℝ≥0 → ℝ) × ℝ≥0∞), IsArcLaunchOutput κ b jumps P E v l k ω₀ c b' J' h' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
        ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ lowerWalkSet κ b jumps E ω ∧
        (∃ y : ℝ, y < 0 ∧ y < realMin (arcPrefix κ b jumps E v l k ω₀) ∧
            (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
          ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
            IsTailLiftOf c (realMax (arcPrefix κ b jumps E v l k ω₀)) m β₀
              (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **SB2(2)'s combined output at the arc seed** (ruling R104a): an output with `IsArcLaunchOutput` whose completed
lower tail lifts (the clauses of `SB2ArcTailLiftStatement` for that output). -/
def ArcLiftOut (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (v : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), IsArcLaunchOutput κ b jumps P E v l k ω₀ c b' J' h' m EL ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ lowerWalkSet κ b jumps E ω ∧
      (∃ y : ℝ, y < 0 ∧ y < realMin (arcPrefix κ b jumps E v l k ω₀) ∧
          (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          IsTailLiftOf c (realMax (arcPrefix κ b jumps E v l k ω₀)) m β₀
            (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **Named input: SB2(2) at the initial-arc seed with the lift on its own output** (ruling R104a). -/
def SB2ArcLaunchLiftStatement : Prop :=
  SB2ArcSetting.{u} fun κ b jumps _ _ _ P _ E v l k ω₀ c b' J' h' => ArcLiftOut κ b jumps P E v l k ω₀ c b' J' h'

/-- The round-1 pair of arc inputs gives the combined one. -/
theorem sb2ArcLaunchLiftStatement_of_pair (hArc : SB2ArcLaunchStatement.{u})
    (hArcLift : SB2ArcTailLiftStatement.{u}) : SB2ArcLaunchLiftStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER v l k hv hlow0 hlow hl hθ hleft
  filter_upwards [hArc κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER v l k hv hlow0 hlow hl hθ hleft,
    hArcLift κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER v l k hv hlow0 hlow hl hθ hleft] with ω₀ h₀ h₁
  intro c θ hcθ b' J' h' hb' hT' hG'
  obtain ⟨m, EL, hout⟩ := h₀ c θ hcθ b' J' h' hb' hT' hG'
  exact ⟨m, EL, hout, h₁ c θ hcθ b' J' h' hb' hT' hG' m EL hout⟩

/-- **R95's premise from the arc word**: on `(m, 0)` old upper sides of angles `ψ > −π/2` or low heights, and the
clause left of the upper tip. -/
theorem lowerLeftAdmissible_of_arcWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {l : List (ℝ × ℝ≥0)}
    (hlθ : ∀ p ∈ l, -(Real.pi / 2) < p.1) {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    (hleft : ∀ y, y ≤ m → y ∉ affJumps 1 m J' →
      -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ))
    (hword : ∀ x ∈ Ioo m 0, x ∉ affJumps 1 m J' →
      (∃ p ∈ l, affData 1 m b' x = sleLambda κ - p.1 * chiC κ ∨
          affData 1 m b' x = -sleLambda κ - p.1 * chiC κ) ∨
        affData 1 m b' x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ) :
    LowerLeftAdmissible κ (affData 1 m b') (affJumps 1 m J') := by
  refine Lz.lowerLeftAdmissible_of_activeHighWord (b := b') (jumps := J') (u := 0) hκ hκ4 hlθ
    (fun x hx => absurd hx (by simp)) hleft fun y hy hyJ => ?_
  rcases hword y hy hyJ with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- **SB4's initial-arc leaf with R95's premise**: for a seed `v > 0` on the lower walk's initial forced arc and an
upper schedule from `v` with angles in `(−π/2, π/2]`, every switch has the launch-form data `Ly.HasScheduleLaunchTailR`
(with no retained original word) against the right side of the completed lower walk. -/
theorem scheduleLaunchTailR_arc_lift (hC : SB2ArcLaunchLiftStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {v : ℝ} (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2))
    (hθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) :
    ScheduleLaunchTailR κ b jumps P h E v l ∅ (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω)) := by
  intro k hk hprev
  have hprog : IsBoundaryContinuedProgram (sspec v l).2.2 :=
    GW2Sched.isBoundaryContinuedProgram_scheduleProgram (fun p hp => Ioc_subset_Icc_self (hθ p hp)) 0
  have hEu := hE _ hprog
  have hRu := hreg _ hprog
  have hprogL := Fin.isBoundaryContinuedProgram_lowerWalk b jumps
  obtain ⟨a, ham, hareg⟩ := Side.exists_rightSide_launch_param hb hEu.1 hRu (hE _ hprogL).1 (hreg _ hprogL) hk
  refine ⟨a, ham, hareg, ?_⟩
  have hleftP : ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k →
      arcPrefix κ b jumps E v l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅ :=
    hprev.mono fun ω hω _ => inter_rightSideOf_union_real hω
  have hout := hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v l k hv hlow0 hlow hl hθ hleftP
  have hβQ := KernelTower.ae_ae_condExpKernel_of_ae (hEu.2.1 k)
    (hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg)
  have havQ := ae_ae_prefix_avoid hEu hRu hprev
  filter_upwards [hout, hβQ, havQ, Retain.ae_launch_word_cases hκ hb hEu hRu k,
    Retain.ae_launch_chosenTrace_readout h13 hκ hEu hRu hk, hRu.ae_pieceRegular]
    with ω₀ hout₀ hβ₀ hav₀ hwc hread hreg₀
  intro c θ hlaunch
  obtain ⟨hcc, bc, jc, hl₀, hbc, hct, hG, hfl₀, hcases⟩ := hwc c θ hlaunch
  obtain ⟨f, -, hf, hfc, -, hreadW⟩ := hread c θ hlaunch
  -- the retained history at `ω₀`
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    exists_path_arcPrefix (κ := κ) (b := b) (jumps := jumps) hv.le l (fun j => E (sspec v l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = arcPrefix κ b jumps E v l k ω₀ := hpA
  have hc := (eq_launch_of_launches (sspec v l) (fun j => E (sspec v l) j ω₀) hlaunch).2.2
  have hnot := stStatus_ne_done_of_launches _ _ hlaunch
  have hAc : IsCompact (arcPrefix κ b jumps E v l k ω₀) :=
    (isCompact_prefixPhysSet_run _ _ hreg₀ k hnot).union (isCompact_Icc.image Complex.continuous_ofReal)
  -- the geometry for any witness with any output
  have hgeo : ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (hl' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
      (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      IsFlowLineDriver κ b' J' θ
        (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀) hl'
        (fun t ω => (E (sspec v l) k ω).1 t) (fun ω => (E (sspec v l) k ω).2) →
      IsArcLaunchOutput κ b jumps P E v l k ω₀ c b' J' hl' m EL →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
        ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ lowerWalkSet κ b jumps E ω ∧
        (∃ y : ℝ, y < 0 ∧ y < realMin (arcPrefix κ b jumps E v l k ω₀) ∧
            (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
          ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
            IsTailLiftOf c (realMax (arcPrefix κ b jumps E v l k ω₀)) m β₀
              (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
        HasRelTailGeometry (schedulePiece κ b jumps v l (fun j => E (sspec v l) j ω) k)
          (rightSideOf (lowerWalkSet κ b jumps E ω))
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω) m
          (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E (sspec v l) k ω).1 t)
            (fun ω => (E (sspec v l) k ω).2) ω t)) (E (sspec v l) k ω).2 := by
    intro b' J' hl' m EL hfl' hout' hlift'
    have hrc : IsRightEntryChart (arcPrefix κ b jumps E v l k ω₀)
        (realMax (arcPrefix κ b jumps E v l k ω₀)) (c.recenter (-m)) := by
      rw [hc]
      refine isRightEntryChart_runChart _ _ hreg₀ k hnot hAc (Lw.fillH_union_real _ _) ?_
      have hsc : stChart (ExplState.run κ b jumps (sspec v l) (fun i => E (sspec v l) i ω₀) k) = c := hc.symm
      rw [hsc]; exact hout'.2.2.1
    refine ae_relTailGeometry_of_path h13 hκ hp hp0 hpH hpA' hcc hout'.1 hrc hf hfc hfl'
      (T := schedDelta 0 l k) ((hreadW b' J' hl' hfl').mono fun _ hω => hω.2.1.subset) hβ₀
      (hlift'.mono fun _ hω => hω.2) ?_ (Eventually.of_forall fun _ => subset_rfl)
    filter_upwards [hlift', hav₀] with ω hω havω β₀ hβ₀ hβ₀0 hβ₀r
    refine subset_closedLeftSide_of_avoid' hβ₀ hβ₀0 hcl ?_ (by rw [hβ₀r]; exact havω)
    intro z hz
    exact Or.inr (Or.inl (hβ₀r ▸ hω.1 hz))
  rcases hcases with hzero | hpos
  · refine Or.inl ?_
    obtain ⟨m, EL, hout', hlift'⟩ := hout₀ c θ hlaunch bc jc hl₀ hbc hct hG
    filter_upwards [hgeo bc jc hl₀ m EL hfl₀ hout' hlift', hzero]
      with ω hg hz _
    rw [hz.1] at hg
    exact hg.hasActualTailSewing_zero
  · refine Or.inr fun b' J' hl' hb' hct' hfl' => ?_
    have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl'
    obtain ⟨m, EL, hout', hlift'⟩ := hout₀ c θ hlaunch b' J' hl' hb' hct' hG'
    have hg := hgeo b' J' hl' m EL hfl' hout' hlift'
    obtain ⟨hm, hlm, -, hword, hst, hregL⟩ := hout'
    refine ⟨m, EL, hm, lowerLeftAdmissible_of_arcWord hκ hκ4 (fun p hp => (hθ p hp).1) hlm hword,
      fun _ => ⟨hst, hregL⟩, fun x hx hxJ => ?_, hpos, hg.mono fun _ hω _ => hω⟩
    rcases hword x hx hxJ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **The initial-arc leaf in the round-1 form** (the pair of arc inputs). -/
theorem scheduleLaunchTailR_arc (hArc : SB2ArcLaunchStatement.{u}) (hArcLift : SB2ArcTailLiftStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {v : ℝ} (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b jumps, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2))
    (hθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) :
    ScheduleLaunchTailR κ b jumps P h E v l ∅ (fun ω => rightSideOf (lowerWalkSet κ b jumps E ω)) :=
  scheduleLaunchTailR_arc_lift (sb2ArcLaunchLiftStatement_of_pair hArc hArcLift) hPR h13 hκ hκ4 hb hh hcf hζ' hE
    hreg hv hlow0 hlow hl hθ

end InteractingSLE.Theorem14.SB.Lf
