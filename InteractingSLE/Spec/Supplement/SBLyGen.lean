/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyRight
import InteractingSLE.Spec.Supplement.SBLyStage
import InteractingSLE.Spec.Supplement.SBTail2EndFlow
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# SB3's induction statement with R95's premise

Packet PROVE-T14-SBLEAVES4. Ruling R95: `SB.SB3InductionGenStatement` (no counterflow binder, arbitrary boundary data)
lets the walk machine take left exits and leftward connectors, so its stage input "right additions" can fail
(PROVE-T14-SBLEAVES3, F9). The amended statement `SB3InductionGenRStatement` adds the premise that the lower walk's
thresholds are right records, in its checkable form on the data (`LowerLeftAdmissible`: every lower-walk left
cumulative weight on the negative axis exceeds `−2`). From it GW1's exit classification gives the right records and
the right additions (`SBLyRight`).

* `sb3InductionGenRStatement_of_gen`: the old statement implies the amended one (the amendment only adds a premise).
* `sb3InductionGenRStatement_of_inputs(_dyCover)`: the amended statement from SB2(1) at launch samples, SB1/S6,
  Theorem 1.3 and the three remaining stage inputs `SB3StageInputsRStatement` (path representation and the two
  null-measurability clauses). The completability input (I4) is PROVE-T14-SBTAIL2's
  `End.ae_isOneSided_right_real_of_isFlowLine`; the right additions (I3) are `ae_walkRightAdds_of_bound`.
* `lowerLeftAdmissible_of_counterflow`: the premise in the counterflow setting (GW1's `GW1Conn.ambient_bounds`), hence
  `sb3InductionRegStatement_of_genR` (the landed counterflow form) and `sb3RegStatement_of_param_genR`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ly

open Lx Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- **R95's premise, checkable form**: every lower-walk (angle `−π/2`) left cumulative weight on the negative real
axis exceeds `−2` ("All these old groups are admissible", SB2(2); GW1's ambient bound in the counterflow setting).
Under it no threshold of the lower walk is a left record (`GW1W.ae_status_ne_left_right_walk`). -/
def LowerLeftAdmissible (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∀ x, x < 0 → x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)

/-- **SB3's stage induction with R95's premise** (`SB.SB3InductionGenStatement` plus `LowerLeftAdmissible`). -/
def SB3InductionGenRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 → range γ = lowerWalkSet κ b jumps E ω →
        ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a

/-- The amendment only adds a premise. -/
theorem sb3InductionGenRStatement_of_gen (h : SB3InductionGenStatement.{u}) : SB3InductionGenRStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh _ E hE hreg u ψ hu hψ hL hH η ζ hη hζ =>
    h κ hκ hκ4 b jumps hb P h' hh E hE hreg u ψ hu hψ hL hH η ζ hη hζ

/-- **The remaining stage inputs of SB3's induction** (named open inputs; SBLEAVES3's `SB3StageInputsStatement` in the
amended setting without its clauses (I4) and (I3), which are now proved): every retained prefix at a launch `k ≥ 1`
is the image of a path with finite fibres from the upper seed, and the stage and truncation claim events are
null-measurable (supplement p. 577: S1 events are universally measurable). -/
def SB3StageInputsRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ spec j ω, IsRegularDriver (E spec j ω)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      (∀ k, 1 ≤ k → ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω →
        ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω)) ∧
      (∀ k, NullMeasurableSet {ω | SB3StageClaim κ b jumps E k u η ζ ω} P) ∧
      ∀ k, NullMeasurableSet {ω | SB3TruncClaim κ b jumps E k u η ζ ω} P

/-! ### SB2(1) in GW1's setting (rulings R94, R96) -/

/-- **SB2(1)'s conclusion at stage `k`** (the conclusion of `Lx.SB2UpperLaunchEntryLStatement` for the given data):
at almost every launch of instruction `k`, for every witness of the launch clause, the entry value `m ≤ 0`, SB2(1)'s
active word, the relative flow line and the remainder link. -/
def SB2UpperConclAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k =
        some (c, θ) →
    ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
      IsPiecewiseConstantBoundaryData b' jumps' →
      (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
      ∃ (m : ℝ) (ηr : Ω → ℝ≥0 → ℂ) (ζr : Ω → ℝ≥0∞), m ≤ 0 ∧
        IsLeftEntryValue c (realMin (lowerPrefix κ b jumps E k u ω₀)) m ∧
        IsActiveLowWord κ b jumps u b' jumps' m ∧
        IsFlowLine κ b' jumps' m ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' ηr ζr ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink c (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) (ηr ω) (ζr ω)

/-- **Lemma SB2(1), entry form, S1 at launch samples, in GW1's setting** (R94's `Lx.SB2UpperLaunchEntryLStatement`
for boundary data with `LowerLeftAdmissible`: the setting in which PROVE-GW1-EXTREC proves SB2(1)'s clause `m ≤ 0`,
`GW1Ext.ae_launchEntry_nonpos_of_ambient`; without it the clause can fail, R96). -/
def SB2UpperLaunchEntryLAmbStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    LowerLeftAdmissible κ b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      StageS1At κ b jumps P E k u η ζ → SB2UpperConclAt κ b jumps P h E k u ψ η ζ

/-- **Lemma SB2(1), entry form, S1 at launch samples, in Theorem 1.4's counterflow setting** (R96: R94's target with
the counterflow binder restored). -/
def SB2UpperLaunchEntryLCfStatement : Prop :=
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
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      StageS1At κ b jumps P E k u η ζ → SB2UpperConclAt κ b jumps P h E k u ψ η ζ

/-- R94's universal target gives the form in GW1's setting. -/
theorem sb2UpperLaunchEntryLAmbStatement_of_L (hSB2 : SB2UpperLaunchEntryLStatement.{u}) :
    SB2UpperLaunchEntryLAmbStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh _ E hE hreg k u ψ hu hψ hL hH η ζ hη hS1 =>
    hSB2 κ hκ hκ4 b jumps hb P h hh E hE hreg k u ψ hu hψ hL hH η ζ hη hS1

/-- **The relative stage ordering from SB2(1)'s conclusion at stage `k`** (the proof of
`Lx.ae_hasRelStageOrderingE_of_L`, which uses SB2(1) only at the data at hand). -/
theorem stageOrderingAt_of_concl (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (k : ℕ) {u ψ : ℝ} (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hconc : SB2UpperConclAt κ b jumps P h E k u ψ η ζ) :
    StageOrderingAt κ ψ b jumps P h E η ζ k u := by
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  unfold SB2UpperConclAt at hconc
  unfold StageOrderingAt
  filter_upwards [hconc, (hE _ hspec).2.2.2 k] with ω₀ hω₀ hlaunch
  intro c θ hcθ
  have hθ : θ = -(Real.pi / 2) := launch_angle_boundaryWalk hcθ
  obtain ⟨b', jumps', h', hb', hct, hfl⟩ := hlaunch c θ hcθ
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨m, ηr, ζr, hm, hent, hword, hηr, hlink⟩ := hω₀ c θ hcθ b' jumps' h' hb' hct hgff
  subst hθ
  have hα := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl
    ((GW2aSingle.ae_chosenTrace h13 hκ hfl).mono fun _ hω => hω.1)
  obtain ⟨hL', hH'⟩ := hybrid_of_activeLowWord hκ hκ4 hL hH hword
  have hord := fun hζα hζβ => Erase.ae_ordered_of_hybrid hSB1 hS6 hκ hκ4 hb' hgff hm hψ hL' hH' hα hηr hζα hζβ
  refine ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, hent, hα, hηr, hlink, ?_⟩
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hα with hL0 | hLp
  · filter_upwards [hL0] with ω hω hpos
    exact absurd hω hpos.ne'
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hηr with hr0 | hrp
  · filter_upwards [hr0] with ω hω _ hpos
    exact absurd hω hpos.ne'
  filter_upwards [hord (hLp.mono fun _ hω => pos_iff_ne_zero.2 hω) (hrp.mono fun _ hω => pos_iff_ne_zero.2 hω)]
    with ω hω _ _
  exact hω

/-- **SB3's stage induction with R95's premise** from SB2(1) in GW1's setting (S1 at launch samples), SB1, S6,
Theorem 1.3 and the three remaining stage inputs. The general family is regularized (`StagedReg.regFam`, almost surely
the same lower walk); the right additions (I3) are `ae_walkRightAdds_of_bound`, the completability (I4) is
`End.ae_isOneSided_right_real_of_isFlowLine`. -/
theorem sb3InductionGenRStatement_of_inputs (hSB2 : SB2UpperLaunchEntryLAmbStatement.{u})
    (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hIn : SB3StageInputsRStatement.{u}) : SB3InductionGenRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hR u ψ hu hψ hL hH η ζ hη hζ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hR
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  obtain ⟨hpath, hmeas, hmeasT⟩ :=
    hIn κ hκ hκ4 b jumps hb P h hh hadm (StagedReg.regFam E) hE' hR' hreg' u ψ hu hψ hL hH η ζ hη hζ
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  have hadd := ae_walkRightAdds_of_bound h13 hκ hb hh (hE' _ hspec) (hreg' _) hamb
  have hcomp : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a :=
    (End.ae_isOneSided_right_real_of_isFlowLine hκ hκ4 hη).mono fun _ hω a ha =>
      hω a ha (Icc u 0) fun _ hy => hy.1
  have hordOf : ∀ k, StageS1At κ b jumps P (StagedReg.regFam E) k u η ζ →
      StageOrderingAt κ ψ b jumps P h (StagedReg.regFam E) η ζ k u := fun k hS1 =>
    stageOrderingAt_of_concl hSB1 hS6 h13 hκ hκ4 hE' k hψ hL hH
      (hSB2 κ hκ hκ4 b jumps hb P h hh hadm (StagedReg.regFam E) hE' hR' k u ψ hu hψ hL hH η ζ hη hS1)
  filter_upwards [ae_sb3_of_inputsO hSB1 hS6 h13 hκ hκ4 hb hh hE' hR' (hreg' _) hu hψ hL hH hη hζ hordOf
    hcomp hpath hadd hmeas hmeasT, hrun _ hspec] with ω hω hrω γ hγ hγ0 hrange
  refine hω γ hγ hγ0 (hrange.trans ?_)
  exact (StagedReg.physSet_eq_of_run_eq (hrω _)).symm

/-- `sb3InductionGenRStatement_of_inputs` with SB1 and S6 discharged by the landed `W5Assembly` results. -/
theorem sb3InductionGenRStatement_of_inputs_dyCover (hSB2 : SB2UpperLaunchEntryLAmbStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB3StageInputsRStatement.{u}) : SB3InductionGenRStatement.{u} :=
  sb3InductionGenRStatement_of_inputs hSB2 (W5Assembly.sb1Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀)
    (W5Assembly.s6Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀) h13 hIn

/-! ### The premise in the counterflow setting -/

/-- The height form of the premise gives the weight form. -/
theorem cumWeightLeft_gt_of_height_lt {κ : ℝ} (hκ : 0 < κ) {y : ℝ} (hy : y < sleLambda κ) :
    -2 < cumWeightLeft κ y := by
  have hl := sleLambda_pos hκ
  unfold cumWeightLeft
  have h1 : y / sleLambda κ < 1 := (div_lt_one hl).2 hy
  have h2 : -y / sleLambda κ = -(y / sleLambda κ) := neg_div _ _
  linarith

/-- **R95's premise in the counterflow setting** (GW1's ambient bound, `GW1Conn.ambient_bounds`, from GW0's forward
implication, which Theorem 1.3 supplies). -/
theorem lowerLeftAdmissible_of_counterflow (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    LowerLeftAdmissible κ b jumps := fun x hx hxJ =>
  cumWeightLeft_gt_of_height_lt hκ
    ((GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ').1 x hx hxJ)

/-- **The landed counterflow form of SB3's induction** from the amended statement: in Theorem 1.4's setting the
premise is GW1's ambient bound. -/
theorem sb3InductionRegStatement_of_genR (hI : SB3InductionGenRStatement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB3InductionRegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh _ _ hcf hζ' E hE hreg u ψ hu hψ hL hH η ζ hη hζ =>
    hI κ hκ hκ4 b jumps hb P h hh (lowerLeftAdmissible_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ') E hE hreg u ψ hu
      hψ hL hH η ζ hη hζ

/-- Lemma SB3 for regular families from GW1's parametrization and the amended induction. -/
theorem sb3RegStatement_of_param_genR (hP : GW1ParamRegStatement.{u}) (hI : SB3InductionGenRStatement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB3RegStatement.{u} :=
  sb3RegStatement_of_param_induction hP (sb3InductionRegStatement_of_genR hI h13₀)

/-! ### The counterflow forms (ruling R96) -/

/-- SB2(1) in GW1's setting gives its counterflow form (the counterflow supplies the ambient bound). -/
theorem sb2UpperLaunchEntryLCfStatement_of_amb (hSB2 : SB2UpperLaunchEntryLAmbStatement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2UpperLaunchEntryLCfStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh _ _ hcf hζ' E hE hreg k u ψ hu hψ hL hH η ζ hη hS1 =>
    hSB2 κ hκ hκ4 b jumps hb P h hh (lowerLeftAdmissible_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ') E hE hreg k u ψ
      hu hψ hL hH η ζ hη hS1

/-- **The remaining stage inputs in the counterflow setting** (`SB3StageInputsRStatement` with the counterflow binder
in place of the ambient premise). -/
def SB3StageInputsCfStatement : Prop :=
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
      (∀ spec j ω, IsRegularDriver (E spec j ω)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      (∀ k, 1 ≤ k → ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω →
        ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω)) ∧
      (∀ k, NullMeasurableSet {ω | SB3StageClaim κ b jumps E k u η ζ ω} P) ∧
      ∀ k, NullMeasurableSet {ω | SB3TruncClaim κ b jumps E k u η ζ ω} P

/-- The inputs in GW1's setting give the counterflow form. -/
theorem sb3StageInputsCfStatement_of_R (hIn : SB3StageInputsRStatement.{u}) (h13₀ : Exist.Theorem13Statement.{0}) :
    SB3StageInputsCfStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh _ _ hcf hζ' E hE hR hreg u ψ hu hψ hL hH η ζ hη hζ =>
    hIn κ hκ hκ4 b jumps hb P h hh (lowerLeftAdmissible_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ') E hE hR hreg u ψ
      hu hψ hL hH η ζ hη hζ

/-- **SB3's stage induction in Theorem 1.4's counterflow setting** (the landed `SB.SB3InductionRegStatement`, ruling
R96) from SB2(1) and the stage inputs in that setting, SB1, S6 and Theorem 1.3 (at universes `u` and `0`): the ambient
bound is `lowerLeftAdmissible_of_counterflow`, R95's right additions `ae_walkRightAdds_of_bound`. -/
theorem sb3InductionRegStatement_of_cfInputs (hSB2 : SB2UpperLaunchEntryLCfStatement.{u})
    (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hIn : SB3StageInputsCfStatement.{u}) :
    SB3InductionRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR u ψ hu hψ hL hH η ζ hη hζ
  have hadm := lowerLeftAdmissible_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ'
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hR
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  obtain ⟨hpath, hmeas, hmeasT⟩ :=
    hIn κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hR' hreg' u ψ hu hψ hL hH η ζ hη hζ
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  have hadd := ae_walkRightAdds_of_bound h13 hκ hb hh (hE' _ hspec) (hreg' _) hamb
  have hcomp : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a :=
    (End.ae_isOneSided_right_real_of_isFlowLine hκ hκ4 hη).mono fun _ hω a ha =>
      hω a ha (Icc u 0) fun _ hy => hy.1
  have hordOf : ∀ k, StageS1At κ b jumps P (StagedReg.regFam E) k u η ζ →
      StageOrderingAt κ ψ b jumps P h (StagedReg.regFam E) η ζ k u := fun k hS1 =>
    stageOrderingAt_of_concl hSB1 hS6 h13 hκ hκ4 hE' k hψ hL hH
      (hSB2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hR' k u ψ hu hψ hL hH η ζ hη hS1)
  filter_upwards [ae_sb3_of_inputsO hSB1 hS6 h13 hκ hκ4 hb hh hE' hR' (hreg' _) hu hψ hL hH hη hζ hordOf
    hcomp hpath hadd hmeas hmeasT, hrun _ hspec] with ω hω hrω γ hγ hγ0 hrange
  refine hω γ hγ hγ0 (hrange.trans ?_)
  exact (StagedReg.physSet_eq_of_run_eq (hrω _)).symm

end InteractingSLE.Theorem14.SB.Ly
