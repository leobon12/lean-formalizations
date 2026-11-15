/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbInv
import InteractingSLE.Spec.Supplement.SB2NeRoot

/-!
# The three branches of (P1)'s step that CANON consumes (D86)

Packet PROVE-SB2-CANON, round 9. The step `StageInv ℓ → StageInv (ℓ + 2)` (`Cz.SB2LowerStageStepStatement`) glues four
pieces at `ℓ + 2` (`SB2CcStep`): base and tail (CANON's `base_branch`, `tail_branch`, proved), zero and root. This file
states the consumed forms:

* **`SB2LowerZeroBranchStatement`** (SB2LIFT's, D86): F3LAW's `Fs.zero_piece` extended to `relOff = ℓ` away from a zero
  root, from the invariant's data at `ℓ` (`Fs.StageLawOn` on CONDFIN's family, the event containing `stageEvent ℓ`, the
  root facts at `R`);
* **`SB2LowerBaseSelectorStatement`** (SB2LIFT's, D86): the widened base event is a selector;
* **`SB2LowerRootBranchStatement`**: the root piece with a selector containing every launch at `relOff = ℓ` that is not
  a zero root and has positive lifetime. **`rootBranch_of_rootEv`**: it follows from the root-event form
  **`SB2LowerRootEvBranchStatement`** (what CONDFIN's `Cd.root_piece` gives with D85's entrance law, selector a.s. equal
  to `Ne.rootEv ℓ`) and the walk fact **`SB2LowerRootPosStatement`** (`entrR < ζ_ℓ` there; ROOTX's
  `Ro.ae_rootEv_of_posRootAt` covers all but the pure piece entries of zero relative lifetime).

R48: the statements use no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Lv Lk Mf Ms

/-- **Named statement (SB2LIFT's, D86): the zero branch of the step**, F3LAW's `Fs.zero_piece` extended to
`relOff = ℓ` away from a zero root (a mark entry with zero lifetime at `ℓ`; the left heights at `ℓ + 2` anchored at
`R` by the invariant's root facts). From the invariant's data at `ℓ` on CONDFIN's line family, for every family of
stage `ℓ + 2`: the stage data at `ℓ + 2`, with the word of stage `ℓ`, on the launches at `ℓ` of lifetime `0` that
are not a zero root at `ℓ`. -/
def SB2LowerZeroBranchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k →
    ∀ ℓ : ℕ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t)) →
    ∀ (C : Set Ω) (β : Ω → BoundaryWord) (S : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ C) →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
          Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) →
    ∀ (𝓖' : Filtration ℝ≥0 mΩ) (A₁' A₂B' A₂' : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖' t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k (ℓ + 2) t u₀ (A₁' t) (A₂B' t) (A₂' t)) →
    Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁'
      (C ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∧
        ¬ (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
          Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))}) β S

/-- **Named statement (SB2LIFT's, D86): the base piece's event is a selector.** At a flow stage `ℓ'`, for every line
family of stage `ℓ'` (its time-`0` σ-algebra), an event of `lineFiltC P 𝓖' 0` and of the completed retained past,
almost surely equal to the widened base event `{upper launch, ℓ' ≤ relOff ∨ (relOff + 2 = ℓ' ∧ zero root)}`. -/
def SB2LowerBaseSelectorStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k →
    ∀ ℓ' : ℕ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ']? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∀ 𝓖' : Filtration ℝ≥0 mΩ,
      (𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ' (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ' + 1)) →
    ∃ Qs : Set Ω, MeasurableSet[lineFiltC P 𝓖' 0] Qs ∧
      MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ') P] Qs ∧
      ∀ᵐ ω ∂P, ω ∈ Qs ↔ (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
        (ℓ' ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∨
          relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2 = ℓ' ∧
            Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)))

/-- **Named statement (the root branch of the step; CONDFIN's root piece, D85 for the piece entry).** From the
invariant's data at `ℓ` on CONDFIN's line family, for every family of stage `ℓ + 2`: stage data at `ℓ + 2` on an
event `DR` and a selector `Rs` inside it (a.s.) containing almost every launch at `ℓ` with `relOff = ℓ`, not a zero
root, of positive lifetime. -/
def SB2LowerRootBranchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k →
    ∀ ℓ : ℕ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t)) →
    ∀ (C : Set Ω) (β : Ω → BoundaryWord) (S : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ C) →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
          Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) →
    ∀ (𝓖' : Filtration ℝ≥0 mΩ) (A₁' A₂B' A₂' : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖' t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k (ℓ + 2) t u₀ (A₁' t) (A₂B' t) (A₂' t)) →
    ∃ (Rs DR : Set Ω) (βR : Ω → BoundaryWord) (SR : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁' DR βR SR ∧
      MeasurableSet[lineFiltC P 𝓖' 0] Rs ∧ MeasurableSet[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] Rs ∧
      (∀ᵐ ω ∂P, ω ∈ Rs → ω ∈ DR) ∧
      ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ →
        ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ω ∈ Rs

/-- **The root branch in root-event form** (what CONDFIN's root piece gives under D85): the selector is almost
surely NOJUMP's root event `Ne.rootEv ℓ`, which lies in `DR` almost surely. -/
def SB2LowerRootEvBranchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k →
    ∀ ℓ : ℕ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t)) →
    ∀ (C : Set Ω) (β : Ω → BoundaryWord) (S : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ C) →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
          Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) →
    ∀ (𝓖' : Filtration ℝ≥0 mΩ) (A₁' A₂B' A₂' : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖' t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k (ℓ + 2) t u₀ (A₁' t) (A₂B' t) (A₂' t)) →
    ∃ (Rs DR : Set Ω) (βR : Ω → BoundaryWord) (SR : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁' DR βR SR ∧
      MeasurableSet[lineFiltC P 𝓖' 0] Rs ∧ MeasurableSet[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] Rs ∧
      (∀ᵐ ω ∂P, ω ∈ Rs ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ) ∧
      ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → ω ∈ DR

/-- **Named statement (a walk fact): at `relOff = ℓ`, a launch that is not a zero root and has positive lifetime
lies in the root event**, i.e. `entrR < ζ_ℓ`. ROOTX's `Ro.ae_rootEv_of_posRootAt` proves it at a mark entry
(`entrR = 0`) and at a pure piece entry of positive RELATIVE lifetime (`entrR = shiftD 0 < ζ_ℓ`); open: a pure piece
entry whose piece first reaches `R` at its death time. -/
def SB2LowerRootPosStatement : Prop :=
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
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k →
    ∀ ℓ : ℕ, ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ →
      ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ω ∈ Ne.rootEv κ b jumps E u l k ℓ

/-- **The root branch from the root-event form and the walk fact.** -/
theorem rootBranch_of_rootEv (hR : SB2LowerRootEvBranchStatement.{u}) (hpos : SB2LowerRootPosStatement.{u}) :
    SB2LowerRootBranchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀
    𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  obtain ⟨Rs, DR, βR, SR, hst', h1, h2, hiff, hsub⟩ := hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu
    hlp hlθ hLw hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀ 𝓖 A₁ A₂B A₂ h𝓖 hfam C β S hst hC hRF 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  refine ⟨Rs, DR, βR, SR, hst', h1, h2, ?_, ?_⟩
  · filter_upwards [hiff, hsub] with ω e1 e2 hω using e2 (e1.1 hω)
  · filter_upwards [hiff, hpos κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ]
      with ω e1 e2 hS ho hz hζ using e1.2 (e2 hS ho hz hζ)

end InteractingSLE.Theorem14.SB.Cz
