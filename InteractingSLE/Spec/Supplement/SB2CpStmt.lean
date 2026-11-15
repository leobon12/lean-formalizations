/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CuStmt
import InteractingSLE.Spec.Supplement.SB2FlTail
import InteractingSLE.Spec.Supplement.SB2CjK2
import InteractingSLE.Spec.Supplement.SB2CxFam

/-!
# The two remaining stage inputs of hcan, in the forms CANON's wiring consumes (D77 item 2)

Packet PROVE-SB2-CANON, round 6 (D77 item 2: wire hcan and the top's hTL modulo F3LAW's (P1) law, CONDFIN's K2 at
the tails, GEOM2's `Ct.SB2LowerRootIdentStatement` and NOJUMP's root statement). F3LAW (D76) and CONDFIN (D77 item 1)
had not stated their two results when this round started, so the wiring is written against these consumer forms (the
second one is CONDFIN's in-flight `Ce.ae_k2_tail` verbatim); an owner who states a different form adds a one-step
bridge to the form below.

* **`SB2LowerStageLawInStatement`** (F3LAW's (P1), D76): at every flow stage `ℓ` and for every line family of the
  stage (`𝓖 t` = upper past ⊔ B's past capped at `t` through `ℓ + 1`; `A₁`, `A₂` the filled retained and joint sets, as
  in `Cz.SB2LowerStageVersionStatement6`'s premise), the retained law `Fl.MvLaw` given `lineFiltC P 𝓖 0` on the
  retained set `A₁ 0` (the form of CONDFIN's `Ct.BaseLawFor` and of F3LAW's step output), its word `β` measurable for
  the completed retained past, its event covering B's launches at `ℓ`, a countable set of word types containing the
  types of every shift of `β` on B's launches, and Statement6's two premises for `β` (F3's mean identity of `A₁ 0` and
  the heights clause).
* **`SB2LowerTailK2Statement`** (CONDFIN's K2 at the tails, D77 item 1): exactly the hypotheses and conclusion of
  CONDFIN's in-flight `Ce.ae_k2_tail` (`SB2CeTail`, untracked when this was written): `Cj.ae_k2_stage`'s conclusion for
  the objects `Cz.SB2LowerStageVersionStatement6` produces over the line family `Cx.exists_rootLineFamily` (its
  `Cx.RootSetsAt` facts, the joint set `A₂J`), from the word's premises (F3's mean identity, sorted, bounded) and its
  conditional law under `lineFiltC P 𝓖 0` on the live event. When `Ce.ae_k2_tail` lands it proves this statement by
  one application.

R48: no source theorem is assumed; these are named statements (owners F3LAW and CONDFIN).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nd
open _root_.InteractingSLE.Theorem14.SB.Ne
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **Named statement (F3LAW's (P1), D76; the form CANON's wiring consumes).** See the module docstring. -/
def SB2LowerStageLawInStatement : Prop :=
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
      0 < k → ∀ ℓ : ℕ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ) (A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            (ℓ + 1) ω) ω) →
    ∃ (K' : Ω → Set ℂ) (G' : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (β : Ω → BoundaryWord) (M : ℝ)
      (types : Set WordType),
      Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) K' G' Y β M ∧
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G') ∧
      types.Countable ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        ∀ x : ℝ, angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x (β ω)) ∈ types) ∧
      (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
        (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
          ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
            ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
              EqOn (fun z => w₁ z + u₀ z)
                (fun z => (β ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
                (H \ A₁ 0 ω))) ∧
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        HeightClause κ b jumps (A₁ 0 ω) (bSeed κ b jumps E ℓ ω) (β ω))

/-- **Named statement (CONDFIN's K2 at the tails, D77 item 1; the form CANON's wiring consumes).** Exactly the
hypotheses and conclusion of CONDFIN's in-flight `Ce.ae_k2_tail` (`SB2CeTail`): K2 at a tail stage for the objects of
`Cz.SB2LowerStageVersionStatement6` over the line family `Cx.exists_rootLineFamily` (joint set `A₂J`). -/
def SB2LowerTailK2Statement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
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
    ∀ ℓ : ℕ, ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) →
    ∀ (F : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (β₁ : Ω → BoundaryWord) (types : Set WordType)
      (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞)
      (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
        (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K →
    ∀ (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
      (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) →
      Measurable[lineFiltC P 𝓖 0] x₀ → MeasurableSet[lineFiltC P 𝓖 0] F →
      (∀ ω, pc ω = Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω)) →
      (∀ ω, tL ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
        (realMax (Nc.retX κ b jumps E u l k ℓ ω))
        ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω))) →
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) →
      Measurable[lineFiltC P 𝓖 0] (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) →
      (∀ ω, (β₁ ω).IsSorted) →
      (∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
        (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
        (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps) →
      (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
              (H \ A₁ 0 ω)) →
      types.Countable →
      (∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) →
    ∀ M : ℝ, 0 ≤ M → (∀ ω, ∀ y ∉ (β₁ ω).jumps, |(β₁ ω).fn y| ≤ M) →
      (∀ w ∈ types, ∀ᵐ ω ∂P,
        ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
        S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W
          (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
          (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω) →
      (∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
        ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
          relLife ω < ⊤ → (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
          FCDet.thr (typedRhoL w) (typedRhoR w) Wc
            (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
            (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω) →
      ∀ᵐ ω ∂P, ω ∈ F →
        (∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
          Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
          (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
        (driverCode h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
          Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω


end InteractingSLE.Theorem14.SB.Cz
