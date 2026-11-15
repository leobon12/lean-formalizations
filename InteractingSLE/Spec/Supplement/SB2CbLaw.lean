/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbK2
import InteractingSLE.Spec.Supplement.SB2FqHgt
import InteractingSLE.Spec.Supplement.SB2KcTypes
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaVersions

/-!
# (P1)'s per-stage clauses for measurable line families at upper launches (D80 item 2, D82 item 3)

Packet PROVE-SB2-CANON, round 8 (D80: the final (P1) assembly; D82 item 3: the law's cover at upper launches).

* **`StageLawClauses`**: the clauses of `Cz.SB2LowerStageLawInStatement` at one stage and line family (the law given
  `lineFiltC P 𝓖 0` on `A₁ 0`, the word's past measurability, countable word types of every shift, F3's mean identity
  and the heights clause), with the law's cover and the types clause asked only at the launches of B's stage `ℓ` AT AN
  UPPER LAUNCH: every piece of the induction, from the base law on, covers only those samples (F3LAW's handoff R6.2),
  and CANON's consumers use the law only there.
* **`SB2LowerStageLawInUStatement`**: `Cz.SB2LowerStageLawInStatement` for the line families whose retained set `A₁ 0`
  is `hittingSigma`-measurable with relatively closed complement in `ℍ`, with these clauses; implied by the landed
  form (**`lawInU_of_lawIn`**). F3's mean identity transfers between a.e. equal versions of `A₁ 0` only for measurable
  ones (`GW4Fix.ae_localSetMean_eq_of_ae_set_eq`); the family hcan uses (`Cx.exists_rootLineFamily`) is measurable.
  hcan and hTL from this form: `SB2CbPkgU`.
* **`mvLaw_congr_set`**: a retained law moves to an almost surely equal retained set.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
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
open Lu Mx Mz

/-- **A retained law moves to an almost surely equal retained set.** -/
theorem mvLaw_congr_set {κ : ℝ} {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {A A' K : Ω → Set ℂ} {G : Set Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ} (hlaw : Fl.MvLaw κ 𝓜 P h A K G Y β M)
    (hAA : ∀ᵐ ω ∂P, A ω = A' ω) : Fl.MvLaw κ 𝓜 P h A' K G Y β M := by
  obtain ⟨hKm, hKc, hKp, hG, hKA, hYm, hYt, hβm, hβs, hM0, hMb, hl⟩ := hlaw
  refine ⟨hKm, hKc, hKp, hG, ?_, hYm, hYt, hβm, hβs, hM0, hMb, hl⟩
  filter_upwards [hKA, hAA] with ω h1 h2 hω
  rw [h1 hω, h2]

/-- **The clauses of `Cz.SB2LowerStageLawInStatement` at one stage and line family**, with the law's cover and the
types clause at the launches of B's stage `ℓ` at an upper launch (D82 item 3). -/
def StageLawClauses (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ)
    (A₁ : ℝ≥0 → Ω → Set ℂ) : Prop :=
    ∃ (K' : Ω → Set ℂ) (G' : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (β : Ω → BoundaryWord) (M : ℝ)
      (types : Set WordType),
      Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) K' G' Y β M ∧
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β ∧
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G') ∧
      types.Countable ∧
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
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

/-- **Named statement (F3LAW's (P1) for measurable line families, covers at upper launches; D80, D82 item 3).**
`Cz.SB2LowerStageLawInStatement` for the line families whose retained set `A₁ 0` is `hittingSigma`-measurable with
relatively closed complement in `ℍ`, with the law's cover and the types clause asked only at the upper launches. -/
def SB2LowerStageLawInUStatement : Prop :=
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
      Measurable[mΩ, hittingSigma] (A₁ 0) → (∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω)) →
    StageLawClauses κ b jumps P h E u l k ℓ 𝓖 A₁

/-- **The landed form implies the measurable-family form with the covers at upper launches.** -/
theorem lawInU_of_lawIn (hP1 : SB2LowerStageLawInStatement.{u}) : SB2LowerStageLawInUStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow 𝓖 A₁ A₂ h𝓖 hA
    _ _
  obtain ⟨K', G', Y, β, M, types, hlaw, hβ, hcov, htypes, hcovT, hmean, hheight⟩ :=
    hP1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow 𝓖 A₁ A₂ h𝓖 hA
  exact ⟨K', G', Y, β, M, types, hlaw, hβ, hcov.mono fun ω h _ => h, htypes, hcovT.mono fun ω h _ => h, hmean,
    hheight⟩

end InteractingSLE.Theorem14.SB.Cz
