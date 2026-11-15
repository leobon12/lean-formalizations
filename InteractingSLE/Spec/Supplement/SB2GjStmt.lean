/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeRoot9E
import InteractingSLE.Spec.Supplement.SB2CtStmt
import InteractingSLE.Spec.Supplement.SB2FpBase
import InteractingSLE.Spec.Supplement.SB2KcTypes

/-!
# The base law with the root facts, the root identification against it, and the positive-root visit (D79)

Packet PROVE-GW2-GEOM2, round 17 (decision D79, GEOM2's option (A) of its round-16 R16.1). The root statement with
F3's mean premise only where `ℓ ≤ relOff` is NOJUMP's `Nf.SB2LowerRootVersionStatement9F` (stated and PROVED by NOJUMP,
`Nf.sb2LowerRootVersionStatement9F`); the identification below is proved against it.
* **`BaseLawForX`** (for CONDFIN): CONDFIN's `Ct.BaseLawFor` with F3LAW's root facts on the law's event (the last
  conjunct of `Fp.SB2LowerBaseWordStatement`) and a countable cover of the word's profiles on the upper launches (the
  root's word types must lie in a countable set for the root versions and K2; a profile cover gives one after any
  recentring, `Lv.angleWordType_shift_mem`). `baseLawFor_of_baseLawForX`.
* **`SB2LowerRootIdentStatementX`**: `Ct.SB2LowerRootIdentStatement` with `BaseLawForX` in place of `BaseLawFor`.
* **`SB2PosRootVisitStatement`** (for ROOTX, D79 item 3): at a positive relative root at `ℓ`, B's piece `ℓ` visits
  `R` (at a mark entry it starts there).

R48: no source theorem is assumed; these are named statements for Theorem 1.4's SB2(2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Gj

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nd

section Defs

variable {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
  (k : ℕ)

/-- **The base law at B's stage `ℓ` with the root facts and a countable profile cover** (`Ct.BaseLawFor` plus the
last conjunct of `Fp.SB2LowerBaseWordStatement` and a countable cover of the word's profiles on the upper launches). -/
def BaseLawForX (ℓ : ℕ) (β₁ : Ω → BoundaryWord) : Prop :=
  Measurable[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k] β₁ ∧
  (∃ S : Set WordProfile, S.Countable ∧
    ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → wordProfile (β₁ ω) ∈ S) ∧
  ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ),
    (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω) →
    ∃ (K : Ω → Set ℂ) (G : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
      Fl.MvLaw κ (Ms.lineFiltC P 𝓖 0) P h (A₁ 0) K G Y β₁ M ∧
      (∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G) ∧
      (∀ᵐ ω ∂P, ω ∈ G → IsHPHull (A₁ 0 ω) ∧ Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
        Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))))

/-- `BaseLawForX` gives CONDFIN's `Ct.BaseLawFor`. -/
theorem baseLawFor_of_baseLawForX {ℓ : ℕ} {β₁ : Ω → BoundaryWord}
    (hX : BaseLawForX (κ := κ) b jumps P h E u l k ℓ β₁) : Ct.BaseLawFor (κ := κ) b jumps P h E u l k ℓ β₁ := by
  refine ⟨hX.1, fun 𝓖 A₁ h𝓖 hA₁ => ?_⟩
  obtain ⟨K, G, Y, M, h1, h2, -⟩ := hX.2.2 𝓖 A₁ h𝓖 hA₁
  exact ⟨K, G, Y, M, h1, h2⟩

end Defs

/-- **Named statement (the root identification against `BaseLawForX`; GEOM2's target, D79).**
`Ct.SB2LowerRootIdentStatement` with `BaseLawForX` in place of `Ct.BaseLawFor`. -/
def SB2LowerRootIdentStatementX (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
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
      0 < k → ∀ (ℓ : ℕ) (β₁ : Ω → BoundaryWord), BaseLawForX (κ := κ) b jumps P h E u l k ℓ β₁ →
        ∃ (G : Set Ω) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
          (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)),
          Ct.RootCover (κ := κ) b jumps P E u l k ℓ G ∧
          Mz.CanonIdentOn h12p hκ b jumps P h E u l k ℓ G (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) K x₀ Dr
            hKc hKp

/-- **Named statement (for ROOTX, D79 item 3): a positive relative root visits `R`.** In SB2(2)'s setting, almost
surely at an upper launch, at a positive relative root at B's stage `ℓ` (`Ct.PosRootAt`), B's piece `ℓ` visits
`R = max (A ∩ ℝ)` before its lifetime (at a pure piece entry `R` is new at `ℓ` and lies on the piece; at a mark entry
the piece starts at `R`, `Lk.markStart_concrete`). -/
def SB2PosRootVisitStatement : Prop :=
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
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ ℓ : ℕ, ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω →
        ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (Mz.lowerD b jumps E ω ℓ).2 ∧
          pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (Mz.lowerD b jumps E ω) ℓ)
            (Mz.lowerD b jumps E ω ℓ) t = ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ)

end InteractingSLE.Theorem14.SB.Gj
