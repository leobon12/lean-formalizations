/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NbStmt
import InteractingSLE.Spec.Supplement.SB2CkEntr

/-!
# F2b′'s root variant, restated (D41 and CONDFIN's two corrections)

Packet PROVE-AUX61-NOJUMP (round 21). **`Nd.SB2LowerRootVersionStatement5`**: `Nb.SB2LowerRootVersionStatement4`
with three changes, and otherwise verbatim (the heights premise of D34 included):

* **D41.** The root case is `¬ ZeroRoot` (it was `¬ ArcEntry`). It now covers mark entries, where B's piece at
  `ℓ = relOff` starts at `R` (entrance time `0`).
* **CONDFIN R5.1.** B's entrance time at `R` uses the stopping convention `Ck.entrTime`: the first visit of `R`
  if the piece visits it, its lifetime otherwise (`entrR`).
  `Na.rootEntry` was `0` when the piece never visits `R`, which is not a stopping time even up to null sets. On a
  visit the two agree (`Ck.entrTime_eq_visitTime`), so the root event
  `entrR < ζ_ℓ` and every conclusion on it are unchanged.
* **CONDFIN R4.4.** The shifted line filtration is built from the COMPLETED capped pasts, as `lineFiltC` is:
  `s ∈ 𝓖 t ↔ s measurable ∧ ∀ r, s ∩ {entrR + t ≤ r} ∈ aeSigma (capPast r) P`. With the raw capped pasts no `𝓖` exists
  when the raw family differs from the regularized one on a null set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb

/-- **B's entrance time at `R = max (A ∩ ℝ)`** at stage `ℓ`, with the stopping convention (`Ck.entrTime`: the first
visit of `R` if the piece visits it, its lifetime otherwise). -/
def entrR (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (ω : Ω) : ℝ≥0∞ :=
  Ck.entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω))

/-- **Named statement (the root variant, restated: D41, CONDFIN R4.4/R5.1; PROVE-AUX61-NOJUMP's).**
`Nb.SB2LowerRootVersionStatement4` at the root case `¬ ZeroRoot`, with the entrance time `entrR` (stopping
convention) and the line filtration of the completed capped pasts stopped at `entrR + t`. -/
def SB2LowerRootVersionStatement5 : Prop :=
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
    ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ) (A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ (t : ℝ≥0) (s : Set Ω), MeasurableSet[𝓖 t] s ↔ MeasurableSet s ∧ ∀ r : ℝ≥0,
        MeasurableSet[aeSigma (Na.capPast κ b jumps E u l k ℓ r) P]
          (s ∩ {ω | entrR κ b jumps E u l k ℓ ω + (t : ℝ≥0∞) ≤ (r : ℝ≥0∞)})) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (fun ω => WalkLaw.stageSet κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
              (entrR κ b jumps E u l k ℓ ω + (t : ℝ≥0∞)))
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) ω) →
    ∀ (β₁ : Ω → BoundaryWord) (types : Set WordType),
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁ → (∀ ω, (β₁ ω).IsSorted) → types.Countable →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
      (∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
              (H \ A₁ 0 ω)) →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ →
        ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        entrR κ b jumps E u l k ℓ ω <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        HeightClause κ b jumps (A₁ 0 ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
        ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
        entrR κ b jumps E u l k ℓ ω <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) ∧
      ((∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) →
        ∃ S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
          (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
          (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife,
          (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
            (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
            ∃ m, (S.ver m).a t ω < S.V m ω) ∧
          (∀ m, ∀ w ∈ types, ∀ᵐ ω ∂P,
            ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver m).W
              (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
              (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω) ∧
          (∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
            ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w → relLife ω < ⊤ →
              (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
              FCDet.thr (typedRhoL w) (typedRhoR w) Wc
                (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
                (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω))

end InteractingSLE.Theorem14.SB.Nd
