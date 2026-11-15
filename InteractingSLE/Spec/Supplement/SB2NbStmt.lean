/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NaStmt

/-!
# F2b′'s successor with the retained word's heights (D34), at the lower walk's angle

Packet PROVE-AUX61-NOJUMP (round 21). The targets of the round:

* **`Nb.SB2LowerStageVersionStatement4`**: `Na.SB2LowerStageVersionStatement3` with two changes:
  * **D34 (H1).** A premise, the retained word's second clause in F3's chart `Mo.hullChart (A₁ 0) 0`
    (`HeightClause`, owner REVIEW-FABLE-T14). Through every continuous extension `g` of the chart's inverse to `ℍ̄`
    there is the entry `e` of B's seed (`g e = seed`) such that:
    * (a) right of `e` the boundary map is real and strictly increasing, and the word's heights there are the
      original heights `b (g y)` off finite sets;
    * (b) every height left of `e` has left weight `> −2` for the lower flow (angle `−π/2`).
  * **The angle is the lower walk's, `ψ = −π/2`.** Statement3 quantified over every `ψ`; for `ψ ≪ 0` it is false.
    Its versions are positive (`ann`) and at most the threshold of their cell (`V_le_thr`). But on the cell of a type
    whose seed is at its threshold for that `ψ`, the threshold is `0` (`Lv.thr_eq_zero_of_seed`). Already the right
    seed weight `cumWeightRight κ (h + ψχ)` of the bounded height `h` right of `0` is `≤ −2` once
    `ψ ≤ −(λ + h)/χ`. Every consumer instantiates `ψ = −π/2` (`Om.hmean_of_stageS2`), and (b) is stated at that
    angle.
* **`Nb.SB2LowerRootVersionStatement4`**: the root variant `Na.SB2LowerRootVersionStatement3` with the same two
  changes; the seed of the relative piece is `R = max (A ∩ ℝ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nb

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms

section Defs

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}

/-- **B's seed at stage `ℓ`**: the start point of B's piece `ℓ` (`Lk.pcPt` at time `0`). -/
def bSeed (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ) (ω : Ω) : ℂ :=
  pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) 0

/-- **The retained word's second clause at one sample** (D34, (H1)): through every continuous extension `g` of the
inverse of the retained hull's chart (offset `0`) to `ℍ̄`, the seed `p` of the relative piece has an entry `e`
(`g e = p`); right of `e` the boundary map is real and strictly increasing and the word `β` has the original heights
`b (g y)` off a finite set; left of `e` every height of `β` has left weight `> −2` for the lower flow. -/
def HeightClause (A : Set ℂ) (p : ℂ) (β : BoundaryWord) : Prop :=
  ∀ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} → EqOn g (Mo.hullChart A 0).2.1 H →
    ∃ e : ℝ, g (e : ℂ) = p ∧ (∀ y : ℝ, e < y → (g (y : ℂ)).im = 0) ∧
      StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici e) ∧
      (∃ Fy : Finset ℝ, ∀ y : ℝ, e < y → y ∉ Fy → (g (y : ℂ)).re ∉ jumps → β.fn y = b (g (y : ℂ)).re) ∧
      ∀ y : ℝ, y < e → y ∉ β.jumps → -2 < Sec4.cumWeightLeft κ (β.fn y + -(Real.pi / 2) * chiC κ)

end Defs

/-- **Named statement (F2b′'s successor with the retained word's heights; PROVE-AUX61-NOJUMP's, D28, D31, D34).**
`Na.SB2LowerStageVersionStatement3` at the lower walk's angle `−π/2`, with the premise `HeightClause` for F3's word on
the live event. -/
def SB2LowerStageVersionStatement4 : Prop :=
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
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            (ℓ + 1)) ω) →
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
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        HeightClause κ b jumps (A₁ 0 ω) (bSeed κ b jumps E ℓ ω) (β₁ ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) ∧
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
                (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω) ∧
          (∀ m, ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
            ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
            Om.IsStageS2 (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω)
              (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
              (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω) (fun s : ℝ => (S.ver m).W s.toNNReal ω)
              ((S.ver m).a t ω).toNNReal))

/-- **Named statement (the root variant with the retained word's heights; PROVE-AUX61-NOJUMP's, D31, D34).**
`Na.SB2LowerRootVersionStatement3` at the angle `−π/2`, with the premise `HeightClause` at `R` on the live event. -/
def SB2LowerRootVersionStatement4 : Prop :=
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
      (∀ (t : ℝ≥0) (s : Set Ω), MeasurableSet[𝓖 t] s ↔ ∀ r : ℝ≥0,
        MeasurableSet[Na.capPast κ b jumps E u l k ℓ r] (s ∩ {ω | ((Na.rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) +
          (t : ℝ≥0∞) ≤ (r : ℝ≥0∞)})) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (fun ω => WalkLaw.stageSet κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
              (((Na.rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) + (t : ℝ≥0∞)))
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
        ¬ Lk.ArcEntry κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        ((Na.rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        HeightClause κ b jumps (A₁ 0 ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
        ¬ Lk.ArcEntry κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
        ((Na.rootEntry κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) <
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

end InteractingSLE.Theorem14.SB.Nb
