/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdStmt5

/-!
# F2b′'s root variant in B's own time (D44)

Packet PROVE-AUX61-NOJUMP (round 22). D44 supersedes the τE-shifted root form (`Na.…3`, `Nb.…4`, `Nd.…5`). The root
stage is indexed by B's OWN time, as the tails are:

* **the line family** is the tail family: `𝓖 t` is the upper past joined with B's past capped at its time `t`;
* **the line sets** are the tail sets, with the second one the filled JOINT set (`A₂ t = fill (A ∪ B_{≤ℓ}` capped at
  `t)`; NOJUMP's round-21 finding on the `hull` field, `SB2NdStmt5`);
* **the live event** is `stageEvent ∩ {ℓ ≤ relOff} ∩ {0 < ζ_ℓ}`;
* **the relative piece** starts at B's entrance at `R = max (A ∩ ℝ)`. The relative clock stays `0` before it (the
  piece's head lies in the retained fill), and the trace field reads from the tail start `tL`;
* **the root event** is `rootEv = stageEvent ∩ {relOff = ℓ} ∩ {¬ ZeroRoot} ∩ {entrance before ζ_ℓ}`, with the entrance
  time `Nd.entrR` (first visit of `R`, else the lifetime). The heights premise (D34) is taken there, at the seed `R`;
* **the clauses that fail without a relative piece** hold only on the root event (`StageVersionSR`, the structure
  `Na.StageVersionS` with `ann` and `V_lt` on the root event):
  * `ann`, `V_lt`;
  * the cover clause (i): with no relative piece the clock is `0`, and `V_sup` with `relLife = 0` forces the stops to
    `0`;
  * the (I4) bound (iii).

  The rest of `Nd.SB2LowerStageVersionStatement5`'s conclusion is verbatim.

* `StageVersionSR`, `rootEv`, **`SB2LowerRootVersionStatement6`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ne

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nd

section Version

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **F2b′'s relative versions at the root** (`Na.StageVersionS` with the announcement `ann` and the bound `V_lt` only
on the root event `Fr`). -/
structure StageVersionSR (κ ψ : ℝ) (P : Measure Ω) (F Fr : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ)
    (A₂ : ℝ≥0 → Ω → Set ℂ) (Φ : Ω → Chart) (β₁ : Ω → BoundaryWord) (types : Set WordType)
    (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (L : Ω → ℝ≥0∞) (relLife : Ω → ℝ≥0∞) where
  ver : ℕ → Na.StageVersionG κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L
  V : ℕ → Ω → ℝ≥0∞
  record : Ω → RecData
  record_meas : Measurable[lineFiltC P 𝓖 0] record
  ρ : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρs : ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρ_meas : ∀ m, Measurable (ρ m)
  ρ_rule : ∀ m, Supp8.GB6.HullId.IsPathRule (ρ m)
  ρs_meas : ∀ m n, Measurable (ρs m n)
  ρs_rule : ∀ m n, Supp8.GB6.HullId.IsPathRule (ρs m n)
  ρs_fin : ∀ m n x, ρs m n x ≠ ⊤
  ρs_mono : ∀ m x, Monotone fun n => ρs m n x
  Λ_eq : ∀ m w, (ver m).Λ w = V m
  V_eq : ∀ m ω, V m ω = ρ m (record ω, fun s => (ver m).W s ω)
  ann : ∀ m, ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Fr → (∀ n, ρs m n (record ω, fun s => (ver m).W s ω) < V m ω) ∧
    ⨆ n, ρs m n (record ω, fun s => (ver m).W s ω) = V m ω
  V_lt : ∀ m, ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Fr → V m ω < relLife ω
  V_mono : ∀ ω, Monotone fun m => V m ω
  V_sup : ∀ᵐ ω ∂P, ω ∈ F → ⨆ m, V m ω = relLife ω
  W_eq : ∀ m m', m ≤ m' → ∀ᵐ ω ∂P, ω ∈ F → ∀ t : ℝ≥0, (t : ℝ≥0∞) < V m ω →
    (ver m).W t ω = (ver m').W t ω

end Version

/-- **The root event** of B's stage `ℓ`: B launches at `ℓ = relOff` off a zero root and enters `R = max (A ∩ ℝ)`
before its lifetime. -/
def rootEv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : Set Ω :=
  {ω | ω ∈ stageEvent κ b jumps E u l k ℓ ∧
    relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
    ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
    entrR κ b jumps E u l k ℓ ω < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2}

/-- **Named statement (F2b′'s root variant in B's own time; PROVE-AUX61-NOJUMP's, D41, D44).**
`Nd.SB2LowerStageVersionStatement5` at a stage `ℓ ≤ relOff`. The heights premise holds on the root event at `R`. The
versions are `StageVersionSR` over the root event, and the cover clause and the (I4) bound are stated on the root
event. -/
def SB2LowerRootVersionStatement6 : Prop :=
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
        A₂ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            (ℓ + 1) ω) ω) →
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
      (∀ᵐ ω ∂P, ω ∈ rootEv κ b jumps E u l k ℓ →
        HeightClause κ b jumps (A₁ 0 ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω)) →
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0) (relLife : Ω → ℝ≥0∞) (F : Set Ω),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ ω, IsCompact (K ω)) ∧
      (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) ∧
      ((∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) →
        ∃ S : StageVersionSR κ (-(Real.pi / 2)) P F (rootEv κ b jumps E u l k ℓ) 𝓖 A₁ A₂
          (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
          (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
          (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife,
          (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → ω ∈ rootEv κ b jumps E u l k ℓ →
            (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
            ∃ m, (S.ver m).a t ω < S.V m ω) ∧
          (∀ m, ∀ w ∈ types, ∀ᵐ ω ∂P,
            ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
            S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver m).W
              (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
              (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω) ∧
          (∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
            ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
              ω ∈ rootEv κ b jumps E u l k ℓ → relLife ω < ⊤ →
              (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
              FCDet.thr (typedRhoL w) (typedRhoR w) Wc
                (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
                (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω))

end InteractingSLE.Theorem14.SB.Ne
