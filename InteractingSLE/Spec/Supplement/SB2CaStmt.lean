/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfStmt9F
import InteractingSLE.Spec.Supplement.SB2FlTail

/-!
# The entrance law at the root (D85): the named statement for F3LAW

Packet PROVE-SB2-CONDFIN, round 16 (decision D85, CONDFIN's handoff R15.2 option (A)). On the PIECE entry of the root
(`R` first added by stage `ℓ`'s own piece, after its head inside `fill (A₁ 0)`) the root event is not an event of the
time-`0` line marks `lineFiltC P 𝓖 0`, so F3LAW's step, which reads the kernel law at the offset under those marks,
cannot run on it. The step runs instead under the **entrance marks** `entrMarks P 𝓖 F' = lineFiltC P 𝓖 0 ⊔ σ(F')`,
`F'` an event almost surely equal to the root event (CONDFIN's `Ca.exists_rootEvent`, (A1)). What it needs there:

* **`SB2LowerRootEntranceLawStatement`** ((A2), **for F3LAW**, D85): the retained law at stage `ℓ` survives adding the
  root event to the marks — for every retained law `Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ M` of the line
  family of a flow stage `ℓ` and every measurable `F'` almost surely equal to `Ne.rootEv … ℓ` and inside `Gℓ`, the
  kernel law of `Yℓ` given `entrMarks P 𝓖 F'` is, almost surely on `F'`, the GFF with data `β₁`. Mathematically: given
  the time-`0` marks, the root event is decided by B's head inside `fill (A₁ 0)` (clock `0` until `entrR`), which is
  independent of the field outside `fill (A₁ 0)` (domain Markov property of the local set at `fill (A₁ 0)`, flow lines
  determined by the field, Theorem 1.2).

The setting is NOJUMP's 9F (`Nf.SB2LowerRootVersionStatement9F`) through the line family of stage `ℓ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ca

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nd

/-- **The entrance marks at the root**: the completed time-`0` line marks of the stage and the event `F'`. -/
abbrev entrMarks {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (F' : Set Ω) :
    MeasurableSpace Ω :=
  lineFiltC P 𝓖 0 ⊔ MeasurableSpace.generateFrom {F'}

/-- **Named statement (the entrance law at the root, (A2); for F3LAW, D85).** See the module docstring. -/
def SB2LowerRootEntranceLawStatement : Prop :=
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
    ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ),
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω) →
    ∀ (Kℓ : Ω → Set ℂ) (Gℓ : Set Ω) (Yℓ : Ω → DistOn upperHalfPlaneOpens) (β₁ : Ω → BoundaryWord) (M : ℝ),
      Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ M →
    ∀ F' : Set Ω, MeasurableSet F' → (∀ᵐ ω ∂P, ω ∈ F' ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ) →
      (∀ᵐ ω ∂P, ω ∈ F' → ω ∈ Gℓ) →
      ∀ᵐ ω₀ ∂P, ω₀ ∈ F' →
        IsGFFWithBoundaryData (condExpKernel P (entrMarks P 𝓖 F') ω₀) Yℓ (β₁ ω₀).fn (β₁ ω₀).jumps

end InteractingSLE.Theorem14.SB.Ca
