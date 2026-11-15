/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CzTail
import InteractingSLE.Spec.Supplement.SB2MzIface

/-!
# `Mz.SB2LowerStageCanonStatement` (hcan) from the per-stage package of the joint induction

Packet PROVE-SB2-CANON. **`sb2LowerStageCanonStatement_of_pkg`** proves the target
`Mz.SB2LowerStageCanonStatement` (Theorems 1.2–1.3 as hypotheses) from one named statement,
**`SB2LowerStagePkgStatement`**: in SB2(2)'s setting, at every B-stage `ℓ` whose instruction is a flow, the outputs of
the joint induction at `ℓ` in the form their producers give them:

* the retained law `Fl.MvLaw` at `ℓ` (base: `Qu`/`Fm` laws on `{ℓ ≤ relOff}`; step: F3LAW's `Fl.mvLaw_succ_succ`,
  `Fl.mvLaw_succ_succ_zero`, `Fl.mvLaw_piecewise`), given marks `𝓜` between the retained past `Ms.stageMarks ℓ` and
  `mΩ`, covering almost every launch of B's stage `ℓ`, on the retained set `fill (A ∪ B_{<ℓ})`, with a word measurable
  for the completed retained past (the step's own output);
* the offset `x₀` (F2b′'s), measurable for the completed retained past;
* a tail event `T` of `Ms.stageMarks (ℓ + 1)` covering almost every tail launch of positive lifetime;
* almost surely on `T` at a launch of positive lifetime, the chain facts `Qx.ChainFacts` of the canonical driver
  (K2's identification of B's piece with the canonical code of `(shiftW x₀ β, field in Mo.hullChart (fill K') x₀)`).

At a stage whose instruction is not a flow B never launches, and the tail objects are trivial.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx Mz LocalSets

/-- **Named statement (the per-stage package of SB2(2)'s joint induction; PROVE-SB2-CANON's remaining input).** In
SB2(2)'s setting (the binders of `Mz.SB2LowerStageCanonStatement`), at every B-stage `ℓ` whose instruction is a flow:
marks `𝓜` between the retained past and `mΩ`, the retained law `Fl.MvLaw` given `𝓜` covering almost every launch at
`ℓ` on the retained set `fill (A ∪ B_{<ℓ})` with a word measurable for the completed retained past, an offset `x₀`
measurable for the completed retained past, a tail event `T` of `Ms.stageMarks (ℓ + 1)` covering almost every tail
launch of positive lifetime, and, almost surely on `T` at a launch of positive lifetime, the chain facts of the
canonical driver of `(shiftW x₀ β, field in Mo.hullChart (fill K') x₀)`. -/
def SB2LowerStagePkgStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
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
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ,
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∃ (𝓜 : MeasurableSpace Ω) (A K' : Ω → Set ℂ) (G' : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens)
      (β : Ω → BoundaryWord) (M : ℝ) (x₀ : Ω → ℝ) (T : Set Ω),
      Ms.stageMarks κ b jumps E u l k ℓ ≤ 𝓜 ∧ 𝓜 ≤ mΩ ∧
      ∃ hlaw : @Fl.MvLaw κ Ω 𝓜 mΩ _ P _ h A K' G' Y β M,
        Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β ∧
        (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G') ∧
        (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → A ω = fillH (Nc.retX κ b jumps E u l k ℓ ω)) ∧
        Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] x₀ ∧
        MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] T ∧
        (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
            (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (lowerD b jumps E ω) + 2 ≤ ℓ →
          (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ T) ∧
        ∀ᵐ ω ∂P, ω ∈ T → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → (lowerD b jumps E ω ℓ).2 ≠ 0 →
          Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
            (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) x₀ hlaw.2.1 hlaw.2.2.1 ω

/-- At a stage whose instruction is not a flow, the tail objects are trivial (B never launches there). -/
theorem tailCanonAt_of_not_flow (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ)
    (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    (hnf : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? ≠ some (Sum.inl (-(Real.pi / 2), ⊤))) :
    TailCanonAt h12p hκ b jumps P h E u l k ℓ := by
  have hKc : ∀ ω : Ω, IsCompact ((fun _ => (∅ : Set ℂ)) ω) := fun _ => isCompact_empty
  have hKp : ∀ ω : Ω, IsPreconnected ((fun _ => (∅ : Set ℂ)) ω ∪ Restart.lowerHalf) := fun _ => by
    rw [empty_union]; exact isPreconnected_lowerHalf
  refine ⟨∅, fun _ => (0, fun _ => 0, fun _ => 0), fun _ => ∅, fun _ => 0, fun _ => Mz.zeroDrv, hKc, hKp,
    measurable_const, fun n j => ?_, measurable_const, Eventually.of_forall fun _ h => h.elim, ?_,
    measurable_const, fun _ => Mz.isRegularDriver_zeroDrv, Eventually.of_forall fun _ h => h.elim⟩
  · simp only [inter_empty, Set.not_nonempty_empty, ofPred_false, MeasurableSet.empty]
  · refine Eventually.of_forall fun ω _ hl _ _ => absurd (Qx.walk_instr_of_launch hl).1 hnf

/-- **hcan from the per-stage package** (Theorems 1.2–1.3 as hypotheses). -/
theorem sb2LowerStageCanonStatement_of_pkg (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hpkg : SB2LowerStagePkgStatement.{u} h12p) :
    SB2LowerStageCanonStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ
  by_cases hflow : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))
  · have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length := (List.getElem?_eq_some_iff.1 hflow).1
    obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    obtain ⟨𝓜, A, K', G', Y, β, M, x₀, T, h𝒮𝓜, h𝓜, hlaw, hβ, hcovL, hA, hx₀, hT, hTcov, hfacts⟩ :=
      hpkg κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow
    exact tailCanonAt_of_mvLaw (mΩ := mΩ) (𝓜 := 𝓜) h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hu₀
      h𝒮𝓜 h𝓜 hlaw hβ hcovL hA
      hx₀ hT hTcov hfacts
  · exact tailCanonAt_of_not_flow h12p hκ b jumps P h E u l k ℓ hflow

end InteractingSLE.Theorem14.SB.Cz
