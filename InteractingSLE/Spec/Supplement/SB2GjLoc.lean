/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CxRoot
import InteractingSLE.Spec.Supplement.SB2FlMarks
import InteractingSLE.Spec.Supplement.SB2QxPhys
import InteractingSLE.Spec.Supplement.SB2QrBase

/-!
# The root's retained set is history-avoidance local for the line σ-algebra at B-time `0`

Packet PROVE-GW2-GEOM2, round 17 (decision D79). F3's mean identity from the retained law (F3LAW's
`Fq.hmean_of_law` / `Fq.ae_meanIdentity_of_mvLaw`) asks the retained set `A₁ 0` to be history-avoidance local for the
law's marks `lineFiltC P 𝓖 0`. At B-time `0` the joint set of the root's line family (CONDFIN's `Cx.RootSetsAt`) is
`A₁ 0` itself: the piece of B's stage `ℓ` run for own time `0` adds no point of `ℍ` (F3LAW's
`Fl.stageSet_capSpec_zero_succ` at a launch, no piece at all otherwise). CONDFIN's `Cx.k2Inputs_of_rootSets` gives the
union `A₁ ∪ A₂J` history-avoidance local for `𝓖 t`, so:

* **`ae_stageSet_capZero_succ`**: almost surely the capped stage set through `ℓ + 1` at own time `0` is the one
  through `ℓ`;
* **`hloc_rootLine`**: `A₁ 0` is history-avoidance local for `lineFiltC P 𝓖 0`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Gj

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Ms

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The piece of B's stage `ℓ` run for own time `0` adds nothing**, almost surely. -/
theorem ae_stageSet_capZero_succ (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {ℓ : ℕ} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))) :
    ∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω =
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        ℓ ω := by
  obtain ⟨-, hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  filter_upwards [Qx.ae_walkChainFacts_regFam h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER] with ω hW
  by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
  · exact Fl.stageSet_capSpec_zero_succ hW hl (hreg' _ ℓ ω).2.1
  · rw [not_not] at hl
    rw [WalkLaw.stageSet_succ]
    have hpc : WalkLaw.pieceSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        ℓ ω = ∅ := by
      unfold WalkLaw.pieceSet
      rw [ite_eq_left]
      rw [launches_run_capSpec_succ hℓ.le hwℓ]
      exact hl
    rw [hpc, union_empty]

/-- **The root's retained set at B-time `0` is history-avoidance local for the completed line σ-algebra.** -/
theorem hloc_rootLine (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) :
    IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (centredField h u₀) P := by
  have hk := (Cx.k2Inputs_of_rootSets h𝓖 hfam).2.2.2 0
  have hcap := ae_stageSet_capZero_succ h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hA1f, -, -, -, -, -, hJf, -⟩ := hfam 0
  have heq : ∀ᵐ ω ∂P, A₁ 0 ω ∪ A₂J 0 ω = A₁ 0 ω := by
    filter_upwards [hA1f, hJf, hcap] with ω h1 h2 h3
    have hJ : fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
            ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω) ω =
        fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
            ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω :=
      Qr.fillVer_congr (by show _ ∪ _ = _ ∪ _; rw [h3])
    rw [h1.1, h2, hJ, union_self]
  exact Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma (P := P)
    (WalkLaw.isHistoryAvoidanceLocal_congr_ae heq hk)

end InteractingSLE.Theorem14.SB.Gj
