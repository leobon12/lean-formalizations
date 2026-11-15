/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FqMean
import InteractingSLE.Spec.Supplement.SB2FmSeed

/-!
# The successor statements' premises from the retained law (target 3's assembly)

Worker PROVE-SB2-F3LAW (round 5, D76). F2b′'s successor statements (SB2LIFT's `Cz.…Statement6E` at the tails,
NOJUMP's `Ne.…Statement9E` at the root) take, for the induction's word `β₁` at B's stage `ℓ`, two premises on the
retained set `A₁` (= the line family's `A₁ 0`):

* **`hmean_of_law`** — F3's mean identity on `stageEvent ℓ`, from the retained law `Fl.MvLaw` on an event covering
  `stageEvent ℓ` (`Fq.ae_meanIdentity_of_mvLaw`);
* **`hheight_of_law`** — D34's `Nb.HeightClause` at B's seed on the tail live event, from the same law and the left
  heights `hL` (`Fm.ae_heightClause_of_leftAdm`). At the root the clause is `Fp.ae_heightClause_root`.

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

namespace InteractingSLE.Theorem14.SB.Fq

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField

/-- **F3's mean identity on B's stage event** (the `hmean` premise of `Cz.…Statement6E` / `Ne.…Statement9E`), from the
retained law on an event covering the stage event. -/
theorem hmean_of_law {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {𝓗 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (h𝓗 : 𝓗 ≤ mΩ)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hloc : IsHistoryAvoidanceLocal 𝓗 A (centredField h u₀) P)
    {K : Ω → Set ℂ} {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ 𝓗 P h A K G Y β M) {S : Set Ω} (hSG : ∀ᵐ ω ∂P, ω ∈ S → ω ∈ G) :
    ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ S → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z)
          (fun z => (β ω).mean ((Mo.hullChart (A ω) 0).1 z) - chiC κ * (Mo.hullChart (A ω) 0).2.2 z)
          (H \ A ω) := by
  intro g₁ hg₁
  filter_upwards [ae_meanIdentity_of_mvLaw hh hu₀ h𝓗 hAm hAc hloc hlaw g₁ hg₁, hSG] with ω h1 h2 hωS
  exact h1 (h2 hωS)

open LQGMetric (DistOn TestOn) in
/-- **D34's clause on the tail live event** (the `hheight` premise of `Cz.…Statement6E`), from the retained law on an
event covering B's stage event and the left heights `hL` of its word. -/
theorem hheight_of_law (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁ : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (h𝓗 : 𝓗 ≤ mΩ)
    (hAm : Measurable[mΩ, hittingSigma] A₁) (hAc : ∀ ω, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hloc : IsHistoryAvoidanceLocal 𝓗 A₁ (centredField h u₀) P)
    {K : Ω → Set ℂ} {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ 𝓗 P h A₁ K G Y β₁ M)
    (hSG : ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ → ω ∈ G)
    (hL : ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))) :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Nb.HeightClause κ b jumps (A₁ ω) (Nb.bSeed κ b jumps E ℓ ω) (β₁ ω) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : IsLocalSet A₁ (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hloc.isAvoidanceLocal
  exact Fm.ae_heightClause_of_leftAdm h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA hu₀ hAm hl
    hlaw.2.2.2.2.2.2.2.2.1 (hmean_of_law hh hu₀ h𝓗 hAm hAc hloc hlaw hSG) hL

end InteractingSLE.Theorem14.SB.Fq
