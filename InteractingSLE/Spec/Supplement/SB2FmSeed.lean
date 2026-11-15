/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmGeo
import InteractingSLE.Spec.Supplement.SBLwChart
import InteractingSLE.Foundations.Loewner.Reflect
import InteractingSLE.Spec.Supplement.SB2NcSeed
import InteractingSLE.Spec.Supplement.SB2NcGeo
import InteractingSLE.Spec.Supplement.SB2NcLive
import InteractingSLE.Spec.Supplement.SB2JwOrder

/-!
# D34's clause at a tail stage: the free ray right of B's seed, and the clause from the left heights

Worker PROVE-SB2-F3LAW (round 2, target 3). Almost surely on B's live event at a tail stage (`relOff < ℓ`, a piece of
positive lifetime), with NOJUMP's walk facts (`Nc.ae_walkGood`, `Nc.ae_retGeom`, `Nc.realMax_retX_eq`): the retained
hull `A₁ = fill (A ∪ B_{<ℓ})` is a hull, B's seed is the walk's real point `stPt (run ℓ)` (`Lk.pcPt_zero_launch`), the
largest real point of `A ∪ B_{<ℓ}`, so `A₁` is free right of it (`exists_ball_disjoint_fillH_right`). With
Lemma 7.8's vanishing harmonic part (`Sec7.IsLocalSetMean.ae_tendsto_zero_of_real`) and F3's mean identity, D34's
clause holds once the heights left of the entry are admissible (`SB2FmGeo.heightClause_of_meanIdentity`).

* `exists_ball_disjoint_fillH_right`, `freeRight_fillH_realMax`, **`ae_seed_freeRight`**,
  **`ae_heightClause_of_leftAdm`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Fm

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide

/-- **A real point right of every real point of a compact set has a ball missing its fill** (mirror of
`Lw.exists_ball_disjoint_fillH`). -/
theorem exists_ball_disjoint_fillH_right {A : Set ℂ} (hA : IsCompact A) {x : ℝ}
    (hx : ∀ y : ℝ, (y : ℂ) ∈ A → y < x) : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH A) := by
  have hAc : IsCompact (LP.reflectC '' A) := hA.image (by unfold LP.reflectC; fun_prop)
  have hx' : ∀ y : ℝ, (y : ℂ) ∈ LP.reflectC '' A → -x < y := by
    rintro y ⟨z, hz, hzy⟩
    have hz' : z = ((-y : ℝ) : ℂ) := by
      apply LP.reflectC_injective
      rw [hzy, LP.reflectC_ofReal, neg_neg]
    rw [hz'] at hz
    have := hx _ hz
    linarith
  obtain ⟨ρ, hρ, hd⟩ := Lw.exists_ball_disjoint_fillH hAc hx'
  refine ⟨ρ, hρ, Set.disjoint_left.2 fun z hzb hzF => ?_⟩
  have h1 : LP.reflectC z ∈ ball (((-x : ℝ) : ℂ)) ρ := by
    rw [← LP.reflectC_ofReal, ← LP.image_reflectC_ball]
    exact mem_image_of_mem _ hzb
  have h2 : LP.reflectC z ∈ fillH (LP.reflectC '' A) := by
    rw [LP.fillH_image_reflectC]
    exact mem_image_of_mem _ hzF
  exact Set.disjoint_left.1 hd h1 h2

/-- **The fill of a compact set is free right of its largest real point.** -/
theorem freeRight_fillH_realMax {X : Set ℂ} (hX : IsCompact X) : FreeRight (fillH X) (realMax X) := by
  intro x hx
  have hS : BddAbove {y : ℝ | (y : ℂ) ∈ X} :=
    (Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hX).isBounded.bddAbove
  exact exists_ball_disjoint_fillH_right hX fun y hy => lt_of_le_of_lt (le_csSup hS hy) hx

open LQGMetric (DistOn) in
/-- **The retained hull at a tail stage is free right of B's seed** (almost surely): on B's stage event at a tail stage
with a piece of positive lifetime, `A₁` is a hull, B's seed is the walk's real point `stPt (run ℓ)`, and every real
point right of it has a ball missing `A₁`. -/
theorem ae_seed_freeRight.{u} (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁ : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω) :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      IsHPHull (A₁ ω) ∧
      Nb.bSeed κ b jumps E ℓ ω = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) : ℝ) : ℂ) ∧
      FreeRight (A₁ ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) := by
  by_cases hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length
  swap
  · refine Eventually.of_forall fun ω hω => absurd (Nc.flow_of_launch hω.2).1 hℓ
  filter_upwards [Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft,
    Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ, hA] with ω hg hgeo hAω hev hoff hpos
  have hgω := hg hev.1
  obtain ⟨hXc, -, -, hHP, hfill⟩ := hgeo hev.2
  have hA' : A₁ ω = fillH (Nc.retX κ b jumps E u l k ℓ ω) := hAω.trans hfill
  have heven := Nc.even_of_launch hev.2
  have hmax := Nc.realMax_retX_eq hgω hev.2 hoff heven
  refine ⟨hA' ▸ hHP, Lk.pcPt_zero_launch hgω.reg hgω.chain hev.2 hpos.ne', ?_⟩
  rw [hA', ← hmax]
  exact freeRight_fillH_realMax hXc

open LQGMetric (DistOn TestOn) in
/-- **D34's clause almost surely from the left heights.** In SB2(2)'s setting at B's stage `ℓ`, for a local set `A₁`
(the retained hull, F2b′'s `A₁ 0`) and a sorted word `β₁` with F3's mean identity (the premise of
`Nb.SB2LowerStageVersionStatement4`), almost surely on the live event of a tail stage, `Nb.HeightClause` holds at B's
seed as soon as the heights of `β₁` left of the entry of the free ray right of the seed are admissible. -/
theorem ae_heightClause_of_leftAdm.{u} (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁ : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] A₁)
    (hloc : IsLocalSet A₁ (WholeField.centredField h u₀) P)
    {β₁ : Ω → BoundaryWord} (hβs : ∀ ω, (β₁ ω).IsSorted)
    (hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens,
      LocalSets.IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) -
                QuantumZipper.chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z) (H \ A₁ ω))
    (hL : ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      LeftAdm κ (β₁ ω) (entry (A₁ ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))) :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Nb.HeightClause κ b jumps (A₁ ω) (Nb.bSeed κ b jumps E ℓ ω) (β₁ ω) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  filter_upwards [ae_seed_freeRight h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA,
    Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hAm hloc hg₁, hmean g₁ hg₁, hg₁.2.1, hL]
    with ω hseed hw hid hharm hLω hev hoff hpos
  obtain ⟨hHP, hbs, hfree⟩ := hseed hev hoff hpos
  obtain ⟨v, hv, hrep⟩ := hharm
  rw [hbs]
  exact heightClause_of_meanIdentity hκ hHP hfree (hβs ω) hu₀ (hid hev v hv hrep) (hw v hv hrep)
    (hLω hev hoff hpos)

end InteractingSLE.Theorem14.SB.Fm
