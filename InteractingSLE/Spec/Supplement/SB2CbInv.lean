/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbConv
import InteractingSLE.Spec.Supplement.SB2CbInd
import InteractingSLE.Spec.Supplement.SB2CbPkgU
import InteractingSLE.Spec.Supplement.SB2FsBase
import InteractingSLE.Spec.Supplement.SB2GjLoc

/-!
# (P1) as an induction over the flow stages: the invariant, the base stage, the conclusion (D80, D82 item 3)

Packet PROVE-SB2-CANON, round 8 (the final (P1) assembly from F3LAW's glue-form pieces).

* **`StageInv ℓ`**, the induction's invariant at stage `ℓ`: for every line family of CONDFIN's form at `ℓ`
  (`Cx.RootSetsAt` at every cap), stage data in F3LAW's glue form (`Fs.StageLawOn`) on an event containing almost
  every launch of B's stage `ℓ` at an upper launch (`stageEvent ℓ`), and the base's root facts at `R` for the stage
  word where `ℓ ≤ relOff` (what CONDFIN's root piece reads at `relOff = ℓ`).
* **`stageLawClauses_of_inv`**: `StageInv ℓ` gives (P1)'s clauses (`StageLawClauses`, the law's cover at upper
  launches, D82 item 3) for EVERY line family of `Cz.SB2LowerStageLawInUStatement`'s form at `ℓ`: CONDFIN's family
  (`Cx.exists_rootLineFamily`) is an exact version of it, its `A₁ 0` is history-avoidance local for the line
  σ-algebra (GEOM2's `Gj.hloc_rootLine`), and `stageLawClauses_of_exact` moves the clauses to the given version.
* **`stageInv_zero`**: the base stage, from F3LAW's base word with profiles (`Fs.sb2LowerBaseWordPStatement_of_thms`)
  read as `Fs.base_piece` (at stage `0`, `0 ≤ relOff` always).
* **`SB2LowerStageStepStatement`**: the induction step `StageInv ℓ → StageInv (ℓ + 2)` between flow stages (the
  gluing at `ℓ + 2` of F3LAW's base, tail and zero pieces, SB2LIFT's zero-root piece and CONDFIN's root piece);
  **`lawInU_of_step`**: (P1) in the form `Cz.SB2LowerStageLawInUStatement` from the step (`flow_induction`), hence
  hcan and the top's hTL (`sb2LowerStageCanonStatement_of_step`, `sb2LowerTailLiftExStatement_of_step`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Lv Lk Mf Ms

/-- **The invariant of (P1)'s induction at stage `ℓ`**: for every line family of CONDFIN's form at `ℓ`, F3LAW's stage
data on an event containing almost every launch of B's stage `ℓ` at an upper launch, and the base's root facts at `R`
for the stage word on the launches with `ℓ ≤ relOff` (the input `hLR` of CONDFIN's root piece at `relOff = ℓ`). -/
def StageInv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) : Prop :=
  ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
  ∀ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ),
    (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
    (∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t)) →
    ∃ (C : Set Ω) (β : Ω → BoundaryWord) (S : Set Lv.WordProfile),
      Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S ∧
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ C) ∧
      ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
          Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))

/-- **(P1)'s clauses from the invariant**, for every line family of `Cz.SB2LowerStageLawInUStatement`'s form. -/
theorem stageLawClauses_of_inv (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
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
    (hflow : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hinv : StageInv κ b jumps P h E u l k ℓ)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
    (hA₁m : Measurable[mΩ, hittingSigma] (A₁ 0)) (hA₁c : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω)) :
    StageLawClauses κ b jumps P h E u l k ℓ 𝓖 A₁ := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hflow).1
  obtain ⟨u₀, hu₀, hu₀u⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  -- CONDFIN's line family at `ℓ` and its filtration (the given one)
  obtain ⟨𝓖c, A₁c, A₂Bc, A₂c, h𝓖c, hfam⟩ :=
    Cx.exists_rootLineFamily (P := P) (u := u) (l := l) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hflow hu₀
  have hGG : 𝓖c = 𝓖 := Filtration.ext (funext fun t => (h𝓖c t).trans (h𝓖 t).symm)
  subst hGG
  obtain ⟨C, β, S, ⟨⟨K, G, Y, M, hlaw, hcov⟩, hβm, hSc, hprof, hL⟩, hC, -⟩ :=
    hinv u₀ hu₀ 𝓖c A₁c A₂Bc A₂c h𝓖c hfam
  obtain ⟨hÂm, -, -, -, -, -, -, -, hÂc, -, hÂf, -⟩ := hfam 0
  have hloc := Gj.hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hflow h𝓖c hfam
  -- the centred field does not depend on the choice of the bounded harmonic extension
  have hcent : ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀' → centredField h u₀' = centredField h u₀ :=
    fun u₀' hu₀' => by
      have hc : ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension b jumps v → ContinuousOn v H := fun v hv x hx =>
        (hv.1 x hx).1.continuousAt.continuousWithinAt
      funext ω
      show h ω - _ = h ω - _
      rw [WangWu.smoothDist_congr (hc u₀' hu₀') (hc u₀ hu₀) (hu₀u u₀' hu₀')]
  refine stageLawClauses_of_exact h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft
    (by filter_upwards [hA 0] with ω h1 using h1.1) hA₁m hA₁c hÂm hÂc
    (fun u₀' hu₀' => by rw [hcent u₀' hu₀']; exact hloc) ?_ hlaw ?_ hβm hSc ?_ ?_
  · filter_upwards [hÂf, hA 0] with ω h1 h2 using h1.1.trans h2.1.symm
  · filter_upwards [hcov, hC] with ω h1 h2 hup hl using h1 (h2 ⟨hup, hl⟩) hl
  · filter_upwards [hprof, hC] with ω h1 h2 hup hl using h1 (h2 ⟨hup, hl⟩) hl
  · filter_upwards [hL, hC] with ω h1 h2 hS hoff _ using h1 (h2 hS) hS hoff

/-- **The base stage of the induction** (Theorems 1.2–1.3): F3LAW's base word with profiles, read as its base piece
(at stage `0` every sample has `0 ≤ relOff`). -/
theorem stageInv_zero (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0) (hlp : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hLw : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    StageInv κ b jumps P h E u l k 0 := by
  obtain ⟨β, hβm, ⟨Sp, hSp, hprof⟩, -, hbase⟩ := Fs.sb2LowerBaseWordPStatement_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4
    b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft
  intro u₀ _ 𝓖 A₁ A₂B A₂ h𝓖 hfam
  obtain ⟨K, G, Y, M, hlaw, hcov, hroot⟩ := hbase 0 𝓖 A₁ h𝓖 fun t => by
    filter_upwards [stmt6Sets_of_rootSets hfam t] with ω h1 using h1.1
  refine ⟨_, β, Sp, Fs.base_piece hβm hSp hprof hlaw hcov,
    Eventually.of_forall fun ω hω => ⟨hω.1, Nat.zero_le _⟩, ?_⟩
  filter_upwards [hcov, hroot] with ω h1 h2 hS ho using ⟨(h2 (h1 hS ho)).2.1, (h2 (h1 hS ho)).2.2⟩

/-- **Named statement (the step of (P1)'s induction; D80's pieces glued at `ℓ + 2`).** In SB2(2)'s setting, between
flow stages `ℓ` and `ℓ + 2`, the invariant at `ℓ` gives the invariant at `ℓ + 2`. -/
def SB2LowerStageStepStatement : Prop :=
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
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ,
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      StageInv κ b jumps P h E u l k ℓ → StageInv κ b jumps P h E u l k (ℓ + 2)

/-- **(P1) from the induction step** (Theorems 1.2–1.3): `Cz.SB2LowerStageLawInUStatement`. -/
theorem lawInU_of_step (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hstep : SB2LowerStageStepStatement.{u}) :
    SB2LowerStageLawInUStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk ℓ hflow 𝓖 A₁ A₂
    h𝓖 hA hA₁m hA₁c
  have hinv : ∀ ℓ, (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      StageInv κ b jumps P h E u l k ℓ :=
    flow_induction b jumps (-(Real.pi / 2)) true
      (stageInv_zero h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlp hlθ hLw hleft)
      (hstep κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hLw hleft hk)
  exact stageLawClauses_of_inv h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hflow (hinv ℓ hflow)
    h𝓖 hA hA₁m hA₁c

/-- **hcan from the induction step** (Theorems 1.2–1.3). -/
theorem sb2LowerStageCanonStatement_of_step (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hstep : SB2LowerStageStepStatement.{u}) :
    Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  sb2LowerStageCanonStatement_of_lawU h12 h13 h12₀ h13₀ (lawInU_of_step h12 h13 h12₀ h13₀ hstep)

/-- **The top's hTL from the induction step and GEOM2's root identification** (Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_step (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hstep : SB2LowerStageStepStatement.{u})
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  sb2LowerTailLiftExStatement_of_lawU h12 h13 h12₀ h13₀ (lawInU_of_step h12 h13 h12₀ h13₀ hstep) hI

end InteractingSLE.Theorem14.SB.Cz
