/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbInv
import InteractingSLE.Spec.Supplement.SB2CbTail
import InteractingSLE.Spec.Supplement.SB2FsPiece

/-!
# The tail branch of (P1)'s induction step (D80)

Packet PROVE-SB2-CANON, round 8. Two pieces of the step `StageInv ℓ → StageInv (ℓ + 2)` (`SB2CbInv`):

* **`hull_succ_succ`**: for a line family of stage `ℓ + 2` (F3LAW's step form: `𝓖' 0` and `A₁' 0` only), a retained
  hull `K₂` of stage `ℓ + 2` hitting-measurable for `lineFiltC P 𝓖' 0` and an event `L₂` of `lineFiltC P 𝓖' 0`
  containing almost every launch at `ℓ + 2`, with `fill K₂ = A₁' 0` on `L₂` (`exists_exactRetHull` at `ℓ + 2`, the
  stage marks inside the line σ-algebra, `Nc.ae_retGeom`);
* **`tail_branch`**: from the invariant's stage data at `ℓ` on CONDFIN's line family (law, word, profiles, left
  heights, the event containing `stageEvent ℓ`), the tail piece at `ℓ + 2` (F3LAW's `Fo.tail_piece`) on SB2LIFT's 6E
  live event `F` of stage `ℓ` — an event of `lineFiltC P 𝓖 0`, almost surely equal to
  `stageEvent ℓ ∩ {relOff < ℓ} ∩ {0 < ζ_ℓ}` — for every line family of stage `ℓ + 2`. Inputs: `tail_inputs`
  (CANON's, with GEOM2's `Gj.hloc_rootLine`) and `hull_succ_succ`.

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

/-- **A retained hull of stage `ℓ + 2` for the line σ-algebra of a stage-`ℓ + 2` family.** -/
theorem hull_succ_succ (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ₂ : ℓ + 2 < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {𝓖' : Filtration ℝ≥0 mΩ} {A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω) :
    ∃ (K₂ : Ω → Set ℂ) (L₂ : Set Ω), @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖' 0) K₂ ∧
      (∀ ω, IsCompact (K₂ ω)) ∧ (∀ ω, IsPreconnected (K₂ ω ∪ Restart.lowerHalf)) ∧
      MeasurableSet[lineFiltC P 𝓖' 0] L₂ ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
          ω ∈ L₂) ∧
      (∀ᵐ ω ∂P, ω ∈ L₂ → fillH (K₂ ω) = A₁' 0 ω) := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨hE', -, -⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮 : Ms.stageMarks κ b jumps E u l k (ℓ + 2) ≤ mΩ := sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 (ℓ + 2))
  have h𝒮𝓖 : Ms.stageMarks κ b jumps E u l k (ℓ + 2) ≤ 𝓖' 0 := by
    rw [h𝓖']
    refine sup_le_sup le_rfl ?_
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := -(Real.pi / 2)) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ₂.le
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ (ℓ + 2))
  have hsm : Ms.stageMarks κ b jumps E u l k (ℓ + 2) ≤ lineFiltC P 𝓖' 0 :=
    le_inf h𝒮 (h𝒮𝓖.trans (le_aeSigma _ P))
  obtain ⟨K, G₁, hKm, hKc, hKp, hG₁, hG₁cov, hG₁f⟩ :=
    exists_exactRetHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hℓ₂ hu₀
  refine ⟨K, G₁, fun n j => hsm _ (hKm n j), hKc, hKp, hsm _ hG₁, hG₁cov, ?_⟩
  filter_upwards [hG₁f, hA', Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hℓ₂]
    with ω h1 h2 h3 hω
  obtain ⟨hl, hK⟩ := h1 hω
  rw [hK, h2]
  exact ((h3 hl).2.2.2.2).symm

/-- **The tail branch of the induction step** (Theorems 1.2–1.3). See the module docstring. -/
theorem tail_branch (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlp : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hLw : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    -- CONDFIN's line family of stage `ℓ` and the invariant's stage data on it
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t))
    {C : Set Ω} {β : Ω → BoundaryWord} {S : Set Lv.WordProfile}
    (hst : Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S)
    (hC : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ C)
    -- a line family of stage `ℓ + 2`
    {𝓖' : Filtration ℝ≥0 mΩ} {A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω) :
    ∃ (F : Set Ω) (β' : Ω → BoundaryWord) (S' : Set Lv.WordProfile),
      MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) ∧
      Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁' F β' S' := by
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  have hℓ₂ : ℓ + 2 < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ₂).1
  obtain ⟨⟨Kℓ, Gℓ, Yℓ, Mℓ, hlaw, hcov⟩, hβm, hSc, hprof, hL⟩ := hst
  obtain ⟨hA₁m, -, -, -, -, -, -, -, hA₁c, -⟩ := hfam 0
  have hloc := Gj.hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ h𝓖 hfam
  have hL' : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ))) := by
    filter_upwards [hL, hC] with ω h1 h2 hS hoff _ using h1 (h2 hS) hS hoff
  obtain ⟨K, x₀, F, types, pc, tL, relLife, hKc, hKp, S6, Dr, hKm, hKF, hx₀, hF, hFl, hcl, htypes, hcover, hseed,
    hK2, hlife, hFG, hFev, hx₀e, hDrm, hDrreg, hDreq, hprofF, hFae⟩ :=
    tail_inputs h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlp hlθ hLw k ℓ hleft hℓ hwℓ hu₀ h𝓖 hfam hloc hlaw
      hβm (by filter_upwards [hcov, hC] with ω h1 h2 hup hl using h1 (h2 ⟨hup, hl⟩) hl) hSc
      (by filter_upwards [hprof, hC] with ω h1 h2 hup hl using h1 (h2 ⟨hup, hl⟩) hl) hL'
  obtain ⟨K₂, L₂, hK₂m, hK₂c, hK₂p, hL₂, hL₂cov, hL₂K⟩ :=
    hull_succ_succ h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ₂ h𝓖' hA'
  exact ⟨F, _, _, hF, hFae, Fo.tail_piece (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h12 h13 h12₀
    h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ k ℓ hwℓ hwℓ₂ (h𝓖 0) (stmt6Sets_of_rootSets hfam) h𝓖' hA' hlaw hβm hKm hKc
    hKp hKF hx₀ hF hFl S6 hcl htypes hcover hseed hK2 hlife hFG hDrm hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K hu₀ hA₁m
    hA₁c hloc hu hleft hFev hx₀e hL' (C' := F) (Eventually.of_forall fun _ h => h)
    (by filter_upwards [hL₂cov] with ω h1 _ hl using h1 hl) hSc hprofF⟩

end InteractingSLE.Theorem14.SB.Cz
