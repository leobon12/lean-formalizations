/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FsGlue
import InteractingSLE.Spec.Supplement.SB2FsLeft
import InteractingSLE.Spec.Supplement.SB2FoZero
import InteractingSLE.Spec.Supplement.SB2FlZero
import InteractingSLE.Spec.Supplement.SB2MzMain

/-!
# The zero-lifetime step of the induction

Worker PROVE-SB2-F3LAW (round 6, D80). **`zero_piece`**: from the induction's stage data at B's stage `ℓ` (`StageLawOn`)
on an event `C`, the stage data at `ℓ + 2` on `C ∩ {B launches at ℓ with lifetime 0, relOff ≠ ℓ}`, with the SAME word
and profiles: the law by `Fl.mvLaw_succ_succ_zero` (the retained hull does not change), the left heights by
`Fo.ae_leftAdm_zero` (the seed moves over admissible connector points; its original heights from F3's mean identity,
`Fq.hmean_of_law`, `Fo.ae_read_of_meanIdentity`). At `relOff = ℓ` the zero piece is the relative root (D80: the
root's owners); for `relOff ≥ ℓ + 2` the left heights at `ℓ + 2` are vacuous.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fs

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms

/-- **The zero-lifetime step of the induction** (Theorems 1.2–1.3). See the module docstring. -/
theorem zero_piece (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {A₁ A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ᵐ ω ∂P, A₁ 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    -- the line family's local-set facts for `A₁ 0`
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] (A₁ 0))
    (hAc : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (centredField h u₀) P)
    -- the stage data at `ℓ`
    {C : Set Ω} {β : Ω → BoundaryWord} {S : Set Lv.WordProfile}
    (hst : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S) :
    StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁'
      (C ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ≠ ℓ}) β S := by
  obtain ⟨⟨K, G, Y, M, hlaw, hcov⟩, hβm, hS, hprof, hL⟩ := hst
  obtain ⟨G₂, hlaw₂, hcov₂⟩ := Fl.mvLaw_succ_succ_zero h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ k ℓ
    hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw
  have h𝓜 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : IsLocalSet (A₁ 0) (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hloc.isAvoidanceLocal
  have hread := Fo.ae_read_of_meanIdentity hh hu₀ hAm hl hlaw.2.2.2.2.2.2.2.2.1
    (Fq.hmean_of_law hh hu₀ h𝓜 hAm hAc hloc hlaw (S := G) (Eventually.of_forall fun _ h => h))
  have hzero := Fo.ae_leftAdm_zero h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA hA' (β := β)
  refine ⟨⟨K, G₂, Y, M, hlaw₂, ?_⟩, hβm.mono (WalkLaw.aeSigma_mono (P := P) (Mz.stageMarks_mono (by omega)))
    le_rfl, hS, ?_, ?_⟩
  · filter_upwards [hcov, hcov₂] with ω e1 e2 hω hl2
    exact e2 (e1 hω.1 hω.2.1) hω.2.1 hω.2.2.1 hl2
  · filter_upwards [hprof] with ω e1 hω _ using e1 hω.1 hω.2.1
  · filter_upwards [hL, hzero, hread, hcov, hlaw.2.2.2.2.1] with ω eL ez er ec ef hω hev2 hoff2
    obtain ⟨hC, hlℓ, hz, hne⟩ := hω
    have hev : ω ∈ stageEvent κ b jumps E u l k ℓ := ⟨hev2.1, hlℓ⟩
    have he1 := Nc.even_of_launch hlℓ
    have he2 := relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
    have hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ := by omega
    have hG : ω ∈ G := ec hC hlℓ
    have hHP : IsHPHull (A₁ 0 ω) := ef hG ▸ Mo.isHPHull_fillH hlaw.2.1 hlaw.2.2.1 ω
    exact (ez hev hev2.2 hoff hz (eL hC hev hoff) (fun x r hr hd hxJ hyJ => er hG hHP x r hr hd hxJ hyJ)).2.2

end InteractingSLE.Theorem14.SB.Fs
