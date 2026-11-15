/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FsTail
import InteractingSLE.Spec.Supplement.SB2FsGlue
import InteractingSLE.Spec.Supplement.SB2FoAsm
import InteractingSLE.Spec.Supplement.SB2FoInp
import InteractingSLE.Spec.Supplement.SB2FpRoot

/-!
# The tail step as a piece of the induction's stage data

Worker PROVE-SB2-F3LAW (round 6, D80). **`Fo.tail_piece`**: the output of `Fo.tail_step'` read as the induction's stage
data at `ℓ + 2` (`Fs.StageLawOn`) on any event `C'` inside F2b′'s live event `F` whose launches at `ℓ + 2` lie in the
retained hull's event `L₂`: the step word's profiles lie in `Lv.stoppedProfiles κ (−π/2) Sp` when the word's profiles
at `ℓ` lie in `Sp` (`Lv.wordProfile_shift_stop_mem`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Qw Fl
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **The tail step as a piece of the induction's stage data** (Theorems 1.2–1.3). See the module docstring. -/
theorem tail_piece (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hwℓ₂ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ + 2]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {𝓖 𝓖' : Filtration ℝ≥0 mΩ} {A₁ A₂ A₁' : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
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
    (h𝓖' : 𝓖' 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 3))
    (hA' : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    -- the law at `ℓ`
    {Gℓ : Set Ω} {Kℓ : Ω → Set ℂ} {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {Mℓ : ℝ}
    (hlaw : MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ Mℓ)
    (hβ₁s : Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁)
    -- F2b′'s objects at `ℓ` for the word `β₁`
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {F : Set Ω} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
      ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w)
    -- the kernel half at `ℓ`: K2's stopped match and the canonical lifetime
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ F → (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Gℓ)
    -- the record matching
    {Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDr : Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] Dr)
    (hDrreg : ∀ ω, IsRegularDriver (Dr ω))
    (hDreq : ∀ᵐ ω ∂P, ω ∈ F → recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
    -- a retained hull of stage `ℓ + 2`
    {K₂ : Ω → Set ℂ} (hK₂m : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖' 0) K₂)
    (hK₂c : ∀ ω, IsCompact (K₂ ω)) (hK₂p : ∀ ω, IsPreconnected (K₂ ω ∪ Restart.lowerHalf)) {L₂ : Set Ω}
    (hL₂ : MeasurableSet[lineFiltC P 𝓖' 0] L₂) (hL₂K : ∀ᵐ ω ∂P, ω ∈ L₂ → fillH (K₂ ω) = A₁' 0 ω)
    -- the line family's local-set facts for `A₁ 0`, F2b′'s live event and offset identity, the left heights at `ℓ`
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] (A₁ 0))
    (hAc : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (WholeField.centredField h u₀) P)
    (hu : u ≤ 0)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hFev : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)
    (hx₀e : ∀ᵐ ω ∂P, ω ∈ F → x₀ ω = Nc.entryRead (fillH (K ω))
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))
    (hL : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ))))
    -- the target event: inside `F`, its launches at `ℓ + 2` in `L₂`; the word's profiles at `ℓ`
    {C' : Set Ω} (hC'F : ∀ᵐ ω ∂P, ω ∈ C' → ω ∈ F)
    (hC'L : ∀ᵐ ω ∂P, ω ∈ C' → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none → ω ∈ L₂)
    {Sp : Set Lv.WordProfile} (hSp : Sp.Countable) (hprof : ∀ᵐ ω ∂P, ω ∈ F → Lv.wordProfile (β₁ ω) ∈ Sp) :
    Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁' C'
      (stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
        (maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))
      (Lv.stoppedProfiles κ (-(Real.pi / 2)) Sp) := by
  obtain ⟨G₂, Y₂, M₂, hlaw₂, hβ₂m, hL₂', -, -, -, hcov₂⟩ := tail_step' h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ'
    hE hER hlθ k ℓ hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw hβ₁s hKm hKc hKp hKF hx₀ hF hFl S hcl2 htypes hcover hseed hK2 hlife
    hFG hDr hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K hu₀ hAm hAc hloc hu hleft hFev hx₀e hL
  refine ⟨⟨_, G₂, Y₂, M₂, hlaw₂, ?_⟩, hβ₂m, Lv.countable_stoppedProfiles κ _ hSp, ?_, ?_⟩
  · filter_upwards [hC'F, hC'L, hcov₂] with ω e1 e2 e3 hω hl2
    exact e3 (e1 hω) (e2 hω hl2) hl2
  · filter_upwards [hC'F, hprof] with ω e1 e2 hω _
    exact Lv.wordProfile_shift_stop_mem κ _ _ (by rw [Lv.wordProfile_shiftW]; exact e2 (e1 hω)) _
  · filter_upwards [hC'F, hC'L, hcov₂, hL₂'] with ω e1 e2 e3 e4 hω hev2 hoff2
    exact e4 (e3 (e1 hω) (e2 hω hev2.2) hev2.2) hev2 hoff2

end InteractingSLE.Theorem14.SB.Fo
