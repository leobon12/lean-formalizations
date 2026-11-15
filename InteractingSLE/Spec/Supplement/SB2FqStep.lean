/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FqHgt
import InteractingSLE.Spec.Supplement.SB2FoAsm
import InteractingSLE.Spec.Supplement.SB2FoInp
import InteractingSLE.Spec.Supplement.SB2FpRoot

/-!
# The tail step of SB2(2)'s induction with the left heights

Worker PROVE-SB2-F3LAW (round 5, D76: CANON's (P1)). **`tail_step`**: the joint-A₂ step twin
`Fo.mvLaw_succ_succ_jointX` (the retained law at `ℓ + 2` with the step word `Qw.stepWord …`) together with the step of
D34's left heights `hL` (`Fo.ae_leftAdm_succ_succ`), whose inputs are all derived here: the kernel law at the offset
(`Fo.ae_lawx_of_mvLaw`), the original heights right of the seed (`Fo.ae_read_of_meanIdentity` with F3's mean identity
`Fq.hmean_of_law`), the seed not at threshold (`Fo.ae_not_thr_of_cells`), the free ray at the seed
(`Fm.ae_seed_freeRight`) and `hx₀le` from F2b′'s offset identity (SB2LIFT's 6E clause, `Fp.ae_le_entry_of_entryRead`).

Its hypotheses are the step twin's (F2b′'s objects at `ℓ` for the law's word, K2's outputs, the record, a retained hull
of `ℓ + 2`) plus the line family's local-set facts for `A₁ 0`, F2b′'s live event and offset identity, and `hL` at `ℓ`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
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

/-- **The tail step with the left heights** (Theorems 1.2–1.3). See the module docstring. -/
theorem tail_step (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))) :
    ∃ (G₂ : Set Ω) (Y₂ : Ω → DistOn upperHalfPlaneOpens) (M₂ : ℝ),
      MvLaw κ (lineFiltC P 𝓖' 0) P h (A₁' 0) K₂ G₂ Y₂ (stepWord κ (-(Real.pi / 2)) x₀
        (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) (maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω))) M₂ ∧
      Measurable[aeSigma (stageMarks κ b jumps E u l k (ℓ + 2)) P] (stepWord κ (-(Real.pi / 2)) x₀
        (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) (maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω))) ∧
      (∀ᵐ ω ∂P, ω ∈ G₂ → ω ∈ stageEvent κ b jumps E u l k (ℓ + 2) →
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ + 2 →
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2) ω).2 →
        Fm.LeftAdm κ (stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
          (maskDrv F fun ω => driverOf h12p hκ (-(Real.pi / 2))
            (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)) ω)
          (Fm.entry (A₁' 0 ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2))))) ∧
      G₂ ⊆ F ∧
      (∀ ω ∈ G₂, (driverOf h12p hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2 ≠ ⊤) ∧
      (∀ᵐ ω ∂P, ω ∈ G₂ →
        LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))) →
        fillH (K₂ ω) = stepHull (fillH (K ω)) (x₀ ω) (recDrv (driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))
          ((driverOf h12p hκ (-(Real.pi / 2))
            (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)).2.toNNReal : ℝ)) ∧
      ∀ᵐ ω ∂P, ω ∈ F → ω ∈ L₂ →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
        ω ∈ G₂  := by
  obtain ⟨G₂, Y₂, M₂, hlaw₂, hβ₂m, hG₂F, hζ₂, hhull₂, hcov₂⟩ := mvLaw_succ_succ_jointX h12p h12 h13 h12₀ h13₀ hκ
    hκ4 hb hh hcf hζ' hE hER hlθ k ℓ hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw hβ₁s hKm hKc hKp hKF hx₀ hF hFl S hcl2 htypes
    hcover hseed hK2 hlife hFG hDr hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K
  refine ⟨G₂, Y₂, M₂, hlaw₂, hβ₂m, ?_, hG₂F, hζ₂, hhull₂, hcov₂⟩
  have h𝓜 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hβ₁m : Measurable[lineFiltC P 𝓖 0] β₁ := hlaw.2.2.2.2.2.2.2.1
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ₁m)
  have hKΩ : @Restart.IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝓜 _ (hKm n j)
  have hZ : Measurable fun ω => canonField κ h x₀ hKc hKp ω :=
    measurable_canonField κ hh.1 hKc hKp hKΩ (hx₀.mono h𝓜 le_rfl)
  have hlawx := ae_lawx_of_mvLaw hh.1 h𝓜 hlaw hKm hKc hKp hx₀ hF hFG hKF
  have hseedF := ae_not_thr_of_cells htypes hcover hseed
  have hfree := Fm.ae_seed_freeRight h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft
    (by filter_upwards [hA 0] with ω hω using hω.1)
  have hp : ∀ᵐ ω ∂P, ω ∈ F → Fm.FreeRight (fillH (K ω))
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) ≤
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) := by
    filter_upwards [hfree, hFev, hKF] with ω h1 h2 h3 hωF
    obtain ⟨he, ho, hz⟩ := h2 hωF
    rw [h3 hωF]
    exact ⟨(h1 he ho hz).2.2, le_rfl⟩
  have hx₀le := Fp.ae_le_entry_of_entryRead hKc hKp hx₀e (by filter_upwards [hp] with ω h hωF using (h hωF).1)
  have hL' : ∀ᵐ ω ∂P, ω ∈ F → Fm.LeftAdm κ (β₁ ω) (Fm.entry (fillH (K ω))
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ))) := by
    filter_upwards [hL, hFev, hKF] with ω h1 h2 h3 hωF
    obtain ⟨he, ho, hz⟩ := h2 hωF
    rw [h3 hωF]
    exact h1 he ho hz
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : IsLocalSet (A₁ 0) (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hloc.isAvoidanceLocal
  have hread0 := ae_read_of_meanIdentity hh hu₀ hAm hl hlaw.2.2.2.2.2.2.2.2.1
    (Fq.hmean_of_law hh hu₀ h𝓜 hAm hAc hloc hlaw hFG)
  have hread : ∀ᵐ ω ∂P, ω ∈ F → ∀ x, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) < x → x ∉ jumps →
      Fm.bdryVal (fillH (K ω)) x ∉ (β₁ ω).jumps → (β₁ ω).fn (Fm.bdryVal (fillH (K ω)) x) = b x := by
    filter_upwards [hread0, hp, hKF] with ω h1 h2 h3 hωF x hx hxJ hyJ
    obtain ⟨hfr, -⟩ := h2 hωF
    obtain ⟨r, hr, hd⟩ := hfr x hx
    rw [h3 hωF] at hfr hd hyJ ⊢
    exact h1 hωF (h3 hωF ▸ Mo.isHPHull_fillH hKc hKp ω) x r hr hd hxJ hyJ
  have hK₂A : ∀ᵐ ω ∂P, ω ∈ G₂ → fillH (K₂ ω) = A₁' 0 ω := hlaw₂.2.2.2.2.1
  exact ae_leftAdm_succ_succ h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft h𝓜 hKc hKp hc hZ hF
    hlawx (by filter_upwards [hFev] with ω h hωF using (h hωF).1) hp hx₀le hL' hread hseedF hA' hG₂F hζ₂ hhull₂ hK₂A

end InteractingSLE.Theorem14.SB.Fo
