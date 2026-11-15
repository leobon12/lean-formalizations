/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CdStep
import InteractingSLE.Spec.Supplement.SB2FsPiece
import InteractingSLE.Spec.Supplement.SB2FpSeed

/-!
# The root step of SB2(2)'s induction with the left heights (D80)

Packet PROVE-SB2-CONDFIN, round 15 (decision D80: the ROOT step of (P1), F3LAW's handoff R5.4 item 4).
**`root_step`** is the root twin of F3LAW's `Fo.tail_step'`: the root joint step `Cd.mvLaw_succ_succ_jointX_root`
(NOJUMP's root versions `Cr.RootVersionS`, tail start `entrR`) together with the step of D34's left heights at every
launch at `ℓ + 2` (`Fs.ae_leftAdm_succ_succ'`) from the seed `p = R = max (A ∩ ℝ)` (F3LAW's R4.2): `hL` at
`relOff` is the base's root clause `FreeRight (A₁ 0) R ∧ LeftAdm κ β₁ (entry (A₁ 0) R)`
(`Fp.SB2LowerBaseWordStatement`'s third conjunct), the seed bound `stPt (run ℓ) ≤ R` is `Fp.ae_stPt_le_root`,
`hx₀le` comes from 9E's offset clause `x₀ = entryRead (fill K) R` (`Fp.ae_le_entry_of_entryRead`), and the kernel
law, the original heights right of `R` and the seed cell's seed are derived as in the tail step
(`Fo.ae_lawx_of_mvLaw`, `Fo.ae_read_of_meanIdentity` with `Fq.hmean_of_law`,
`Fo.ae_not_thr_of_cells`). **`root_piece`** reads it as F3LAW's gluing datum `Fs.StageLawOn` at `ℓ + 2` (the root twin
of `Fo.tail_piece`).

**Two events.** NOJUMP's versions, K2's outputs, `hKF`, `hFl` and the offset clause live on the version event `Fr`
(9E's, `= rootEv` a.s.); the step itself runs on an event `F ⊆ Fr` (a.s.) of the line σ-algebra at time `0`
(`lineFiltC P 𝓖 0`), which the kernel law at the offset and the masked record need. `F = Fr` is allowed whenever `Fr`
is such an event. By its definition, on the MARK entry (`R` added by the connector of stage `ℓ - 1` at a restart mark;
the piece is launched at `R`) the root event reads B's runs through `ℓ` and the sign of `ζ_ℓ` only (not formalized
here). On the PIECE entry (`R` first added by stage `ℓ`'s own piece, after the head) it also reads the piece after
time `0` (whether it reaches `R` before `ζ_ℓ`), so it is not an event of the time-`0` marks in general (CONDFIN's
handoff, round 15).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cd

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Qw Fl Fo
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **The root step with the left heights** (Theorems 1.2–1.3; D80). See the module docstring. -/
theorem root_step (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {F Fr : Set Ω} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F) (hFFr : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Fr)
    (hFl : ∀ᵐ ω ∂P, ω ∈ Fr → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (S : Cr.RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w →
      ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w)
    -- the kernel half at `ℓ`: K2's stopped match and the canonical lifetime
    (hK2 : ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ Fr → (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
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
    -- the line family's local-set facts for `A₁ 0`; 9E's root event, offset identity; the base's root facts
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] (A₁ 0))
    (hAc : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (WholeField.centredField h u₀) P)
    (hu : u ≤ 0)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hFev : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Ne.rootEv κ b jumps E u l k ℓ)
    (hx₀e : ∀ᵐ ω ∂P, ω ∈ Fr → x₀ ω = Nc.entryRead (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω)))
    (hLR : ∀ᵐ ω ∂P, ω ∈ F → Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) :
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
  obtain ⟨G₂, Y₂, M₂, hlaw₂, hβ₂m, hG₂F, hζ₂, hhull₂, hcov₂⟩ := mvLaw_succ_succ_jointX_root h12p h12 h13 h12₀ h13₀
    hκ hκ4 hb hh hcf hζ' hE hER hlθ k ℓ hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw hβ₁s hKm hKc hKp hKF hx₀ hF hFFr hFl S hcl2
    htypes hcover hseed hK2 hlife hFG hDr hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K
  refine ⟨G₂, Y₂, M₂, hlaw₂, hβ₂m, ?_, hG₂F, hζ₂, hhull₂, hcov₂⟩
  have h𝓜 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hβ₁m : Measurable[lineFiltC P 𝓖 0] β₁ := hlaw.2.2.2.2.2.2.2.1
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ₁m)
  have hKΩ : @Restart.IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝓜 _ (hKm n j)
  have hZ : Measurable fun ω => canonField κ h x₀ hKc hKp ω :=
    measurable_canonField κ hh.1 hKc hKp hKΩ (hx₀.mono h𝓜 le_rfl)
  have hKF' : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω := by
    filter_upwards [hKF, hFFr] with ω h1 h2 hωF using h1 (h2 hωF)
  have hlawx := ae_lawx_of_mvLaw hh.1 h𝓜 hlaw hKm hKc hKp hx₀ hF hFG hKF'
  have hseedF : ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0
        (-(Real.pi / 2)))
      (flowLineRhoR κ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0
        (-(Real.pi / 2))) 0
      (flowLineXL (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0)
      (flowLineXR (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps 0) := by
    filter_upwards [ae_not_thr_of_cells htypes hcover hseed, hFFr] with ω h1 h2 hωF using h1 (h2 hωF)
  -- the seed `R`: free ray (the base's root facts) and B's point left of it (`Fp.ae_stPt_le_root`)
  have hp : ∀ᵐ ω ∂P, ω ∈ F → Fm.FreeRight (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) ≤
        realMax (upperPrefix κ b jumps E u l k ω) := by
    filter_upwards [hLR, hKF', hFev, Fp.ae_stPt_le_root h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ
      hleft] with ω h1 h2 h3 h4 hωF
    rw [h2 hωF]
    exact ⟨(h1 hωF).1, h4 (h3 hωF)⟩
  have hx₀e' : ∀ᵐ ω ∂P, ω ∈ F → x₀ ω = Nc.entryRead (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω)) := by
    filter_upwards [hx₀e, hFFr] with ω h1 h2 hωF using h1 (h2 hωF)
  have hx₀le := Fp.ae_le_entry_of_entryRead hKc hKp hx₀e' (by filter_upwards [hp] with ω h hωF using (h hωF).1)
  have hL' : ∀ᵐ ω ∂P, ω ∈ F → Fm.LeftAdm κ (β₁ ω)
      (Fm.entry (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω))) := by
    filter_upwards [hLR, hKF'] with ω h1 h2 hωF
    rw [h2 hωF]
    exact (h1 hωF).2
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : IsLocalSet (A₁ 0) (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hloc.isAvoidanceLocal
  have hread0 := ae_read_of_meanIdentity hh hu₀ hAm hl hlaw.2.2.2.2.2.2.2.2.1
    (Fq.hmean_of_law hh hu₀ h𝓜 hAm hAc hloc hlaw hFG)
  have hread : ∀ᵐ ω ∂P, ω ∈ F → ∀ x, realMax (upperPrefix κ b jumps E u l k ω) < x → x ∉ jumps →
      Fm.bdryVal (fillH (K ω)) x ∉ (β₁ ω).jumps → (β₁ ω).fn (Fm.bdryVal (fillH (K ω)) x) = b x := by
    filter_upwards [hread0, hp, hKF'] with ω h1 h2 h3 hωF x hx hxJ hyJ
    obtain ⟨hfr, -⟩ := h2 hωF
    obtain ⟨r, hr, hd⟩ := hfr x hx
    rw [h3 hωF] at hfr hd hyJ ⊢
    exact h1 hωF (h3 hωF ▸ Mo.isHPHull_fillH hKc hKp ω) x r hr hd hxJ hyJ
  have hK₂A : ∀ᵐ ω ∂P, ω ∈ G₂ → fillH (K₂ ω) = A₁' 0 ω := hlaw₂.2.2.2.2.1
  exact Fs.ae_leftAdm_succ_succ' h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft h𝓜 hKc hKp hc hZ hF
    hlawx (by filter_upwards [hFev] with ω h hωF using (h hωF).1) hp hx₀le hL' hread hseedF hA' hG₂F hζ₂ hhull₂ hK₂A

/-- **The root step as a piece of the induction's stage data** (`Fs.StageLawOn` at `ℓ + 2` on any `C' ⊆ F` whose
launches at `ℓ + 2` lie in `L₂`; the root twin of `Fo.tail_piece`). -/
theorem root_piece (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {F Fr : Set Ω} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F) (hFFr : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Fr)
    (hFl : ∀ᵐ ω ∂P, ω ∈ Fr → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (S : Cr.RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w →
      ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr w)
    -- the kernel half at `ℓ`: K2's stopped match and the canonical lifetime
    (hK2 : ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ Fr → (driverOf h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
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
    -- the line family's local-set facts for `A₁ 0`; 9E's root event, offset identity; the base's root facts
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] (A₁ 0))
    (hAc : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (WholeField.centredField h u₀) P)
    (hu : u ≤ 0)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hFev : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Ne.rootEv κ b jumps E u l k ℓ)
    (hx₀e : ∀ᵐ ω ∂P, ω ∈ Fr → x₀ ω = Nc.entryRead (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω)))
    (hLR : ∀ᵐ ω ∂P, ω ∈ F → Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))))
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
  obtain ⟨G₂, Y₂, M₂, hlaw₂, hβ₂m, hL₂', -, -, -, hcov₂⟩ := root_step h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ'
    hE hER hlθ k ℓ hwℓ hwℓ₂ h𝓖 hA h𝓖' hA' hlaw hβ₁s hKm hKc hKp hKF hx₀ hF hFFr hFl S hcl2 htypes hcover hseed hK2
    hlife hFG hDr hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K hu₀ hAm hAc hloc hu hleft hFev hx₀e hLR
  refine ⟨⟨_, G₂, Y₂, M₂, hlaw₂, ?_⟩, hβ₂m, Lv.countable_stoppedProfiles κ _ hSp, ?_, ?_⟩
  · filter_upwards [hC'F, hC'L, hcov₂] with ω e1 e2 e3 hω hl2
    exact e3 (e1 hω) (e2 hω hl2) hl2
  · filter_upwards [hC'F, hprof] with ω e1 e2 hω _
    exact Lv.wordProfile_shift_stop_mem κ _ _ (by rw [Lv.wordProfile_shiftW]; exact e2 (e1 hω)) _
  · filter_upwards [hC'F, hC'L, hcov₂, hL₂'] with ω e1 e2 e3 e4 hω hev2 hoff2
    exact e4 (e3 (e1 hω) (e2 hω hev2.2) hev2.2) hev2 hoff2

end InteractingSLE.Theorem14.SB.Cd
