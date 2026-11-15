/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FuRoot
import InteractingSLE.Spec.Supplement.SB2CaRoot

/-!
# The root piece from the proved entrance law (D85)

Worker PROVE-SB2-F3LAW (round 8, D85). **`root_piece_clockF`**: CONDFIN's `Ca.root_piece_clock` (the root piece at
`ℓ + 2` on the whole root event, mark and piece entries alike, for CANON's gluing, D86) with its entrance-law argument
`hA2 : Ca.SB2LowerRootEntranceLawStatement` replaced by the proved `Fu.SB2LowerRootEntranceLawFStatement` and one more
premise `hbase` (the law at `ℓ` covers the base region; in CANON's `StageInv ℓ`). Same proof (`Ca.root_piece_entr` at
the clock event of NOJUMP's first root version).

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

namespace InteractingSLE.Theorem14.SB.Fu

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Qw Fl Fo Cd Ca
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **CONDFIN's root piece on the whole root event, from the entrance law with the invariant's data** (D85).
`Ca.root_piece_clock` with `hA2 : Ca.SB2LowerRootEntranceLawStatement` replaced by
`hA2F : Fu.SB2LowerRootEntranceLawFStatement` (PROVED, `Fu.sb2LowerRootEntranceLawFStatement`) and one more premise,
`hbase`: the law at `ℓ` covers the base region `stageEvent ℓ ∩ {ℓ ≤ relOff}` (CANON's `StageInv ℓ`). The other three
premises of the F-form are read from `root_piece_clock`'s own (`hβ₁s`, and `hprof`, `hLR` on `Fr = rootEv` a.s.). -/
theorem root_piece_clockF (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hA2F : SB2LowerRootEntranceLawFStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
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
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
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
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Fr : Set Ω} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
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
    (hFG : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ Gℓ)
    (hbase : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ Gℓ)
    -- the record matching
    {Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDr : Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] Dr)
    (hDrreg : ∀ ω, IsRegularDriver (Dr ω))
    (hDreq : ∀ᵐ ω ∂P, ω ∈ Fr → recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
    -- a retained hull of stage `ℓ + 2`
    {K₂ : Ω → Set ℂ} (hK₂m : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖' 0) K₂)
    (hK₂c : ∀ ω, IsCompact (K₂ ω)) (hK₂p : ∀ ω, IsPreconnected (K₂ ω ∪ Restart.lowerHalf)) {L₂ : Set Ω}
    (hL₂ : MeasurableSet[lineFiltC P 𝓖' 0] L₂) (hL₂K : ∀ᵐ ω ∂P, ω ∈ L₂ → fillH (K₂ ω) = A₁' 0 ω)
    -- the line family's local-set facts for `A₁ 0`; 9E's root event, offset identity; the base's root facts
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hAm : Measurable[mΩ, hittingSigma] (A₁ 0))
    (hAc : ∀ ω, A₁ 0 ω ⊆ H ∧ IsOpen (H \ A₁ 0 ω))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (WholeField.centredField h u₀) P)
    (hu : u ≤ 0) (hpair : l.Pairwise (fun p q => p.2 < q.2))
    (hlw : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hFev : ∀ᵐ ω ∂P, ω ∈ Fr ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ)
    (hx₀e : ∀ᵐ ω ∂P, ω ∈ Fr → x₀ ω = Nc.entryRead (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω)))
    (hLR : ∀ᵐ ω ∂P, ω ∈ Fr → Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))))
    -- the target event: inside `F`, its launches at `ℓ + 2` in `L₂`; the word's profiles at `ℓ`
    {C' : Set Ω} (hC'F : ∀ᵐ ω ∂P, ω ∈ C' → ω ∈ clockEv (S.ver 0).a)
    (hC'L : ∀ᵐ ω ∂P, ω ∈ C' → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none → ω ∈ L₂)
    {Sp : Set Lv.WordProfile} (hSp : Sp.Countable) (hprof : ∀ᵐ ω ∂P, ω ∈ Fr → Lv.wordProfile (β₁ ω) ∈ Sp) :
    Fs.StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁' C'
      (stepWord κ (-(Real.pi / 2)) x₀ (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
        (maskDrv (clockEv (S.ver 0).a) fun ω => driverOf h12p hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω), canonField κ h x₀ hKc hKp ω)))
      (Lv.stoppedProfiles κ (-(Real.pi / 2)) Sp) := by
  classical
  obtain ⟨hFℋ, hFs⟩ := measurableSet_clockEv (P := P) (E := E) (u := u) (l := l) (k := k) hwℓ hwℓ₂ h𝓖 h𝓖'
    (S.ver 0).clock_meas
  have hcl := ae_mem_clockEv_iff S htypes hcover hseed
  have hFFr : ∀ᵐ ω ∂P, ω ∈ clockEv (S.ver 0).a → ω ∈ Fr := by
    filter_upwards [hcl] with ω h using h.1
  have hFm : MeasurableSet (clockEv (S.ver 0).a) := (lineFiltC P 𝓖').le 0 _ hFℋ
  have hFG' : ∀ᵐ ω ∂P, ω ∈ clockEv (S.ver 0).a → ω ∈ Gℓ := by
    filter_upwards [hFFr, hFG] with ω h1 h2 hω using h2 (h1 hω)
  have hprofR : ∃ Sp' : Set Lv.WordProfile, Sp'.Countable ∧
      ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → Lv.wordProfile (β₁ ω) ∈ Sp' :=
    ⟨Sp, hSp, by filter_upwards [hFev, hprof] with ω h1 h2 hω using h2 (h1.2 hω)⟩
  have hLRR : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))) := by
    filter_upwards [hFev, hLR] with ω h1 h2 hω using h2 (h1.2 hω)
  have hentr := hA2F κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hpair hlθ hlw hleft ℓ 𝓖 A₁ hwℓ h𝓖
    (fun t => by filter_upwards [hA t] with ω hω using hω.1) Kℓ Gℓ Yℓ β₁ Mℓ hlaw hβ₁s hbase hprofR hLRR _ hFm
    (by filter_upwards [hcl, hFev] with ω h1 h2 using h1.trans h2) hFG'
  have hDreq' : ∀ᵐ ω ∂P, ω ∈ clockEv (S.ver 0).a → recOf ⊤ (Dr ω) = recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
      (BoundaryWord.shiftW (x₀ ω) (β₁ ω), Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ)
        (h ω))) := by
    filter_upwards [hFFr, hDreq] with ω h1 h2 hω using h2 (h1 hω)
  have hFev' : ∀ᵐ ω ∂P, ω ∈ clockEv (S.ver 0).a → ω ∈ Ne.rootEv κ b jumps E u l k ℓ := by
    filter_upwards [hFFr, hFev] with ω h1 h2 hω using h2.1 (h1 hω)
  have hLR' : ∀ᵐ ω ∂P, ω ∈ clockEv (S.ver 0).a → Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))) := by
    filter_upwards [hFFr, hLR] with ω h1 h2 hω using h2 (h1 hω)
  have hprof' : ∀ᵐ ω ∂P, ω ∈ clockEv (S.ver 0).a → Lv.wordProfile (β₁ ω) ∈ Sp := by
    filter_upwards [hFFr, hprof] with ω h1 h2 hω using h2 (h1 hω)
  exact root_piece_entr h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ k ℓ hwℓ hwℓ₂ (h𝓖 0) hA h𝓖' hA' hlaw
    hβ₁s hKm hKc hKp hKF hx₀ hFℋ hFs hFFr hFl S hcl2 htypes hcover hseed hK2 hlife hFG' hentr hDr hDrreg hDreq' hK₂m
    hK₂c hK₂p hL₂ hL₂K hu₀ hAm hAc hloc hu hleft hFev' hx₀e hLR' hC'F hC'L hSp hprof'

end InteractingSLE.Theorem14.SB.Fu
