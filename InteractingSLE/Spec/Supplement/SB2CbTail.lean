/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbRec
import InteractingSLE.Spec.Supplement.SB2FoInp

/-!
# The inputs of the induction's tail step at a stage (D80 item 2)

Packet PROVE-SB2-CANON, round 8 (the final (P1) assembly from F3LAW's step lemmas). **`tail_inputs`**: at a flow stage
`ℓ`, from the induction's data — CONDFIN's line family (`Cx.RootSetsAt`; joint set `A₂`), the locality of `A₁ 0` for
`lineFiltC P 𝓖 0`, the retained law on `A₁ 0` with its word `β₁` (measurable for the completed retained past, its
event covering B's launches), countably many word profiles containing `β₁`'s on the launches, and the left heights on
the tail live event (the cover and the profiles at upper launches, D82 item 3) — every input of F3LAW's
`Fo.tail_step` at `ℓ` (equivalently of `Fo.tail_piece`), and the live event `F` with its a.s. description: SB2LIFT's 6E
objects for `β₁` (`Sx.sb2LowerStageVersionStatement6E`, premises from the law: `Fq.hmean_of_law`, `Fq.hheight_of_law`;
types from the profiles), the versions' clock coverage and seed cells (`Ci.hseed_of_le_thr`), K2 (CONDFIN's
`Ce.ae_k2_tail` with the conditional law at the offset `Fo.ae_lawx_of_mvLaw`), the live event inside the law's event,
the offset identity, and the record matching (`tail_record` on CANON's chain facts `ae_chainFacts_tail`).

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

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **The inputs of `Fo.tail_step` at a stage from the induction's data.** See the module docstring. -/
theorem tail_inputs (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
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
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    -- CONDFIN's line family of stage `ℓ` and the locality of `A₁ 0`
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂B A₂ : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, Cx.RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂B t) (A₂ t))
    (hloc : IsHistoryAvoidanceLocal (lineFiltC P 𝓖 0) (A₁ 0) (WholeField.centredField h u₀) P)
    -- the induction's data at `ℓ`
    {Kℓ : Ω → Set ℂ} {Gℓ : Set Ω} {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {Mℓ : ℝ}
    (hlaw : Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ Mℓ)
    (hβ₁s : Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁)
    (hcovL : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ Gℓ)
    {Sp : Set Lv.WordProfile} (hSp : Sp.Countable)
    (hprof : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lv.wordProfile (β₁ ω) ∈ Sp)
    (hL : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ →
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)))) :
    ∃ (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (F : Set Ω) (types : Set WordType) (pc : Ω → ℝ≥0 → ℂ) (tL : Ω → ℝ≥0)
      (relLife : Ω → ℝ≥0∞) (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
      (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
        (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
      (Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K ∧ (∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) ∧
      Measurable[lineFiltC P 𝓖 0] x₀ ∧ MeasurableSet[lineFiltC P 𝓖 0] F ∧
      (∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
        (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        ∃ m, (S.ver m).a t ω < S.V m ω) ∧
      types.Countable ∧
      (∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types) ∧
      (∀ w ∈ types, ∀ᵐ ω ∂P,
        ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
        ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w) ∧
      (∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch
        (driverCode (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
            Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ F → (driverOf (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) hκ
        (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
          Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω) ∧
      (∀ᵐ ω ∂P, ω ∈ F → ω ∈ Gℓ) ∧
      (∀ᵐ ω ∂P, ω ∈ F → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) ∧
      (∀ᵐ ω ∂P, ω ∈ F → x₀ ω = Nc.entryRead (fillH (K ω))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ))) ∧
      Measurable[stageMarks κ b jumps E u l k (ℓ + 1)] Dr ∧ (∀ ω, IsRegularDriver (Dr ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ F → recOf ⊤ (Dr ω) = recOf ⊤
        (driverOf (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) hκ (-(Real.pi / 2))
          (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
            Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))) ∧
      (∀ᵐ ω ∂P, ω ∈ F → Lv.wordProfile (β₁ ω) ∈ Sp) ∧
      (∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hA := stmt6Sets_of_rootSets hfam
  obtain ⟨hA₁m, -, -, -, -, -, -, -, hA₁c, -⟩ := hfam 0
  have h𝓗 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hlaw' := hlaw
  obtain ⟨-, -, -, -, -, -, -, hβ𝓜, hsort, hM0, hMb, -⟩ := hlaw'
  -- the premises of 6E from the law
  have hSG : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ → ω ∈ Gℓ := by
    filter_upwards [hcovL] with ω h1 hω using h1 hω.1 hω.2
  have hmean := Fq.hmean_of_law hh hu₀ h𝓗 hA₁m hA₁c hloc hlaw hSG
  have hA0 : ∀ᵐ ω ∂P, A₁ 0 ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        ℓ ω) ω := by
    filter_upwards [hA 0] with ω h1 using h1.1
  have hheight := Fq.hheight_of_law h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA0 hu₀ h𝓗 hA₁m
    hA₁c hloc hlaw hSG hL
  -- the types of the profiles
  set types : Set WordType := angleType κ (-(Real.pi / 2)) '' profileTypes κ Sp with htypesdef
  have htypes : types.Countable := (countable_profileTypes κ hSp).image _
  -- SB2LIFT's 6E for the law's word
  obtain ⟨K, x₀, pc, tL, relLife, F, hKm, hKc, hKp, hKF, hx₀, hF, hpc, htL, hent, hx₀e, hFae, hS⟩ :=
    Sx.sb2LowerStageVersionStatement6E h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu
      hlp hlθ hLw hleft ℓ 𝓖 A₁ A₂ h𝓖 hA β₁ types hβ₁s hsort htypes u₀ hu₀ hmean hheight
  have hFev : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := by
    filter_upwards [hFae] with ω h1 using h1.1
  have hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    filter_upwards [hFev] with ω h1 hω using (h1 hω).1.2
  have hcover : ∀ᵐ ω ∂P, ω ∈ F →
      angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types := by
    filter_upwards [hFev, hprof] with ω h1 h2 hω using
      angleWordType_shift_mem κ _ _ (h2 (h1 hω).1.1 (h1 hω).1.2)
  obtain ⟨S, hcl, hleAll, hlife6⟩ := hS hcover
  have hseed := Ci.hseed_of_le_thr S (hleAll 0)
  -- K2 at the stage
  have hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Gℓ := by
    filter_upwards [hFev, hcovL] with ω h1 h2 hω using h2 (h1 hω).1.1 (h1 hω).1.2
  have hlawK := Fo.ae_lawx_of_mvLaw hh.1 h𝓗 hlaw hKm hKc hKp hx₀ hF hFG hKF
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ𝓜)
  have hk2 := Ce.ae_k2_tail h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft hℓ hu₀ h𝓖 hfam S hKm hKc
    hKp hKF hx₀ hF hpc htL hent hFae hc hsort hlawK hmean htypes hcover hM0 hMb (hleAll 0) hlife6
  -- the chain facts and the record
  obtain ⟨-, hlc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hKm hKc hKp hx₀
  have hZm : Measurable fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => h𝓗 _ (hdom z))
      (fun z => (hfwd z).mono h𝓗 le_rfl) (fun z => (hliftm z).mono h𝓗 le_rfl) hlc hh.1 1 0 (chiC κ)
  have hcont := ae_continuousOn_driverOf (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hκ hκ4
    (-(Real.pi / 2)) h𝓗 hc hZm hF hlawK
  have hfacts := ae_chainFacts_tail (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h12 h13 h12₀ h13₀
    hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hA hKc hKp hKF hent hFev htypes hcover S hcl (hleAll 0) hk2 hcont
  have hFfill : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    filter_upwards [hKF, hA0, hFl, Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ]
      with ω h1 h2 h3 h4 hω
    rw [h1 hω, h2]; exact (h4 (h3 hω)).2.2.2.2
  have hFlpos : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := by
    filter_upwards [hFev] with ω h1 hω using ⟨(h1 hω).1.2, (h1 hω).2.2⟩
  obtain ⟨Dr, hDrm, hDrreg, hDreq⟩ := tail_record (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)
    h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hwℓ hu₀ (h𝓖 0) (hβ𝓜.mono h𝓗 le_rfl) hKc hKp hx₀ hF hFlpos
    hFfill hfacts
  refine ⟨K, x₀, F, types, pc, tL, relLife, hKc, hKp, S, Dr, hKm, hKF, hx₀, hF, hFl, hcl, htypes, hcover, hseed,
    ?_, ?_, hFG, hFev, hx₀e, hDrm, hDrreg, hDreq, ?_, hFae⟩
  · filter_upwards [hk2] with ω h1 hω using (h1 hω).1
  · filter_upwards [hk2] with ω h1 hω using (h1 hω).2
  · filter_upwards [hFev, hprof] with ω h1 h2 hω using h2 (h1 hω).1.1 (h1 hω).1.2

end InteractingSLE.Theorem14.SB.Cz
