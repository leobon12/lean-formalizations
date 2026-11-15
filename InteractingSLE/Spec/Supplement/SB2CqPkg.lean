/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CqTail
import InteractingSLE.Spec.Supplement.SB2CqCont
import InteractingSLE.Spec.Supplement.SB2CvOff
import InteractingSLE.Spec.Supplement.SB2CzTail
import InteractingSLE.Spec.Supplement.SB2FlZero

/-!
# (P4) at a tail stage in the package's form

Packet PROVE-SB2-CANON, round 5 ((P4) at the tails; D76: (P1) moves to F3LAW, which consumes (P4) as CANON states it).
**`pkgTail_of_k2`**: at a tail stage `ℓ` (a flow instruction), from

* the retained law at `ℓ` (`Fl.MvLaw` given `𝓜`, with its word `β`, covering B's launches, with `A = fill (A ∪ B_{<ℓ})`
  on launches) — the induction's own object;
* the objects of `Cz.SB2LowerStageVersionStatement6` at `ℓ` for the word `β` (the line family `𝓖, A₁, A₂` in the
  statement's premise form, e.g. `Cs.exists_jointLineFamily`'s);
* K2's inputs and outputs at `ℓ` used here: the word `shiftW x₀ β` measurable for `lineFiltC P 𝓖 0`, its conditional
  law under `lineFiltC P 𝓖 0` on the live event (`Cj.ae_k2_stage`'s `hc`, `hlaw`), and `Cj.ae_k2_stage`'s
  conclusion —

the package's last four clauses (`Cz.SB2LowerStagePkgStatement`): an offset `x₀'` measurable for the completed
retained past ((P2), `exists_offset_stageMarks`), a tail event `T` of `Ms.stageMarks (ℓ + 1)` ((P3),
`exists_eq_of_measurableSet_inf_aeSigma`) covering almost every tail launch of positive lifetime, and almost surely on
`T` at a launch of positive lifetime the chain facts of the canonical driver of `(shiftW x₀' β, field in
Mo.hullChart (fill K') x₀')` with the law's hull `K'` ((P4): `ae_chainFacts_tail`, `ae_continuousOn_driverOf`,
moved to the law's objects by round 1's `chainFacts_congr`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms Mf WalkSide Lk Lu Mx Mz
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **(P4) at a tail stage, with (P2) and (P3), in the package's form.** See the module docstring. -/
theorem pkgTail_of_k2 (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    -- the retained law at `ℓ`
    {A K' : Ω → Set ℂ} {G' : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    (hlaw : @Fl.MvLaw κ Ω 𝓜 mΩ _ P _ h A K' G' Y β M)
    (hcovL : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      ω ∈ G')
    (hAL : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠
      none →
      A ω = fillH (Nc.retX κ b jumps E u l k ℓ ω))
    -- the line family
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
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
    -- Statement6's objects for the word `β`
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {relLife : Ω → ℝ≥0∞} {F : Set Ω}
    (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hent : ∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (Nc.retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω)))
    (hFae : ∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ
          ∧ 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    {types : Set WordType} (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω)) ∈ types)
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) types pc tL
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2
      → ∃ m, (S.ver m).a t ω < S.V m ω)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W
        (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) w)
        (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) w) ω)
    -- K2's inputs and outputs at `ℓ`
    (hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β ω))
    (hlawK : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).jumps)
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F →
      (∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω),
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω),
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω) :
    ∃ (x₀' : Ω → ℝ) (T : Set Ω),
      Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] x₀' ∧
      MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] T ∧
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (lowerD b jumps E ω) + 2 ≤ ℓ →
        (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ T) ∧
      ∀ᵐ ω ∂P, ω ∈ T → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none →
        (lowerD b jumps E ω ℓ).2 ≠ 0 →
        Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
          (fun ω => BoundaryWord.shiftW (x₀' ω) (β ω)) x₀' hlaw.2.1 hlaw.2.2.1 ω := by
  classical
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  -- the σ-algebras
  have h𝒮₁ : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 (ℓ + 1))
  have h𝒮 : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ := (Mz.stageMarks_mono (Nat.le_succ ℓ)).trans h𝒮₁
  have hG0 : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ
          := by rw [← h𝓖 0]; exact 𝓖.le 0
  have hx₀' : Measurable[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) P] x₀ := by
    rw [← h𝓖 0]; exact hx₀
  have hF' : MeasurableSet[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) P] F := by
    rw [← h𝓖 0]; exact hF
  -- (P2) the offset and (P3) the tail event
  obtain ⟨x₁, hx₁m, hx₁e⟩ := exists_offset_stageMarks E u l k ℓ hℓ hwℓ hG0 hx₀'
  obtain ⟨T, hTm, hFT⟩ := exists_eq_of_measurableSet_inf_aeSigma
    (capPast_le_stageMarks_succ E u l k ℓ hℓ hwℓ) hF'
  refine ⟨x₁, T, hx₁m.mono (le_inf h𝒮 (le_aeSigma _ P)) le_rfl, hTm, ?_, ?_⟩
  · filter_upwards [hFae, hFT.mem_iff] with ω h1 h2 hup hl hoff hpos
    exact h2.1 (h1.2 ⟨⟨hup, hl⟩, lt_of_lt_of_le (Nat.lt_add_of_pos_right two_pos) hoff, pos_iff_ne_zero.2 hpos⟩)
  -- (P4) the chain facts
  have hFae' : ∀ᵐ ω ∂P, ω ∈ F → (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ
          ∧ 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) := by
    filter_upwards [hFae] with ω h1 using h1.1
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  obtain ⟨-, hlc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hKm hKc hKp hx₀
  have hZm : Measurable fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => hle0 _ (hdom z))
      (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc hh.1 1 0 (chiC κ)
  have hcont := ae_continuousOn_driverOf h12p h13 hκ hκ4 (-(Real.pi / 2)) hle0 hc hZm hF hlawK
  have hfacts := ae_chainFacts_tail h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hA hKc hKp
    hKF hent hFae' htypes hcover S hcl hle hK2 hcont
  have hgood := ae_stageGoodAt_retX h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hFae' hent
  filter_upwards [hFT.mem_iff, hfacts, hgood, hKF, hA 0, hx₁e, hcovL, hAL, hlaw.2.2.2.2.1, hrun' _ hw]
    with ω hFTω hf hg hKω hA0 hx₁ω hcov hAω hK'A hrw hT hl hpos
  have hωF : ω ∈ F := hFTω.2 hT
  have hfillK : fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    rw [hKω hωF, hA0.1]; exact fillVer_first_eq (hg hωF) _
  have hfill : fillH (K' ω) = fillH (K ω) := by rw [hK'A (hcov hl), hAω hl, hfillK]
  -- the offsets agree
  have hlr : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
      none := by
    rw [hrw (ℓ + 1)]; exact hl
  have hlife : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2
    = (lowerD b jumps E ω ℓ).2 := by
    have e1 := Fl.retained_lifetime_of_launch hlr
    have e2 := Fl.retained_lifetime_of_launch hl
    rw [hrw (ℓ + 1)] at e1
    exact e1.symm.trans e2
  have hx : x₀ ω = x₁ ω := hx₁ω hlr (by rw [hlife]; exact hpos) (hreg' _ ℓ ω).2.1
  exact chainFacts_congr h12p hκ E u l k ℓ hfill (by rw [hx]) hx.symm (hf hωF)

end InteractingSLE.Theorem14.SB.Cz
