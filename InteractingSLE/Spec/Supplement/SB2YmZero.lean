/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FsZero
import InteractingSLE.Spec.Supplement.SB2YmSeed

/-!
# The zero-lifetime step of the induction at `relOff = ℓ`

Packet PROVE-T14-SB2LIFT (round 37, decision D86, CANON's handoff R8.2 option (A)). F3LAW's `Fs.zero_piece` gives the
stage data at `ℓ + 2` on `C ∩ {B launches at ℓ with lifetime 0, relOff ≠ ℓ}`. CANON's R8.2 finds that no piece of
the step covers `{relOff = ℓ, ¬ ZeroRoot, ζ_ℓ = 0}` (a zero-lifetime piece launched at the restart mark `R`). This
file widens the zero piece to that event.

* **`ae_leftAdm_zero_root`**: the left heights at `ℓ + 2` there, seeded at `R`. The base's root facts at `R` (a free
  ray, the word admissible left of `R`'s entry) give, through `Fo.leftAdm_entry_mono`:
  * B's point at `ℓ` is left of `R` (`Sx.ae_root_seed`);
  * `R` has entered by `ℓ + 1`, so the new seed `stPt (run (ℓ + 2))` is right of `R`;
  * the points between the seeds are admissible (`Fo.ae_free_between_seeds`), and the hull does not change
    (`Qx.stageSet_succ_succ_eq_of_zero`).
* **`zero_piece_root`**: `Fs.zero_piece` verbatim on `C ∩ {launch at ℓ, ζ_ℓ = 0, ¬ (relOff = ℓ ∧ ZeroRoot)}`, with the
  same word and profiles. The law is still `Fl.mvLaw_succ_succ_zero`. The left heights use `Fo.ae_leftAdm_zero` off
  `relOff = ℓ` and `ae_leftAdm_zero_root` at `relOff = ℓ`. The extra input `hLR` is the root-facts clause of CANON's
  `Cz.StageInv ℓ`, verbatim.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sz

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Supp8.Q3Stop Lv Lk Mf Ms Fs

/-- **D34's left heights through a zero-lifetime stage at `relOff = ℓ`**, almost surely: off a zero root, when B's
piece at `ℓ` has lifetime `0` and B launches again at `ℓ + 2`, the retained hull does not change, B's point at `ℓ` is
left of `R` (`ae_root_seed`) and `R` has entered by `ℓ + 1`, so the new seed is right of `R`; the word, admissible
left of `R`'s entry, stays admissible left of the new entry (`Fo.leftAdm_entry_mono` over the admissible points
between the seeds, `Fo.ae_free_between_seeds`). -/
theorem ae_leftAdm_zero_root (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
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
    {A₁ A₁' : Ω → Set ℂ} (hA : ∀ᵐ ω ∂P, A₁ ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω)
    (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω)
    {β : Ω → BoundaryWord} :
    ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ →
      ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 →
      IsHPHull (A₁ ω) → Fm.FreeRight (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)) →
      Fm.LeftAdm κ (β ω) (Fm.entry (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω))) →
      (∀ x r : ℝ, 0 < r → Disjoint (ball (x : ℂ) r) (A₁ ω) → x ∉ jumps →
        Fm.bdryVal (A₁ ω) x ∉ (β ω).jumps → (β ω).fn (Fm.bdryVal (A₁ ω) x) = b x) →
      Fm.LeftAdm κ (β ω) (Fm.entry (A₁' ω) (stPt (ExplState.run κ b jumps
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)))) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Er := StagedReg.regFam E w with hEr
  by_cases hℓ2 : ℓ + 2 < w.2.2.length
  swap
  · exact Eventually.of_forall fun ω _ hl2 => absurd (SB.Nc.flow_of_launch hl2).1 hℓ2
  filter_upwards [SB.Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft, hA, hA',
    hrun w hwbc, SB.Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hℓ2,
    Qx.ae_walkChainFacts_regFam h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER,
    Fo.ae_free_between_seeds h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA',
    Sx.ae_root_seed h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft]
    with ω hg hAω hA'ω hrω hgeo2 hWC hfree hseed hev hl2 hoff hZ h0 hHP hFR hLR hread
  have hgω := hg hev.1
  -- the hull does not change
  have hl' : (ExplState.run κ b jumps w (fun j => Er j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hrω]; exact hev.2
  obtain ⟨old, q₀, q₁, hS⟩ := Qx.pieceSimpleAt_of_chainFacts hWC hl'
  have h0' : (Er ℓ ω).2 = 0 := by rw [hEr, StagedReg.regFam, StagedReg.regHist_snd]; exact h0
  have hst := Qx.stageSet_succ_succ_eq_of_zero (κ := κ) (b := b) (jumps := jumps) (E := Er) hl' hS h0'
  obtain ⟨-, hlen⟩ := Qx.walk_instr_of_launch hl'
  have hlen2 : ℓ + 2 ≤ w.2.2.length := hℓ2.le
  have hAA : A₁' ω = A₁ ω := by
    rw [hA'ω, hAω]
    unfold Mf.fillVer
    beta_reduce
    rw [WalkInf.stageSet_capSpec_of_le hlen2 ω le_rfl, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, hst]
  rw [hAA]
  -- the seeds: B's point at `ℓ` is left of `R`, the next seed right of it
  obtain ⟨hpt, hRin⟩ := hseed hev hoff hZ
  have hRp' : realMax (upperPrefix κ b jumps E u l k ω) ≤
      stPt (ExplState.run κ b jumps w (fun i => E w i ω) (ℓ + 2)) := by
    have hmem : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈ SB.Nc.retX κ b jumps E u l k (ℓ + 2) ω :=
      Or.inr (WalkIntRunChron.prefixPhysSet_mono w _ (by omega : ℓ + 1 ≤ ℓ + 2) hRin)
    obtain ⟨hXc2, -, -, -, -⟩ := hgeo2 hl2
    have hmax2 := SB.Nc.realMax_retX_eq hgω hl2 (lt_of_eq_of_lt hoff (by omega)) (SB.Nc.even_of_launch hl2)
    rw [← hmax2]
    exact SB.Lx.le_realMax_of_mem hXc2 hmem
  refine Fo.leftAdm_entry_mono (b := b) (jumps := jumps) hHP hFR hRp' hLR (fun x hx hxJ hyJ => ?_)
    (fun x hx hxp' hxJ => ?_)
  · obtain ⟨r, hr, hd⟩ := hFR x hx
    exact hread x r hr hd hxJ hyJ
  · obtain ⟨r, hr, hd⟩ := hFR x hx
    exact hfree hev hl2 x (lt_of_le_of_lt hpt hx) hxp' ⟨r, hr, by rw [hAA]; exact hd⟩ hxJ

/-- **The zero-lifetime step of the induction, at `relOff = ℓ` as well** (Theorems 1.2–1.3). F3LAW's
`Fs.zero_piece` with its event `relOff ≠ ℓ` widened to `¬ (relOff = ℓ ∧ ZeroRoot)`, given the base's root facts at
`R` for the stage word (`hLR`, as CANON's invariant `Cz.StageInv` carries them). -/
theorem zero_piece_root (h12p : Theorem12ParamStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
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
    (hst : StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S)
    -- the base's root facts at `R` for the stage word (CANON's `Cz.StageInv`)
    (hLR : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
        Fm.LeftAdm κ (β ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) :
    StageLawOn κ b jumps P h E u l k (ℓ + 2) 𝓖' A₁'
      (C ∩ {ω | (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∧
        ¬ (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
          ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))}) β S := by
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
  have hzr := ae_leftAdm_zero_root h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hA hA'
    (β := β)
  refine ⟨⟨K, G₂, Y, M, hlaw₂, ?_⟩, hβm.mono (WalkLaw.aeSigma_mono (P := P) (Mz.stageMarks_mono (by omega)))
    le_rfl, hS, ?_, ?_⟩
  · filter_upwards [hcov, hcov₂] with ω e1 e2 hω hl2
    exact e2 (e1 hω.1 hω.2.1) hω.2.1 hω.2.2.1 hl2
  · filter_upwards [hprof] with ω e1 hω _ using e1 hω.1 hω.2.1
  · filter_upwards [hL, hzero, hread, hcov, hlaw.2.2.2.2.1, hLR, hzr] with ω eL ez er ec ef eR ezr hω hev2 hoff2
    obtain ⟨hC, hlℓ, hz, hne⟩ := hω
    have hev : ω ∈ stageEvent κ b jumps E u l k ℓ := ⟨hev2.1, hlℓ⟩
    have hG : ω ∈ G := ec hC hlℓ
    have hHP : IsHPHull (A₁ 0 ω) := ef hG ▸ Mo.isHPHull_fillH hlaw.2.1 hlaw.2.2.1 ω
    by_cases hro : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ
    · -- the new case: a mark or piece entry at `relOff = ℓ`, seeded at `R`
      have hZ : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) := fun hZ => hne ⟨hro, hZ⟩
      obtain ⟨hFR, hLadm⟩ := eR hev hro.ge
      exact ezr hev hev2.2 hro hZ hz hHP hFR hLadm (fun x r hr hd hxJ hyJ => er hG hHP x r hr hd hxJ hyJ)
    · have he1 := Nc.even_of_launch hlℓ
      have he2 := relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      have hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ := by omega
      exact (ez hev hev2.2 hoff hz (eL hC hev hoff) (fun x r hr hd hxJ hyJ => er hG hHP x r hr hd hxJ hyJ)).2.2

end InteractingSLE.Theorem14.SB.Sz
