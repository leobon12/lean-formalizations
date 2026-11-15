/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FuCore
import InteractingSLE.Spec.Supplement.SB2GjMain
import InteractingSLE.Spec.Supplement.SB2CaStmt

/-!
# The entrance law at the root, PROVED (D85, (A2))

Worker PROVE-SB2-F3LAW (round 8, D85). **`ae_entranceLaw_root`**: CONDFIN's (A2) conclusion — the retained law at a
flow stage `ℓ` survives adding the root event to the time-`0` marks (the kernel law of `Yℓ` given
`Ca.entrMarks P 𝓖 F'` is, almost surely on `F'`, the GFF with data `β₁`) — from Theorems 1.2–1.3 and the data of the
retained-law invariant at `ℓ` (CANON's `StageInv ℓ`): the word is measurable for the completed stage marks, the law's
event covers the base region `stageEvent ℓ ∩ {ℓ ≤ relOff}`, the word's profiles on the root event lie in a countable
set, and the base's root facts at `R` hold on the root event. **`SB2LowerRootEntranceLawFStatement`** is CONDFIN's
`Ca.SB2LowerRootEntranceLawStatement` with these four premises; **`sb2LowerRootEntranceLawFStatement`** proves it.

Proof (no new probabilistic input):
* NOJUMP's 9F (`Nf.sb2LowerRootVersionStatement9F`) at the root's line family (CONDFIN's `Cx.exists_rootLineFamily`),
  its premises from the law (`Fq.hmean_of_law`, `ae_heightClause_rootR`) and its types from the profiles;
* K2's (S) at the root from the line family (`Cr.hasSafeLaw_hasSafeMembers_of_rootLines`, the line mean
  `Cy.hmean_root_obj` exactly as in GEOM2's `Gj.sb2LowerRootIdentStatementX_of_visit`);
* (S) at relative time `0`: the law given the entrance σ-algebra (`Fu.ae_condExp_entrance`); down to the entrance marks
  (`Fu.ae_condExp_sup_singleton`), the kernel law, the chart back to offset `0` (`Fu.ae_isGFF_hullChart_unshift`) and
  the law's own field `Yℓ`.

Why the four premises (CONDFIN's statement has none of them): NOJUMP's versions exist only for a word with countably
many types on the root event and F3's mean identity on the whole base region (9F's premises), and the heights clause
needs the root facts. Without them the root event is decided only by B's head inside `fill (A₁ 0)` at the random
entrance time, and no landed local-set statement covers that time.

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

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Mf Ms Lu Mz Lk Nd Fm Fp

/-- **D34's clause on the root event, with the root facts read on the root event** (GEOM2's `Gj.ae_heightClause_rootB`
with `hroot` on `rootEv` instead of on an event covering the base region). -/
theorem ae_heightClause_rootR {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} (k ℓ : ℕ)
    {A₁ : Ω → Set ℂ} {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hAm : Measurable[mΩ, hittingSigma] A₁) (hloc : IsLocalSet A₁ (WholeField.centredField h u₀) P)
    {β₁ : Ω → BoundaryWord} (hβs : ∀ ω, (β₁ ω).IsSorted)
    (hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens,
      LocalSets.IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
          ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) -
                QuantumZipper.chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z) (H \ A₁ ω))
    (hroot : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → IsHPHull (A₁ ω) ∧
      FreeRight (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β₁ ω) (entry (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)))) :
    ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      Nb.HeightClause κ b jumps (A₁ ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  filter_upwards [Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hAm hloc hg₁, hmean g₁ hg₁, hg₁.2.1, hroot]
    with ω hw hid hharm hrω hωr
  obtain ⟨hHP, hfree, hL⟩ := hrω hωr
  obtain ⟨hev, hoff, -, -⟩ := hωr
  obtain ⟨v, hv, hrep⟩ := hharm
  exact heightClause_of_meanIdentity hκ hHP hfree (hβs ω) hu₀ (hid hev hoff.ge v hv hrep) (hw v hv hrep) hL

/-- **The entrance law at the root** (D85, (A2); Theorems 1.2–1.3 and the retained-law invariant's data at `ℓ`). See
the module docstring. -/
theorem ae_entranceLaw_root (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (k : ℕ) (hu : u ≤ 0) (hlp : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (ℓ : ℕ) {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ}
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω)
    {Kℓ : Ω → Set ℂ} {Gℓ : Set Ω} {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ M)
    -- the invariant's data at `ℓ`
    (hβs : Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁)
    (hbase : ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ Gℓ)
    {Sp : Set WordProfile} (hSp : Sp.Countable)
    (hprof : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → wordProfile (β₁ ω) ∈ Sp)
    (hLR : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β₁ ω) (entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))))
    -- the root event
    {F' : Set Ω} (hF'm : MeasurableSet F') (hF' : ∀ᵐ ω ∂P, ω ∈ F' ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F' →
      IsGFFWithBoundaryData (condExpKernel P (Ca.entrMarks P 𝓖 F') ω₀) Yℓ (β₁ ω₀).fn (β₁ ω₀).jumps := by
  classical
  set h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hℓ, -⟩ := List.getElem?_eq_some_iff.1 hwℓ
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  -- the root's line sets (CONDFIN's family, over the same filtration `𝓖`)
  obtain ⟨-, A₁x, A₂, A₂J, -, hfam⟩ := Cx.exists_rootLineFamily h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ hu₀
  have hA9 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁x t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E w) ℓ ω) ω ∧
      A₂J t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E w) (ℓ + 1) ω)
        ω := fun t => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, -, -, -, -, -, h16, -⟩ := hfam t
    filter_upwards [h10, h16] with ω h1 h2 using ⟨h1.1, h2⟩
  have hA₁x : ∀ᵐ ω ∂P, A₁x 0 ω = A₁ 0 ω := by
    filter_upwards [hA9 0, hA 0] with ω h1 h2 using h1.1.trans h2.symm
  -- the law, read for the family's retained set
  obtain ⟨hKℓm, hKℓc, hKℓp, hGm, hfill, hYm, hYt, hβm, hβsort, hM0, hMb, hlawY⟩ := hlaw
  have hfill' : ∀ᵐ ω ∂P, ω ∈ Gℓ → fillH (Kℓ ω) = A₁x 0 ω := by
    filter_upwards [hfill, hA₁x] with ω h1 h2 hω using (h1 hω).trans h2.symm
  have hmv : Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁x 0) Kℓ Gℓ Yℓ β₁ M :=
    ⟨hKℓm, hKℓc, hKℓp, hGm, hfill', hYm, hYt, hβm, hβsort, hM0, hMb, hlawY⟩
  -- NOJUMP's 9F premises
  obtain ⟨hAm, -, -, hAl, -, -, -, -, hAc, -, -⟩ := hfam 0
  have hloc := Gj.hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ h𝓖 hfam
  have hmeanS := Fq.hmean_of_law hh hu₀ ((lineFiltC P 𝓖).le 0) hAm hAc hloc hmv
    (S := {ω | ω ∈ Ms.stageEvent κ b jumps E u l k ℓ ∧
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)})
    (hbase.mono fun ω h hω => h hω.1 hω.2)
  have hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁x 0) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁x 0 ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁x 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => (β₁ ω).mean ((Mo.hullChart (A₁x 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁x 0 ω) 0).2.2 z)
            (H \ A₁x 0 ω) := fun g₁ hg₁ =>
    (hmeanS g₁ hg₁).mono fun ω h hst hoff => h ⟨hst, hoff⟩
  have hroot : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → IsHPHull (A₁x 0 ω) ∧
      FreeRight (A₁x 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β₁ ω) (entry (A₁x 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))) := by
    filter_upwards [hLR, hA₁x, hfill', hbase] with ω h1 h2 h3 h4 hω
    have hG : ω ∈ Gℓ := h4 hω.1 hω.2.1.ge
    refine ⟨?_, ?_⟩
    · rw [← h3 hG]
      exact Mo.isHPHull_fillH hKℓc hKℓp ω
    · rw [h2]
      exact h1 hω
  have hheight := ae_heightClause_rootR hκ hh k ℓ hu₀ hAm hAl hβsort hmean hroot
  -- the countable word types and NOJUMP's root statement
  set types : Set WordType := Lv.angleType κ (-(Real.pi / 2)) '' Lv.profileTypes κ Sp with htypesdef
  have htypes : types.Countable := (Lv.countable_profileTypes κ hSp).image _
  obtain ⟨K, x₀, pc, relLife, FB, Fr, hKm, hKc, hKp, hKF, hx₀m, hFBm, hpc, hent, -, hFBiff, hFriff, hFrB, hS⟩ :=
    Nf.sb2LowerRootVersionStatement9F h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k
      hu hlp hlθ hL hleft ℓ 𝓖 A₁x A₂J h𝓖 hA9 β₁ types hβs hβsort htypes u₀ hu₀ hmean hheight
  have hcover : ∀ᵐ ω ∂P, ω ∈ Fr →
      angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types := by
    filter_upwards [hFriff, hprof] with ω h1 h2 hω
    exact Lv.angleWordType_shift_mem κ _ (x₀ ω) (h2 (h1.1 hω))
  obtain ⟨S, hz, hre, -, hle, -⟩ := hS hcover
  -- K2's inputs at the root (as in GEOM2's `Gj.sb2LowerRootIdentStatementX_of_visit`)
  obtain ⟨hBm, hBc, hBl, hlocB⟩ := Cx.k2Inputs_of_rootSets h𝓖 hfam
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀m.prodMk hβm)
  have hF : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E w i ω) = ℓ ∧
      ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) :=
    hFriff.mono fun ω h hω => ⟨(h.1 hω).1, (h.1 hω).2.1, (h.1 hω).2.2.1⟩
  have hA₁eq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁x t ω = A₁x 0 ω := fun t => by
    filter_upwards [hA9 t, hA9 0] with ω ht h0
    rw [ht.1, h0.1]
    congr 1
    funext ω'
    rw [WalkInf.stageSet_capSpec_of_le hℓ.le ω' le_rfl, WalkInf.stageSet_capSpec_of_le hℓ.le ω' le_rfl]
  have hA₁K : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr → A₁x t ω = fillH (K ω) := fun t => by
    filter_upwards [hA₁eq t, hKF, hFrB] with ω h1 h2 h3 hω
    rw [h1, h2 (h3 hω)]
  have hgood := Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  have hgeo := Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  obtain ⟨-, -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hKret : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = fillH (upperPrefix κ b jumps E u l k ω ∪
      SB.prefixPhysSet κ b jumps w (fun i => E w i ω) ℓ) := by
    filter_upwards [hKF, hFrB, hFriff, hA9 0, hgeo, hrun w hw, hrun _ hsu] with ω h1 h2 h3 h4 h5 h6 h7 hω
    have hl := (h3.1 hω).1.2
    rw [h1 (h2 hω), h4.1]
    exact Cz.fillVer_first_eq_of hl h6 h7 (h5 hl).1 _
  have hx₀' : ∀ᵐ ω ∂P, ω ∈ Fr → IsRightEntryChart (upperPrefix κ b jumps E u l k ω ∪
      SB.prefixPhysSet κ b jumps w (fun i => E w i ω) ℓ) (realMax (upperPrefix κ b jumps E u l k ω ∪
      SB.prefixPhysSet κ b jumps w (fun i => E w i ω) ℓ)) ((Mo.hullChart (fillH (upperPrefix κ b jumps E u l k ω ∪
      SB.prefixPhysSet κ b jumps w (fun i => E w i ω) ℓ)) 0).recenter (x₀ ω)) := by
    filter_upwards [hent, hFriff, hgood] with ω h1 h2 h3 hω
    obtain ⟨hst, -, -, hentr⟩ := h2.1 hω
    have hrm := Gj.realMax_retX_root (h3 hst.1) hst.2 hentr
    have h1' := h1 hω
    rw [← hrm] at h1'
    exact h1'
  have hzero : ∀ m, ∀ᵐ ω ∂P, ω ∈ Fr → (S.ver m).a (Na.rootEntry κ b jumps E u l k ℓ ω) ω = 0 := fun m => by
    filter_upwards [hz m, hre] with ω h1 h2 hω
    exact h1 hω _ (h2 hω).le
  have hFBs : ∀ᵐ ω ∂P, ω ∈ FB → ω ∈ Ms.stageEvent κ b jumps E u l k ℓ ∧
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E w i ω) :=
    hFBiff.mono fun ω h hω => ⟨(h.1 hω).1, (h.1 hω).2.1⟩
  have hF3 := Gj.hF3_of_premiseB hh hℓ.le hu₀ (A₁ := A₁x) (fun t => (hfam t).1)
    (fun t => (hfam t).2.2.2.2.2.2.2.2.1) (fun t => (hfam t).2.2.2.1) (fun t => (hA9 t).mono fun ω h => h.1)
    (K := K) (x₀ := x₀) (β₁ := β₁) hFrB hKF hFBs hmean
  have hmeanK := Cy.hmean_root_obj h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft hu₀ h𝓖 hfam S hKc
    hKp (fun ω => BoundaryWord.isSorted_shiftW (hβsort ω) _) hF hA₁K hKret hx₀' hpc (fun ω => rfl) hzero hF3
  -- K2's (S) at the root, on every type cell
  obtain ⟨-, hliftc, hlift, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hKm hKc hKp hx₀m
  obtain ⟨hlocC, g, hg⟩ := Mt.lineSets_inputs hh hu₀ hBm hBc hBl hlocB
  have hseed := Cr.hseed_of_le_thr_root S (hle 0)
  have hsafe : ∀ wt ∈ types, HasSafeLaw κ (typedRhoL wt) (typedRhoR wt) P (S.ver 0).𝓗
      (seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) Fr wt) (S.V 0) (S.ver 0).W
      (geomLW (S.ver 0).W (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) wt))
      (geomRW (S.ver 0).W (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) wt))
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
        (h ω)) := fun wt hwt => by
    have h2 := (Cr.hasSafeLaw_hasSafeMembers_of_rootLines hh hu₀ (S.ver 0) hwt hc (Mu.isConformal_canon x₀ hKc hKp)
      hliftc hlift hdom hfwd hliftm (fun t ω => A₁x t ω ∪ A₂J t ω) hBm hBc hlocC
      (fun t => (S.ver 0).hull wt hwt t) g hg (hmeanK g hg 0 wt hwt)).1
    rw [S.Λ_eq 0 wt] at h2
    exact h2
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hHm : Measurable fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => hle0 _ (hdom z))
      (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hliftc hh.1 1 0 (chiC κ)
  have hsort' : ∀ ω, (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).IsSorted := fun ω =>
    BoundaryWord.isSorted_shiftW (hβsort ω) _
  have hent0 := fun φ => ae_condExp_entrance hκ S hc hsort' (Mu.isConformal_canon x₀ hKc hKp) hHm htypes hcover
    hseed hsafe φ
  -- down to the entrance marks
  have hF'Fr : ∀ᵐ ω ∂P, ω ∈ F' ↔ ω ∈ Fr := by
    filter_upwards [hF', hFriff] with ω h1 h2 using h1.trans h2.symm
  have h𝒢 : Ca.entrMarks P 𝓖 F' ≤ mΩ :=
    sup_le hle0 (MeasurableSpace.generateFrom_le fun t ht => by rw [mem_singleton_iff.1 ht]; exact hF'm)
  have hF'𝒢 : MeasurableSet[Ca.entrMarks P 𝓖 F'] F' :=
    le_sup_right (a := lineFiltC P 𝓖 0) _ (MeasurableSpace.measurableSet_generateFrom (mem_singleton F'))
  have hgiven : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ F' →
      P[fun ω' => Complex.exp (Complex.I *
        (Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω') 1 0 (chiC κ) (h ω') φ : ℂ)) |
        Ca.entrMarks P 𝓖 F'] ω = gaussCF (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) φ := fun φ =>
    ae_condExp_sup_singleton ((S.ver 0).𝓗.le 0) (S.ver 0).marks_le (S.ver 0).root_meas hF'm hF'Fr
      (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply φ).comp hHm))
      ((Restart.measurable_gaussCF φ).comp hc).stronglyMeasurable
      (Integrable.of_bound ((((Restart.measurable_gaussCF φ).comp hc).mono hle0 le_rfl).aestronglyMeasurable) 1
        (Eventually.of_forall fun ω => Restart.norm_gaussCF_le _ φ)) (hent0 φ)
  have hlawx := Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel h𝒢
    (Eventually.of_forall fun ω _ => hsort' ω) hHm hgiven
  -- the chart back to offset `0`, then the law's own field
  have hKΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j => hle0 _ (hKm n j)
  have hlaw0 := ae_isGFF_hullChart_unshift (β := β₁) h𝒢 hKc hKp (hx₀m.mono le_sup_left le_rfl)
    (Fl.measurable_canonField κ hh.1 hKc hKp hKΩ measurable_const) hlawx
  have heq : ∀ᵐ ω ∂P, ω ∈ F' →
      Chart.chartTransport (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω) 1 0 (chiC κ) (h ω) = Yℓ ω := by
    filter_upwards [hF'Fr, hFrB, hKF, hfill', hYt, hbase, hFriff] with ω h1 h2 h3 h4 h5 h6 h7 hω
    have hFr : ω ∈ Fr := h1.1 hω
    have hev := h7.1 hFr
    have hG : ω ∈ Gℓ := h6 hev.1 hev.2.1.ge
    have e : fillH (Kℓ ω) = fillH (K ω) := (h4 hG).trans (h3 (h2 hFr)).symm
    have h5' := h5 hG
    rw [e] at h5'
    exact (Fl.canonField_eq_of_transport (x₀ := fun _ => (0 : ℝ)) hKc hKp h5').symm
  exact Fl.ae_isGFF_congr_on h𝒢 hF'𝒢 hYm hlaw0 heq

/-- **Named statement (the entrance law at the root with the invariant's data; D85, (A2)).** CONDFIN's
`Ca.SB2LowerRootEntranceLawStatement` with four more premises after the law: the word is measurable for the completed
stage marks, the law's event covers the base region, the word's profiles on the root event lie in a countable set, and
the base's root facts at `R` hold on the root event (all four are in CANON's `StageInv ℓ`). -/
def SB2LowerRootEntranceLawFStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    ∀ (ℓ : ℕ) (𝓖 : Filtration ℝ≥0 mΩ) (A₁ : ℝ≥0 → Ω → Set ℂ),
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) →
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω) →
    ∀ (Kℓ : Ω → Set ℂ) (Gℓ : Set Ω) (Yℓ : Ω → DistOn upperHalfPlaneOpens) (β₁ : Ω → BoundaryWord) (M : ℝ),
      Fl.MvLaw κ (lineFiltC P 𝓖 0) P h (A₁ 0) Kℓ Gℓ Yℓ β₁ M →
      -- the retained-law invariant's data at `ℓ` (not in CONDFIN's form)
      Measurable[aeSigma (stageMarks κ b jumps E u l k ℓ) P] β₁ →
      (∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ Gℓ) →
      (∃ Sp : Set WordProfile, Sp.Countable ∧
        ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → wordProfile (β₁ ω) ∈ Sp) →
      (∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
        FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
        LeftAdm κ (β₁ ω) (entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)))) →
    ∀ F' : Set Ω, MeasurableSet F' → (∀ᵐ ω ∂P, ω ∈ F' ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ) →
      (∀ᵐ ω ∂P, ω ∈ F' → ω ∈ Gℓ) →
      ∀ᵐ ω₀ ∂P, ω₀ ∈ F' →
        IsGFFWithBoundaryData (condExpKernel P (Ca.entrMarks P 𝓖 F') ω₀) Yℓ (β₁ ω₀).fn (β₁ ω₀).jumps

/-- **`SB2LowerRootEntranceLawFStatement`, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerRootEntranceLawFStatement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerRootEntranceLawFStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft ℓ 𝓖 A₁ hwℓ h𝓖 hA Kℓ Gℓ Yℓ
    β₁ M hlaw hβs hbase hprof hLR F' hF'm hF' _
  obtain ⟨Sp, hSp, hprof⟩ := hprof
  exact ae_entranceLaw_root h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER k hu hlp hlθ hL hleft ℓ hwℓ h𝓖 hA hlaw hβs
    hbase hSp hprof hLR hF'm hF'

end InteractingSLE.Theorem14.SB.Fu
