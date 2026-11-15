/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FuPiece
import InteractingSLE.Spec.Supplement.SB2CcRoot

/-!
# The root branch of (P1)'s step, with no entrance-law input (D85, D86)

Worker PROVE-SB2-F3LAW (round 8, D85). **`sb2LowerRootEvBranchStatement`**: CANON's `Cz.SB2LowerRootEvBranchStatement`
from Theorems 1.2–1.3 alone. CANON's proof (`Cz.sb2LowerRootEvBranchStatement_of_entr`, copied) with its one use of the
entrance law changed: `Ca.root_piece_clock … hA2 …` becomes `Fu.root_piece_clockF … hA2F … hcov …`, where
`hA2F := Fu.sb2LowerRootEntranceLawFStatement` (PROVED) and `hcov` is the base word's cover of
`stageEvent ℓ ∩ {ℓ ≤ relOff}` (already in CANON's proof, from `Fs.sb2LowerBaseWordPStatement_of_thms`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
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
  WholeField Supp8.Q3Stop Lv Mf Ms Lu Mz Lk Nd Cz

/-- **The root branch in root-event form, PROVED** (Theorems 1.2–1.3; CANON's proof with the proved entrance law).
See the module docstring. -/
theorem sb2LowerRootEvBranchStatement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : Cz.SB2LowerRootEvBranchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hwℓ hwℓ₂ u₀ hu₀
    𝓖 A₁ A₂ A₂J h𝓖 hfam _ _ _ _ _ _ 𝓖' A₁' A₂B' A₂' h𝓖' hfam'
  classical
  set h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hvisω := Ro.sb2PosRootVisitStatement κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlθ hleft ℓ
  have hℓ : ℓ < w.2.2.length := (List.getElem?_eq_some_iff.1 hwℓ).1
  have hℓ₂ : ℓ + 2 < w.2.2.length := (List.getElem?_eq_some_iff.1 hwℓ₂).1
  -- the base word with its law at every stage (F3LAW)
  obtain ⟨β₁, hβm, ⟨Sp, hSp, hprof⟩, -, hbase⟩ := Fs.sb2LowerBaseWordPStatement_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4
    b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hX : Gj.BaseLawForX (κ := κ) b jumps P h E u l k ℓ β₁ := ⟨hβm, ⟨Sp, hSp, hprof⟩, hbase ℓ⟩
  obtain ⟨-, -, -, -, -, -, hmean, hheight⟩ :=
    Gj.premises9F_of_baseLawForX h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ hu₀ h𝓖 hfam hX
  have hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E w) ℓ ω) ω ∧
      A₂J t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E w) (ℓ + 1) ω)
        ω := fun t => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, -, -, -, -, -, h16, -⟩ := hfam t
    filter_upwards [h10, h16] with ω h1 h2 using ⟨h1.1, h2⟩
  -- the base law of the family at `ℓ` with its root facts
  obtain ⟨K', G', Y, M, hmv, hcov, hroot⟩ := hbase ℓ 𝓖 A₁ h𝓖 fun t => (hA t).mono fun ω h => h.1
  -- the countable word types
  obtain ⟨Sp, hSp, hprof⟩ := hX.2.1
  set types : Set WordType := Lv.angleType κ (-(Real.pi / 2)) '' Lv.profileTypes κ Sp with htypesdef
  have htypes : types.Countable := (Lv.countable_profileTypes κ hSp).image _
  have hβℋ : Measurable[lineFiltC P 𝓖 0] β₁ := hmv.2.2.2.2.2.2.2.1
  have hβm9 : Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β₁ :=
    hX.1.mono (le_sup_left.trans fun s hs => ⟨s, hs, EventuallyEq.rfl⟩) le_rfl
  have hsort : ∀ ω, (β₁ ω).IsSorted := hmv.2.2.2.2.2.2.2.2.1
  -- NOJUMP's root statement
  obtain ⟨K, x₀, pc, relLife, FB, Fr, hKm, hKc, hKp, hKF, hx₀m, hFBm, hpc, hent, hx₀e, hFBiff, hFriff, hFrB, hS⟩ :=
    Nf.sb2LowerRootVersionStatement9F h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k
      hu hlp hlθ hL hleft ℓ 𝓖 A₁ A₂J h𝓖 hA β₁ types hβm9 hsort htypes u₀ hu₀ hmean hheight
  have hcover : ∀ᵐ ω ∂P, ω ∈ Fr →
      angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types := by
    filter_upwards [hFriff, hprof] with ω h1 h2 hω
    exact Lv.angleWordType_shift_mem κ _ (x₀ ω) (h2 (h1.1 hω).1.1)
  obtain ⟨S, hz, hre, hcl, hle, hlife⟩ := hS hcover
  -- K2 at the root
  obtain ⟨hBm, hBc, hBl, hloc⟩ := Cx.k2Inputs_of_rootSets h𝓖 hfam
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀m.prodMk hβℋ)
  have hF : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E w i ω) = ℓ ∧
      ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) :=
    hFriff.mono fun ω h hω => ⟨(h.1 hω).1, (h.1 hω).2.1, (h.1 hω).2.2.1⟩
  have hA₁eq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = A₁ 0 ω := fun t => by
    filter_upwards [hA t, hA 0] with ω ht h0
    rw [ht.1, h0.1]
    congr 1
    funext ω'
    rw [WalkInf.stageSet_capSpec_of_le hℓ.le ω' le_rfl, WalkInf.stageSet_capSpec_of_le hℓ.le ω' le_rfl]
  have hA₁K : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ Fr → A₁ t ω = fillH (K ω) := fun t => by
    filter_upwards [hA₁eq t, hKF, hFrB] with ω h1 h2 h3 hω
    rw [h1, h2 (h3 hω)]
  have hgood := Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  have hgeo := Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  obtain ⟨-, -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hKret : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = fillH (upperPrefix κ b jumps E u l k ω ∪
      SB.prefixPhysSet κ b jumps w (fun i => E w i ω) ℓ) := by
    filter_upwards [hKF, hFrB, hFriff, hA 0, hgeo, hrun w hw, hrun _ hsu] with ω h1 h2 h3 h4 h5 h6 h7 hω
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
  have hF3 := Gj.hF3_of_premiseB hh hℓ.le hu₀ (A₁ := A₁) (fun t => (hfam t).1)
    (fun t => (hfam t).2.2.2.2.2.2.2.2.1) (fun t => (hfam t).2.2.2.1) (fun t => (hA t).mono fun ω h => h.1)
    (K := K) (x₀ := x₀) (β₁ := β₁) hFrB hKF hFBs hmean
  have hmeanK := Cy.hmean_root_obj h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft hu₀ h𝓖 hfam S hKc
    hKp (fun ω => BoundaryWord.isSorted_shiftW (hsort ω) _) hF hA₁K hKret hx₀' hpc (fun ω => rfl) hzero hF3
  -- the law of the canonical field given the line marks, on the live event
  have hFBG' : ∀ᵐ ω ∂P, ω ∈ FB → ω ∈ G' := by
    filter_upwards [hFBiff, hcov] with ω h1 h2 hω
    obtain ⟨hst, hoff, -⟩ := h1.1 hω
    exact h2 hst hoff
  obtain ⟨c', -, hc'e, hlawc⟩ := Cz.exists_stageLaw_of_mvLaw (𝒮 := lineFiltC P 𝓖 0) le_rfl ((lineFiltC P 𝓖).le 0)
    hh.1 hmv (hβℋ.mono (fun s hs => ⟨s, hs, EventuallyEq.rfl⟩) le_rfl) hKc hKp hKm hx₀m
    (hFBm.inter hmv.2.2.2.1) (Eventually.of_forall fun ω hω => hω.2)
    (by filter_upwards [hKF] with ω h1 hω using h1 hω.1)
  have hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ FB → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps := by
    filter_upwards [hlawc, hc'e, hFBG'] with ω₀ h1 h2 h3 hFB₀
    have hG : ω₀ ∈ FB ∩ G' := ⟨hFB₀, h3 hFB₀⟩
    have h1' := h1 hG
    rw [h2 hG] at h1'
    exact h1'
  have hM0 : 0 ≤ M := hmv.2.2.2.2.2.2.2.2.2.1
  have hM : ∀ ω, ∀ y ∉ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps, |(BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn y| ≤ M :=
    fun ω => Fl.abs_fn_shiftW_le (hmv.2.2.2.2.2.2.2.2.2.2.1 ω) (x₀ ω)
  have hK2 := Cr.ae_k2_root h12p h13 hκ hh hu₀ S hKm hKc hKp hx₀m hc hFBm hFrB htypes hcover hBm hBc hBl hloc
    hmeanK hlaw hM0 hM (hle 0) hlife
  -- the continuity of the canonical driver
  have hle0 : lineFiltC P 𝓖 0 ≤ ‹MeasurableSpace Ω› := (lineFiltC P 𝓖).le 0
  obtain ⟨-, hlc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hKm hKc hKp hx₀m
  have hZm : Measurable fun ω =>
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => hle0 _ (hdom z))
      (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc hh.1 1 0 (chiC κ)
  have hcont := Cz.ae_continuousOn_driverOf h12p h13 hκ hκ4 (-(Real.pi / 2)) hle0 hc hZm hFBm hlaw
  have hcontFr : ∀ᵐ ω ∂P, ω ∈ Fr → ContinuousOn (Qx.canonDrvAt h12p hκ h (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
      x₀ hKc hKp ω).1 {s | (s : ℝ≥0∞) ≤ (Qx.canonDrvAt h12p hκ h (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
      x₀ hKc hKp ω).2} := by
    filter_upwards [hcont, hFrB] with ω h1 h2 hω using h1 (h2 hω)
  -- the root construction's two facts
  obtain ⟨hdrv, hhd⟩ := Gi.ae_rootFacts h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft
    (hFriff.mono fun ω h => h.1) hent
  -- the versions read with tail start `entrR`
  let S' : Cr.RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc (fun ω => (entrR κ b jumps E u l k ℓ ω).toNNReal)
      (fun ω => (E w ℓ ω).2) relLife :=
    { S with
      ver := fun m =>
        { (S.ver m) with
          trace := fun v hv t => by
            filter_upwards [(S.ver m).trace v hv t, hre] with ω h1 h2 hseed hlt
            obtain ⟨ηr, hη, hη2⟩ := h1 hseed hlt
            refine ⟨ηr, hη, fun s hs hts hdom => hη2 s hs ?_ hdom⟩
            have he := h2 hseed.1.1
            rw [← he, ENNReal.toNNReal_coe] at hts
            exact hts } }
  have hfacts := Cz.ae_chainFacts_root h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hA
    hKc hKp hKF hFrB (hFriff.mono fun ω h => h.1) htypes hcover S' (fun m t => (hz m).mono fun ω h hω ht => h hω t ht)
    hcl (hle 0) hK2 hcontFr hdrv hhd
  -- the record on the root event
  obtain ⟨Dr, hDrm, hDrreg, hDreq⟩ := root_record h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hwℓ hu₀
    (h𝓖 0) ((hA 0).mono fun ω h => h.1) hKc hKp hx₀m hFBm hKF hFBiff hFriff (hβℋ.mono hle0 le_rfl) hfacts hvisω hFrB
    (Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft)
  -- the seed cells, the hull of stage `ℓ + 2`, the line facts of `A₁ 0`
  have hseed := Cr.hseed_of_le_thr_root S (hle 0)
  have hA'0 : ∀ᵐ ω ∂P, A₁' 0 ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec w (ℓ + 2) (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E w) (ℓ + 2) ω) ω := by
    filter_upwards [stmt6Sets_of_rootSets hfam' 0] with ω h1 using h1.1
  obtain ⟨K₂, L₂, hK₂m, hK₂c, hK₂p, hL₂, hL₂cov, hL₂K⟩ :=
    hull_succ_succ h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ₂ (h𝓖' 0) hA'0
  obtain ⟨hA₁m, -, -, -, -, -, -, -, hA₁c, -⟩ := hfam 0
  have hloc := Gj.hloc_rootLine h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ h𝓖 hfam
  -- the root event's facts for the piece
  have hFG : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ G' := by
    filter_upwards [hFriff, hcov] with ω h1 h2 hω using h2 (h1.1 hω).1 (h1.1 hω).2.1.ge
  have hLR : ∀ᵐ ω ∂P, ω ∈ Fr → Fm.FreeRight (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      Fm.LeftAdm κ (β₁ ω) (Fm.entry (A₁ 0 ω) (realMax (upperPrefix κ b jumps E u l k ω))) := by
    filter_upwards [hFG, hroot] with ω h1 h2 hω using ⟨(h2 (h1 hω)).2.1, (h2 (h1 hω)).2.2⟩
  have hKFr : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ 0 ω := by
    filter_upwards [hKF, hFrB] with ω h1 h2 hω using h1 (h2 hω)
  have hFl : ∀ᵐ ω ∂P, ω ∈ Fr → (ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none :=
    hFriff.mono fun ω h hω => (h.1 hω).1.2
  have hprofFr : ∀ᵐ ω ∂P, ω ∈ Fr → Lv.wordProfile (β₁ ω) ∈ Sp := by
    filter_upwards [hFriff, hprof] with ω h1 h2 hω using h2 (h1.1 hω).1.1
  -- CONDFIN's root piece on the clock event
  have hpiece := root_piece_clockF h12p h12 h13 h12₀ h13₀ (sb2LowerRootEntranceLawFStatement h12 h13 h12₀ h13₀) hκ
    hκ4 hb hh hcf hζ' hE hER hlθ k ℓ hwℓ hwℓ₂ h𝓖 hA
    (h𝓖' 0) hA'0 hmv hβm9 hKm hKc hKp hKFr hx₀m hFl S hcl htypes hcover hseed (hK2.mono fun ω h hω => (h hω).1)
    (hK2.mono fun ω h hω => (h hω).2) hFG hcov hDrm hDrreg hDreq hK₂m hK₂c hK₂p hL₂ hL₂K hu₀ hA₁m hA₁c hloc hu hlp hL
    hleft hFriff hx₀e hLR (C' := Ca.clockEv (S.ver 0).a) (Eventually.of_forall fun _ h => h)
    (by filter_upwards [hL₂cov] with ω h1 _ hl using h1 hl) hSp hprofFr
  obtain ⟨hR1, hR2⟩ := Ca.measurableSet_clockEv (P := P) (E := E) (u := u) (l := l) (k := k) hwℓ hwℓ₂ h𝓖 (h𝓖' 0)
    (S.ver 0).clock_meas
  have hiffc := Ca.ae_mem_clockEv_iff S htypes hcover hseed
  refine ⟨_, _, _, _, hpiece, hR1, hR2, ?_, ?_⟩
  · filter_upwards [hiffc, hFriff] with ω h1 h2 using h1.trans h2
  · filter_upwards [hiffc, hFriff] with ω h1 h2 hω using h1.2 (h2.2 hω)

end InteractingSLE.Theorem14.SB.Fu
