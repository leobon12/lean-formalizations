/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GjBook
import InteractingSLE.Spec.Supplement.SB2GjPrem
import InteractingSLE.Spec.Supplement.SB2GjF3
import InteractingSLE.Spec.Supplement.SB2GjRmax
import InteractingSLE.Spec.Supplement.SB2NfFin
import InteractingSLE.Spec.Supplement.SB2CqRTail
import InteractingSLE.Spec.Supplement.SB2CqCont
import InteractingSLE.Spec.Supplement.SB2MfUnb

/-!
# SB2(2)'s root identification against NOJUMP's 9F (D70, D79)

Packet PROVE-GW2-GEOM2, round 17. **`sb2LowerRootIdentStatementX_of_visit`**: `Gj.SB2LowerRootIdentStatementX` (the
root's canonical objects `Mz.CanonIdentOn` at `ℓ = relOff` with the word `shiftW x₀ β₁`, covering the positive roots,
for every word with `Gj.BaseLawForX`) from Theorems 1.2–1.3 and ROOTX's `Gj.SB2PosRootVisitStatement`. At a stage `ℓ`
that is a flow instruction of B's program:

* the root's line family: CONDFIN's `Cx.exists_rootLineFamily`;
* NOJUMP's root statement `Nf.SB2LowerRootVersionStatement9F` (PROVED, `Nf.sb2LowerRootVersionStatement9F`), its
  premises from `BaseLawForX` (`Gj.premises9F_of_baseLawForX`) and its countable word types from the profile cover;
* K2 at the root: CONDFIN's `Cr.ae_k2_root` with the line facts `Cx.k2Inputs_of_rootSets`, the line mean
  `Cy.hmean_root_obj` (its `hx₀` through `Gj.realMax_retX_root`, its `hF3` through `Gj.hF3_of_premiseB`) and the law of
  the canonical field given the line marks (`Cz.exists_stageLaw_of_mvLaw` on the live event);
* the continuity of the canonical driver: `Cz.ae_continuousOn_driverOf`;
* CANON's root chain facts `Cz.ae_chainFacts_root`, with the root construction's facts `Gi.ae_rootFacts` and the
  versions re-read with tail start `entrR` (`Na.rootEntry = entrR` on the root event);
* the bookkeeping `Gj.canonIdent_of_rootChainFacts`.

At any other stage there is no positive root, and the empty event does.

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

namespace InteractingSLE.Theorem14.SB.Gj

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Lv Mf Ms Lu Mz Lk Nd

/-- **The root identification against `BaseLawForX`** (Theorems 1.2–1.3 and ROOTX's positive-root visit). -/
theorem sb2LowerRootIdentStatementX_of_visit (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hvis : SB2PosRootVisitStatement.{u}) :
    SB2LowerRootIdentStatementX.{u} (Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ β₁ hX
  classical
  set h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hvisω := hvis κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlθ hleft ℓ
  by_cases hflow : ∃ (θ : ℝ) (t : ℝ≥0∞), w.2.2[ℓ]? = some (Sum.inl (θ, t))
  swap
  · -- no flow instruction at `ℓ`: no positive root
    refine ⟨∅, fun _ => ∅, fun _ => 0, fun _ => Lk.zeroDrv, fun _ => isCompact_empty, fun _ => ?_, ?_,
      measurable_const, fun _ => Lk.isRegularDriver_zeroDrv,
      Eventually.of_forall fun _ h' => absurd h' (notMem_empty _)⟩
    · rw [empty_union]; exact Mf.isPreconnected_lowerHalf
    · refine Eventually.of_forall fun ω _ hpos => absurd ?_ hflow
      obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hpos.1
      obtain ⟨hins, -, -⟩ := eq_launch_of_launches _ _ hcθ
      exact ⟨θ, _, hins⟩
  obtain ⟨θ, t, hwℓ⟩ := hflow
  obtain ⟨rfl, rfl⟩ := WalkLeaf.boundaryWalkSpec_inl hwℓ
  obtain ⟨hℓ, -⟩ := List.getElem?_eq_some_iff.1 hwℓ
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  -- the root's line family and NOJUMP's premises
  obtain ⟨𝓖, A₁, A₂, A₂J, h𝓖, hfam⟩ := Cx.exists_rootLineFamily h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ hu₀
  obtain ⟨K', G', Y, M, hmv, hcov, hmean, hheight⟩ :=
    premises9F_of_baseLawForX h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hℓ hwℓ hu₀ h𝓖 hfam hX
  have hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E w) ℓ ω) ω ∧
      A₂J t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E w) (ℓ + 1) ω)
        ω := fun t => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h10, -, -, -, -, -, h16, -⟩ := hfam t
    filter_upwards [h10, h16] with ω h1 h2 using ⟨h1.1, h2⟩
  -- the countable word types
  obtain ⟨Sp, hSp, hprof⟩ := hX.2.1
  set types : Set WordType := Lv.angleType κ (-(Real.pi / 2)) '' Lv.profileTypes κ Sp with htypesdef
  have htypes : types.Countable := (Lv.countable_profileTypes κ hSp).image _
  have hβℋ : Measurable[lineFiltC P 𝓖 0] β₁ := hmv.2.2.2.2.2.2.2.1
  have hβm9 : Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β₁ :=
    hX.1.mono (le_sup_left.trans fun s hs => ⟨s, hs, EventuallyEq.rfl⟩) le_rfl
  have hsort : ∀ ω, (β₁ ω).IsSorted := hmv.2.2.2.2.2.2.2.2.1
  -- NOJUMP's root statement
  obtain ⟨K, x₀, pc, relLife, FB, Fr, hKm, hKc, hKp, hKF, hx₀m, hFBm, hpc, hent, -, hFBiff, hFriff, hFrB, hS⟩ :=
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
    have hrm := realMax_retX_root (h3 hst.1) hst.2 hentr
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
  have hF3 := hF3_of_premiseB hh hℓ.le hu₀ (A₁ := A₁) (fun t => (hfam t).1)
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
  exact canonIdent_of_rootChainFacts h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hwℓ hu₀ (h𝓖 0)
    ((hA 0).mono fun ω h => h.1) hKc hKp hx₀m hFBm hKF hFBiff hFriff (hβℋ.mono hle0 le_rfl) hfacts hvisω

end InteractingSLE.Theorem14.SB.Gj
