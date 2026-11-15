/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfCond
import InteractingSLE.Spec.Supplement.SB2NvAS
import InteractingSLE.Spec.Supplement.SB2YaV5
import InteractingSLE.Spec.Supplement.SB2YbCond

/-!
# SB2(2): the corrected data with root facts, and the range identity over the corrected bundle

Packet PROVE-SB2-CONDFIN (round 2). Two of round 1's named hypotheses discharged from landed work:

* **`sb2LowerRangeTWStatement`**: `Cf.SB2LowerRangeTWStatement` PROVED (Theorems 1.2–1.3), from SB2LIFT's tail-free
  range copies (`range_eq_physSet_of_bundlesW`, `range_eq_physSet_of_topVW`, with `Mn.tailArc_of_bundle`) — the range
  part of `Mq.sb2LowerTailLiftExStatement_of_relDriverTW_condW`;
* **`sb2LowerRelDriverStatementTWR_of_v6`**: `Cf.SB2LowerRelDriverStatementTWR` (SB2LIFT's corrected data with
  LIFTSET's root facts) from GEOM2's corrected item-3 input `Nv.SB2LowerGeomFactsV6Statement` and SB2LIFT's item 4
  (`Lk.sb2LowerClauseOfLiftsV5StatementW_of_thms`, PROVED); this is GEOM2's `Nv.sb2LowerRelDriverStatementTR_of_v6`
  with `ClauseTW` and the root facts kept; **`sb2LowerRelDriverStatementTWR_of_rest`** from LIFTSET's remaining v6
  input `Nv.SB2LowerGeomRestV6Statement` (GEOM2's `Nv.sb2LowerGeomFactsV6Statement_of_rest`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Cg

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn Mq Nv LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

/-- **The range identity over the corrected bundle** (`Cf.SB2LowerRangeTWStatement`), PROVED from SB2LIFT's
tail-free range copies (Theorems 1.2–1.3). -/
theorem sb2LowerRangeTWStatement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : Cf.SB2LowerRangeTWStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    Lk.sb2LowerArcsIci h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hH₀ hA₀ hX₀ hI₀ hC₀ hZ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' _ m hm EL _ hELr hae _
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hZ₀ c θ hlaunch b' J' h' hb' hT' hG']
    with ω hω hHω hAω hXω hIω hCω hZω
  intro β₀ hβ hβ0 hβr
  obtain ⟨tL, γ, hγ⟩ := hCω β₀ hβ hβ0 hβr
  obtain ⟨ι, hι, hlim, hray, hS'⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have htail := Mn.tailArc_of_bundle hβ hβr hγ.1 hhead hZω hP₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hS'
  have hC : CurveInputsW κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) β₀ γ tL :=
    ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩
  refine isTailLiftOf_iff.2 ⟨tL, γ, hγ, ?_⟩
  rcases hS' with ⟨N, hR, hS'⟩ | ⟨hP, htop⟩
  · have hDc : LiftCurveData β₀ γ tL (realMax (upperPrefix κ b jumps E u l k ω₀)) ι :=
      ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
        fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
    exact range_eq_physSet_of_bundlesW hι hC hR (fun j => hELr j ω) hP₁ hW₁ (fun j => (hn j).1)
      (fun j => (hn j).2.1) (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hDc hS'
  · exact range_eq_physSet_of_topVW hι hC hP htop (hn _).2.1

/-- **The corrected data with the root facts from GEOM2's corrected item-3 input and SB2LIFT's item 4**
(Theorems 1.2–1.3; GEOM2's `Nv.sb2LowerRelDriverStatementTR_of_v6` with `ClauseTW`, keeping the root facts). -/
theorem sb2LowerRelDriverStatementTWR_of_v6 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV6Statement.{u}) :
    Cf.SB2LowerRelDriverStatementTWR.{u} := by
  have hC := sb2LowerClauseOfLiftsV5StatementW_of_thms h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft,
    hRLQ, hβex,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerLaunchRelOff h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft] with ω₀ hG₀ hC₀ hU₀ hH₀ hI₀ hD₀ hR₀ hβ₀ hT₀ hL₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨hcc, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨Gd, -, hok, hfacts⟩ := hG₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  set ρ := lρ3 κ b jumps E u l k ω₀ c b' J' m with hρ
  set Z := lZ4 κ b jumps E u l k ω₀ with hZdef
  set M := lMask κ b jumps E u l k ω₀ c b' J' m Gd with hMdef
  have hok' : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd Z i F, F i ω = Lk.zeroDrv) →
      (∀ i < j, ∀ ω ∈ M i F, ω ∉ mZ Gd Z i F →
        (F i ω).2 = capLife (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω) ∧
        ∀ T < capLife (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω))) →
      StageOK (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j F) (M j F) (mZ Gd Z j F) := by
    intro j F hm1 hm2 hz hg
    refine hok j F hm1 hm2 hz fun i hi ω hω => ?_
    have h := hg i hi ω hω (not_mem_mZ_of_maskEv hω)
    have e : lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω = ρ i F ω := mρ6_of_mem hω
    rwa [e] at h
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_rec' (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd) M (mZ Gd Z)
    (hdep6 Gd) hok'
  have hgen' : ∀ j, ∀ ω ∈ M j EL, (EL j ω).2 = capLife (ρ j EL ω) ∧
      ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω)) := by
    intro j ω hω
    have h := hgen j ω hω (not_mem_mZ_of_maskEv hω)
    have e : lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j EL ω = ρ j EL ω := mρ6_of_mem hω
    rwa [e] at h
  have hZ' : ∀ j, ∀ ω ∈ Z j EL, EL j ω = Lk.zeroDrv := fun j ω hω => hZ j ω (subset_mZ hω)
  obtain ⟨hgeom, hSF⟩ := hfacts EL hmeas hreg hZ hgen'
  have hdrv : ∀ j, ∀ ω ∈ M j EL, IsDrivenCurve (ρ j EL ω) := by
    intro j ω hω
    have h := (hok' j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hω
    have e : lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j EL ω = ρ j EL ω := mρ6_of_mem hω
    rwa [e] at h
  have hPL : PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
      hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
    intro β₀ hβ hβ0 hβr tL γ hγ
    exact piecesLift2_of_geom4 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
      (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
      (fun j => hreg j ω) (fun j hGj _ => hgen' j ω hGj) (fun j hGj => hdrv j ω hGj)
  have hRoot : RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hSF, hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm,
      hL₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hSFω hβω hTω hLω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
    have hst := (hω β₀ hβ hβ0 hβr tL γ hγ).1
    refine rootFactsAt_of (fun hz => hZ' 0 ω ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 hz)) (fun hnZ hs => ?_) hSFω
      (hreg 0 ω)
    have hM : ω ∈ M 0 EL := ((hst hnZ (hLω hnZ)).1 hs).1
    rw [(hgen' 0 ω hM).1]
    exact (capLife_pos_of_driven (hdrv 0 ω hM)).ne'
  exact ⟨EL, hmeas, hreg, hC₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
    (fun j ω _ => ω ∈ M j EL) EL hmeas hreg hZ' (fun j ω hω _ => hgen' j ω hω) hgeom hSF hRoot hPL, hSF, hRoot⟩

/-- **The corrected data with the root facts from LIFTSET's remaining v6 input** (GEOM2's
`Nv.sb2LowerGeomFactsV6Statement_of_rest`). -/
theorem sb2LowerRelDriverStatementTWR_of_rest (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hR : SB2LowerGeomRestV6Statement.{u}) :
    Cf.SB2LowerRelDriverStatementTWR.{u} :=
  sb2LowerRelDriverStatementTWR_of_v6 h12 h13 h12₀ h13₀ (sb2LowerGeomFactsV6Statement_of_rest h12 h13 h12₀ h13₀ hR)

end InteractingSLE.Theorem14.SB.Cg
