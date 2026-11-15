/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvAS
import InteractingSLE.Spec.Supplement.SB2YbTL

/-!
# SB2(2)'s `hTL` from GEOM2's corrected v6 input and the conditional half over the tail-free bundle

Packet PROVE-T14-ASSEMBLE7 (round 2; decision D36). Two landed successors did not fit together:

* SB2LIFT's route to `hTL` (`Mq.sb2LowerTailLiftExStatement_of_geomV5_condW`, 73afd97cd) consumes LIFTSET's
  `Lk.SB2LowerGeomFactsV5Statement`, which GEOM2 proved false on the zero stages (`Nv.not_stageOK_v5_of_life_zero`,
  bf260b134);
* GEOM2's corrected input `Nv.SB2LowerGeomRestV6Statement` feeds only the false strengthened target
  `Lk.SB2LowerRelDriverStatementTR` (`Nv.sb2LowerRelDriverStatementTR_of_rest`, which carries the false `tail`, D36).

Here:

* **`sb2LowerRelDriverStatementTW_of_v6Cur`**: GEOM2's `sb2LowerRelDriverStatementTR_of_v6` with SB2LIFT's tail-free
  item 4 `Lk.SB2LowerClauseOfLiftsV5StatementW` and the corrected conclusion `Lk.SB2LowerRelDriverStatementTW` (the
  proof is GEOM2's, unchanged: the two item-4 statements have the same hypotheses, as SB2LIFT's
  `Lk.sb2LowerRelDriverStatementTW_of_v5` copy of LIFTSET's `…TR_of_v5` shows);
* **`sb2LowerRelDriverStatementTW_of_restCur`**: the corrected data from GEOM2's `SB2LowerGeomRestV6Statement` alone
  (item (A) GEOM2's, item 4 SB2LIFT's `Lk.sb2LowerClauseOfLiftsV5StatementW_of_thms`, both proved);
* **`sb2LowerTailLiftExStatement_of_restV6_condW`**: `hTL` from `Nv.SB2LowerGeomRestV6Statement` (LIFTSET) and
  `Mq.SB2LowerRelStageCondWStatement` (CONDFIN), with SB2LIFT's `Mq.sb2LowerTailLiftExStatement_of_relDriverTW_condW`;
* **`sb2LowerRelDriverStatementTWR_of_restCur`**: the same data together with LIFTSET's root facts `Lk.RootFactsAS`
  (`SB2LowerRelDriverStatementTWRCur`, the shape of PROVE-SB2-CONDFIN's in-progress `RelDriverAtTWR`), from the same
  input.

Theorems 1.2–1.3 may be used (R48). No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C FlowDilate

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep GW1P in
/-- **The corrected relative-driver data from the v6 half and SB2LIFT's tail-free item 4** (GEOM2's
`sb2LowerRelDriverStatementTR_of_v6` with `ClauseTW`; Theorems 1.2–1.3; no S3 input). -/
theorem sb2LowerRelDriverStatementTW_of_v6Cur (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV6Statement.{u})
    (hC : SB2LowerClauseOfLiftsV5StatementW.{u}) : SB2LowerRelDriverStatementTW.{u} := by
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
  -- the v6 rule is admissible: the generation hypotheses agree on the mask
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
  -- the root facts (D25)
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
    (fun j ω _ => ω ∈ M j EL) EL hmeas hreg hZ' (fun j ω hω _ => hgen' j ω hω) hgeom hSF hRoot hPL, hSF⟩

/-- **The corrected relative-driver data from GEOM2's remaining v6 input alone** (item (A) and item 4 proved;
Theorems 1.2–1.3). -/
theorem sb2LowerRelDriverStatementTW_of_restCur (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hR : SB2LowerGeomRestV6Statement.{u}) :
    SB2LowerRelDriverStatementTW.{u} :=
  sb2LowerRelDriverStatementTW_of_v6Cur h12 h13 h12₀ h13₀ (sb2LowerGeomFactsV6Statement_of_rest h12 h13 h12₀ h13₀ hR)
    (Lk.sb2LowerClauseOfLiftsV5StatementW_of_thms h12 h13 h12₀ h13₀)

/-- **`hTL` of the current top from GEOM2's remaining v6 input and the conditional half over the corrected bundle**
(Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_restV6_condW (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hR : SB2LowerGeomRestV6Statement.{u})
    (hcond : Mq.SB2LowerRelStageCondWStatement.{u}) : Lk.SB2LowerTailLiftExStatement.{u} :=
  Mq.sb2LowerTailLiftExStatement_of_relDriverTW_condW h12 h13 h12₀ h13₀
    (sb2LowerRelDriverStatementTW_of_restCur h12 h13 h12₀ h13₀ hR) hcond

/-! ### The data with the root facts (the shape of PROVE-SB2-CONDFIN's `RelDriverAtTWR`) -/

/-- **The corrected relative-driver data with LIFTSET's root facts at one launch**: a measurable, regular family
`EL` with `Mn.ClauseTW`, `Mn.StageFactsAS` and `Lk.RootFactsAS` (D25). -/
def RelDriverAtTWRCur (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -Lu.upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    (Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL ∧ Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL ∧
      Lk.RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL)

/-- **SB2(2)'s corrected relative-driver data with the root facts** (conclusion of
`sb2LowerRelDriverStatementTWR_of_v6Cur`). -/
def SB2LowerRelDriverStatementTWRCur : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAtTWRCur κ b jumps P E u l k ω₀ c b' J'

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep GW1P in
/-- **The corrected data with the root facts from the v6 half and SB2LIFT's tail-free item 4** (the same proof as
`sb2LowerRelDriverStatementTW_of_v6Cur`, also returning the root facts GEOM2's proof builds). -/
theorem sb2LowerRelDriverStatementTWR_of_v6Cur (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV6Statement.{u})
    (hC : SB2LowerClauseOfLiftsV5StatementW.{u}) : SB2LowerRelDriverStatementTWRCur.{u} := by
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
  -- the v6 rule is admissible: the generation hypotheses agree on the mask
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
  -- the root facts (D25)
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

/-- **The corrected data with the root facts from GEOM2's remaining v6 input alone** (Theorems 1.2–1.3). -/
theorem sb2LowerRelDriverStatementTWR_of_restCur (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hR : SB2LowerGeomRestV6Statement.{u}) :
    SB2LowerRelDriverStatementTWRCur.{u} :=
  sb2LowerRelDriverStatementTWR_of_v6Cur h12 h13 h12₀ h13₀ (sb2LowerGeomFactsV6Statement_of_rest h12 h13 h12₀ h13₀ hR)
    (Lk.sb2LowerClauseOfLiftsV5StatementW_of_thms h12 h13 h12₀ h13₀)

end InteractingSLE.Theorem14.SB.Nv

/-! ### The range identity standalone, and `hTL` from a conditional half that may use the root facts -/

namespace InteractingSLE.Theorem14.SB.Mq

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn
open LuM (trOf)

/-- **The range identity over the corrected bundle** (the shape of PROVE-SB2-CONDFIN's in-progress
`SB2LowerRangeTWStatement`): for every measurable, regular family `EL` with `Mn.ClauseTW` and `Mn.StageFactsAS`, the
actual tail lifts onto `EL`'s relative walk under the retained kernel. -/
def SB2LowerRangeTWStatementCur : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
            (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **The range identity over the corrected bundle, PROVED** (the range part of SB2LIFT's
`sb2LowerTailLiftExStatement_of_relDriverTW_condW`, which does not use the conditional half; Theorems 1.2–1.3). -/
theorem sb2LowerRangeTWStatementCur (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : SB2LowerRangeTWStatementCur.{u} := by
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

section CondR

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
  (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The conditional half at one launch over families carrying the corrected bundle and LIFTSET's root facts** (the
shape of PROVE-SB2-CONDFIN's in-progress `Cf.RelStageCondW`: `RelStageCondW` with `Lk.RootFactsAS` added). -/
def RelStageCondWRCur : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    (Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL ∧ Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL ∧
      Lk.RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL) →
    ∀ j, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ (c₁ : Chart) (θ : ℝ),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω₁)
          (j + 1)).2.2.2.1 j = some (c₁, θ) →
        ∃ (b'' : ℝ → ℝ) (J'' : Finset ℝ) (h'' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b'' J'' ∧
          (∀ ω, IsChartTransport c₁ 1 0 (chiC κ) (affField m one_pos (h' ω)) (h'' ω)) ∧
          IsFlowLineDriver κ b'' J'' θ
            (condExpKernel (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) ω₁)
            h'' (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

end CondR

/-- **SB2(2)'s conditional half over the corrected bundle with the root facts** (the shape of PROVE-SB2-CONDFIN's
in-progress `Cf.SB2LowerRelStageCondWStatement`). -/
def SB2LowerRelStageCondWRStatementCur : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCondWRCur κ b jumps P E u l k ω₀ c b' J' h'

/-- **SB2LIFT's conditional half (no root facts) gives the one with the root facts.** -/
theorem sb2LowerRelStageCondWRStatementCur_of_condW (h : SB2LowerRelStageCondWStatement.{u}) :
    SB2LowerRelStageCondWRStatementCur.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hf hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P hf hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl
  exact h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl.1 hcl.2.1

/-- **`hTL` from the corrected data with the root facts and the conditional half with the root facts** (Theorems
1.2–1.3; SB2LIFT's `sb2LowerTailLiftExStatement_of_relDriverTW_condW` with the root facts passed to the conditional
half, and the range identity `sb2LowerRangeTWStatementCur`). -/
theorem sb2LowerTailLiftExStatement_of_TWR_condWRCur (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hD : Nv.SB2LowerRelDriverStatementTWRCur.{u}) (hcond : SB2LowerRelStageCondWRStatementCur.{u}) :
    SB2LowerTailLiftExStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRangeTWStatementCur h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hD₀ hr₀ hcond₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hELm, hELr, hcl⟩ := hD₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  have hst := hcond₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hpast : ∀ j, Measurable (pastMap κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) :=
    fun j => measurable_pastMap runMeasStatement hb'' (relLowerSpec b' J' m) (k := j) (fun i _ => hELm i)
      (fun i _ => hELr i) j le_rfl
  have hS : IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL := by
    refine ⟨hELm, fun j => ?_, fun j => Eventually.of_forall fun ω hne hpos c₀ hc₀ =>
      (hELr j ω).2.2.2 hne hpos c₀ hc₀, hst⟩
    rw [pastSigma_eq_comap]
    exact (hpast j).comap_le
  exact ⟨EL, hS, stagedPiecesRegular_of_regular h13 hκ hb'' hS hELr,
    hr₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl.1 hcl.2.1⟩

/-- **`hTL` from GEOM2's remaining v6 input (LIFTSET) and the conditional half with the root facts (CONDFIN)**
(Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_restV6_condWRCur (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hR : Nv.SB2LowerGeomRestV6Statement.{u}) (hcond : SB2LowerRelStageCondWRStatementCur.{u}) :
    SB2LowerTailLiftExStatement.{u} :=
  sb2LowerTailLiftExStatement_of_TWR_condWRCur h12 h13 h12₀ h13₀
    (Nv.sb2LowerRelDriverStatementTWR_of_restCur h12 h13 h12₀ h13₀ hR) hcond

end InteractingSLE.Theorem14.SB.Mq
