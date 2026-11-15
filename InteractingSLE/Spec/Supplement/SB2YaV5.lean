/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvV5
import InteractingSLE.Spec.Supplement.SB2XzTW
import InteractingSLE.Spec.Supplement.SB2YaCl
import InteractingSLE.Spec.Supplement.SB2JwRayAS
import InteractingSLE.Spec.Supplement.SB2MbFill
import InteractingSLE.Spec.Supplement.SB2MeInputs
import InteractingSLE.Spec.Supplement.SB2JqRun
import InteractingSLE.Spec.Supplement.SB2JqArc
import InteractingSLE.Spec.Supplement.SB2JyHull
import InteractingSLE.Spec.Supplement.SB2MeRel
import InteractingSLE.Spec.Supplement.SB2UxExit
import InteractingSLE.Spec.Supplement.SB2LpAE
import InteractingSLE.Spec.Supplement.SBS3LtDensity
import InteractingSLE.Spec.Supplement.SB2LuLift

/-!
# Item 4 over the corrected bundle, v5 form, PROVED

Packet PROVE-T14-SB2LIFT (round 31; item 4, decisions D25, D36). LIFTSET's v5 split of the relative-driver data
(`SB2JvV5`) concludes the false bundle `Mn.ClauseTR`. Over the corrected bundle `Mn.ClauseTW` (no `tail`):
* **`SB2LowerClauseOfLiftsV5StatementW`**: item 4 in v5 form (`SB2LowerClauseOfLiftsV5Statement` with `ClauseTW`);
* **`sb2LowerRelDriverStatementTW_of_v5`**: LIFTSET's `sb2LowerRelDriverStatementTR_of_v5` with `ClauseTW`;
* **`sb2LowerClauseOfLiftsV5StatementW_of_thms`**: item 4, PROVED (Theorems 1.2–1.3), via `clauseTW_sample`;
* **`sb2LowerRelDriverStatementTW_of_geomV5`**: `SB2LowerRelDriverStatementTW` from LIFTSET's
  `SB2LowerGeomFactsV5Statement` alone (and Theorems 1.2–1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **SB2LIFT's item 4 with the root facts, over the corrected bundle** (D25, D36): as
`SB2LowerClauseOfLiftsV4StatementW`, with `RootFactsAS` as an extra input. -/
def SB2LowerClauseOfLiftsV5StatementW : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ (ΦG : ℕ → _ → ExplState → Prop) (EL : ℕ → _ → Drv),
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ4 κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ4 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m ΦG EL → Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL

/-- **The corrected target from the v5 half and SB2LIFT's item 4** (LIFTSET's `sb2LowerRelDriverStatementTR_of_v5`
with `ClauseTW`; Theorems 1.2–1.3; no S3 input). -/
theorem sb2LowerRelDriverStatementTW_of_v5 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV5Statement.{u})
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
  have hdep : ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) → ρ j F = ρ j F' ∧ Z j F = Z j F' := by
    intro j F F' hFF
    obtain ⟨h1, -, h3⟩ := hdep_concrete4 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
      (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) (fun _ _ _ => True) j F F' hFF
    exact ⟨h1, h3⟩
  -- the masked rule is admissible: the generation hypotheses agree on `Gd`
  have hok' : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd Z i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ (fun _ _ => Gd) i F, ω ∉ mZ Gd Z i F → (F i ω).2 = capLife (mρ Gd ρ i F ω) ∧
        ∀ T < capLife (mρ Gd ρ i F ω), IsGeneratingTrace (F i ω).1 T (capTrace (mρ Gd ρ i F ω))) →
      StageOK (mρ Gd ρ j F) ((fun _ _ => Gd) j F) (mZ Gd Z j F) := by
    intro j F hm1 hm2 hz hg
    refine hok j F hm1 hm2 hz fun i hi ω hω hnZ => ?_
    have h := hg i hi ω hω (not_mem_mZ hω hnZ)
    rwa [mρ_of_mem hω] at h
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_rec' (mρ Gd ρ) (fun _ _ => Gd) (mZ Gd Z)
    (hdep_mask Gd hdep) hok'
  have hgen' : ∀ j, ∀ ω ∈ Gd, ω ∉ Z j EL → (EL j ω).2 = capLife (ρ j EL ω) ∧
      ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω)) := by
    intro j ω hω hnZ
    have h := hgen j ω hω (not_mem_mZ hω hnZ)
    rwa [mρ_of_mem hω] at h
  have hZ' : ∀ j, ∀ ω ∈ Z j EL, EL j ω = zeroDrv := fun j ω hω => hZ j ω (subset_mZ hω)
  obtain ⟨hgeom, hSF⟩ := hfacts EL hmeas hreg hZ hgen'
  have hdrv : ∀ j, ∀ ω ∈ Gd, IsDrivenCurve (ρ j EL ω) := by
    intro j ω hω
    have h := (hok' j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hω
    rwa [mρ_of_mem hω] at h
  have hPL : PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
      hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
    intro β₀ hβ hβ0 hβr tL γ hγ
    exact piecesLift2_of_geom4 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
      (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
      (fun j => hreg j ω) (fun j hGj hnZ => hgen' j ω hGj hnZ) (fun j hGj => hdrv j ω hGj)
  -- the root facts (D25)
  have hRoot : RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hSF, hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm,
      hL₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hSFω hβω hTω hLω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
    have hst := (hω β₀ hβ hβ0 hβr tL γ hγ).1
    refine rootFactsAt_of (fun hz => hZ' 0 ω ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 hz)) (fun hnZ hs => ?_) hSFω
      (hreg 0 ω)
    have hGd : ω ∈ Gd := ((hst hnZ (hLω hnZ)).1 hs).1
    have hnZ' : ω ∉ Z 0 EL := fun hz => ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).1 hz).elim hnZ hs
    rw [(hgen' 0 ω hGd hnZ').1]
    exact (capLife_pos_of_driven (hdrv 0 ω hGd)).ne'
  exact ⟨EL, hmeas, hreg, hC₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm (fun _ ω _ => ω ∈ Gd) EL hmeas hreg hZ'
    (fun j ω hω hnZ => hgen' j ω hω hnZ) hgeom hSF hRoot hPL, hSF⟩


/-! ### Item 4, PROVED -/

/-- **Item 4 (the clause from the piece lifts, v5 form, corrected bundle), PROVED** (Theorems 1.2–1.3): per sample
the ray correspondence `sb2LowerRayCorr`, the ray clause `lift_eq_of_rayChartInj` and the start disjunction
`clauseTW_sample`, from GW1's walk facts, the upper chart, the head and its hull, the good-time density and the
v5 inputs `Mn.StageFactsAS`, `RootFactsAS`, `PiecesLift2AS`. -/
theorem sb2LowerClauseOfLiftsV5StatementW_of_thms (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2LowerClauseOfLiftsV5StatementW.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [sb2LowerRunExit h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft,
    sb2LowerRayCorr h13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hX₀ hI₀ hA₀ hd₀ hRH₀ hH₀ hK₀ hU₀ hgd₀ hRC₀
  intro c θ hlaunch b' J' h' hb' hT' hG' _ m hm _ EL _ hELr _ _ _ hSF hRoot hPL
  obtain ⟨-, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨hι, hcont, hlim, hinj⟩ := hRC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm
  filter_upwards [hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hA₀ c θ hlaunch b' J' h' hb' hT' hG', hd₀ c θ hlaunch b' J' h' hb' hT' hG',
    hRH₀ c θ hlaunch b' J' h' hb' hT' hG', hH₀ c θ hlaunch b' J' h' hb' hT' hG',
    hK₀ c θ hlaunch b' J' h' hb' hT' hG', hgd₀ c θ hlaunch b' J' h' hb' hT' hG', hSF, hRoot, hPL]
    with ω hXω hIω hAω hdω hRHω hHω hKω hgdω hSFω hRFω hPLω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  refine ⟨_, hι, hlim, lift_eq_of_rayChartInj hγ hinj, ?_⟩
  exact clauseTW_sample hb hXω hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) (fun j => (hn j).2.2) hAω hdω
    hRHω hι hcont (liftCurveData_of hβ hγ hhead hinj hlim) hγ hβ hβ0 hβr hU (hKω β₀ hβ hβ0 hβr tL hγ.1) hDom hhead
    (fun j => hELr j ω) hSFω (hgdω β₀ hβ hβ0 hβr tL hγ.1) hRFω (hPLω β₀ hβ hβ0 hβr tL γ hγ)

/-- **The corrected relative-driver data from LIFTSET's v5 half alone** (Theorems 1.2–1.3): item 4 is proved
(`sb2LowerClauseOfLiftsV5StatementW_of_thms`). -/
theorem sb2LowerRelDriverStatementTW_of_geomV5 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV5Statement.{u}) :
    SB2LowerRelDriverStatementTW.{u} :=
  sb2LowerRelDriverStatementTW_of_v5 h12 h13 h12₀ h13₀ hG
    (sb2LowerClauseOfLiftsV5StatementW_of_thms h12 h13 h12₀ h13₀)

end InteractingSLE.Theorem14.SB.Lk
