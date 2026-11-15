/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwTR
import InteractingSLE.Spec.Supplement.SB2XzAS

/-!
# SB2(2)'s relative-driver target over the bundle without `tail`

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle, handoff §R29.3). `SB2LowerRelDriverStatementTR`
asks for `ClauseTR`, whose field `tail` is false (§R29.1), so it is false. The corrected target
**`SB2LowerRelDriverStatementTW`** asks for `ClauseTW` (no `tail`); its split into LIFTSET's
`SB2LowerGeomFactsV4Statement` and the corrected item 4 **`SB2LowerClauseOfLiftsV4StatementW`** is
**`sb2LowerRelDriverStatementTW_of_v4`**, the landed proof with `ClauseTR` replaced by `ClauseTW`. R2 over the
corrected bundle is `Mn.sb2LowerStageChainStatementWA_of_thms` (`SB2XzAS`).
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

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

/-- **The strengthened relative-driver data at one launch** (D23): a measurable, everywhere regular relative family
carrying the corrected bundle at the offset `relOff` and the per-stage facts. -/
def RelDriverAtTW (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL ∧ Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named target: SB2(2)'s strengthened relative-driver data** (D23). -/
def SB2LowerRelDriverStatementTW : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAtTW κ b jumps P E u l k ω₀ c b' J'

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **Named input (SB2LIFT, item 4, D23): the clause from the piece lifts.** For every measurable, everywhere regular
family that is `zeroDrv` on the v4 zero events, generates the v4 curves on driven events `lG ΦG`, and has the
per-stage facts, the piece lifts give the corrected bundle at the offset `relOff`. -/
def SB2LowerClauseOfLiftsV4StatementW : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ (ΦG : ℕ → _ → ExplState → Prop) (EL : ℕ → _ → Drv),
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ4 κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ4 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m ΦG EL → Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL

/-- **The strengthened target from the two halves** (Theorems 1.2–1.3; no S3 input). -/
theorem sb2LowerRelDriverStatementTW_of_v4 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV4Statement.{u})
    (hC : SB2LowerClauseOfLiftsV4StatementW.{u}) : SB2LowerRelDriverStatementTW.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft,
    hRLQ] with ω₀ hG₀ hC₀ hU₀ hH₀ hI₀ hD₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨hcc, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨ΦG, hok, hfacts⟩ := hG₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_concrete4 κ (-(Real.pi / 2)) b jumps (affData 1 m b')
    (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) ΦG hok
  obtain ⟨hgeom, hSF⟩ := hfacts EL hmeas hreg hZ hgen
  have hPL : PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
      hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
    intro β₀ hβ hβ0 hβr tL γ hγ
    exact piecesLift2_of_geom4 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
      (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
      (fun j => hreg j ω) (fun j hG hnZ => hgen j ω hG hnZ)
      (fun j hG => (hok j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
        (fun i _ => hgen i)).2.2.2 ω hG)
  exact ⟨EL, hmeas, hreg, hC₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm ΦG EL hmeas hreg hZ hgen hgeom hSF hPL, hSF⟩

end InteractingSLE.Theorem14.SB.Lk
