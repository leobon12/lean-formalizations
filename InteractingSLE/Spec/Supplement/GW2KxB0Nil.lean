/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Form
import InteractingSLE.Spec.Supplement.GW2KxB0Inst
import InteractingSLE.Spec.Supplement.GW2KxB0Stmt
import InteractingSLE.Spec.Supplement.GW2TyContact
import InteractingSLE.Spec.Supplement.GW2KxStep
import InteractingSLE.Spec.Supplement.GW2KcNil
import InteractingSLE.Spec.Supplement.GW2TwCons
import InteractingSLE.Spec.Supplement.GW2FbDual
import InteractingSLE.Spec.Supplement.GW2PwWrap
import InteractingSLE.Spec.Supplement.BW1LMeanRet

/-!
# Claim(k)'s base at a root `x`: `ClaimAtX` for the history `l = []`

Packet PROVE-GW2-GEOM2, round 14 (D49). The root piece is a stage read from the root's start:
* its stage-start identity is the counterflow's retained mean read in `relChartX` (`inst0_rootX`, from
  `GW2Fb.ae_eqOn_retMean_gw2`);
* its kernel forms at `P` are `ae_base_formsX`;
* its reading at the root piece's end is `sample_stage_read0X`, with RELDET's kernel-side readings
  `SampleContactRoot0XStatement` (D62).
Restarted at the instance's stage start (`stgMeanRX_restart`, STAGEMEAN's explored identity `eqOn_explored_typed`,
the word map's base word `baseWordX_augRecX` at `N = 1`), this is `ClaimAtX` at `l = []`.

* `ae_shape_root0X`: the shape of the root piece's stage union, read from the root's start;
* **`claimAtX_nilX`**, **`claimAllX_nilX`** (RELDET's `hnil` form, `GW2Rd.ClaimAllX c r cw []`), given the named
  readings;
* **`claimAtX_nil_rootX`**, **`claimAllX_nil_rootX`**: the same outright, with RELDET's proof of the readings
  (`GW2Rd.sampleContactRoot0XStatement`, `GW2TyContact`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open GW2Kb GW2Psm GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm GW2Rz GW2Rv Supp8 Supp8.GB6
  GW2JointKernel Supp8.Q3Stop GW2Sde Restart.DomainMarkov MartChar.RealFlow Sec7.PocketTraversal Supp8.GB6.RelDrv
  GW2Xk Restart.MarkovChart Supp8.GB6LineL
open Supp8.Q3Rel (invHull relLog)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The shape of the root piece's stage union, read from the root's start** (on the history's success). -/
theorem ae_shape_root0X (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) (hx : 0 ≤ rootPt r.1)
    (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ GT → oldSuccess c r [] ω → ∀ u : ℝ≥0,
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT u ω) (V ω) < V ω →
      H \ schedUnionX c r [] a 0 u ω = (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun q => R q ω) (capA (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V 0 u ω)) := by
  filter_upwards [ae_compl_union_eq_relChartX_all hGT hs0 hx hv] with ω hω hωG hsucc u hlt
  have h := hω hωG (0 + u) (by rwa [zero_add])
  have e : schedUnionX c r [] a 0 u ω = Supp8.Q3Rel.invHull (rdrv (cfRec c.s c.W c.ζ ω)) c.s ∪
      (fun z : ℂ => z + ((rootPt r.1 : ℝ) : ℂ)) ''
        fwdHull (fun q : ℝ => schedW c r [] a q.toNNReal ω) ((0 + u : ℝ≥0) : ℝ) := by
    simp only [schedUnionX, schedHullX, hsucc, ↓reduceIte, schedHull]
    congr 1
    exact congrArg (fun f : ℂ → ℂ => f '' _) (funext fun z => add_comm _ _)
  rw [e]
  exact h

variable [StandardBorelSpace Ω]

/-- **Claim(k)'s base at a root `x`** (`ClaimAtX` at `l = []`, roots `0 ∨ lowerArcRoots`), given RELDET's kernel-side
readings `SampleContactRoot0XStatement` (D62). -/
theorem claimAtX_nilX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hRD : SampleContactRoot0XStatement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    (hβ : ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r [])
      ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) (GW2Rd.length_historyProgram c r [])
      (candAngle c r [] a))
    (hσ : ch.σa = specOffset c.κ + candAngle c r [] a * chiC c.κ) (w : WordType) :
    ClaimAtX c r [] a GT hA ch w := by
  classical
  intro g₀ hg₀ φ
  have hx : (0 : ℝ) ≤ rootPt r.1 := hroot.elim (fun h => h.ge) fun h => (GW2Sched.pos_of_mem_lowerArcRoots h).le
  set I := schedInstSX c r [] a GT hA ch with hIdef
  set T : ℝ≥0 := historyTime c r [] with hT
  set θr : ℝ := (rootEntry r.1).1 with hθr
  have hB0 : I.B 0 = schedUnionX c r [] a T 0 := schedUnionSX_eq_schedUnionX c r [] a 0
  have hg₀' : IsLocalSetMean (schedUnionX c r [] a T 0) (centredField c.h ch.u₀) c.P g₀ := by
    rw [← hB0]; exact hg₀
  have hhm : Measurable c.h := c.hh.1
  -- the kernel forms at `P`
  obtain ⟨g, g₁, hg, hg₁, hconf, b', J', u', Wk, ζk, ℓ, c', γ, uθ, hb', hu', hfl', hcfk, huθ, hcomp, hd, hmain,
    hmain₀⟩ := ae_base_formsX h12 h13 h12₀ h13₀ c r a hroot hu₀
  have hgg := IsLocalSetMean.ae_apply_eq (measurable_schedUnionX c r [] a T 0)
    (measurable_centredField hhm ch.u₀) hg₀' hg φ
  -- the retained mean
  obtain ⟨b'', J'', h'', hb'', hTr, hcfl, hJ, hfn⟩ := hcw
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData c.κ
    (flowLineRhoL c.κ c.b c.jumps 0 0) (flowLineRhoR c.κ c.b c.jumps 0 0) (flowLineXL c.b c.jumps 0)
    (flowLineXR c.b c.jumps 0)
  have huh' : IsBoundedHarmonicExtension (Supp8.Q3Chain.cfData c.κ c.b c.jumps)
      (forceJumpSet (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0)) uh := huh
  have heqU : EqOn uh ch.u₀ H := fun z hz => by
    have h1 := eqOn_flowLine_harmonicExtension c.hκ c.hb 0 0 hu₀ huh hz
    simpa only [Complex.ofReal_zero, add_zero, zero_mul] using h1
  have hcen : centredField c.h uh = centredField c.h ch.u₀ := by
    funext ω
    simp only [centredField]
    rw [WangWu.smoothDist_congr huh.1.continuousOn hu₀.1.continuousOn heqU]
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h uh) c.P := by
    rw [hcen]; exact hh0
  have hg₁' : IsLocalSetMean (retSet c.s c.W c.ζ) (centredField c.h uh) c.P g₁ := by
    rw [hcen]; exact hg₁
  have hret := GW2Fb.ae_eqOn_retMean_gw2 h12 h13 c.hκ c.hb c.hh hb'' hTr hcfl hJ hfn huh' hh0' c.s hg₁'
  -- the instance's record
  have hver := hA.1
  have hv := hver.1
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r [] (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  -- the schedule's pieces
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h (futSpec c r [] a) (futFam c r [] a) :=
    isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle (futSpec c r [] a)) (specDelta (futSpec c r [] a))
      h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := futSpec c r [] a) rfl
      (isFlowProg_spec (rootPt r.1) true (futureProgram c r [] a)) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (futFam c r [] a j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle (futSpec c r [] a))
      (specDelta (futSpec c r [] a)) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  -- almost-sure facts
  have hζk : ∀ᵐ ω ∂c.P, ζk ω = ⊤ := hd.mono fun _ h => h.1
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb' hfl'
  have hNRp := GW2Rd.counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 c.b c.jumps c.hb c.P c.h c.hh c.W c.ζ c.hcf
    c.hζ
  have hNRk := GW2Rd.counterflowNoReturn_of_thm13 h13 c.κ c.hκ c.hκ4 b' J' hb' c.P _ hG' Wk ζk hcfk hζk
  have hWkreg := GW2Later.ae_counterflow_regular h13 c.hκ hcfk hζk
  have hcfreg := GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ
  have hαc := GW2aSingle.ae_chosenTrace h13 c.hκ hfl'
  have hvisP := ae_mem_tipSet_root h13 h13₀ c r hroot
  -- the clock of the root piece
  set A : ℝ≥0 → Ω → ℝ≥0 := fun u ω => capA (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V 0 u ω with hAdef
  have hAT : ∀ ω, A T ω = stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω := fun ω => by
    rw [← capA_zero T ω]
    show (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (0 + T) ω) (V ω)).toNNReal =
      (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (T + 0) ω) (V ω)).toNNReal
    rw [zero_add, add_zero]
  filter_upwards [hgg, hg.2.1, hg₁.2.1, hret, hmain, hmain₀, hd, hcomp, hcfreg, c.hζ, c.hα, hNRp, hNRk, hWkreg,
    hαc, hvisP, Gm.ae_futureJoined_trace h13 c r, hR.ae_pieceRegular, ae_schedW_trace c r [] a h13,
    ae_shape_root0X c r a hx hs0 hGT.1 hv, ae_noContact_rootX hGT.1 hs0 hx hv, hEgood, hGT.2.2]
    with ω hggω hgω hg₁ω hretω hmainω hmain₀ω hdω hcompω hcfω hζω hαω hNRω hNRkω hWkω hαcω hvisω hfutω hprω
      hschω hshω hncω hEω hGTω hlive hcap hsupp
  have hωGT : ω ∈ GT := hGTω.2 (hEω hlive.1).1
  have hsucc : oldSuccess c r [] ω := (GW2Sdi.augRec_mem_succRec_iff c r [] _ ω).1 hlive.1.1.2
  rw [hB0] at hsupp
  obtain ⟨hgood, -⟩ := hfutω [] a hsucc
  have hc0 := stopDrv_cont_of_oldSuccess c r [] a hsucc hprω 0 (by simp [curIdx])
  have hsζ : (c.s : ℝ≥0∞) < c.ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  obtain ⟨-, -, hW'c, hW'0, -⟩ := hcfω
  obtain ⟨-, -, hWkc, hWk0, -⟩ := hWkω
  obtain ⟨-, hℓc, hℓm, hℓr, hiff⟩ := hdω
  have hRc : Continuous fun u => R u ω := hv.2.1 ω
  have hR0 : R 0 ω = 0 := hv.2.2.1 ω
  have hTζ : (T : ℝ≥0∞) < (futFam c r [] a 0 ω).2 := (oldSuccess_nil_iff c r a ω).1 hsucc
  -- the clock is below the cap up to `T`
  have hstartne : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω ≠ ⊤ :=
    ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hltT : min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT T ω) (V ω) < V ω := by
    have h2 : I.capX c (rootPt r.1) ω =
        V ω - stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω := by
      show V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T ω).toNNReal : ℝ≥0∞) = _
      rw [ENNReal.coe_toNNReal hstartne]
    have h3 := hcap
    rw [h2] at h3
    exact tsub_pos_iff_lt.1 h3
  have hltu : ∀ u ≤ T, min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT u ω) (V ω) < V ω :=
    fun u hu => lt_of_le_of_lt (monotone_min_physClockX hGT.1 hs0 hx (V := V) ω hu) hltT
  have hncT := hncω hωGT T hltT
  have hce : Continuous fun u => schedW c r [] a u ω := by
    simp only [schedW, hsucc, ite_true]
    exact (Gm.continuous_futureJoined c r [] a ω).1
  have h0e : schedW c r [] a 0 ω = 0 := by
    simp only [schedW, hsucc, ite_true]
    exact (Gm.continuous_futureJoined c r [] a ω).2
  -- RELDET's kernel-side readings
  obtain ⟨t₀, ht₀, hγt₀, hcontact⟩ := hRD c r a hx hsucc hgood hc0 (hreg 0 ω) hαcω.1 hW'c hW'0 hαω
    (fun v hv => hNRω (c.α ω) hαω v hv) hsζ hs0 (physGoodX_tip_marks (hGT.1 ω hωGT)).1 hschω.1 hncT hWkc hWk0
    hcompω.2 (fun q hq => hNRkω (γ ω) hcompω.2 q hq) hℓc hℓm hℓr hiff
  -- the representatives and the launch forms
  obtain ⟨wP, hwP, hgP⟩ := hgω
  obtain ⟨wP₀, hwP₀, hgP₀⟩ := hg₁ω
  have hdc : IsDomainChart H (Chart.id.recenter (rootPt r.1)) :=
    SB.Lf.isDomainChart_recenter isDomainChart_id (rootPt r.1)
  have hdomH : ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ) = H := coe_dom_recenter_id (rootPt r.1)
  have hlc : ContinuousOn (Chart.id.recenter (rootPt r.1)).2.2 (Chart.id.recenter (rootPt r.1)).dom := by
    rw [hdomH]; exact hdc.continuousOn_lift
  have hlh : InnerProductSpace.HarmonicOnNhd (Chart.id.recenter (rootPt r.1)).2.2
      (Chart.id.recenter (rootPt r.1)).dom := by
    rw [hdomH]; exact harmonicOnNhd_lift_of_isDomainChart hdc
  have hcompL : ∀ B : Set ℂ, H \ (Chart.id.recenter (rootPt r.1)).1 '' (B ∩ ((Chart.id.recenter (rootPt r.1)).dom :
      Set ℂ)) = chartPre (Chart.id.recenter (rootPt r.1)) (H \ B) := fun B => by
    rw [GW2Rd.launchUnion_eq hconf, sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
  obtain ⟨hw₀h, hw₀p⟩ := launch_rep hconf hlc hlh hwP₀ hgP₀ hu₀.1 hu'.1 (chiC c.κ)
  obtain ⟨hwh, hwp⟩ := launch_rep hconf hlc hlh hwP hgP hu₀.1 hu'.1 (chiC c.κ)
  have hformT := hmainω t₀ ht₀ hTζ hγt₀ (GW2Pw.historyTime_pos c r []) hcontact _
    (by rw [hcompL]; exact hwh) (by rw [hcompL]; exact hwp)
  have hform0 := hmain₀ω t₀ ht₀ (lt_of_le_of_lt zero_le hTζ) _ (by rw [hcompL]; exact hw₀h)
    (by rw [hcompL]; exact hw₀p)
  -- the root word's typed data
  set rec := cfRec c.s c.W c.ζ ω with hrec
  set β₀ : BoundaryWord := upW (θr * chiC c.κ) (GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s rec) with hβ₀
  set w₀ : WordType := wordType c.κ β₀ with hw₀
  set Q : ℝ := ((A T ω : ℝ≥0) : ℝ) with hQ
  set Sd : ℝ → ℝ := Ito.rpath (stgDrv (fun q => R q ω) 0) with hSd
  have hU₀r := LocalExt.isBoundedHarmonicExtension_bheAt c.κ (typedRhoL w₀) (typedRhoR w₀) (typedXL c.κ w₀ β₀)
    (typedXR c.κ w₀ β₀)
  set U : ℂ → ℝ := LocalExt.bheAt c.κ (typedRhoL w₀) (typedRhoR w₀)
    (fun i => -rightImg (fun s => -Sd s) (-typedXL c.κ w₀ β₀ i) Q - Sd Q)
    (fun j => rightImg Sd (typedXR c.κ w₀ β₀ j) Q - Sd Q) with hUdef
  have hUr : IsBoundedHarmonicExtension
      (forceBoundaryData c.κ (typedRhoL w₀) (typedRhoR w₀)
        (fun i => -rightImg (fun s => -Sd s) (-typedXL c.κ w₀ β₀ i) Q - Sd Q)
        (fun j => rightImg Sd (typedXR c.κ w₀ β₀ j) Q - Sd Q))
      (forceJumpSet (fun i => -rightImg (fun s => -Sd s) (-typedXL c.κ w₀ β₀ i) Q - Sd Q)
        (fun j => rightImg Sd (typedXR c.κ w₀ β₀ j) Q - Sd Q)) U :=
    LocalExt.isBoundedHarmonicExtension_bheAt c.κ _ _ _ _
  -- the stage-start identity from the retained mean
  set K := jointWordOfRec (specOffset c.κ) c.κ cw rec with hK
  set G₀ : ℂ → ℝ := LocalExt.bheAt c.κ (flowLineRhoL c.κ K.fn K.jumps 0 0) (flowLineRhoR c.κ K.fn K.jumps 0 0)
    (flowLineXL K.fn K.jumps 0) (flowLineXR K.fn K.jumps 0) with hG₀def
  have hG₀ : IsBoundedHarmonicExtension (Supp8.Q3Chain.cfData c.κ K.fn K.jumps)
      (Supp8.Q3Chain.cfJumps K.fn K.jumps) G₀ := by
    unfold Supp8.Q3Chain.cfJumps
    rw [Supp8.Q3Chain.coe_initJumps]
    exact LocalExt.isBoundedHarmonicExtension_bheAt c.κ _ _ _ _
  have hG₀m := BW1LMean.eqOn_bhe_cfData_mean c.hκ (isSorted_jointWordOfRec _ _ _ _) hG₀
  have hretE := hretω hsζ G₀ hG₀ wP₀ hwP₀ hgP₀
  have hretS : retSet c.s c.W c.ζ ω = invHull (fun q : ℝ => c.W q.toNNReal ω) c.s := by
    rw [retSet_of_lt hsζ]
    exact Supp8.RelSafeS.invHull_record_eq hW'0 hW'c.continuousOn hsζ
  have hUc : Continuous fun q : ℝ => c.W q.toNNReal ω := hW'c.comp continuous_real_toNNReal
  have hUq0 : (fun q : ℝ => c.W q.toNNReal ω) 0 = 0 := by simp [hW'0]
  have hjD := Supp8.Q3Rel.isDomainChart_rel hUc hUq0 c.s.coe_nonneg
  have hret' : ∀ z ∈ H \ invHull (fun q : ℝ => c.W q.toNNReal ω) c.s, wP₀ z + ch.u₀ z =
      K.mean (Supp8.GB6.relMap (fun q : ℝ => c.W q.toNNReal ω) c.s z) -
        chiC c.κ * (relLog (fun q : ℝ => c.W q.toNNReal ω) c.s z).im := by
    intro z hz
    have h1 := hretE (show z ∈ H \ retSet c.s c.W c.ζ ω by rw [hretS]; exact hz)
    simp only at h1
    have hmapH : Supp8.GB6.relMap (fun q : ℝ => c.W q.toNNReal ω) c.s z ∈ H := hjD.fwd_mem hz
    rw [← heqU hz.1, h1, hG₀m hmapH]
  have hinst0 := inst0_rootX (θ := θr) c.hκ cw (rootPt r.1) hW'0 hW'c hsζ hRc hR0 hret' (w := w₀) rfl hU₀r
  -- the far-right heights
  have hneg0 := (physGoodX_tip_marks (hGT.1 ω hωGT)).2.2
  have hfarβ := far_typed c.hκ (c := β₀) (w := w₀) rfl
    (GW2Wm.farR_upW (θr * chiC c.κ) (GW2Wm.farR_rootWordX c.hκ cw (rootPt r.1) c.s rec hneg0))
  have hγ'k : IsGeneratingTrace (fun t => Wk t ω) (ζk ω) (γ ω) := by rw [hcompω.1]; exact hcompω.2
  have hWkc' : ContinuousOn (fun t => Wk t ω) {t | (t : ℝ≥0∞) < ζk ω} := hWkc.continuousOn
  have hnegK := ((Supp8.GB6.gb6_rec_spec t₀ hWk0 hWkc' hγ'k (by rw [hcompω.1]; exact ENNReal.coe_lt_top)).2.2.2.2
    hγt₀).2
  have hfarK := GW2Wm.farR_jointWordOfRec c.hκ c' (cfRec t₀ Wk ζk ω) hnegK
  -- the stage reading at the root piece's end
  have hshape : ∀ u ≤ T, H \ schedUnionX c r [] a 0 u ω =
      (relChartX (rootPt r.1) c.s rec).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω)) :=
    fun u hu => hshω hωGT hsucc u (hltu u hu)
  have hA0 : A 0 ω = 0 := by
    show (min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT (0 + 0) ω) (V ω)).toNNReal = 0
    rw [add_zero, physClockX_zero hGT.1 hs0 hx ω, min_eq_left zero_le, ENNReal.toNNReal_zero]
  have hAc : Continuous fun u => A u ω := continuous_capA hGT.1 hs0 hx 0 (hV ω)
  have eT : schedUnionX c r [] a 0 T ω = schedUnionX c r [] a T 0 ω := by
    simp only [schedUnionX, add_zero, zero_add]
  have e0 : schedUnionX c r [] a 0 0 ω = retSet c.s c.W c.ζ ω := by
    have hK0 : fwdHull (fun q : ℝ => schedW c r [] a q.toNNReal ω) 0 = ∅ :=
      fwdHull_zero_eq_empty (hce.comp continuous_real_toNNReal) (by simp [h0e])
    rw [retSet_of_lt hsζ]
    simp only [schedUnionX, schedHullX, hsucc, ↓reduceIte, schedHull, add_zero, NNReal.coe_zero]
    rw [hK0, image_empty, union_empty]
  have key := sample_stage_read0X c r a hx T (GW2Pw.historyTime_pos c r []) le_rfl ω hsucc hgood hc0 hTζ
    (hreg 0 ω) hαcω.1 hWkc hWk0 hcompω.2 hW'c hW'0 hαω hsζ hce h0e hℓc hℓm hℓr
    (fun hxp => vis_of_mem_tipSet hαω hW'c hW'0 (hvisω hxp)) hiff ht₀ hcontact (θ := θr) hRc hR0 hA0
    (fun u => zero_le) hAc hshape hb' hu' huθ c' (by rw [e0]; exact hform0) (by rw [eT]; exact hformT)
    (typedRhoL w₀) (typedRhoR w₀) (fun i => typedXL_nonpos _ _ _ i) (fun j => typedXR_nonneg _ _ _ j) hU₀r
    hinst0 hfarK hfarβ rfl (by simpa only [NNReal.coe_zero, sub_zero] using hUr)
  simp only [NNReal.coe_zero, sub_zero] at key
  -- the representative is the stage mean read from the root's start
  have hsh := GW2Rd.stgChart_inv_image (relChartX (rootPt r.1) c.s rec) hRc hR0 0 (A T ω)
  rw [zero_add, ← hshape T le_rfl, eT] at hsh
  have hcsD := isDomainChart_stgChart_relChartX (rootPt r.1) c.s rec hRc hR0 0
  have hpt : ∀ y ∈ H \ schedUnionX c r [] a T 0 ω,
      wP y = stgMeanRX c.κ (rootPt r.1) c.s rec (fun q => R q ω) 0 Q U ch.u₀ (specOffset c.κ + θr * chiC c.κ) y := by
    intro y hy
    rw [← hsh] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h1 := key z hz
    have hcz : (stgChart (relChartX (rootPt r.1) c.s rec) (fun q => R q ω) 0).1
        ((stgChart (relChartX (rootPt r.1) c.s rec) (fun q => R q ω) 0).2.1 z) = z := hcsD.fwd_inv hz.1
    simp only [stgMeanRX]
    rw [hcz]
    linarith
  set L := historyProgram c r [] with hLdef
  have hLN : L.length = (entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1 := GW2Rd.length_historyProgram c r []
  set P : Fin ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) → RecData :=
    fun k => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) k ω with hP
  have hagree : ∀ u ≤ T, RootJ31.joinedRead L (fun i => P (Fin.cast hLN i)) u = schedW c r [] a u ω := by
    intro u hu
    have e1 : schedW c r [] a u ω = Gm.futureJoined c r [] a ω u :=
      congrFun (schedW_of_oldSuccess c r [] a hsucc) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r [] a ω hu]
    rfl
  have hE0 : (entryList ([] : List (EntryIdx c.Θ c.Q))).length = 0 := rfl
  have hbw := GW2Wm.baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r [] a) (Wα := c.W)
    (ζα := c.ζ) (GT := GT) (V := V) (T := T) (R := R) (γ := schedTr c r [] a) (α := c.α) c.κ cw hGT.1 hs0 hx
    L _ hLN (xr := stageEncRec c r []) (ω := ω) (P := P) rfl hRc hR0 hωGT (hV ω)
    (fun j hj => by
      have hj0 : j = 0 := by rw [hE0] at hj; omega
      subst hj0
      exact zero_le)
    (fun j hj => by
      have hj0 : j = 0 := by rw [hE0] at hj; omega
      subst hj0
      exact zero_le)
    (fun j h0 h1 => by rw [hE0] at h1; omega) hagree
  have hdrv : (fun u => GW2Rd.stgDrv (fun q => R q ω) 0 u) = fun q => R q ω := by
    funext q
    simp [GW2Rd.stgDrv, hR0]
  have hbd0 : GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L
      ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) T ω 0 = 0 := by
    simp [GW2Wm.trueBdX]
  have hbd1 : GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L
      ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) T ω 1 = A T ω := by
    rw [hAT ω]
    simp [GW2Wm.trueBdX, hE0]
  have hβs : ch.β (I.srecX c r [] (rootPt r.1) ω) = GW2Rd.upW (candAngle c r [] a * chiC c.κ)
      (stopWord c.κ (GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω), (rootEntry r.1).1,
        recOf ((A T ω : ℝ≥0) : ℝ≥0∞) (fun q => R q ω, ⊤))) := by
    rw [hβ]
    show GW2Rd.upW (candAngle c r [] a * chiC c.κ) (GW2Wm.baseWordX c.κ cw (rootPt r.1) c.s L _ hLN
      (GW2Rd.augRec (stageEncRec c r []) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V T R) ω)) = _
    rw [hbw]
    show GW2Rd.upW (candAngle c r [] a * chiC c.κ) (stopWord c.κ
      (GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω), GW2Wm.progAngle L 0,
        recOf (((GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L _ T ω 1 -
          GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L _ T ω 0 : ℝ≥0)) : ℝ≥0∞)
          (fun u => GW2Rd.stgDrv (fun q => R q ω)
            (GW2Wm.trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) GT V L _ T ω 0) u, ⊤))) = _
    rw [hbd0, hbd1, tsub_zero, hdrv]
    rfl

  -- the instance's typed data at clock `0`
  have hdc' : Continuous fun q => I.drvX c (rootPt r.1) q ω := continuous_stgDrv hRc _
  have hd0 : I.drvX c (rootPt r.1) 0 ω = 0 := stgDrv_zero _ _
  have hUi := bhe_bheProc_typedX_zero (r := r) (l := []) I (rootPt r.1) w ω hdc' hd0
  rw [show I.β (I.srecX c r [] (rootPt r.1) ω) = _ from hβs] at hUi
  have hw : wordType c.κ (GW2Rd.upW (candAngle c r [] a * chiC c.κ)
      (stopWord c.κ (GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω), (rootEntry r.1).1,
        recOf ((A T ω : ℝ≥0) : ℝ≥0∞) (fun q => R q ω, ⊤)))) = w := by
    rw [← hβs]
    exact hlive.2
  have hUiE := eqOn_typed_upW_mean c.hκ _ (isSorted_stopWord _ _) _ hw hUi
  have hUE := eqOn_explored_typed (θ := θr) (c := GW2Wm.rootWordX c.κ cw (rootPt r.1) c.s rec) (w := w₀) rfl
    (S := stgDrv (fun q => R q ω) 0) (continuous_stgDrv hRc _) (stgDrv_zero _ _) (A T ω) hUr
  have hdrv' : stgDrv (fun q => R q ω) 0 = fun q => R q ω := hdrv
  rw [hdrv'] at hUE
  -- the restart at the instance's stage start
  have hdom' : ∀ y ∈ H \ schedUnionX c r [] a T 0 ω,
      y ∈ ((stgChart (relChartX (rootPt r.1) c.s rec) (fun q => R q ω) (0 + A T ω)).dom : Set ℂ) := by
    intro y hy
    rw [GW2Rd.dom_stgChart (GW2Rz.isConformal_relChartX _ _ _) hRc hR0, zero_add, ← hshape T le_rfl, eT]
    exact hy
  rw [hggω, hgP φ hsupp]
  congr 1
  funext z
  by_cases hz : z ∈ tsupport φ
  · have hy := hsupp hz
    rw [hpt z hy, stgMeanRX_restart c.κ (rootPt r.1) c.s rec hRc hR0 0 (A T ω)
      (U₀ := bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drvX c (rootPt r.1))
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (ch.β y.1)) i t
          (I.srecX c r [] (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (ch.β y.1)) j t
          (I.srecX c r [] (rootPt r.1) ω, relVar I.Hr (I.drvX c (rootPt r.1)) (I.capX c (rootPt r.1)) ω)) ω 0)
      (σa := ch.σa) (fun z hz => (hUiE z hz).trans (by rw [hUE hz, hσ]; ring)) (hdom' z hy), zero_add, hAT ω]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

/-- **RELDET's `hnil` form**: `ClaimAllX` at the history `l = []` at a root `x ∈ {0} ∪ lowerArcRoots`, for a word `cw`
of the counterflow's data (given RELDET's `SampleContactRoot0XStatement`, D62). -/
theorem claimAllX_nilX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hRD : SampleContactRoot0XStatement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) (hs0 : 0 < c.s) {cw : BoundaryWord}
    (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw) : GW2Rd.ClaimAllX c r cw [] := by
  intro a GT hGT R V hA hV ch hu₀ _ _ hβ hσa w
  exact claimAtX_nilX h12 h13 h12₀ h13₀ hRD c r a hroot hs0 hGT hA hV ch hu₀ hcw hβ hσa w

/-- **Claim(k)'s base at a root `x`, outright** (`ClaimAtX` at `l = []`; RELDET's readings discharged). -/
theorem claimAtX_nil_rootX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r [] a) (schedTr c r [] a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : GW2Sdh.SchedChoice Ω) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps ch.u₀)
    {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    (hβ : ch.β = GW2Wm.schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r [])
      ((entryList ([] : List (EntryIdx c.Θ c.Q))).length + 1) (GW2Rd.length_historyProgram c r [])
      (candAngle c r [] a))
    (hσ : ch.σa = specOffset c.κ + candAngle c r [] a * chiC c.κ) (w : WordType) :
    ClaimAtX c r [] a GT hA ch w :=
  claimAtX_nilX h12 h13 h12₀ h13₀ GW2Rd.sampleContactRoot0XStatement c r a hroot hs0 hGT hA hV ch hu₀ hcw hβ hσ w

/-- **RELDET's `hnil`, outright**: `ClaimAllX` at `l = []` at every root `x ∈ {0} ∪ lowerArcRoots`, for a word `cw` of
the counterflow's data. -/
theorem claimAllX_nil_rootX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)
    (hs0 : 0 < c.s) {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw) : GW2Rd.ClaimAllX c r cw [] :=
  claimAllX_nilX h12 h13 h12₀ h13₀ GW2Rd.sampleContactRoot0XStatement c r hroot hs0 hcw

end InteractingSLE.Theorem14.GW2Kx
