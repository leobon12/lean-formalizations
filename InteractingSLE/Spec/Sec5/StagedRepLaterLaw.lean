/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterIdent

/-!
# Prop 5.9's root stage: identifications on PIECES' space and on the glued space

Packet PROVE-STAGED-REP2. The two a.s. identities used by the law transfer:

* `startLam`, `startC`: the dilation `rootLam` read from the junction marks of the stage start (a Borel function of
  the start), and its time factor;
* `exists_cfTrace`: PIECES' counterflow has a generating trace a.s. (Zhan's admissible-word trace);
* **`rootObs_eq_gamObs`**: at good samples, PIECES' root start and candidate samples are `gamObs` of
  `(qField, counterflow history)`;
* **`glueObs_eq_gamObs`**: at good glued samples, the dilated image word's start and samples are `gamObs` of
  `(qField, glued history)`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Sec4 GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces StagedKCand StagedKill
open WangWu.ImgWord

/-! ### The dilation read from the start -/

section Start

variable {nL nR : ℕ}

open scoped Classical in
/-- **The root dilation read from a start**: `3 / min(−x_L^{last}, x_R^{last})` (`1` if a junction gap fails), the
form of `rootLam` on the junction marks. -/
def startLam (y : Start (nL + 1) (nR + 1)) : ℝ :=
  if 0 < -y.2.1 (Fin.last nL) ∧ 0 < y.2.2 (Fin.last nR) then 3 / min (-y.2.1 (Fin.last nL)) (y.2.2 (Fin.last nR))
  else 1

theorem startLam_pos (y : Start (nL + 1) (nR + 1)) : 0 < startLam y := by
  classical
  unfold startLam
  split_ifs with h
  · exact div_pos (by norm_num) (lt_min h.1 h.2)
  · exact one_pos

theorem measurable_startLam : Measurable (startLam (nL := nL) (nR := nR)) := by
  classical
  have hL : Measurable fun y : Start (nL + 1) (nR + 1) => y.2.1 (Fin.last nL) :=
    (measurable_pi_apply _).comp measurable_snd.fst
  have hR : Measurable fun y : Start (nL + 1) (nR + 1) => y.2.2 (Fin.last nR) :=
    (measurable_pi_apply _).comp measurable_snd.snd
  refine Measurable.ite ?_ (measurable_const.div (hL.neg.min hR)) measurable_const
  exact (measurableSet_lt measurable_const hL.neg).inter (measurableSet_lt measurable_const hR)

/-- The time factor of the root dilation. -/
def startC (y : Start (nL + 1) (nR + 1)) : ℝ≥0 := tf (startLam y)

theorem measurable_startC : Measurable (startC (nL := nL) (nR := nR)) :=
  (measurable_startLam.inv.pow_const 2).real_toNNReal

theorem startC_ne_zero (y : Start (nL + 1) (nR + 1)) : startC y ≠ 0 := tf_ne_zero (startLam_pos y)

theorem startLam_histStart (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (r : ℝ≥0) (y : HistorySpace 0 0) :
    startLam (histStart xL xR r y) =
      if 0 < -junL (cfDrv0 r y) r ∧ 0 < junR (cfDrv0 r y) r then 3 / min (-junL (cfDrv0 r y) r) (junR (cfDrv0 r y) r)
      else 1 := by
  simp only [startLam, histStart, Fin.snoc_last]

end Start

/-! ### PIECES' counterflow trace -/

theorem exists_cfTrace {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hb : IsFig51Bounds κ a b a' b') {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∃ γ : Ω → ℝ≥0 → ℂ, ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω) := by
  classical
  obtain ⟨b₀, J₀, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hae := ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk'
    (Theorem15.isOrderedForceWord_flowLine b₀ J₀ 0) hadm hC.1
  refine ⟨fun ω => if hω : ∃ η, IsGeneratingTrace (fun t => W t ω) (ζ ω) η then hω.choose else fun _ => 0, ?_⟩
  filter_upwards [hae] with ω hω
  obtain ⟨hζ, -, η, hη⟩ := hω
  have hex : ∃ η, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := ⟨η, by rw [hζ]; exact hη⟩
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

/-! ### PIECES' root candidate at good samples -/

section Pieces

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The (field in chart `Q`, counterflow history) pair on PIECES' space. -/
def pieceZ (κ' : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω' : Ω × Ωa) :
    Gam :=
  (qField x₀ κ' h ω'.1, Cond44Ref.cfHistory W ζ ω'.1)

theorem measurable_pieceZ (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    Measurable (pieceZ (Ωa := Ωa) x₀ κ h W ζ) :=
  (((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm).comp measurable_fst).prodMk
    ((measurable_cfHistory_of_strip hcf).comp measurable_fst)

omit mΩ [MeasurableSpace Ωa] in
theorem gamPath_pieceZ (ω' : Ω × Ωa) :
    gamPath h44 hκ hκ4 (x₀ := x₀) hb (pieceZ x₀ κ h W ζ ω') =
      qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) 0 Fin.elim0 ω'.1 := by
  funext u
  simp only [gamPath, qPath, qDrv_zero, pieceZ]

omit [MeasurableSpace Ωa] in
/-- **PIECES' root start and root candidate samples at a good sample are `gamObs` of (field, history).** -/
theorem rootObs_eq_gamObs (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) {q : ℚ} (t : Fin 0 → ℝ≥0) {ω' : Ω × Ωa}
    (h1 : ω'.1 ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal)
    (h2 : pieceZ x₀ κ h W ζ ω' ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q ω',
      pieceSamp (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q 0 t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q 0 t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q 0 t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q 0 t).ζ ω') =
    gamObs h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal (pieceZ x₀ κ h W ζ ω') := by
  have ht : t = Fin.elim0 := funext fun i => i.elim0
  subst ht
  rw [gamObs_eq h44 hκ hκ4 hb _ h2]
  set r : ℝ≥0 := (q : ℝ).toNNReal with hr
  set D := rootData x₀ h44 hκ hκ4 hb P h W ζ r (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
    (canonXR x₀ hκ hb W ζ q) (noise q) with hD
  have hcfm := measurable_cfHistory_of_strip hcf
  have hlamm : Measurable (canonLam W ζ q) := (measurable_rootLam _).comp hcfm
  have hxLm : Measurable (canonXL x₀ hκ hb W ζ q) := measurable_pi_iff.2 fun i =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm))
  have hxRm : Measurable (canonXR x₀ hκ hb W ζ q) := measurable_pi_iff.2 fun j =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp hcfm))
  have hReg := isReg_rootData x₀ h44 hκ hκ4 hb hhm hcf hlamm (fun ω => rootLam_pos _ _) hxLm hxRm (r := r)
    (noise := noise q)
  have hv : D.valid 0 Fin.elim0 := isValid_zero _
  have hGc : ω'.1 ∈ D.Gc 0 Fin.elim0 := ⟨hv, h1⟩
  have hgood := hReg.good_Gc 0 Fin.elim0 ω'.1 hGc
  have hS := TreeData.pieceSamp_cand_zero D Fin.elim0 ((hReg.isKilledFamily 0 Fin.elim0).arc ω'.1) h1 hv
  have himg : D.img 0 Fin.elim0 ω'.1 = fun u => (rootLam r (Cond44Ref.cfHistory W ζ ω'.1) : ℂ) *
      imgCurve (cfDrv0 r (Cond44Ref.cfHistory W ζ ω'.1)) r
        (gamPath h44 hκ hκ4 (x₀ := x₀) hb (pieceZ x₀ κ h W ζ ω')) u := by
    rw [gamPath_pieceZ]; exact tImg_of_mem hGc
  have hpre : D.pre 0 Fin.elim0 ω'.1 = preContact (gamPath h44 hκ hκ4 (x₀ := x₀) hb (pieceZ x₀ κ h W ζ ω'))
      (cfHullQ r (Cond44Ref.cfHistory W ζ ω'.1)) := by
    rw [gamPath_pieceZ]; exact tPre_of_mem hGc
  have hxL : D.xL0 ω'.1 = fun i => rootLam r (Cond44Ref.cfHistory W ζ ω'.1) *
      rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω'.1) i := rfl
  have hxR : D.xR0 ω'.1 = fun j => rootLam r (Cond44Ref.cfHistory W ζ ω'.1) *
      rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω'.1) j := rfl
  rw [himg, hpre, hxL, hxR] at hS
  have hcfg : CfGood r (Cond44Ref.cfHistory W ζ ω'.1) := hgood.1
  have hα : IsProperArc (gamPath h44 hκ hκ4 (x₀ := x₀) hb (pieceZ x₀ κ h W ζ ω')) := by
    rw [gamPath_pieceZ]; exact hgood.2
  have hg : IsKilledArc (imgCurve (cfDrv0 r (Cond44Ref.cfHistory W ζ ω'.1)) r
      (gamPath h44 hκ hκ4 (x₀ := x₀) hb (pieceZ x₀ κ h W ζ ω')))
      (preContact (gamPath h44 hκ hκ4 (x₀ := x₀) hb (pieceZ x₀ κ h W ζ ω'))
        (cfHullQ r (Cond44Ref.cfHistory W ζ ω'.1))) := by
    rw [hcfg.2]
    exact isKilledArc_imgCurve (continuous_cfDrv0 r _) (cfDrv0_zero r _) r.coe_nonneg hcfg.1 hα
  rw [samp_kW_smul hg (rootLam_pos r _)] at hS
  exact Prod.ext rfl hS

end Pieces

/-! ### The dilated glued image word at good samples -/

section Glue

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The root code driver's seed line is the stage-0 code path (infinite lifetime). -/
theorem seedLine_rootDrv {ω : Ω} (htop : (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2 = ⊤) (y : HistorySpace 0 0) :
    seedLine (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2)
      (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) ω =
      gamPath h44 hκ hκ4 (x₀ := x₀) hb (qField x₀ κ h ω, y) := by
  have hk : (fun t => killedProc (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2)
      (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) t ω) =
      fun t => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t := funext (killedProc_of_eq_top htop)
  funext s
  simp only [seedLine, hk]
  simp only [gamPath, qPath, qDrv_zero, rootDrv]

/-- **The dilated glued image word at a good sample is `gamObs` of (field, glued history).** -/
theorem glueObs_eq_gamObs (r : ℝ≥0) {E : Set (Ω × HistorySpace 0 0)}
    {p : Ω × HistorySpace 0 0} (hpE : p ∈ E)
    (hZ : (qField x₀ κ h p.1, p.2) ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb)
    (htop : (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h p.1).2 = ⊤) :
    (dilV (startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2))
      (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2),
      samp (fun t => (√(startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) : ℝ))⁻¹ *
          imgW r (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2)
            (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) E
            (startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) * t) p)
        (fun i t => (√(startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) : ℝ))⁻¹ *
          imgVL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r
            (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2)
            (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) E i
            (startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) * t) p)
        (fun j t => (√(startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) : ℝ))⁻¹ *
          imgVR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r
            (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2)
            (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) E j
            (startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
              (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) * t) p)
        ((show ℝ≥0∞ from imgT r (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2)
          (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) E p) /
          (startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) : ℝ≥0∞))) =
    gamObs h44 hκ hκ4 (x₀ := x₀) hb r (qField x₀ κ h p.1, p.2) := by
  rw [gamObs_eq h44 hκ hκ4 hb r hZ]
  have hC : startC (histStart (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
      (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) r p.2) =
      tf (rootLam r p.2) := by
    rw [startC, startLam_histStart]; rfl
  have hseed := seedLine_rootDrv h44 hκ hκ4 hb htop p.2
  rw [hC]
  simp only [Word49.imgW, Word49.imgVL, Word49.imgVR, Word49.imgT, Word49.gCurve_of_mem hpE,
    Word49.gPre_of_mem hpE, Word49.gXL_of_mem hpE, Word49.gXR_of_mem hpE,
    hseed, dilV, histStart, sqrt_tf_inv (rootLam_pos r p.2), mul_zero, scSamp]
  rfl

end Glue

end InteractingSLE.Sec5.CrossCond.StagedRepLater
