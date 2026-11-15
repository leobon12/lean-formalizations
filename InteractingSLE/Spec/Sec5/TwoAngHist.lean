/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoAngDrivers

/-!
# The two-angle paths as staged histories of the field, and the two-angle strip system (R48-safe)

Packet PROVE-TWOANGLE. The drivers `TwoAngle.twoFam` (first piece `admDrv θ₀` of the field, continuation the
record-angle stage driver of the conditional field after the first piece, `TwoAngDrivers`) realize the two-angle
program `η^{t₀,∞}_{θ₀,θ}` (`StripSys.twoAngleSpec θ₀ t₀ θ`) as a staged history (`IsStagedHistory`) of the field, by
the forward route of PROVE-PROP59-SCHED (Astra follow-up 5 §2.1, ruling R73), with two stages:

* **`stageOK_of_witness`** (any program): given the marked conditional field `(β, Y)` before stage `k`
  (`IsStageWitness`) and `E k = D (β, Y)` at every sample, stage `k` is a conditional flow line as soon as `D` turns
  every GFF with the data of `β ω₀` into its flow-line driver (PROVE-PROP59-SCHED's `stageOK_schedDrivers`, abstracted);
* stage `0`: the witness is `StripDet.stageWitness_zero`, `D = admDrv θ₀` (direct (4.4) at `θ₀`);
* stage `1`: the witness is the stop word and record field of the first piece (`post_stage` with the stop law, as in
  `StripDet.ae_drv_one`), `D = recStage θ₀ θ`, which is a flow-line driver of every GFF with the stop word's data by
  `StripDet.cond44_flowLine_stopWord` (`θ₀ ≤ θ`) or `cond44_reflWord_stopWord` (`θ < θ₀`) and
  `isFlowLineDriver_recStage`;
* later instructions launch nothing.

Main results: **`isStagedHistory_twoFam`** (record-angle heights), **`isStagedHistory_twoFam_strip`** (the strip heights
of Aux. lemma 130 at every angle of `[−π/2, π/2]`), and **`exists_isTwoAngleStripSystem`**: a two-angle strip system
exists, R48-safely, on every field and centred counterflow with the strip heights (drivers regular at every sample) —
the construction asked for by Theorems 1.2–1.3's leaf `hWordT` (PROVE-WORDSAFE §4 item 1).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only
named input is `Theorem12ParamCond44Statement` (`h44`, R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.TwoAngle

open LQGMetric (DistOn)
open QuantumZipper (H chiC)
open Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord
open Sec7 Sec7.AdmCode Sec7.StripWall Sec7.StripDet Prop513Schedule

/-! ### A stage clause from the marked conditional field -/

section Generic

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A stage clause from the marked conditional field** (PROVE-PROP59-SCHED's `stageOK_schedDrivers`, for any
program and any stage map `D`). If `(β, Y)` is the marked conditional field before stage `k`, the stage driver is
`D (β, Y)` at every sample, and, for almost every launching `ω₀`, `D (β ω₀, ·)` turns every GFF with the data of
`β ω₀` into its angle-`θ_k` flow-line driver, then stage `k` is a conditional flow line. -/
theorem stageOK_of_witness (hb : IsPiecewiseConstantBoundaryData b J) (hhm : Measurable h) {spec : ExplSpec}
    {E : ℕ → Ω → Driver}
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hw : IsStageWitness κ b J P h spec E k β Y) (D : Context → Driver)
    (hE : ∀ ω, E k ω = D (β ω, Y ω))
    (hD : ∀ᵐ ω₀ ∂P, (ExplState.run κ b J spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∀ (Q : Measure Ω) [IsProbabilityMeasure Q] (Y' : Ω → DistOn upperHalfPlaneOpens) (E' : Ω → Driver),
        IsGFFWithBoundaryData Q Y' (β ω₀).fn (β ω₀).jumps → Measurable E' →
        (∀ᵐ ω ∂Q, E' ω = D (β ω₀, Y' ω)) →
        IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps (instrAngle spec k) Q Y'
          (fun t ω => (E' ω).1 t) (fun ω => (E' ω).2)) :
    StageOK κ b J P h spec E k := by
  have hB := runMeasStatement.{u}
  have hEm' : ∀ j < k, Measurable (E j) := fun j _ => hEm j
  have hreg' : ∀ j < k, ∀ ω, IsRegularDriver (E j ω) := fun j _ => hreg j
  have hpm : Measurable (pastMap κ b J spec E k) := measurable_pastMap hB hb spec hEm' hreg' k le_rfl
  have h𝒢 : pastSigma κ b J spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hβf : β.FactorsThrough (pastMap κ b J spec E k) := by
    have hβ := hw.1
    rw [pastSigma_eq_comap] at hβ
    exact hβ.factorsThrough
  filter_upwards [hw.2.2.2, hw.2.2.1, hD, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hw.2.2.1,
    ae_ae_run_eq hB hb spec hEm' hreg' (P := P)] with ω₀ hk₀ hp₀ hD₀ hpK hrunK c' θ' hcθ
  have hl : (ExplState.run κ b J spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hcθ]; exact Option.some_ne_none _
  obtain ⟨hspec', -, hc'⟩ := eq_launch_of_launches spec _ hcθ
  have hθ' : instrAngle spec k = θ' := by unfold instrAngle; rw [hspec']
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  set c₀ := (ExplState.run κ b J spec (fun j => E j ω₀) k).2.2.2.2.1 with hc₀
  set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) with hh'def
  have hT' : ∀ ω, IsChartTransport c₀ 1 0 (chiC κ) (h ω) (h' ω) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ _
  have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf 1 0 _).comp hhm
  have hYh' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b J spec E k) ω₀), Y ω = h' ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b J spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω] at hT
    exact IsChartTransport.unique hconf hT (hT' ω)
  have hβK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b J spec E k) ω₀), β ω = β ω₀ := by
    filter_upwards [hrunK] with ω hrω
    refine hβf (a := ω) (b := ω₀) ?_
    funext i
    simp only [pastMap, hrω]
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b J spec E k) ω₀) h' (β ω₀).fn (β ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm hYh'
  have hEK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b J spec E k) ω₀), E k ω = D (β ω₀, h' ω) := by
    filter_upwards [hYh', hβK] with ω hωY hωβ
    rw [hE ω, hωY, hωβ]
  have hfl := hD₀ hl (condExpKernel P (pastSigma κ b J spec E k) ω₀) h' (E k) hG (hEm k) hEK
  rw [hθ'] at hfl
  rw [← hc'] at hT'
  exact ⟨_, _, h', (β ω₀).isPiecewiseConstantBoundaryData, hT', hfl⟩

end Generic

/-! ### The two stages of `η^{t₀,∞}_{θ₀,θ}` -/

section Two

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {c₀ : BoundaryWord} {θ₀ θ : ℝ} {t₀ : ℝ≥0}

/-- A two-angle program launches nothing from its third instruction on. -/
theorem stageOK_of_two_le {E : ℕ → Ω → Driver} {k : ℕ} (hk : 2 ≤ k) :
    StageOK κ b J P h (StripSys.twoAngleSpec θ₀ t₀ θ) E k := by
  refine Eventually.of_forall fun ω₀ c θ' hl => ?_
  have h1 := (eq_launch_of_launches _ _ hl).1
  have hnone : (StripSys.twoAngleSpec θ₀ t₀ θ).2.2[k]? = none := by
    simp only [StripSys.twoAngleSpec, StripSys.twoAngleProg]
    exact List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)
  rw [hnone] at h1
  exact absurd h1 (by simp)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The data of the field as the word `shiftW 0 c₀`. -/
theorem isGFF_word₀ (hh : IsGFFWithBoundaryData P h b J) (hc₀J : c₀.jumps = J) (hc₀ : ∀ y ∉ J, c₀.fn y = b y) :
    IsGFFWithBoundaryData P (fun ω => flowField 0 0 (h ω)) (shiftW 0 c₀).fn (shiftW 0 c₀).jumps := by
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (J : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  exact isGFFWithBoundaryData_shiftW 0 hh₀

/-- **Stage `0`**: the first piece is the angle-`θ₀` flow line of the field (direct (4.4) heights at `θ₀`), with
infinite lifetime almost surely. -/
theorem stageOK_twoFam_zero (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hc₀J : c₀.jumps = J) (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    StageOK κ b J P h (StripSys.twoAngleSpec θ₀ t₀ θ) (twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h) 0 ∧
      ∀ᵐ ω ∂P, (twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h 0 ω).2 = ⊤ := by
  set E := twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h with hEdef
  have hEm : ∀ j, Measurable (E j) := measurable_twoFam h44 hκ hκ4 c₀ θ₀ _ θ hh.1
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := twoFam_regular h44 hκ hκ4 c₀ θ₀ _ θ h
  obtain ⟨hL', hR'⟩ := shiftW_zero_heights hc₀J hc₀ hL0 hR0
  have h44θ := cond44_flowLine_of_heights hκ (shiftW 0 c₀).isPiecewiseConstantBoundaryData θ₀ hL' hR'
  have hE : ∀ ω, E 0 ω = admDrv h44 hκ hκ4 θ₀ ((fun _ => shiftW 0 c₀) ω, flowField 0 0 (h ω)) :=
    fun ω => twoFam_zero h44 hκ hκ4 c₀ θ₀ _ θ h ω
  refine ⟨stageOK_of_witness hb hh.1 hEm hreg
    (stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀) (admDrv h44 hκ hκ4 θ₀) hE
    (Eventually.of_forall fun ω₀ _ Q _ Y' E' hG hE'm hE' =>
      (Prop59Sched.isFlowLineDriver_admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀) h44θ hG hE'm hE').2), ?_⟩
  exact (Prop59Sched.isFlowLineDriver_admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀) h44θ (isGFF_word₀ hh hc₀J hc₀)
    (hEm 0) (Eventually.of_forall hE)).1

/-- **Stage `1`**: the continuation is the angle-`θ` flow line of the conditional field after the first piece, read in
its record chart — directly when `θ₀ ≤ θ` (direct (4.4) heights at `θ`), through the reflection when `θ < θ₀`
(reflected heights at `θ`). -/
theorem stageOK_twoFam_one (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hc₀J : c₀.jumps = J) (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hup : θ₀ ≤ θ → (∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ * chiC κ)
    (hdown : θ < θ₀ → (∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ)
    (hθπ : θ ≤ θ₀ + Real.pi) (hθπ' : θ₀ ≤ θ + Real.pi) :
    StageOK κ b J P h (StripSys.twoAngleSpec θ₀ t₀ θ) (twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h) 1 := by
  set spec := StripSys.twoAngleSpec θ₀ t₀ θ with hspec
  set E := twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h with hEdef
  have hB := runMeasStatement.{u}
  have hEm : ∀ j, Measurable (E j) := measurable_twoFam h44 hκ hκ4 c₀ θ₀ _ θ hh.1
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := twoFam_regular h44 hκ hκ4 c₀ θ₀ _ θ h
  obtain ⟨hok₀, hζ₀⟩ := stageOK_twoFam_zero h44 hκ hκ4 (t₀ := t₀) (θ := θ) hb hh hc₀J hc₀ hL0 hR0
  obtain ⟨hβ₀, hY₀, hpath₀, hker₀⟩ := stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀
  have hpost := post_stage (spec := spec) (E := E) (ℓ := 0)
    (StripSideHeightProb.isStopLaw_stopWord hκ) hB hκ hb hh (fun j _ => hEm j) (fun j _ => hreg j) hok₀
    hβ₀ hY₀ hpath₀ hker₀
  have hpm : Measurable (pastMap κ b J spec E 1) :=
    measurable_pastMap hB hb _ (fun j _ => hEm j) (fun j _ => hreg j) 1 le_rfl
  have h𝒢 : pastSigma κ b J spec E 1 ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hr : Measurable (rec₀ κ b J θ₀ θ t₀ E) := measurable_pi_iff.1 hpm (Fin.last 0)
  have hβ₁ : Measurable[pastSigma κ b J spec E 1] (fun ω => word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω)) :=
    Measurable.comp (g := word₁ κ θ₀ c₀) (f := rec₀ κ b J θ₀ θ t₀ E) (measurable_word₁ κ θ₀ c₀)
      measurable_rec₀_past
  have hY₁ : Measurable (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun ω => (rec₀ κ b J θ₀ θ t₀ E ω, h ω)) (measurable_field₁ κ) (hr.prodMk hh.1)
  have hpath₁ : ∀ᵐ ω ∂P, (ExplState.run κ b J spec (fun j => E j ω) (1 + 1)).2.2.2.1 1 ≠ none →
      (ExplState.run κ b J spec (fun j => E j ω) 1).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b J spec (fun j => E j ω) 1).2.2.2.2.1.2.2
        ((ExplState.run κ b J spec (fun j => E j ω) 1).2.2.2.2.1.2.1 w)) H ∧
      IsChartTransport (ExplState.run κ b J spec (fun j => E j ω) 1).2.2.2.2.1 1 0
        (chiC κ) (h ω) (field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) := by
    filter_upwards [hζ₀] with ω hω _
    have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω]; exact ENNReal.coe_lt_top
    have hrec : rec₀ κ b J θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_one_last ω
    rw [chart_one_eq (hreg 0 ω) h0, hrec]
    refine ⟨isConformal_recChart _, continuousOn_recChart_lift _, ?_⟩
    rw [field₁, Prop74B.flowField_zero_zero]
    exact isChartTransport_recField κ _ _
  have hker₁ : ∀ᵐ ω₀ ∂P, (ExplState.run κ b J spec (fun j => E j ω₀) (1 + 1)).2.2.2.1 1 ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b J spec E 1) ω₀)
        (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) (word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω₀)).fn
        (word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω₀)).jumps := by
    have hG := ae_isGFFWithBoundaryData_condExpKernel h𝒢 (M := univ)
      (β := fun ω => word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω))
      (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hY₁ (fun φ => by
        filter_upwards [hpost.2 φ] with ω hω _
        exact hω (launch_zero _) (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)))
    filter_upwards [hG] with ω₀ hω₀ _
    exact hω₀ (mem_univ _)
  have hw : IsStageWitness κ b J P h spec E 1 (fun ω => word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω))
      (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) := ⟨hβ₁, hY₁, hpath₁, hker₁⟩
  have hE : ∀ ω, E 1 ω = recStage h44 hκ hκ4 θ₀ θ
      ((fun ω => word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω)) ω, (fun ω => field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω)) ω) := by
    intro ω
    have hrec : rec₀ κ b J θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (drv₀ h44 hκ hκ4 c₀ θ₀ (h ω)) := by
      rw [show rec₀ κ b J θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) from pastMap_one_last ω, hEdef, twoFam_zero]
    change E 1 ω = recStage h44 hκ hκ4 θ₀ θ (word₁ κ θ₀ c₀ (rec₀ κ b J θ₀ θ t₀ E ω),
      field₁ κ (rec₀ κ b J θ₀ θ t₀ E ω) (h ω))
    rw [hrec]
    exact (twoFam_succ h44 hκ hκ4 c₀ θ₀ _ θ h 0 ω).trans rfl
  -- the heights of the word `shiftW 0 c₀`
  have hfn : ∀ y, y ∉ (shiftW 0 c₀).jumps → y ∉ J ∧ (shiftW 0 c₀).fn y = b y := fun y hy =>
    shiftW_zero_fn_of_notMem hc₀J hc₀ hy
  refine stageOK_of_witness hb hh.1 hEm hreg hw (recStage h44 hκ hκ4 θ₀ θ) hE
    (Eventually.of_forall fun ω₀ _ Q _ Y' E' hG hE'm hE' => ?_)
  refine (isFlowLineDriver_recStage h44 hκ hκ4 (fun hθ => ?_) (fun hθ => ?_) hG hE'm hE').2
  · obtain ⟨hL, hR⟩ := hup hθ
    obtain ⟨hL', hR'⟩ := shiftW_zero_heights hc₀J hc₀ hL hR
    exact cond44_flowLine_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ θ _ hθ hθπ hL' hR'
  · obtain ⟨hL, hR⟩ := hdown hθ
    refine cond44_reflWord_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ θ _ hθ.le hθπ' (fun y hy hyJ => ?_)
      (fun y hy hyJ => ?_)
    · obtain ⟨hyJ', he⟩ := hfn y hyJ
      rw [he]; exact hL y hy hyJ'
    · obtain ⟨hyJ', he⟩ := hfn y hyJ
      rw [he]; exact hR y hy hyJ'

/-- **The two-angle drivers are a staged history of `η^{t₀,∞}_{θ₀,θ}`** (R48-safe), under the record-angle heights:
direct (4.4) heights at `θ₀`; at `θ`, direct heights if `θ₀ ≤ θ` and reflected heights if `θ < θ₀`; and
`|θ − θ₀| ≤ π`. -/
theorem isStagedHistory_twoFam (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hc₀J : c₀.jumps = J) (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hup : θ₀ ≤ θ → (∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ * chiC κ)
    (hdown : θ < θ₀ → (∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ)
    (hθπ : θ ≤ θ₀ + Real.pi) (hθπ' : θ₀ ≤ θ + Real.pi) :
    IsStagedHistory κ b J P h (StripSys.twoAngleSpec θ₀ t₀ θ) (twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h) := by
  have hEm := measurable_twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ hh.1
  have hreg := twoFam_regular h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h
  refine ⟨hEm, fun k => ?_, fun k => Eventually.of_forall fun ω => (hreg k ω).2.2.2, fun k => ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb _ (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  · rcases k with _ | _ | k
    · exact (stageOK_twoFam_zero h44 hκ hκ4 hb hh hc₀J hc₀ hL0 hR0).1
    · exact stageOK_twoFam_one h44 hκ hκ4 hb hh hc₀J hc₀ hL0 hR0 hup hdown hθπ hθπ'
    · exact stageOK_of_two_le (by omega)

/-- **The two-angle staged history under the strip heights** of Aux. lemma 130 (`b + aχ ≤ −λ` left of `0`,
`λ ≤ b + aχ` right of `0`, for every `a ∈ [−π/2, π/2]`): every pair of angles in `[−π/2, π/2]` and every switch time. -/
theorem isStagedHistory_twoFam_strip (hb : IsPiecewiseConstantBoundaryData b J)
    (hcumL : ∀ a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hh : IsGFFWithBoundaryData P h b J) (hc₀J : c₀.jumps = J) (hc₀ : ∀ y ∉ J, c₀.fn y = b y)
    (hθ₀ : θ₀ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    IsStagedHistory κ b J P h (StripSys.twoAngleSpec θ₀ t₀ θ) (twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπ := Real.pi_pos
  have hπχ : 0 ≤ Real.pi * chiC κ := (mul_pos hπ hχ).le
  refine isStagedHistory_twoFam h44 hκ hκ4 hb hh hc₀J hc₀ (fun y hy hyJ => ?_) (fun y hy hyJ => hcumR θ₀ hθ₀ y hy hyJ)
    (fun _ => ⟨fun y hy hyJ => ?_, fun y hy hyJ => hcumR θ hθ y hy hyJ⟩)
    (fun _ => ⟨fun y hy hyJ => hcumL θ hθ y hy hyJ, fun y hy hyJ => ?_⟩) ?_ ?_
  · linarith [hcumL θ₀ hθ₀ y hy hyJ]
  · linarith [hcumL θ hθ y hy hyJ]
  · linarith [hcumR θ hθ y hy hyJ]
  · linarith [hθ.2, hθ₀.1]
  · linarith [hθ.1, hθ₀.2]

end Two

/-! ### The two-angle strip system -/

section System

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

include h44 hκ hκ4 in
/-- **A two-angle strip system exists, R48-safely** (the construction behind Theorems 1.2–1.3's leaf `hWordT`), on
every standard Borel probability space carrying a GFF `h` with data `b` (strip heights `hcumL`, `hcumR` at every angle
of `[−π/2, π/2]`) and a centred counterflow of `h` with infinite lifetime: the drivers `twoAngleFam` (field-determined,
from `h44`), regular at every sample. The same hypotheses as PROVE-STRIPSYS-SAFE's `exists_isConstStripSystem`. -/
theorem exists_isTwoAngleStripSystem {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hcumL : ∀ a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∃ Es : ExplSpec → ℕ → Ω → Driver, Sec7.WordSafe.IsTwoAngleStripSystem κ b J P h W' ζ' Es ∧
      ∀ spec k ω, IsRegularDriver (Es spec k ω) := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  refine ⟨twoAngleFam h44 hκ hκ4 c₀ h, ⟨hκ, hκ4, hb, hh, hcf, hζ', fun θ hθ => ?_, fun {θ₀ θ} hθ₀ hθ t₀ => ?_⟩,
    twoAngleFam_regular h44 hκ hκ4 c₀ h⟩
  · rw [twoAngleFam_constSpec]
    obtain ⟨hL, hR⟩ := R7Aux131.heights_const hκ hκ4 hcumL hcumR hθ
    exact StripSafe.isStagedHistory_constFam h44 hκ hκ4 hb hc₀J hc₀ hh hL hR
  · rw [twoAngleFam_twoAngleSpec]
    exact isStagedHistory_twoFam_strip h44 hκ hκ4 hb hcumL hcumR hh hc₀J hc₀ hθ₀ hθ

end System

end InteractingSLE.Sec5.TwoAngle
