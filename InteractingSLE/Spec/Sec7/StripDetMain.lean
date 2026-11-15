/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripDetWord
import InteractingSLE.Spec.Sec7.StripMark
import InteractingSLE.Spec.Sec7.Prop74BShift

/-!
# The two pieces of the angle-varying path are Borel functions of the field

Packet PROVE-STRIPSYS21, §5.1 (i) of `planning/handoffs/PROVE-STRIPSYS19.md` (ruling R48). Specification §7.4, proof of
Aux. lemma 130 (p. 410): "Conditional field determination makes the continuation measurable from the first prefix and
the original field." For a staged history `E` of the two-angle program `η^{t₀,∞}_{θ₀,θ}` (`StripSys.twoAngleSpec`) of
a GFF `h` whose boundary data has (4.4) heights at both angles, and `θ₀ ≤ θ ≤ θ₀ + π`:

* **`ae_drv_zero`** (the first piece): almost surely the first driver has infinite lifetime and is
  `admDrv θ₀ (c₀, h)` (the flow line of `h` itself, `stageLaw_zero`'s witness);
* **`ae_drv_one`** (the continuation): almost surely the continuation is launched, has infinite lifetime and is
  `admDrv θ (stopWord κ (c₀, θ₀, rec₀), recField κ rec₀ h)`, where `rec₀` is the record of the first piece at `t₀`: the
  conditional field after the first piece is the field read in the record chart, with the stop word's data
  (`post_stage` with PROVE-STAGEDLAW's stop law), and the stop word's flow-line word satisfies (4.4)
  (`cond44_flowLine_stopWord`);
* **`exists_borel_drivers`**: hence there are Borel maps `D₀`, `D₁` of the field with, almost surely,
  `E 0 = D₀(h)` and `E 1 = D₁(h)` (paths at every time, infinite lifetimes).

Inputs: `AdmCode.Theorem12ParamCond44Statement` (proved from the §4.2 reference). No Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripDet

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord AdmCode Sec4 QuantumZipper

/-! ### Heights of the shifted word -/

theorem shiftW_zero_fn_of_notMem {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps)
    (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {y : ℝ} (hy : y ∉ (shiftW 0 c₀).jumps) :
    y ∉ jumps ∧ (shiftW 0 c₀).fn y = b y := by
  have hyc : y ∉ c₀.jumps := fun h => hy (by rw [jumps_shiftW]; exact Finset.mem_image.2 ⟨y, h, sub_zero y⟩)
  rw [hc₀J] at hyc
  exact ⟨hyc, by rw [fn_shiftW, add_zero, hc₀ y hyc]⟩

/-- The (4.4) heights of `b` at angle `α` are those of the word `shiftW 0 c₀`. -/
theorem shiftW_zero_heights {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps)
    (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {α : ℝ}
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + α * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + α * chiC κ) :
    (∀ y : ℝ, y < 0 → y ∉ (shiftW 0 c₀).jumps →
      (shiftW 0 c₀).fn y + α * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ) ∧
    ∀ y : ℝ, 0 < y → y ∉ (shiftW 0 c₀).jumps → sleLambda κ ≤ (shiftW 0 c₀).fn y + α * chiC κ := by
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
    rw [he]; exact hL y hy hyj
  · obtain ⟨hyj, he⟩ := shiftW_zero_fn_of_notMem hc₀J hc₀ hyJ
    rw [he]; exact hR y hy hyj

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-! ### The program -/

theorem launch_zero (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D (0 + 1)).2.2.2.1 0 ≠ none := by
  change (ExplState.launch (ExplState.init 0) 0 (D 0) θ₀ (t₀ : ℝ≥0∞)).2.2.2.1 0 ≠ none
  rw [launches_launch, Function.update_self]
  exact Option.some_ne_none _

theorem instrAngle_zero : instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 0 = θ₀ := rfl

theorem instrAngle_one : instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1 = θ := rfl

theorem instrTime_zero : instrTime (StripSys.twoAngleSpec θ₀ t₀ θ) 0 = (t₀ : ℝ≥0∞) := rfl

/-- The continuation is launched as soon as the first piece is alive at `t₀`. -/
theorem launch_one_of_lt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (h0 : (t₀ : ℝ≥0∞) < (D 0).2) :
    (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D (1 + 1)).2.2.2.1 1 ≠ none := by
  have h := StripMark.mem_launchOne_of_lt (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (r := 0)
    (E := fun j (_ : Unit) => D j) (ω := ()) h0
  change (ExplState.run κ b jumps (StripSideHeightProb.stopSpec θ₀ t₀ θ 0) D 2).2.2.2.1 1 ≠ none at h
  rw [StripSideHeightProb.launches_run_two_stopSpec] at h
  exact h

omit mΩ [StandardBorelSpace Ω] in
/-- The first record. -/
theorem pastMap_one_last (ω : Ω) :
    pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ω (Fin.last 0) = recOf (t₀ : ℝ≥0∞) (E 0 ω) :=
  pastMap_last_of_launch (launch_zero _)

omit mΩ [StandardBorelSpace Ω] in
/-- The chart after the first piece, alive at `t₀`, is the record chart of its record. -/
theorem chart_one_eq {ω : Ω} (hreg : IsRegularDriver (E 0 ω)) (h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2) :
    (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1 =
      recChart (recOf (t₀ : ℝ≥0∞) (E 0 ω)) := by
  rw [recChart_eq_loewner hreg (isDrvGood_recOf_of_lt hreg h0)]
  change (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ₀ (t₀ : ℝ≥0∞)).2.2.2.2.1 = _
  rw [chart_launch _ _ _ _ _ (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
  change (Chart.id.recenter 0).loewner _ _ = _
  rw [Chart.recenter_zero]
  rfl

/-! ### The first stage -/

variable (κ) in
/-- The stage-`0` word: the data `b` as a sorted word (centred at the root `0`). -/
abbrev word₀ (c₀ : BoundaryWord) : BoundaryWord := shiftW 0 c₀

/-- **The stage-`0` witness** (`stageLaw_zero`'s, with the word explicit). -/
theorem stageWitness_zero (hh : IsGFFWithBoundaryData P h b jumps)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    Measurable[pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 0] (fun _ : Ω => shiftW 0 c₀) ∧
    Measurable (fun ω => flowField 0 0 (h ω)) ∧
    (∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (0 + 1)).2.2.2.1 0 ≠ none →
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 0).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 0).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 0).2.2.2.2.1.2.1 w)) H ∧
      IsChartTransport (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 0).2.2.2.2.1 1 0
        (chiC κ) (h ω) (flowField 0 0 (h ω))) ∧
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω₀) (0 + 1)).2.2.2.1 0 ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 0) ω₀)
        (fun ω => flowField 0 0 (h ω)) (shiftW 0 c₀).fn (shiftW 0 c₀).jumps := by
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have hgff := isGFFWithBoundaryData_shiftW 0 hh₀
  refine ⟨measurable_const, (measurable_flowField _ _).comp hh.1, Eventually.of_forall fun ω _ => ?_, ?_⟩
  · exact ⟨Chart.isConformal_id.recenter _, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift,
      isChartTransport_shiftChart _ _ _⟩
  · rw [pastSigma_zero]
    filter_upwards [ae_isGFFWithBoundaryData_condExpKernel_bot hgff] with ω₀ h0 _
    exact h0

/-- **The first piece is the field-determined flow line** (R48-safe): almost surely its lifetime is infinite and it is
`admDrv θ₀ (c₀, h)`. -/
theorem ae_drv_zero (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ) :
    ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀, flowField 0 0 (h ω))).2 = (E 0 ω).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E 0 ω).2 →
        (admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀, flowField 0 0 (h ω))).1 t = (E 0 ω).1 t := by
  obtain ⟨hβ, hY, hpath, hker⟩ := stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀
  obtain ⟨hL', hR'⟩ := shiftW_zero_heights hc₀J hc₀ hL hR
  have h44w : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (0 + 1)).2.2.2.1 0
      ≠ none → Cond44 κ (flowLineRhoL κ (shiftW 0 c₀).fn (shiftW 0 c₀).jumps 0
        (instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 0))
        (flowLineRhoR κ (shiftW 0 c₀).fn (shiftW 0 c₀).jumps 0 (instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 0)) :=
    Eventually.of_forall fun _ _ => cond44_flowLine_of_heights hκ (shiftW 0 c₀).isPiecewiseConstantBoundaryData θ₀
      hL' hR'
  filter_upwards [ae_stageDrv_eq h44 hκ hκ4 hb hh hE hreg 0 hβ hY hpath hker h44w] with ω hω
  exact hω (launch_zero _)

/-! ### The second stage -/

variable (κ b jumps θ₀ θ t₀ E) in
/-- The first record, read from the retained past before the continuation. -/
abbrev rec₀ (ω : Ω) : RecData := pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ω (Fin.last 0)

/-- The stage-`1` word: the stop word of the first piece. -/
abbrev word₁ (κ θ₀ : ℝ) (c₀ : BoundaryWord) (r : RecData) : BoundaryWord := stopWord κ (shiftW 0 c₀, θ₀, r)

/-- The stage-`1` field: the field read in the record chart. -/
abbrev field₁ (κ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  recField κ r (flowField 0 0 f)

theorem measurable_word₁ (κ θ₀ : ℝ) (c₀ : BoundaryWord) : Measurable (word₁ κ θ₀ c₀) :=
  (measurable_stopWord κ).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem measurable_field₁ (κ : ℝ) :
    Measurable fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2 :=
  Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2)
    (f := fun p : RecData × DistOn upperHalfPlaneOpens => (p.1, flowField 0 0 p.2)) (measurable_recField κ)
    (measurable_fst.prodMk ((measurable_flowField 0 0).comp measurable_snd))

omit mΩ [StandardBorelSpace Ω] in
theorem measurable_rec₀_past :
    Measurable[pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1]
      fun ω => pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ω (Fin.last 0) := by
  rw [pastSigma_eq_comap]
  exact (measurable_pi_apply (X := fun _ : Fin 1 => RecData) (Fin.last 0)).comp
    (comap_measurable (pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1))

/-- **The continuation is the field-determined flow line of the conditional field** (R48-safe; spec p. 410). If the data
`b` has (4.4) heights at both angles `θ₀` and `θ`, with `θ₀ ≤ θ ≤ θ₀ + π`, then almost surely the continuation has
infinite lifetime and is `admDrv θ (stopWord κ (c₀, θ₀, rec₀), recField κ rec₀ h)`, `rec₀ = recOf t₀ (E 0)`. -/
theorem ae_drv_one (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) :
    ∀ᵐ ω ∂P, (E 1 ω).2 = ⊤ ∧
      (admDrv h44 hκ hκ4 θ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω)),
        field₁ κ (recOf (t₀ : ℝ≥0∞) (E 0 ω)) (h ω))).2 = (E 1 ω).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E 1 ω).2 →
        (admDrv h44 hκ hκ4 θ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (E 0 ω)),
          field₁ κ (recOf (t₀ : ℝ≥0∞) (E 0 ω)) (h ω))).1 t = (E 1 ω).1 t := by
  have hB := runMeasStatement.{u}
  have hζ₀ := ae_drv_zero h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0
  obtain ⟨hβ₀, hY₀, hpath₀, hker₀⟩ := stageWitness_zero (E := E) (θ := θ) (t₀ := t₀) (θ₀ := θ₀) hh hc₀J hc₀
  have hpost := post_stage (spec := StripSys.twoAngleSpec θ₀ t₀ θ) (E := E) (ℓ := 0)
    (StripSideHeightProb.isStopLaw_stopWord hκ) hB hκ hb hh (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 0)
    hβ₀ hY₀ hpath₀ hker₀
  have hpm : Measurable (pastMap κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1) :=
    measurable_pastMap hB hb _ (fun j _ => hE.1 j) (fun j _ => hreg j) 1 le_rfl
  have h𝒢 : pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1 ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hr : Measurable (rec₀ κ b jumps θ₀ θ t₀ E) := measurable_pi_iff.1 hpm (Fin.last 0)
  have hβ₁ : Measurable[pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1]
      (fun ω => word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)) :=
    Measurable.comp (g := word₁ κ θ₀ c₀) (f := rec₀ κ b jumps θ₀ θ t₀ E) (measurable_word₁ κ θ₀ c₀)
      measurable_rec₀_past
  have hY₁ : Measurable (fun ω => field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun ω => (rec₀ κ b jumps θ₀ θ t₀ E ω, h ω)) (measurable_field₁ κ) (hr.prodMk hh.1)
  have hpath₁ : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (1 + 1)).2.2.2.1 1
      ≠ none →
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1.2.1 w)) H ∧
      IsChartTransport (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) 1).2.2.2.2.1 1 0
        (chiC κ) (h ω) (field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) := by
    filter_upwards [hζ₀] with ω hω _
    have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω.1]; exact ENNReal.coe_lt_top
    have hrec : rec₀ κ b jumps θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_one_last ω
    rw [chart_one_eq (hreg 0 ω) h0, hrec]
    refine ⟨isConformal_recChart _, continuousOn_recChart_lift _, ?_⟩
    rw [field₁, Prop74B.flowField_zero_zero]
    exact isChartTransport_recField κ _ _
  have hker₁ : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω₀) (1 + 1)).2.2.2.1 1
      ≠ none → IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E 1) ω₀)
        (fun ω => field₁ κ (rec₀ κ b jumps θ₀ θ t₀ E ω) (h ω)) (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω₀)).fn
        (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω₀)).jumps := by
    have hG := ae_isGFFWithBoundaryData_condExpKernel h𝒢 (M := univ)
      (β := fun ω => word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω))
      (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hY₁ (fun φ => by
        filter_upwards [hpost.2 φ] with ω hω _
        exact hω (launch_zero _) (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)))
    filter_upwards [hG] with ω₀ hω₀ _
    exact hω₀ (mem_univ _)
  obtain ⟨hL', hR'⟩ := shiftW_zero_heights hc₀J hc₀ hL hR
  have h44w : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) (fun j => E j ω) (1 + 1)).2.2.2.1 1
      ≠ none → Cond44 κ (flowLineRhoL κ (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).fn
        (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).jumps 0 (instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1))
        (flowLineRhoR κ (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).fn
          (word₁ κ θ₀ c₀ (rec₀ κ b jumps θ₀ θ t₀ E ω)).jumps 0 (instrAngle (StripSys.twoAngleSpec θ₀ t₀ θ) 1)) :=
    Eventually.of_forall fun _ _ => cond44_flowLine_stopWord hκ hκ4 (shiftW 0 c₀) θ₀ θ _ hθ hθπ hL' hR'
  filter_upwards [ae_stageDrv_eq h44 hκ hκ4 hb hh hE hreg 1 hβ₁ hY₁ hpath₁ hker₁ h44w, hζ₀] with ω hω hω₀
  have h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by rw [hω₀.1]; exact ENNReal.coe_lt_top
  have hrec : rec₀ κ b jumps θ₀ θ t₀ E ω = recOf (t₀ : ℝ≥0∞) (E 0 ω) := pastMap_one_last ω
  obtain ⟨h1, h2, h3⟩ := hω (launch_one_of_lt h0)
  rw [hrec] at h2 h3
  exact ⟨h1, h2, h3⟩

end Strip

end StripDet

end Sec7

end InteractingSLE
