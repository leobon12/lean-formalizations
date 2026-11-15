/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedPath
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# The stages of a finite extreme-angle schedule

Packet PROVE-QSCHED. For a staged history `E` of a schedule `s` (regular at every sample) of a field `h` whose word
`c` has `ExtremeHeights`:

* `stageWord`, `stageField`: the conditional word and the field read in the chart after `k` pieces (the stop word
  and the record field of the last piece, iterated: Figure 5.5, right panel);
* `isStageWitness_stage`: they are the witnesses of the staged law (`Prop513Schedule.stageWitness_succ`);
* `extremeHeights_stageWord`: every stage word has `ExtremeHeights` (`extremeHeights_stopWord`);
* `ae_isFlowLineDriver_stage_eq`: under the conditional law given the retained past, the piece is the flow line of
  a null modification of the stage field (`Theorem14.GW1W.ae_isFlowLineDriver_stage`, with the null modification
  exported);
* `ae_tower_stage`, `ae_stageField_succ`: the conditional law given the piece's record is the next stage's law, and
  there the next stage field is the stage field read in the record chart.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.QSched

open Exist Exist.Staged Exist.StagedLaw Restart
open Prop513TreeExtract Prop513Schedule

section Stage

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {s : Schedule}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

variable (κ c s E) in
/-- The conditional word after the first `k` pieces: the stop word of the last piece, iterated. -/
def stageWord : ℕ → Ω → BoundaryWord
  | 0 => fun _ => c
  | k + 1 => fun ω => stopWord κ (stageWord k ω, instrAngle (scheduleSpec s) k,
      pastMap κ c.fn c.jumps (scheduleSpec s) E (k + 1) ω (Fin.last k))

variable (κ c s E) in
/-- The field read in the chart after the first `k` pieces: the record field of the last piece, iterated. -/
def stageField (h : Ω → DistOn upperHalfPlaneOpens) : ℕ → Ω → DistOn upperHalfPlaneOpens
  | 0 => h
  | k + 1 => fun ω => recField κ (pastMap κ c.fn c.jumps (scheduleSpec s) E (k + 1) ω (Fin.last k))
      (stageField h k ω)

/-- **The stage witnesses**: the stage words and fields are the witnesses of the staged law at every stage. -/
theorem isStageWitness_stage (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤) :
    ∀ k, k ≤ (scheduleSpec s).2.2.length →
      IsStageWitness κ c.fn c.jumps P h (scheduleSpec s) E k (stageWord κ c s E k) (stageField κ c s E h k)
  | 0, _ => stageWitness_zero s c hh
  | k + 1, hk => stageWitness_succ hκ c.isPiecewiseConstantBoundaryData hh s hE hr (by omega)
      (hTop.mono fun _ hω j hj => hω j (by omega)) (isStageWitness_stage hκ hh hE hr hTop k (by omega))

omit mΩ [StandardBorelSpace Ω] in
/-- Every stage word has `ExtremeHeights`. -/
theorem extremeHeights_stageWord (hκ : 0 < κ) (hκ4 : κ < 4) (hc : ExtremeHeights κ c) :
    ∀ k, k ≤ (scheduleSpec s).2.2.length → ∀ ω : Ω, ExtremeHeights κ (stageWord κ c s E k ω)
  | 0, _, _ => hc
  | k + 1, hk, ω => extremeHeights_stopWord hκ hκ4 (extremeHeights_stageWord hκ hκ4 hc k (by omega) ω)
      (instrAngle_extreme s (by omega)) _

/-- **At almost every launch, the piece is the conditional flow line of a null modification of the witness
field**, for the witness word (`Theorem14.GW1W.ae_isFlowLineDriver_stage`, with the null modification exported). -/
theorem ae_isFlowLineDriver_stage_eq {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec} (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {ℓ : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens} (hW : IsStageWitness κ b jumps P h spec E ℓ β Y) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      ∃ h' : Ω → DistOn upperHalfPlaneOpens, IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps (instrAngle spec ℓ)
        (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (fun t ω => (E ℓ ω).1 t) (fun ω => (E ℓ ω).2) ∧
        Y =ᵐ[condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀] h' := by
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  filter_upwards [hE.2.2.2 ℓ, hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hW.2.2.1,
    ae_ae_run_eq runMeasStatement hb spec (k := ℓ) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)]
    with ω₀ hstg hp₀ hk₀ hpK hrunK
  intro hl
  obtain ⟨⟨c', θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c' θ' hcθ
  obtain ⟨hspec, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  have hθ' : instrAngle spec ℓ = θ' := by unfold instrAngle; rw [hspec]
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hgT : ∀ ω, IsChartTransport c' 1 0 (QuantumZipper.chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => (hT' ω).unique hconf (hgT ω)
  have hh'm : Measurable h' := by
    rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYe : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀), Y ω = h' ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact hT.unique hconf (hT' ω)
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (β ω₀).fn
      (β ω₀).jumps := isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm hYe
  rw [hθ']
  exact ⟨h', isFlowLineDriver_word hκ hG hb' hfl, hYe⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The last record is the record of the launched piece at its instruction time. -/
theorem ae_lastRec_eq (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) :
    ∀ᵐ ω ∂P, Theorem14.GW2aCont.lastRec κ c.fn c.jumps (scheduleSpec s) E k ω =
      recOf ((dur s k : ℝ≥0) : ℝ≥0∞) (E k ω) := by
  filter_upwards [hTop] with ω hω
  rw [Theorem14.GW2aCont.lastRec_of_launch (scheduleSpec s) E k
      (launch_of_previous_top s _ hk fun j hj => hω j (by omega)),
    instrTime_eq_dur (by rwa [← length_scheduleSpec])]

/-- **The tower at a stage**: for almost every world before piece `k`, almost surely the conditional law given the
piece's record is the conditional law given the retained past before piece `k + 1`. -/
theorem ae_tower_stage (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E)
    (hr : ∀ j ω, IsRegularDriver (E j ω))
    (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀),
      condExpKernel (condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀)
          (MeasurableSpace.comap (fun ω => recOf ((dur s k : ℝ≥0) : ℝ≥0∞) (E k ω)) inferInstance) ω₁ =
        condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E (k + 1)) ω₁ := by
  have hle := hE.2.1
  have hgm := Theorem14.GW2aCont.measurable_lastRec hle k
  have hRm : Measurable fun ω => recOf ((dur s k : ℝ≥0) : ℝ≥0∞) (E k ω) := measurable_recOf (hE.1 k) (hr k) _
  have hlast := ae_lastRec_eq (κ := κ) (c := c) hTop hk
  filter_upwards [Theorem14.GW2aCont.ae_ae_condExpKernel_succ_eq (P := P) hle k,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hle k) hlast] with ω₀ hsucc hlastK
  have hker := KernelTower.ae_condExpKernel_comap_eq
    (P := condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀) hgm hRm (φ := id) measurable_id
    (ψ := id) measurable_id hlastK (hlastK.mono fun _ hω => hω.symm)
  filter_upwards [hsucc, hker] with ω₁ h1 h2
  rw [← h2, h1]

/-- **The next stage field**: for almost every world before piece `k`, for almost every world after it, the next
stage field is almost surely the stage field read in the chart of the piece's record. -/
theorem ae_stageField_succ (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E)
    (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀),
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E (k + 1)) ω₁),
        stageField κ c s E h (k + 1) ω = recField κ (recOf ((dur s k : ℝ≥0) : ℝ≥0∞) (E k ω₁))
          (stageField κ c s E h k ω) := by
  have hle := hE.2.1
  have hpm : Measurable[pastSigma κ c.fn c.jumps (scheduleSpec s) E (k + 1)]
      (pastMap κ c.fn c.jumps (scheduleSpec s) E (k + 1)) := fun A hA => by
    rw [pastSigma_eq_comap]
    exact ⟨A, hA, rfl⟩
  have hlm : Measurable[pastSigma κ c.fn c.jumps (scheduleSpec s) E (k + 1)]
      (Theorem14.GW2aCont.lastRec κ c.fn c.jumps (scheduleSpec s) E k) := (measurable_pi_apply _).comp hpm
  have hstep : ∀ᵐ ω₁ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E (k + 1)) ω₁),
      stageField κ c s E h (k + 1) ω = recField κ (recOf ((dur s k : ℝ≥0) : ℝ≥0∞) (E k ω₁))
        (stageField κ c s E h k ω) := by
    filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hle (k + 1)) hlm,
      ae_lastRec_eq (κ := κ) (c := c) hTop hk] with ω₁ h1 h2
    filter_upwards [h1] with ω hω
    change recField κ (Theorem14.GW2aCont.lastRec κ c.fn c.jumps (scheduleSpec s) E k ω) (stageField κ c s E h k ω) = _
    rw [hω, h2]
  exact Sec7.Aux122Disint.ae_ae_condExpKernel (hle k) hstep

end Stage

end InteractingSLE.Sec5.QSched
