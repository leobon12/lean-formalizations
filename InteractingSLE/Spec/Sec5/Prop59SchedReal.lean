/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleInduction

/-!
# The field-determined extreme-angle driver realizes a flow line (R48-safe)

Packet PROVE-PROP59-SCHED (Astra follow-up 5 §2.1, ruling R73; R74). For a word satisfying (4.4), the Borel
determination map of `Theorem12ParamCond44Statement` applied to a GFF with the word's data is a flow-line driver of
that GFF. This is the existence half of the §4.2 determination: PROVE-STAGED's `Exist.Staged.isOptionalHullCoupling_drv`
with its two inputs (the parametric Theorem 1.2 and Theorem 1.3) replaced by the restricted map `h44` and the trace of
(4.4) words (Remark 2.3, `Sec7.AdmCode.ae_trace_of_cond44`).

* **`isOptionalHullCoupling_admCode`**: the realization on one probability space. The reference coupling is the sealed
  Theorem 1.1; its field-determined history is realized on the given space (`Lemma71H.exists_fieldDetermination_
  realization_of_det`, fed by `h44` and the trace), the hull clauses transfer (`hullClauseTransferStatement`), and the
  realized coupling is moved to the given driver by determination **on the realized coupling itself**
  (`ae_detCode_eq_of_trace`), so no comparison with the reference law is needed;
* **`isFlowLineDriver_admDrv`**: the flow-line form (`IsFlowLineDriver`), for the flow field `f + θχ`;
* **`isFlowLineDriver_stageDriver`**: the extreme angles `±π/2` of `Prop513Schedule.stageDriver`, the lower one through
  the reflection `z ↦ −z̄`.

Every conclusion also records that the lifetime is infinite almost surely. Nothing here uses Theorem 1.2, Theorem 1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` (R48); the only named input is `h44` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop59Sched

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly WholeField
open Sec7 Sec7.AdmCode Sec7.StripWall Prop513Schedule

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- **The field-determined driver of a (4.4) word realizes an optional hull coupling** with a GFF carrying the word's
data, on the GFF's own probability space; its lifetime is infinite almost surely. -/
theorem isOptionalHullCoupling_admCode {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hc44 : Sec4.Cond44 κ ρL ρR)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsGFFWithBoundaryData Q h₀ (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR))
    {E : Ω → Driver} (hEm : Measurable E)
    (hE : ∀ᵐ ω ∂Q, E ω = drvOf (detCode (admΦ h44 hκ hκ4 nL nR) (((xL, xR), (ρL, ρR)), h₀ ω))) :
    (∀ᵐ ω ∂Q, (E ω).2 = ⊤) ∧
      ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
        (B : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 (fun t ω => (E ω).1 t) VL VR B (fun ω => (E ω).2) h₀ := by
  set Φ := admΦ h44 hκ hκ4 nL nR with hΦdef
  have hΦm : Measurable Φ := measurable_admΦ h44 hκ hκ4 nL nR
  -- the reference coupling (sealed Theorem 1.1) and its field-determined realization
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hr, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hκ hF
  have htr₀ : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η :=
    (ae_trace_of_cond44 hκ hκ4 hF hc44 hcoup.1).mono fun _ hω => hω.2
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, -, hreal⟩ := Sec7.Lemma71H.exists_fieldDetermination_realization_of_det hκ hcoup
    ⟨fun f => Φ (((xL, xR), (ρL, ρR)), f), hΦm.comp (measurable_const.prodMk measurable_id),
      (h44 κ hκ hκ4 nL nR).choose_spec.2 xL xR ρL ρR hF hc44 hcoup⟩ htr₀
  obtain ⟨u, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := ρL) (ρR := ρR) (vL := xL) (vR := xR)
  have hr' : IsGFFWithBoundaryData P₀ hr (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) :=
    ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hlaw : Q.map h₀ = P₀.map hr := map_eq_of_isGFFWithBoundaryData hh₀ hr' hu
  -- the realization on `(Ω, Q)`, on the usual augmentation, with the hull clauses
  obtain ⟨𝓕, B, hEv⟩ := hreal Q h₀ hh₀.1 hlaw
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hEv
  have hdet : ∀ᵐ ω ∂P₀, (pathsOfCode (Ψ (hr ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (pathsOfCode (Ψ (hr ω))).2.1 t = W₀ t ω ∧ (∀ i, (pathsOfCode (Ψ (hr ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (pathsOfCode (Ψ (hr ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : IsFieldRealizationDatum κ xL xR ρL ρR (pathsOfCode ∘ Ψ) Q h₀ :=
    ⟨hκ, hF, measurable_pathsOfCode.comp hΨm, hh₀.1, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hr, hcoup,
      hdet, hlaw⟩
  have hC := hullClauseTransferStatement κ _ _ _ _ (pathsOfCode ∘ Ψ) Q h₀ hdatum _ B hEa
  -- determination on the realized coupling itself
  have htrC := ae_trace_of_cond44 hκ hκ4 hF hc44 hC.1
  have hdc := ae_detCode_eq_of_trace hκ hC (htrC.mono fun _ hω => hω.2)
    ((h44 κ hκ hκ4 nL nR).choose_spec.2 xL xR ρL ρR hF hc44 hC)
  have hX' : IsMeasurableKilledDriving (fun t ω => (E ω).1 t) (fun i t ω => cvL (Ψ (h₀ ω)) i t)
      (fun j t ω => cvR (Ψ (h₀ ω)) j t) (fun ω => (E ω).2) := by
    intro t A hA
    refine (measurableSet_lt measurable_const (measurable_snd.comp hEm)).inter (hA.preimage ?_)
    refine ((measurable_pi_apply t).comp (measurable_fst.comp hEm)).prodMk
      ((measurable_pi_iff.2 fun i => (measurable_cvL_at i t).comp (hΨm.comp hh₀.1)).prodMk
        (measurable_pi_iff.2 fun j => (measurable_cvR_at j t).comp (hΨm.comp hh₀.1)))
  have hagree := hE.and (hdc.and htrC)
  refine ⟨?_, _, _, _, B, IsOptionalHullCoupling.congr_ae hC
    (fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t) hX' ?_⟩
  · filter_upwards [hagree] with ω hω
    obtain ⟨hEω, ⟨x₀, hx₀, hζx, -, hcode⟩, hζ, -⟩ := hω
    have hcode' : detCode Φ (((xL, xR), (ρL, ρR)), h₀ ω) = dOf x₀ := hcode
    rw [hEω, hcode', drvOf_of_mem (dOf_mem_DSet hx₀)]
    exact hζx.trans hζ
  · filter_upwards [hagree] with ω hω
    obtain ⟨hEω, ⟨x₀, hx₀, hζx, hwx, hcode⟩, hζ, -⟩ := hω
    have hcode' : detCode Φ (((xL, xR), (ρL, ρR)), h₀ ω) = dOf x₀ := hcode
    rw [hEω, hcode', drvOf_of_mem (dOf_mem_DSet hx₀)]
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < cζ x₀ := by rw [hζx, hζ]; exact ENNReal.coe_lt_top
    refine ⟨hζx, ?_, fun t ht => ?_⟩
    · change drvPath (dOf x₀) 0 = _
      rw [(drvPath_dOf_agree x₀).1]
      exact (hwx 0 (hζx ▸ h0)).1
    · change drvPath (dOf x₀) t = _
      rw [(drvPath_dOf_agree x₀).2 t (hζx ▸ ht)]
      exact (hwx t ht).1

/-- **The field-determined flow-line driver is a flow-line driver** (for a boundary word whose angle-`θ` flow-line word
satisfies (4.4)); its lifetime is infinite almost surely. -/
theorem isFlowLineDriver_admDrv (θ : ℝ) (c : BoundaryWord)
    (hc44 : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps)
    {E : Ω → Driver} (hEm : Measurable E) (hE : ∀ᵐ ω ∂Q, E ω = admDrv h44 hκ hκ4 θ (c, Y ω)) :
    (∀ᵐ ω ∂Q, (E ω).2 = ⊤) ∧
      IsFlowLineDriver κ c.fn c.jumps θ Q Y (fun t ω => (E ω).1 t) (fun ω => (E ω).2) := by
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hgff := isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData 0 θ hY
  obtain ⟨htop, 𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_admCode h44 hκ hκ4 hF hc44 hgff hEm
    (hE.mono fun ω hω => by rw [hω, admDrv_eq])
  exact ⟨htop, _, 𝓕, VL, VR, B, fun ω => isTranslateAddConst_flowField 0 _ (Y ω), hC⟩

/-- The reflected GFF carries the data of the reflected word. -/
theorem isGFFWithBoundaryData_reflWord {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps) :
    IsGFFWithBoundaryData Q (fun ω => FlowReflect.reflField (Y ω)) (reflWord c).fn (reflWord c).jumps := by
  rw [jumps_reflWord]
  refine (Restart.isGFFWithBoundaryData_congr Q _ (S := (FlowReflect.reflJumps c.jumps : Set ℝ))
    fun y hy => ?_).2 (FlowReflect.IsGFFWithBoundaryData.reflect hY)
  exact fn_reflWord fun h => hy (FlowReflect.mem_reflJumps.2 h)

/-- **The extreme-angle stage driver is a flow-line driver** of a GFF whose data has the extreme heights; its lifetime
is infinite almost surely. At `−π/2` this is the reflection of the angle-`π/2` statement for the reflected word. -/
theorem isFlowLineDriver_stageDriver {θ : ℝ} (hθ : θ = -(Real.pi / 2) ∨ θ = Real.pi / 2) {c : BoundaryWord}
    (hc : ExtremeHeights κ c) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps)
    {E : Ω → Driver} (hEm : Measurable E) (hE : ∀ᵐ ω ∂Q, E ω = stageDriver h44 hκ hκ4 θ (c, Y ω)) :
    (∀ᵐ ω ∂Q, (E ω).2 = ⊤) ∧
      IsFlowLineDriver κ c.fn c.jumps θ Q Y (fun t ω => (E ω).1 t) (fun ω => (E ω).2) := by
  rcases hθ with rfl | rfl
  · have hn : -(Real.pi / 2) < 0 := by linarith [Real.pi_pos]
    have hE' : ∀ᵐ ω ∂Q, negDrv (E ω) =
        admDrv h44 hκ hκ4 (Real.pi / 2) (reflWord c, FlowReflect.reflField (Y ω)) := by
      filter_upwards [hE] with ω hω
      rw [hω]
      simp only [stageDriver, hn, ↓reduceIte, neg_neg, negDrv]
    obtain ⟨htop, hfl⟩ := isFlowLineDriver_admDrv h44 hκ hκ4 (Real.pi / 2) (reflWord c) (cond44_lower hκ hc)
      (isGFFWithBoundaryData_reflWord hY) (measurable_negDrv.comp hEm) hE'
    have hfl' := isFlowLineDriver_reflect (reflWord c).isPiecewiseConstantBoundaryData hfl
    simp only [FlowReflect.reflField_reflField] at hfl'
    have e : (-fun t ω => ((negDrv ∘ E) ω).1 t) = fun t ω => (E ω).1 t := by
      funext t ω
      simp only [Function.comp_apply, negDrv, Pi.neg_apply, neg_neg]
    rw [e] at hfl'
    exact ⟨htop, isFlowLineDriver_word hκ hY
      (FlowReflect.isPiecewiseConstantBoundaryData_reflData (reflWord c).isPiecewiseConstantBoundaryData) hfl'⟩
  · have hn : ¬Real.pi / 2 < 0 := by linarith [Real.pi_pos]
    refine isFlowLineDriver_admDrv h44 hκ hκ4 (Real.pi / 2) c (cond44_upper hκ hc) hY hEm ?_
    filter_upwards [hE] with ω hω
    rw [hω]
    simp only [stageDriver, hn, ↓reduceIte]

end InteractingSLE.Sec5.Prop59Sched
