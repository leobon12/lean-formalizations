/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalTransport

/-!
# Arbitrary-source stopped models from the two precise remaining inputs

Packet PROVE-RETPLUMB. All measure, filtration, Gaussian integrability, force
threshold and (S)/(L) transport is performed here. The two displayed residual
inputs are Borel coding of the generating-trace relation and an observable
boundary approach in the canonical killed driving filtration.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Sec7.PocketTraversal DomainMarkov DomainMarkov.K2 FCDet
universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- No standard Borel assumption on the original source remains. The R1 and
retained-geometry lemmas supply `hint` and `hn`; the two remaining mathematical
inputs are named explicitly. -/
def stoppedModelTransfer_of_canonicalInputs {κ θ : ℝ} (a : ForceWordType)
    {𝓗 : Filtration ℝ≥0 mΩ} {M : Set Ω}
    (hM : MeasurableSet[𝓗 0] M) (hPM : P M ≠ 0)
    {c : Ω → BoundaryWord} (hc : Measurable[𝓗 0] c)
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hWa : StronglyAdapted 𝓗 W)
    {V : Ω → ℝ≥0∞} (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t})
    {xL : Ω → Fin a.nL → ℝ} {xR : Ω → Fin a.nR → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {Y : Ω → RetCanonSpace} (hY : Measurable Y)
    (hCY : ∀ ω, RetCanonSpace.word (Y ω) = c ω)
    (hHY : ∀ ω, RetCanonSpace.field (Y ω) = Hc ω)
    (hWY : ∀ ω t, RetCanonSpace.driver t (Y ω) = W t ω)
    (hVY : ∀ ω, RetCanonSpace.life (Y ω) = V ω)
    (hγY : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) ≤ V ω → RetCanonSpace.trace (Y ω) t = γ ω t)
    (hLY : ∀ ω, retCanonicalXL κ θ a (Y ω) = xL ω)
    (hRY : ∀ ω, retCanonicalXR κ θ a (Y ω) = xR ω)
    (hXY : ∀ ω, Exist.flowField 0 (θ * QuantumZipper.chiC κ) (RetCanonSpace.field (Y ω)) = X ω)
    (htype : ∀ᵐ ω ∂P, ω ∈ M → c ω ∈ typeSet κ θ a.nL a.nR a.rhoL a.rhoR)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) (P.restrict M))
    (hn : RetPrelifeNonThreshold (P := P) a.rhoL a.rhoR W xL xR V M)
    (hS : HasSafeLaw κ a.rhoL a.rhoR P 𝓗 M V W (geomLW W xL) (geomRW W xR) X)
    (hL : HasSafeMembers P 𝓗 M V W X)
    (hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V ω) (γ ω))
    (hBorel : RetCanonicalGeneratingTraceBorel)
    (hB : RetBoundaryApproachObservable ((P[|M]).map Y) (retCanonicalKilledMeas κ θ a)) :
    StoppedModelTransfer κ θ P M c Hc V γ := by
  let Q := (P[|M]).map Y
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_retCanonicalLaw hPM hY
  let 𝓕 := retImageFiltration Y 𝓗
  let XL := retCanonicalXL κ θ a
  let XR := retCanonicalXR κ θ a
  let Z : RetCanonSpace → DistOn upperHalfPlaneOpens := fun s =>
    Exist.flowField 0 (θ * QuantumZipper.chiC κ) (RetCanonSpace.field s)
  have hMm := 𝓗.le 0 _ hM
  have hcw : Measurable[𝓕 0] RetCanonSpace.word := by
    apply measurable_from_retImageFiltration RetCanonSpace.measurable_word
    have he : RetCanonSpace.word ∘ Y = c := funext hCY
    rwa [he]
  have hxLm : Measurable[𝓕 0] XL :=
    (measurable_typeXL κ θ a.nL a.nR a.rhoL a.rhoR).comp hcw
  have hxRm : Measurable[𝓕 0] XR :=
    (measurable_typeXR κ θ a.nL a.nR a.rhoL a.rhoR).comp hcw
  have hWap : StronglyAdapted 𝓕 RetCanonSpace.driver := stronglyAdapted_retCanonicalDriver hWa hWY
  have hVsp : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {s | RetCanonSpace.life s ≤ t} := by
    apply isStoppingTime_retImageFiltration RetCanonSpace.measurable_life
    intro t
    simpa only [hVY] using hVs t
  have hZm : Measurable Z := (Exist.measurable_flowField 0 _).comp RetCanonSpace.measurable_field
  have htyp : ∀ᵐ s ∂Q, IsFlowType κ θ (RetCanonSpace.word s) (XL s) (XR s) a.rhoL a.rhoR := by
    have hp : ∀ᵐ s ∂Q, RetCanonSpace.word s ∈ typeSet κ θ a.nL a.nR a.rhoL a.rhoR := by
      apply (ae_map_iff hY.aemeasurable
        (RetCanonSpace.measurable_word (measurableSet_typeSet κ θ a.nL a.nR a.rhoL a.rhoR))).2
      apply ae_cond_of_ae_imp hMm
      simpa only [hCY] using htype
    filter_upwards [hp] with s hs
    exact isFlowType_of_mem_typeSet hs
  have hi : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun s => Z s φ) Q := by
    intro φ
    have hm : Measurable fun s => Z s φ :=
      ((measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)).comp hZm
    rw [integrable_map_measure hm.aestronglyMeasurable hY.aemeasurable]
    have he : (fun ω => Z (Y ω) φ) = fun ω => X ω φ :=
      funext fun ω => congrArg (fun H : DistOn upperHalfPlaneOpens => H φ) (hXY ω)
    change Integrable (fun ω => Z (Y ω) φ) (P[|M])
    rw [he, ProbabilityTheory.cond]
    exact (hint φ).smul_measure (ENNReal.inv_ne_top.2 hPM)
  have hthr : ∀ᵐ s ∂Q, RetCanonSpace.life s ≤ thr a.rhoL a.rhoR RetCanonSpace.driver XL XR s := by
    apply (ae_map_iff hY.aemeasurable
      (measurableSet_le RetCanonSpace.measurable_life
        (measurable_thr RetCanonSpace.continuous_driver hWap hxLm hxRm))).2
    apply ae_cond_of_ae_imp hMm
    have hp := life_le_thr_of_retPrelifeNonThreshold hWc hn
    filter_upwards [hp] with ω hω hωM
    rw [hVY, thr_congr (hWY ω) (hLY ω) (hRY ω)]
    exact hω hωM
  have hXP := isMeasurableKilledDriving_geom hWap RetCanonSpace.continuous_driver hxLm hxRm hVsp
  have hp : RetDrivingLifetimePredictable Q hXP := retDrivingLifetimePredictable_of_boundaryApproach hB
  let hs := exists_stoppedK2_sequences (P := Q) hWap RetCanonSpace.continuous_driver hxLm hxRm hVsp hp
  let T := Classical.choose hs
  obtain ⟨hT, hσ, hσm, hσlt, hσlim⟩ := Classical.choose_spec hs
  have hpos : ∀ᵐ s ∂Q, 0 < RetCanonSpace.life s := ae_pos_of_isAnnouncingSeq hT
  have hord := fun s => isOrderedForceWord_typeXL (κ := κ) (θ := θ)
    (nL := a.nL) (nR := a.nR) (ρL := a.rhoL) (ρR := a.rhoR) (RetCanonSpace.word s)
  let D : StoppedTypeData RetCanonSpace Q κ θ := {
    nL := a.nL, nR := a.nR, rhoL := a.rhoL, rhoR := a.rhoR, filt := 𝓕
    word := RetCanonSpace.word, wordMeas := hcw
    xL := XL, xR := XR, xLMeas := hxLm, xRMeas := hxRm
    xLNonpos := fun s => (hord s).2.1, xRNonneg := fun s => (hord s).2.2.2
    xLAnti := fun s => (hord s).1, xRMono := fun s => (hord s).2.2.1
    typed := htyp
    driver := RetCanonSpace.driver, driverZero := RetCanonSpace.driver_zero
    driverCont := RetCanonSpace.continuous_driver, driverAdapted := hWap
    field := RetCanonSpace.field, shiftedField := Z
    fieldMeas := RetCanonSpace.measurable_field, shiftedMeas := hZm
    shifted := fun s => Exist.isTranslateAddConst_flowField 0 _ _
    integrable := hi
    life := RetCanonSpace.life, lifeStop := hVsp, lifePos := hpos, lifeThreshold := hthr
    announce := T, announcing := hT, killedMeas := hXP
    driveStops := fun n s => (T n s : WithTop ℝ≥0)
    driveStopping := hσ, driveMono := hσm, driveLt := hσlt, driveLimit := hσlim
    safeLaw := hasSafeLaw_map_retImage hM hY hZm hXY hWY hVY hLY hRY
      RetCanonSpace.driver_zero RetCanonSpace.continuous_driver hWap hxLm hxRm hVsp hS
    safeMembers := hasSafeMembers_map_retImage hM hY hZm hXY hWY hVY hL
    trace := RetCanonSpace.trace, traceMeas := RetCanonSpace.measurable_trace
    traceCont := fun s => (RetCanonSpace.continuous_trace s).continuousOn
    generates := ae_retCanonical_generates hBorel hY hMm hWY hVY hγY hg }
  exact {
    model := { space := RetCanonSpace
               sigma := inferInstance
               borel := inferInstance
               law := Q
               probability := inferInstance
               data := D }
    read := Y, readMeas := hY, mapLaw := rfl
    agrees := Eventually.of_forall fun ω _ => ⟨hCY ω, hHY ω, hVY ω, hγY ω⟩ }

end InteractingSLE.Restart.RetAux79
