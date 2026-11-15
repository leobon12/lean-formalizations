/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetLeafModel
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCanonicalModel

/-!
# Arbitrary-source stopped models from pathwise trace facts

Packet PROVE-T15-RET. PROVE-RETPLUMB's constructor `RetAux79.stoppedModelTransfer_of_canonicalInputs`
takes two named inputs: the Borel coding of the generating-trace relation (`RetCanonicalGeneratingTraceBorel`,
proved in `RetLeafTraceBorel.lean`) and an observable boundary approach continuous at time `0`
(`RetBoundaryApproachObservable`, which natural boundary-distance processes cannot supply). The constructor
`stoppedModelTransfer_of_traceInputs` below takes neither. In their place it takes three pathwise facts
about the source path on the type event, almost surely:

* the path is in `ℍ` at positive times before its lifetime;
* at a finite lifetime its endpoint is real;
* the lifetime is positive.

The proof pushes these facts and the generating property to the model law (`measurableSet_retTraceGood`:
the corresponding event on the carrier is Borel) and applies `retDrivingLifetimePredictable_of_trace`. The
rest of the construction is PROVE-RETPLUMB's, unchanged.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Restart.RetLeaf

open LQGMetric (DistOn TestOn)
open RetAux79 Sec7.PocketTraversal DomainMarkov DomainMarkov.K2 FCDet Sec7.Coding

/-! ### The good event on the carrier is Borel -/

/-- Interiority at positive times before the lifetime, as countably many rational conditions. -/
theorem retCanonical_interior_iff (s : RetCanonSpace) :
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < RetCanonSpace.life s → 0 < (RetCanonSpace.trace s t).im) ↔
      ∀ a b : ℚ≥0, 0 < a → ((b : ℝ≥0) : ℝ≥0∞) < RetCanonSpace.life s → ∃ m : ℕ, ∀ r : ℚ≥0, a ≤ r →
        r ≤ b → 1 / ((m : ℝ) + 1) ≤ (RetCanonSpace.trace s r).im := by
  set f : ℝ≥0 → ℝ := fun t => (RetCanonSpace.trace s t).im with hf
  have hfc : Continuous f := Complex.continuous_im.comp (RetCanonSpace.continuous_trace s)
  constructor
  · intro h a b ha hb
    rcases le_or_gt a b with hab | hab
    · have hab' : (a : ℝ≥0) ≤ b := by exact_mod_cast hab
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab') hfc.continuousOn
      have ht₀pos : 0 < f t₀ := h t₀ (lt_of_lt_of_le (by exact_mod_cast ha) ht₀.1)
        (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₀.2) hb)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt ht₀pos
      refine ⟨m, fun r har hrb => ?_⟩
      exact hm.le.trans (isMinOn_iff.1 hmin _ ⟨by exact_mod_cast har, by exact_mod_cast hrb⟩)
    · exact ⟨0, fun r har hrb => absurd (har.trans hrb) (not_le.2 hab)⟩
  · intro h t ht0 ht
    obtain ⟨a, ha0, hat⟩ := exists_nnrat_btwn ht0
    obtain ⟨b, htb, hb, -⟩ := exists_nnrat_gt_lt ht one_pos
    have ha0' : 0 < a := by exact_mod_cast ha0
    obtain ⟨m, hm⟩ := h a b ha0' hb
    have hlim : Tendsto (fun n => f (apxQ t n)) atTop (𝓝 (f t)) :=
      (hfc.tendsto t).comp (tendsto_apxQ t)
    have hev : ∀ᶠ n in atTop, 1 / ((m : ℝ) + 1) ≤ f (apxQ t n) := by
      have hIoo : Ioo (a : ℝ≥0) (b : ℝ≥0) ∈ 𝓝 t := Ioo_mem_nhds hat htb
      filter_upwards [tendsto_apxQ t hIoo] with n hn
      have hn' : ((apxQ t n : ℚ≥0) : ℝ≥0) ∈ Ioo (a : ℝ≥0) (b : ℝ≥0) := hn
      exact hm (apxQ t n) (by exact_mod_cast hn'.1.le) (by exact_mod_cast hn'.2.le)
    exact lt_of_lt_of_le (by positivity) (ge_of_tendsto hlim hev)

/-- **The good event on the carrier is Borel.** -/
theorem measurableSet_retTraceGood : MeasurableSet {s | RetTraceGood s} := by
  have hlife : ∀ c : ℝ≥0∞, Measurable fun s : RetCanonSpace => c < RetCanonSpace.life s := fun c =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const RetCanonSpace.measurable_life)
  refine measurableSet_setOfPred.2 (Measurable.and
    (measurableSet_setOfPred.1 retCanonicalGeneratingTraceBorel) (Measurable.and (hlife 0)
      (Measurable.and ?_ ?_)))
  · have e : (fun s : RetCanonSpace => ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < RetCanonSpace.life s →
        0 < (RetCanonSpace.trace s t).im) = fun s => ∀ a b : ℚ≥0, 0 < a →
          ((b : ℝ≥0) : ℝ≥0∞) < RetCanonSpace.life s → ∃ m : ℕ, ∀ r : ℚ≥0, a ≤ r → r ≤ b →
            1 / ((m : ℝ) + 1) ≤ (RetCanonSpace.trace s r).im :=
      funext fun s => propext (retCanonical_interior_iff s)
    rw [e]
    refine Measurable.forall fun a => Measurable.forall fun b => measurable_imp_const fun _ =>
      (hlife _).imp (Measurable.exists fun m => Measurable.forall fun r => measurable_imp_const fun _ =>
        measurable_imp_const fun _ => ?_)
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
      (Complex.measurable_im.comp (RetCanonSpace.measurable_trace _)))
  · have hj : Measurable fun s : RetCanonSpace =>
        RetCanonSpace.trace s (RetCanonSpace.life s).toNNReal := by
      have hu := measurable_uncurry_of_continuous_of_measurable
        (u := fun (t : ℝ≥0) (s : RetCanonSpace) => RetCanonSpace.trace s t)
        (fun s => RetCanonSpace.continuous_trace s) (fun t => RetCanonSpace.measurable_trace t)
      exact hu.comp ((ENNReal.measurable_toNNReal.comp RetCanonSpace.measurable_life).prodMk
        measurable_id)
    exact (measurableSet_setOfPred.1 (measurableSet_eq_fun RetCanonSpace.measurable_life
      measurable_const)).not.imp
      (measurableSet_setOfPred.1 (measurableSet_eq_fun (Complex.measurable_im.comp hj) measurable_const))

/-- The good facts on the carrier from the pathwise source facts and the coordinate reader. -/
theorem retTraceGood_of_source {Ω : Type*} {Y : Ω → RetCanonSpace} {W : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hWY : ∀ ω t, RetCanonSpace.driver t (Y ω) = W t ω)
    (hVY : ∀ ω, RetCanonSpace.life (Y ω) = V ω)
    (hγY : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) ≤ V ω → RetCanonSpace.trace (Y ω) t = γ ω t) {ω : Ω}
    (hg : IsGeneratingTrace (W · ω) (V ω) (γ ω))
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → 0 < (γ ω t).im)
    (hreal : V ω ≠ ⊤ → (γ ω (V ω).toNNReal).im = 0) (hpos : 0 < V ω) : RetTraceGood (Y ω) := by
  have hWf : (fun t => RetCanonSpace.driver t (Y ω)) = (W · ω) := funext (hWY ω)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hWf, hVY]
    exact isGeneratingTrace_congr_le hg (hγY ω)
  · rw [hVY]
    exact hpos
  · intro t ht0 ht
    rw [hVY] at ht
    rw [hγY ω t ht.le]
    exact hH t ht0 ht
  · intro htop
    rw [hVY] at htop ⊢
    rw [hγY ω _ ENNReal.coe_toNNReal_le_self]
    exact hreal htop

/-! ### The constructor -/

universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **PROVE-RETPLUMB's stopped model on an arbitrary source, without its two named inputs.** The same
model as `RetAux79.stoppedModelTransfer_of_canonicalInputs`; its generating-trace Borel input is proved
(`retCanonicalGeneratingTraceBorel`) and its boundary-approach input is replaced by three pathwise facts
about the source path on the type event: interior at positive times before the lifetime, real at a finite
lifetime, and a positive lifetime. -/
def stoppedModelTransfer_of_traceInputs {κ θ : ℝ} (a : ForceWordType)
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
    (hH : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → 0 < (γ ω t).im)
    (hreal : ∀ᵐ ω ∂P, ω ∈ M → V ω ≠ ⊤ → (γ ω (V ω).toNNReal).im = 0)
    (hVpos : ∀ᵐ ω ∂P, ω ∈ M → 0 < V ω) :
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
  have hgoodQ : ∀ᵐ s ∂Q, RetTraceGood s := by
    apply (ae_map_iff hY.aemeasurable measurableSet_retTraceGood).2
    apply ae_cond_of_ae_imp hMm
    filter_upwards [hg, hH, hreal, hVpos] with ω hgω hHω hrω hpω hωM
    exact retTraceGood_of_source hWY hVY hγY (hgω hωM) (hHω hωM) (hrω hωM) (hpω hωM)
  have hp : RetDrivingLifetimePredictable Q hXP := retDrivingLifetimePredictable_of_trace hXP hgoodQ
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
    generates := ae_retCanonical_generates retCanonicalGeneratingTraceBorel hY hMm hWY hVY hγY hg }
  exact {
    model := { space := RetCanonSpace
               sigma := inferInstance
               borel := inferInstance
               law := Q
               probability := inferInstance
               data := D }
    read := Y, readMeas := hY, mapLaw := rfl
    agrees := Eventually.of_forall fun ω _ => ⟨hCY ω, hHY ω, hVY ω, hγY ω⟩ }

end InteractingSLE.Restart.RetLeaf
