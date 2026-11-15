/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualChart

/-!
# Recovering the physical chart path from killed histories

Packet PROVE-RETPLUMB. Freeze the good original path at its recorded lifetime
and clip it at the current line. This continuous proxy is read by the existing
capped-history reader. Before the boundary stop it equals the original path.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7 Sec7.Lemma76F Sec7.Lemma76G LocalSets
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A killed and clipped proxy, with zero value outside the initial event. -/
def retObservedPath (F : Set Ω) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (m b : ℝ≥0) (ω : Ω) (s : ℝ≥0) : ℂ :=
  F.indicator (fun ω => η ω (capTime m (ζ ω) (min s b))) ω

omit mΩ in
/-- Freezing at the recorded death gives a continuous proxy, also after death. -/
theorem continuous_retObservedPath {F : Set Ω} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} {x : ℝ} (hp : ∀ ω ∈ F, IsPathGood (η ω) (ζ ω) x)
    (m b : ℝ≥0) (ω : Ω) : Continuous (retObservedPath F η ζ m b ω) := by
  classical
  by_cases hω : ω ∈ F
  · change Continuous (fun s => F.indicator (fun ω => η ω (capTime m (ζ ω) (min s b))) ω)
    simp only [indicator_of_mem hω]
    exact (continuous_capTime_comp m (hp ω hω).continuousOn).comp
      (continuous_id.min continuous_const)
  · have he : retObservedPath F η ζ m b ω = fun _ => 0 := by
      funext s
      exact indicator_of_notMem hω _
    rw [he]
    exact continuous_const

/-- The proxy has measurable coordinates without requiring good behavior off
its supporting event. -/
theorem measurable_retObservedPath {F : Set Ω} (hF : MeasurableSet F)
    {η : Ω → ℝ≥0 → ℂ} (hm : ∀ s, Measurable fun ω => η ω s)
    {ζ : Ω → ℝ≥0∞} (hζ : Measurable ζ) {x : ℝ}
    (hp : ∀ ω ∈ F, IsPathGood (η ω) (ζ ω) x) (m b s : ℝ≥0) :
    Measurable fun ω => retObservedPath F η ζ m b ω s := by
  classical
  have htime : Measurable fun ω => capTime m (ζ ω) (min s b) :=
    measurable_const.min (ENNReal.measurable_toNNReal.comp (hζ.min measurable_const))
  have h := measurable_piecewise_eval hF hm htime fun ω hω =>
    (hp ω hω).continuousOn.mono fun q hq =>
      (ENNReal.coe_le_coe.2 hq).trans (capTime_le m (ζ ω) (min s b))
  simpa only [retObservedPath, indicator_apply] using h

/-- The killed proxy is an actual observable of the current completed killed
histories, including samples whose original path has already died. -/
theorem measurable_retObservedPath_retSigma76 {P : Measure Ω}
    {F : Set Ω} {η₁ η₂ η₂' ηc : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {u b : ℝ≥0} (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u b] F)
    (hm : ∀ s, Measurable fun ω => η₂' ω s) (hζ : Measurable ζ₂) {x : ℝ}
    (hp : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x)
    (ha : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hc : ∀ ω, Continuous (ηc ω)) (hmc : ∀ s, Measurable fun ω => ηc ω s)
    (hac : ∀ᵐ ω ∂P, ∀ s, ηc ω s = η₂ ω (capTime (capR u b) (ζ₂ ω) s)) (s : ℝ≥0) :
    Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u b]
      (fun ω => retObservedPath F η₂' ζ₂ (capR u b) b ω s) := by
  apply measurable_retSigma76_congr
    (measurable_retObservedPath (retSigma76_le P η₁ η₂ ζ₁ ζ₂ u b _ hF) hm hζ hp _ _ _)
    ((measurable_capped_right_retSigma76 hc hmc hac (min_le_right s b)).indicator hF)
  filter_upwards [ha, hac] with ω he hcω
  by_cases hω : ω ∈ F
  · simp only [retObservedPath, indicator_of_mem hω]
    rw [hcω]
    exact he _ (capTime_le _ _ _)
  · simp only [retObservedPath, indicator_of_notMem hω]

/-- Construct all three physical prefix observations. The two chart-coordinate
premises are supplied by the landed `chart_measurability_retSigma76`; no full
future-lifetime measurability at the current line is assumed. -/
theorem retPrefixObservations_retPhysFiltration {P : Measure Ω}
    {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {G : ℝ≥0 → Set Ω} {u r : ℝ≥0} {F : Set Ω} {x₁ x₂ : ℝ}
    (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F) (hG : F ⊆ G r)
    (hζ₂ : Measurable ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ)
    (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s)
    (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s =
      η₁ ω (capTime (capR u (r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s =
      η₂ ω (capTime (capR u (r + t)) (ζ₂ ω) s))
    (hdom : ∀ z, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r]
      {ω | z ∈ (retFam G η₁' η₂' u r).D ω})
    (hfwd : ∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r]
      ({ω | z ∈ (retFam G η₁' η₂' u r).D ω}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z)) :
    RetPrefixObservations (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) F G η₁' η₂' ζ₂ u r := by
  classical
  let 𝓖 := retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r
  have hF₀ : MeasurableSet[𝓖 0] F := by
    change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + 0)] F
    rw [add_zero]
    exact hF
  have hsurv := measurableSet_retLifeP_retPhysFiltration hd hF hG hζ₂ ha₁ ha₂ hp₁ hp₂ hpair
    ηc₁ ηc₂ hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  refine ⟨hF₀, ?_, hsurv⟩
  intro t s hst
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have hs : s = 0 := le_antisymm hst zero_le
    subst s
    have he : (F.indicator fun ω => retChartPath G η₁' η₂' ζ₂ u r ω 0) = fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ F
      · simp only [indicator_of_mem hω]
        exact (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).2
      · exact indicator_of_notMem hω _
    rw [he]
    exact measurable_const
  have hFt : MeasurableSet[𝓖 t] F := 𝓖.mono zero_le _ hF₀
  let ηk := retObservedPath F η₂' ζ₂ (capR u (r + t)) (r + t)
  have hmη : ∀ q, Measurable[𝓖 t] fun ω => ηk ω q := fun q =>
    measurable_retObservedPath_retSigma76 hFt hd.meas₂ hζ₂ hp₂ ha₂ (hc₂ t) (hm₂ t) (hag₂ t) q
  have hprefix : ∀ ω ∈ F, ∀ q : ℝ≥0,
      (q : ℝ≥0∞) < min (retLifeP η₁' η₂' ζ₂ u r ω) (t : ℝ≥0∞) →
      ηk ω (r + q) = η₂' ω (r + q) := by
    intro ω hω q hq
    have hqt : q < t := ENNReal.coe_lt_coe.1 ((lt_min_iff.1 hq).2)
    have hζ : ((r + q : ℝ≥0) : ℝ≥0∞) ≤ ζ₂ ω :=
      ((coe_add_lt_iff.1 (lt_min_iff.1 hq).1).trans_le contStop_le).le
    simp only [ηk, retObservedPath, indicator_of_mem hω,
      min_eq_left (add_le_add le_rfl hqt.le)]
    rw [capTime_of_le _ _ (le_min hζ (ENNReal.coe_le_coe.2
      ((add_le_add le_rfl hqt.le).trans (lt_capR_right u (r + t)).le)))]
  have hE : ∀ ω ∈ F, ω ∈ (retFam G η₁' η₂' u r).E := fun ω hω =>
    mem_E_of_isDisjointPair hd (hG hω) (fun _ _ => rfl) (fun _ _ => rfl) (hpair ω hω)
  suffices hm : Measurable[𝓖 t] (F.indicator fun ω =>
      contPath ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).chart ω).1
        (η₂' ω) r (retLifeP η₁' η₂' ζ₂ u r ω) s) by
    convert hm using 1
    funext ω
    by_cases hω : ω ∈ F
    · simp only [indicator_of_mem hω, RetData.chart_of_mem (hE ω hω)]
      rfl
    · simp only [indicator_of_notMem hω]
  apply @measurable_contPath_of_past Ω (𝓖 t) F hFt
    (fun ω => (retFam G η₁' η₂' u r).D ω) (fun ω => hd.isOpen_D ω)
    (fun z => (retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl le_self_add) _ (hdom z))
    (fun ω => ((retFam G η₁' η₂' u r).chart ω).1)
    (fun z => (hfwd z).mono
      (retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl le_self_add) le_rfl)
    η₂' ηk hmη (fun ω _ => continuous_retObservedPath hp₂ _ _ ω) r t ht
    (retLifeP η₁' η₂' ζ₂ u r)
    (measurable_indicator_min_of_survival hF₀ hsurv t)
    (fun ω hω => (retLife_pos_of_good_pair hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1)
    hprefix ?_ ?_ ?_ s hst
  · intro ω hω q hq
    obtain ⟨hR, hD, hL⟩ := isRetCont_retFam hd (hG hω) (hp₂ ω hω) (hpair ω hω)
    rw [hD]
    rw [hL] at hq
    exact hR.mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add (coe_add_lt_iff.1 hq).le)
  · intro ω hω q hq
    rw [RetData.chart_of_mem (hE ω hω)]
    obtain ⟨hR, hD, hL⟩ := isRetCont_retFam hd (hG hω) (hp₂ ω hω) (hpair ω hω)
    rw [hD]
    rw [hL] at hq
    exact ⟨_, (hR.contPath_spec_lt hq).2.1⟩
  · intro ω hω
    rw [RetData.chart_of_mem (hE ω hω)]
    exact (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1

end InteractingSLE.Restart.RetAux79
