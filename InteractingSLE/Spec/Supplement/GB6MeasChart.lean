/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Meas
import InteractingSLE.GFF.PushforwardLoewner

/-!
# Proposition GB6: a measurable version of the chart field in the flow's own target component

Packet PROVE-GB6D, the measurability layer of GB6's restart variable (part 2). The chart field of GB6 is the field
`h` read in the chart of the flow's own target component `U = ℍ \ K_s`, `ownComponentChart = I ∘ f_s`
(`Spec/Jordan/Coupling.lean`), in the counterflow frame (`IsChartTransport` with `σ = −1`, `a = −πχ`, `k = χ(16/κ)`).

* `measurable_chartTransport_ownComponentChart`: for a driving process with continuous paths, `W 0 = 0`, measurable at
  each time, the field transported by the own-component chart at time `s` is a random distribution (from
  PROVE-PUSHFWD's `Chart.measurable_chartTransport_loewnerChartAt` data: the chart domain is the Loewner chart's, the
  forward map is `−1/f_s`, the lift adds `Im(−2 Log f_s)`);
* `IsChartTransport.congr_chart`: the transport relation only reads `fwd`, `lift` and `inv` on `ℍ`;
* **`exists_measurable_chartField`**: for the driver of a flow line, there is a measurable `Hc` that is the chart
  transport of `h` almost surely on `{s < ζα}` (the driver is replaced by a continuous version frozen at `s`, defined on
  a measurable full-measure event; the charts agree since `f_s`, `log f_s′` only read the driver on `[0, s]` and `f_s⁻¹`
  agrees on `ℍ` for continuous drivers, `fwdMapInv_eq_of_eqOn_Icc`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB6

open LQGMetric

/-! ### The own-component chart of a random continuous driver -/

theorem ownComponentChart_dom_eq {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    ((ownComponentChart w s).dom : Set ℂ) = H \ QuantumZipper.fwdHull w s := by
  have hD := isDomainChart_ownComponentChart hw hw0 hs
  rw [hD.1.coe_dom, hD.2.1]

theorem loewner_dom_eq {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    ((Chart.id.loewner w s).dom : Set ℂ) = H \ QuantumZipper.fwdHull w s := by
  have hD := isDomainChart_loewner hw hw0 hs
  rw [hD.1.coe_dom, hD.2.1]

theorem ownComponentChart_fst (w : ℝ → ℝ) (s : ℝ) (z : ℂ) :
    (ownComponentChart w s).1 z = -((Chart.id.loewner w s).1 z)⁻¹ := rfl

theorem ownComponentChart_lift (w : ℝ → ℝ) (s : ℝ) (z : ℂ) :
    (ownComponentChart w s).2.2 z =
      (-2 * Complex.log ((Chart.id.loewner w s).1 z)).im + (Chart.id.loewner w s).2.2 z := rfl

section Random

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {V : ℝ≥0 → Ω → ℝ}

/-- **The field transported by the own-component chart of a random continuous driver is a random distribution.** -/
theorem measurable_chartTransport_ownComponentChart (hVm : ∀ t, Measurable (V t))
    (hVc : ∀ ω, Continuous fun t => V t ω) (hV0 : ∀ ω, V 0 ω = 0) (s : ℝ≥0)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (σ a k : ℝ) :
    Measurable fun ω => Chart.chartTransport (isDomainChart_ownComponentChart
      (Chart.continuous_rpath_of_continuous (hVc ω)) (Chart.rpath_zero_of (hV0 ω)) s.coe_nonneg).1 σ a k (h ω) := by
  set 𝓖 : Filtration ℝ≥0 mΩ := Chart.constFiltration le_rfl with h𝓖
  have hVa : Adapted 𝓖 V := fun t => hVm t
  set c : Ω → Chart := fun ω => ownComponentChart (Ito.rpath (V · ω)) s with hcdef
  have hrc : ∀ ω, Continuous (Ito.rpath (V · ω)) := fun ω => Chart.continuous_rpath_of_continuous (hVc ω)
  have hr0 : ∀ ω, Ito.rpath (V · ω) 0 = 0 := fun ω => Chart.rpath_zero_of (hV0 ω)
  have hdomeq : ∀ ω, {z | z ∈ (c ω).dom} = {z | z ∈ (Chart.loewnerChartAt V s ω).dom} := fun ω => by
    ext z
    change z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ ((Chart.loewnerChartAt V s ω).dom : Set ℂ)
    rw [ownComponentChart_dom_eq (hrc ω) (hr0 ω) s.coe_nonneg,
      loewner_dom_eq (hrc ω) (hr0 ω) s.coe_nonneg]
  have hdomω : ∀ z, {ω | z ∈ (c ω).dom} = {ω | z ∈ (Chart.loewnerChartAt V s ω).dom} := fun z => by
    ext ω
    exact (Set.ext_iff.1 (hdomeq ω) z)
  have hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom} := fun z => by
    rw [hdomω z]
    exact 𝓖.le s _ (Chart.measurableSet_mem_dom_loewnerChartAt hVa hVc hV0 s z)
  have hfL : ∀ z, Measurable ({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator
      fun ω => (Chart.loewnerChartAt V s ω).1 z) := fun z =>
    (Chart.measurable_indicator_fwd_loewnerChartAt hVa hVc hV0 s z).mono (𝓖.le s) le_rfl
  have hlL : ∀ z, Measurable ({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator
      fun ω => (Chart.loewnerChartAt V s ω).2.2 z) := fun z =>
    (Chart.measurable_indicator_lift_loewnerChartAt hVa hVc hV0 s z).mono (𝓖.le s) le_rfl
  have hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z) := fun z => by
    rw [hdomω z]
    have e : ({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator fun ω => (c ω).1 z) =
        fun ω => -(({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator
          fun ω => (Chart.loewnerChartAt V s ω).1 z) ω)⁻¹ := by
      funext ω
      by_cases hω : ω ∈ {ω | z ∈ (Chart.loewnerChartAt V s ω).dom}
      · rw [indicator_of_mem hω, indicator_of_mem hω]; rfl
      · rw [indicator_of_notMem hω, indicator_of_notMem hω, inv_zero, neg_zero]
    rw [e]
    exact (hfL z).inv.neg
  have hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z) := fun z => by
    rw [hdomω z]
    have e : ({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator fun ω => (c ω).2.2 z) =
        fun ω => (-2 * Complex.log (({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator
          fun ω => (Chart.loewnerChartAt V s ω).1 z) ω)).im +
          ({ω | z ∈ (Chart.loewnerChartAt V s ω).dom}.indicator
            fun ω => (Chart.loewnerChartAt V s ω).2.2 z) ω := by
      funext ω
      by_cases hω : ω ∈ {ω | z ∈ (Chart.loewnerChartAt V s ω).dom}
      · rw [indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω]; rfl
      · rw [indicator_of_notMem hω, indicator_of_notMem hω, indicator_of_notMem hω, Complex.log_zero,
          mul_zero, Complex.zero_im, add_zero]
    rw [e]
    exact (Complex.measurable_im.comp ((Complex.measurable_log.comp (hfL z)).const_mul _)).add (hlL z)
  have hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom := fun ω => by
    have hdo : ((c ω).dom : Set ℂ) = H \ QuantumZipper.fwdHull (Ito.rpath (V · ω)) s :=
      ownComponentChart_dom_eq (hrc ω) (hr0 ω) s.coe_nonneg
    have hdL : ((Chart.id.loewner (Ito.rpath (V · ω)) s).dom : Set ℂ) =
        H \ QuantumZipper.fwdHull (Ito.rpath (V · ω)) s := loewner_dom_eq (hrc ω) (hr0 ω) s.coe_nonneg
    have hf := (QuantumZipper.FwdHolo.differentiableOn_fwdMap (hrc ω) s.coe_nonneg).continuousOn
    have hmap := QuantumZipper.FwdHolo.mapsTo_fwdMap (hrc ω) s.coe_nonneg
    have hl := Chart.continuousOn_lift_loewner (hrc ω) (hr0 ω) s.coe_nonneg
    rw [hdL] at hl
    change ContinuousOn (fun z => (ownComponentChart (Ito.rpath (V · ω)) s).2.2 z) ((c ω).dom : Set ℂ)
    simp_rw [ownComponentChart_lift]
    rw [hdo]
    refine (Complex.continuous_im.comp_continuousOn ((continuousOn_const.mul ?_))).add hl
    refine ContinuousOn.clog hf fun z hz => ?_
    exact Complex.mem_slitPlane_iff.2 (Or.inr (hmap hz).ne')
  exact Chart.measurable_chartTransport_random' (fun ω => (isDomainChart_ownComponentChart (hrc ω) (hr0 ω)
    s.coe_nonneg).1) hdom hfwd hliftm hliftc hh σ a k

end Random

/-! ### The transport relation only reads the chart on `ℍ` -/

/-- **The transport relation only reads `fwd`, `lift` and `inv` on `ℍ`.** -/
theorem isChartTransport_congr_chart {c c' : Chart} (h1 : c.1 = c'.1) (h2 : c.2.2 = c'.2.2)
    (h3 : EqOn c.2.1 c'.2.1 H) {σ a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport c σ a k h h') : IsChartTransport c' σ a k h h' := by
  have himg : c.2.1 '' H = c'.2.1 '' H := image_congr h3
  intro φ φ' hφ hφ'
  rw [← himg] at hφ hφ'
  rw [← h1] at hφ'
  have hint : (∫ w, c'.2.2 (c'.2.1 w) * φ' w) = ∫ w, c.2.2 (c.2.1 w) * φ' w := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · simp only [h3 hw, h2]
    · have h0 : φ' w = 0 := φ'.zero_on_compl hw
      simp only [h0, mul_zero]
  rw [hint]
  exact ht φ φ' hφ hφ'

/-! ### A measurable chart field for the driver of a flow line -/

/-- **A measurable version of the own-component chart field.** For the driver `Wα` of a flow line (any parameter,
angle, boundary data) and a measurable field `h`, at every own time `s` there is a measurable `Hc` which, almost surely
on `{s < ζα}`, is the transport of `h` by the chart of the flow's own target component at time `s`. -/
theorem exists_measurable_chartField {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hh : Measurable h) (s : ℝ≥0) (σ a k : ℝ) :
    ∃ Hc : Ω → DistOn upperHalfPlaneOpens, Measurable Hc ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω →
        IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) σ a k (h ω) (Hc ω) := by
  classical
  have hgood0 := ae_driver_zero_continuousOn hfl
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hfl
  have hWa : AdaptedBefore 𝓕 ζα Wα := hC.1.2.1
  -- the good event
  set Good : Ω → Prop := fun ω => Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω}
    with hGooddef
  have hgood : ∀ᵐ ω ∂P, Good ω := hgood0
  set G : Set Ω := (toMeasurable P {ω | ¬ Good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra hn; exact hω (subset_toMeasurable _ _ hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G} = toMeasurable P {ω | ¬ Good ω} := by
      ext ω; simp only [hGdef, mem_ofPred_eq, mem_compl_iff, not_not]
    rw [this, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hsζ : MeasurableSet {ω | (s : ℝ≥0∞) < ζα ω} := by
    have h1 := hWa s univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h1
    exact 𝓕.le s _ h1
  set E : Set Ω := G ∩ {ω | (s : ℝ≥0∞) < ζα ω} with hEdef
  have hEm : MeasurableSet E := hGm.inter hsζ
  -- the continuous version of the driver, frozen at `s`
  set V : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ E then Wα (min t s) ω else 0 with hVdef
  have hVm : ∀ t, Measurable (V t) := fun t => by
    have hk := (Girsanov.measurable_killed hWa (min t s)).mono (𝓕.le _) le_rfl
    have e : V t = fun ω => if ω ∈ E then Girsanov.killed ζα Wα (min t s) ω else 0 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [hVdef, hω, ↓reduceIte]
        rw [Girsanov.killed_of_lt (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right t s)) hω.2)]
      · simp only [hVdef, hω, ↓reduceIte]
    rw [e]
    exact Measurable.ite hEm hk measurable_const
  have hVc : ∀ ω, Continuous fun t => V t ω := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hVdef, hω, ↓reduceIte]
      have hc := (hGgood ω hω.1).2
      refine hc.comp_continuous (continuous_id.min continuous_const) fun t => ?_
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right t s)) hω.2
    · simp only [hVdef, hω, ↓reduceIte]
      exact continuous_const
  have hV0 : ∀ ω, V 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hVdef, hω, ↓reduceIte, zero_min, (hGgood ω hω.1).1]
    · simp only [hVdef, hω, ↓reduceIte]
  have hrc : ∀ ω, Continuous (Ito.rpath (V · ω)) := fun ω => Chart.continuous_rpath_of_continuous (hVc ω)
  have hr0 : ∀ ω, Ito.rpath (V · ω) 0 = 0 := fun ω => Chart.rpath_zero_of (hV0 ω)
  have hD : ∀ ω, IsDomainChart (H \ QuantumZipper.fwdHull (Ito.rpath (V · ω)) s)
      (ownComponentChart (Ito.rpath (V · ω)) s) := fun ω =>
    isDomainChart_ownComponentChart (hrc ω) (hr0 ω) s.coe_nonneg
  refine ⟨fun ω => Chart.chartTransport (hD ω).1 σ a k (h ω),
    measurable_chartTransport_ownComponentChart hVm hVc hV0 s hh σ a k, ?_⟩
  filter_upwards [hGae] with ω hωG hsω
  have hωE : ω ∈ E := ⟨hωG, hsω⟩
  obtain ⟨hW0, hWc⟩ := hGgood ω hωG
  -- the version agrees with `Wα` on `[0, s]`
  have hagree : ∀ r ∈ Icc (0 : ℝ) s, Ito.rpath (V · ω) r = Wα r.toNNReal ω := fun r hr => by
    have hrs : r.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [Ito.rpath, hVdef, hωE, ↓reduceIte, min_eq_left hrs]
  have hEq : EqOn (Ito.rpath (V · ω)) (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (s : ℝ)) := hagree
  -- the chart of the version is a transport
  have hlift : ContinuousOn (ownComponentChart (Ito.rpath (V · ω)) s).2.2
      (ownComponentChart (Ito.rpath (V · ω)) s).dom := by
    have hdo := ownComponentChart_dom_eq (hrc ω) (hr0 ω) s.coe_nonneg
    have hdL := loewner_dom_eq (hrc ω) (hr0 ω) s.coe_nonneg
    have hf := (QuantumZipper.FwdHolo.differentiableOn_fwdMap (hrc ω) s.coe_nonneg).continuousOn
    have hmap := QuantumZipper.FwdHolo.mapsTo_fwdMap (hrc ω) s.coe_nonneg
    have hl := Chart.continuousOn_lift_loewner (hrc ω) (hr0 ω) s.coe_nonneg
    rw [hdL] at hl
    change ContinuousOn (fun z => (ownComponentChart (Ito.rpath (V · ω)) s).2.2 z)
      ((ownComponentChart (Ito.rpath (V · ω)) s).dom : Set ℂ)
    simp_rw [ownComponentChart_lift]
    rw [hdo]
    refine (Complex.continuous_im.comp_continuousOn ((continuousOn_const.mul ?_))).add hl
    exact ContinuousOn.clog hf fun z hz => Complex.mem_slitPlane_iff.2 (Or.inr (hmap hz).ne')
  have htr := Chart.isChartTransport_chartTransport (hD ω).1
    (Chart.locallyIntegrableOn_of_continuousOn ((hD ω).1.continuousOn_lift_inv hlift)) σ a k (h ω)
  refine isChartTransport_congr_chart ?_ ?_ ?_ htr
  · funext z
    show -(QuantumZipper.fwdMap (Ito.rpath (V · ω)) s z)⁻¹ = -(QuantumZipper.fwdMap _ s z)⁻¹
    rw [Ito.fwdMap_congr_of_eqOn hEq]
  · funext z
    rw [ownComponentChart_lift, ownComponentChart_lift]
    show (-2 * Complex.log (QuantumZipper.fwdMap (Ito.rpath (V · ω)) s z)).im +
        ((QuantumZipper.logDerivFwd (Ito.rpath (V · ω)) s z).im + 0) =
      (-2 * Complex.log (QuantumZipper.fwdMap _ s z)).im + ((QuantumZipper.logDerivFwd _ s z).im + 0)
    rw [Ito.fwdMap_congr_of_eqOn hEq, Ito.logDerivFwd_congr_of_eqOn hEq s.coe_nonneg le_rfl]
  · intro w hw
    -- through the driver frozen at some `t₂ ∈ (s, ζα)`
    obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hsω
    have hfc : Continuous (frozenDrive (fun t => Wα t ω) t₂) := continuous_frozenDrive_of_lt hWc ht₂
    have hf0 : frozenDrive (fun t => Wα t ω) t₂ 0 = 0 := by
      rw [frozenDrive_zero (le_trans s.coe_nonneg hst₂.le)]; exact hW0
    have h1 : (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s).2.1 =
        (ownComponentChart (frozenDrive (fun t => Wα t ω) t₂) s).2.1 :=
      ownComponentChart_inv_eq_of_eqOn s.coe_nonneg hst₂ fun r hr =>
        (frozenDrive_eq (w := fun t => Wα t ω) hr).symm
    rw [h1]
    have hwH : -w⁻¹ ∈ H := Chart.isConformal_infinitySourceChart.2.1 hw
    show QuantumZipper.fwdMapInv (Ito.rpath (V · ω)) s (-w⁻¹) =
      QuantumZipper.fwdMapInv (frozenDrive (fun t => Wα t ω) t₂) s (-w⁻¹)
    refine LP.fwdMapInv_eq_of_eqOn_Icc (hrc ω) hfc (hr0 ω) hf0 s.coe_nonneg (fun r hr => ?_) hwH
    rw [hagree r hr, frozenDrive_eq ⟨hr.1, hr.2.trans hst₂.le⟩]

end GB6

end Supp8

end InteractingSLE
