/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondWordFilt
import InteractingSLE.GFF.PushforwardLoewner
import InteractingSLE.Spec.Jordan.Chart
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# The counterflow chart `Ψ` of `ℍ ∖ R(K′_s)` with its continuous branch of `arg Ψ′`

Packet PROVE-GLUECOND7 (specification §4.2, proof of Proposition 4.9 and Remark 4.10; Astra's Part E.6 at general
`κ`). At `κ = 4` the chart of the image word carries the zero lift (`χ = 0`). At general `κ` the coordinate rule (1.4)
needs a **continuous branch of `arg Ψ′`** on `ℍ ∖ R(K′_s)`, measurable in the counterflow history. It is the analytic
chain-rule lift of `Ψ = R ∘ f′_s ∘ R` (`R z = −1/z`):

`L_Ψ(z) = −2 log f′_s(R z) + log f′_s′(R z) − 2 log z`,

with principal logarithms of points of `ℍ` and the hydrodynamic branch `logDerivFwd` of `log f′_s′`. As a chart it is
literally `(R-chart).loewner W′ s` followed by the `R`-chart (`Chart.trans`), so the landed Loewner-chart API applies.
On the physical real line `Ψ′ > 0` while `Im L_Ψ → −2π`; the coordinate rule therefore uses the height shift
`a = 2πχ` with this lift (equivalently the lift `Im L_Ψ + 2π` with `a = 0`).

## Main results

* `psiLog`, **`isDerivLog_revChart`**: `L_Ψ` is an analytic logarithm of `Ψ′` on `ℍ ∖ R(K′_s)`;
* `cfChart s y`: the chart `(Ψ, Ψ⁻¹, Im L_Ψ)` read from the counterflow history stopped at `s`; `cfChart_fst`,
  `cfChart_inv`, `cfChart_lift`;
* `isConformal_cfChart`, `mem_dom_cfChart_iff` (the domain is `ℍ ∖ R(K′_s)`), **`continuousOn_lift_cfChart`**;
* **measurability for the stopped history** (`stopSigma s`): `measurableSet_mem_dom_cfChart`,
  `measurable_indicator_fwd_cfChart`, `measurable_indicator_lift_cfChart`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q

namespace Word49

/-! ### The derivative lift of `Ψ = R ∘ f_s ∘ R` -/

section Lift

variable {w : ℝ → ℝ} {s : ℝ}

/-- **The derivative lift of `Ψ = R ∘ f_s ∘ R`** (analytic chain rule, specification p. 2):
`L_Ψ(z) = −2 log f_s(R z) + (log f_s′(R z) − 2 log z)`, `R z = −1/z`. -/
def psiLog (w : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  -2 * log (fwdMap w s (negInv z)) + (logDerivFwd w s (negInv z) + -2 * log z)

theorem revChart_eq_comp (w : ℝ → ℝ) (s : ℝ) :
    revChart w s = (fun z : ℂ => -z⁻¹) ∘ (fwdMap w s ∘ fun z : ℂ => -z⁻¹) := rfl

theorem negInv_mapsTo_H : MapsTo (fun z : ℂ => -z⁻¹) H H := Chart.isConformal_infinitySourceChart.2.1

theorem differentiableOn_negInv_H : DifferentiableOn ℂ (fun z : ℂ => -z⁻¹) H :=
  Chart.isConformal_infinitySourceChart.1

/-- **`L_Ψ` is an analytic logarithm of `Ψ′` on `ℍ ∖ R(K_s)`** (the continuous branch of `arg Ψ′` is its imaginary
part). -/
theorem isDerivLog_revChart (hw : Continuous w) (hs : 0 ≤ s) :
    IsDerivLog (revChart w s) (psiLog w s) (H \ negInv '' fwdHull w s) := by
  have hDo : IsOpen (H \ negInv '' fwdHull w s) := isOpen_H_diff_negInv_fwdHull hw hs
  have hEo : IsOpen (H \ fwdHull w s) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw hs
  have hmaps1 : MapsTo (fun z : ℂ => -z⁻¹) (H \ negInv '' fwdHull w s) (H \ fwdHull w s) := fun z hz =>
    negInv_notMem_fwdHull hz
  have hL1 : IsDerivLog (fun z : ℂ => -z⁻¹) (fun z => -2 * log z) (H \ negInv '' fwdHull w s) :=
    isDerivLog_neg_inv.mono sdiff_subset
  have hin := IsDerivLog.comp hDo hEo (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs)
    (differentiableOn_negInv_H.mono sdiff_subset) hmaps1 (isDerivLog_fwdMap hw hs) hL1
  have hmaps2 : MapsTo (fwdMap w s ∘ fun z : ℂ => -z⁻¹) (H \ negInv '' fwdHull w s) H := fun z hz =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hmaps1 hz)
  have hdiff2 : DifferentiableOn ℂ (fwdMap w s ∘ fun z : ℂ => -z⁻¹) (H \ negInv '' fwdHull w s) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).comp (differentiableOn_negInv_H.mono sdiff_subset)
      hmaps1
  have h := IsDerivLog.comp hDo QuantumZipper.isOpen_H differentiableOn_negInv_H hdiff2 hmaps2 isDerivLog_neg_inv hin
  rw [revChart_eq_comp]
  exact h

/-- The lift is continuous on `ℍ ∖ R(K_s)`. -/
theorem continuousOn_psiLog (hw : Continuous w) (hs : 0 ≤ s) :
    ContinuousOn (psiLog w s) (H \ negInv '' fwdHull w s) :=
  (isDerivLog_revChart hw hs).1.continuousOn

end Lift

/-! ### The chart -/

section Chart

/-- **The counterflow chart** `(Ψ, Ψ⁻¹, Im L_Ψ)` of `ℍ ∖ R(K′_s)`, read from the counterflow history stopped at `s`:
the `R`-chart, the centred Loewner stage of the recentred stopped counterflow driver, then the `R`-chart again. -/
def cfChart (s : ℝ≥0) (y : HistorySpace 0 0) : Chart :=
  (infinitySourceChart.loewner (cfDrv0 s y) s).trans infinitySourceChart

variable {s : ℝ≥0}

theorem cfChart_fst (y : HistorySpace 0 0) : (cfChart s y).1 = revChart (cfDrv0 s y) s := rfl

theorem cfChart_inv (y : HistorySpace 0 0) : (cfChart s y).2.1 = revChartInv (cfDrv0 s y) s := rfl

theorem cfChart_lift (y : HistorySpace 0 0) (z : ℂ) : (cfChart s y).2.2 z = (psiLog (cfDrv0 s y) s z).im := by
  simp only [cfChart, Chart.trans_lift, Chart.loewner, infinitySourceChart, psiLog, negInv, add_im]

theorem isConformal_cfChart (y : HistorySpace 0 0) : (cfChart s y).IsConformal :=
  (Chart.isConformal_infinitySourceChart.loewner (continuous_cfDrv0 s y) (cfDrv0_zero s y) s.coe_nonneg).trans
    Chart.isConformal_infinitySourceChart

/-- The domain of the chart is `ℍ ∖ R(K′_s)`. -/
theorem coe_dom_cfChart (y : HistorySpace 0 0) :
    ((cfChart s y).dom : Set ℂ) = H \ negInv '' fwdHull (cfDrv0 s y) s := by
  rw [(isConformal_cfChart y).coe_dom, cfChart_inv]
  exact (isConformalBijection_revChartInv (continuous_cfDrv0 s y) (cfDrv0_zero s y) s.coe_nonneg).2.image_eq

theorem mem_dom_cfChart_iff (y : HistorySpace 0 0) {z : ℂ} :
    z ∈ (cfChart s y).dom ↔ z ∈ H ∧ negInv z ∉ fwdHull (cfDrv0 s y) s := by
  rw [← SetLike.mem_coe, coe_dom_cfChart]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, fun h => hn ⟨negInv z, h, negInv_negInv' z⟩⟩
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact hn (by rwa [negInv_negInv'])

/-- **The lift of the chart is continuous on its domain.** -/
theorem continuousOn_lift_cfChart (y : HistorySpace 0 0) : ContinuousOn (cfChart s y).2.2 (cfChart s y).dom := by
  have h := (continuous_im.comp_continuousOn (continuousOn_psiLog (continuous_cfDrv0 s y) s.coe_nonneg))
  rw [← coe_dom_cfChart (s := s) y] at h
  exact h.congr fun z _ => cfChart_lift y z

end Chart

/-! ### Measurability in the stopped counterflow history -/

section Meas

variable {s : ℝ≥0}

/-- The recentred stopped counterflow driver as a process on histories. -/
def cfProc (s : ℝ≥0) : ℝ≥0 → HistorySpace 0 0 → ℝ := fun t y => cfDrv0 s y t

/-- The constant filtration at the stopped-history σ-algebra. -/
abbrev stopFilt (s : ℝ≥0) : MeasureTheory.Filtration ℝ≥0 (inferInstance : MeasurableSpace (HistorySpace 0 0)) :=
  MeasureTheory.Filtration.const ℝ≥0 (stopSigma s) (stopSigma_le s)

theorem adapted_cfProc : Adapted (stopFilt s) (cfProc s) := fun t => measurable_cfDrv0_apply s t

theorem continuous_cfProc (y : HistorySpace 0 0) : Continuous fun t => cfProc s t y :=
  (continuous_cfDrv0 s y).comp NNReal.continuous_coe

theorem cfProc_zero (y : HistorySpace 0 0) : cfProc s 0 y = 0 := cfDrv0_zero s y

theorem rpath_cfProc (y : HistorySpace 0 0) : Ito.rpath (cfProc s · y) = cfDrv0 s y := by
  funext r
  exact cfDrv0_toNNReal s y r

theorem loewnerChartAt_cfProc (y : HistorySpace 0 0) :
    Chart.loewnerChartAt (cfProc s) s y = Chart.id.loewner (cfDrv0 s y) s := by
  rw [Chart.loewnerChartAt, rpath_cfProc]

theorem mem_dom_loewnerChartAt_cfProc (y : HistorySpace 0 0) {x : ℂ} :
    x ∈ (Chart.loewnerChartAt (cfProc s) s y).dom ↔ x ∈ H ∧ x ∉ fwdHull (cfDrv0 s y) s := by
  have hw := continuous_cfDrv0 s y
  have hw0 := cfDrv0_zero s y
  rw [loewnerChartAt_cfProc, ← SetLike.mem_coe, (Chart.isConformal_id.loewner hw hw0 s.coe_nonneg).coe_dom]
  change x ∈ fwdMapInv (cfDrv0 s y) s '' H ↔ _
  rw [QuantumZipper.RS.image_fwdMapInv_H hw hw0 s.coe_nonneg]
  rfl

theorem setOf_mem_dom_cfChart {z : ℂ} (hz : z ∈ H) :
    {y : HistorySpace 0 0 | z ∈ (cfChart s y).dom} =
      {y | negInv z ∈ (Chart.loewnerChartAt (cfProc s) s y).dom} := by
  ext y
  have hn : negInv z ∈ H := Sec7.StripSysField.negInv_mem_H hz
  simp only [mem_ofPred_eq, mem_dom_cfChart_iff, mem_dom_loewnerChartAt_cfProc, hz, hn, true_and]

theorem setOf_mem_dom_cfChart_of_notMem {z : ℂ} (hz : z ∉ H) :
    {y : HistorySpace 0 0 | z ∈ (cfChart s y).dom} = ∅ := by
  ext y
  simp only [mem_ofPred_eq, mem_dom_cfChart_iff, hz, false_and, mem_empty_iff_false]

/-- **The domain events of the chart are known from the stopped history.** -/
theorem measurableSet_mem_dom_cfChart (z : ℂ) :
    MeasurableSet[stopSigma s] {y : HistorySpace 0 0 | z ∈ (cfChart s y).dom} := by
  by_cases hz : z ∈ H
  · rw [setOf_mem_dom_cfChart hz]
    exact Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := stopFilt s) adapted_cfProc continuous_cfProc
      cfProc_zero _ _
  · rw [setOf_mem_dom_cfChart_of_notMem hz]
    exact @MeasurableSet.empty _ (stopSigma s)

theorem cfChart_fst_eq_loewnerChartAt (y : HistorySpace 0 0) (z : ℂ) :
    (cfChart s y).1 z = negInv ((Chart.loewnerChartAt (cfProc s) s y).1 (negInv z)) := by
  rw [loewnerChartAt_cfProc]
  rfl

theorem cfChart_lift_eq_loewnerChartAt (y : HistorySpace 0 0) (z : ℂ) :
    (cfChart s y).2.2 z = (-2 * log ((Chart.loewnerChartAt (cfProc s) s y).1 (negInv z))).im +
      (Chart.loewnerChartAt (cfProc s) s y).2.2 (negInv z) + (-2 * log z).im := by
  rw [loewnerChartAt_cfProc]
  simp only [cfChart, Chart.trans_lift, Chart.loewner, Chart.id, infinitySourceChart, negInv, add_zero]
  ring

/-- **The forward map of the chart is known from the stopped history** (on its domain). -/
theorem measurable_indicator_fwd_cfChart (z : ℂ) :
    Measurable[stopSigma s]
      ({y : HistorySpace 0 0 | z ∈ (cfChart s y).dom}.indicator fun y => (cfChart s y).1 z) := by
  classical
  by_cases hz : z ∈ H
  · have h := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := stopFilt s) adapted_cfProc continuous_cfProc
      cfProc_zero s (negInv z)
    have e : ({y : HistorySpace 0 0 | z ∈ (cfChart s y).dom}.indicator fun y => (cfChart s y).1 z) =
        negInv ∘ ({y | negInv z ∈ (Chart.loewnerChartAt (cfProc s) s y).dom}.indicator
          fun y => (Chart.loewnerChartAt (cfProc s) s y).1 (negInv z)) := by
      rw [setOf_mem_dom_cfChart hz]
      funext y
      by_cases hy : y ∈ {y | negInv z ∈ (Chart.loewnerChartAt (cfProc s) s y).dom}
      · rw [indicator_of_mem hy, Function.comp_apply, indicator_of_mem hy, cfChart_fst_eq_loewnerChartAt]
      · rw [indicator_of_notMem hy, Function.comp_apply, indicator_of_notMem hy]
        simp [negInv]
    rw [e]
    exact measurable_negInv.comp h
  · rw [setOf_mem_dom_cfChart_of_notMem hz, indicator_empty]
    exact measurable_const

/-- **The lift of the chart is known from the stopped history** (on its domain). -/
theorem measurable_indicator_lift_cfChart (z : ℂ) :
    Measurable[stopSigma s]
      ({y : HistorySpace 0 0 | z ∈ (cfChart s y).dom}.indicator fun y => (cfChart s y).2.2 z) := by
  classical
  by_cases hz : z ∈ H
  · set D := {y : HistorySpace 0 0 | negInv z ∈ (Chart.loewnerChartAt (cfProc s) s y).dom} with hD
    have hDm : MeasurableSet[stopSigma s] D :=
      Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := stopFilt s) adapted_cfProc continuous_cfProc
        cfProc_zero _ _
    have hf := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := stopFilt s) adapted_cfProc continuous_cfProc
      cfProc_zero s (negInv z)
    have hl := Chart.measurable_indicator_lift_loewnerChartAt (𝓖 := stopFilt s) adapted_cfProc continuous_cfProc
      cfProc_zero s (negInv z)
    set F : ℂ → ℝ := fun v => (-2 * log v).im with hF
    have hFm : Measurable F := (continuous_im.measurable.comp (measurable_const.mul measurable_log))
    have e : ({y : HistorySpace 0 0 | z ∈ (cfChart s y).dom}.indicator fun y => (cfChart s y).2.2 z) =
        D.indicator fun y => F (D.indicator (fun y => (Chart.loewnerChartAt (cfProc s) s y).1 (negInv z)) y) +
          D.indicator (fun y => (Chart.loewnerChartAt (cfProc s) s y).2.2 (negInv z)) y + (-2 * log z).im := by
      rw [setOf_mem_dom_cfChart hz]
      refine indicator_congr fun y hy => ?_
      rw [indicator_of_mem hy, indicator_of_mem hy, cfChart_lift_eq_loewnerChartAt]
    rw [e]
    exact (((hFm.comp hf).add hl).add_const _).indicator hDm
  · rw [setOf_mem_dom_cfChart_of_notMem hz, indicator_empty]
    exact measurable_const

end Meas

end Word49

end InteractingSLE.Sec5.CrossCond
