/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKillFilt
import InteractingSLE.Spec.Sec5.CrossRestartKernelQMean

/-!
# Lemma 4.7 in the chart `Q`: the flow chart of the field, read from the stopped flow history

Packet PROVE-CFRESTART5, item D2 (chart part). The field `h` lives in the chart `Q`; the counterflow's killed image word
(PROVE-CFRESTART4, `Kill47`) lives in the image chart of `Ψ = revChart Wf s = R ∘ f_s ∘ R`. The chart of the field in
the image coordinate is `Ψ ∘ R = R ∘ f_s` (`R z = −1/z`): the identity chart, the Loewner stage of the flow driver
up to the flow time `s`, then the infinity-source chart `R`. Its domain is `ℍ ∖ K_s` (the flow hull in the chart `Q`),
its lift is `Im(−2 log f_s + log f_s′)`.

* `regDrvH`, `fChartH`: the regularized driver of a history and the chart built from it; `fChart W VL VR ζ s p` reads
  it from the flow history stopped at `s` (`flowStop`), which is time-`0` information of the image word's filtration;
* `isConformal_fChartH`, `coe_dom_fChartH`, `mem_dom_fChartH_iff`, `continuousOn_lift_fChartH`;
* measurability of the domain events, forward map and lift in the history (`measurableSet_mem_dom_fChartH`,
  `measurable_indicator_fwd_fChartH`, `measurable_indicator_lift_fChartH`,
  `measurableSet_closedBall_subset_dom_fChartH`) and, for any σ-algebra in which `flowStop` is measurable (the raw
  image filtration: `measurable_flowStop_qRaw`), of the glued chart (`*_fChart_of`);
* on good samples: `fChart_fst_eq` (`(fChart p).1 z = Ψ(R z)`), `fChart_lift_eq` (the lift is
  `Im L_Ψ(R z) − 2 arg z`, the lift of PROVE-CFRESTART3's mean formula).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q

namespace Kill47

/-! ### The regularized driver of a history and its chart -/

section Chart

variable {nL nR : ℕ}

/-- **The regularized driver of a history**, recentred at `0`. -/
def regDrvH (y : HistorySpace nL nR) (r : ℝ) : ℝ :=
  Ito.rpath (Sec4.regPath y) r - Ito.rpath (Sec4.regPath y) 0

theorem continuous_regDrvH (y : HistorySpace nL nR) : Continuous (regDrvH y) :=
  (Sec4.continuous_rpath_regPath _).sub continuous_const

theorem regDrvH_zero (y : HistorySpace nL nR) : regDrvH y 0 = 0 := sub_self _

theorem regDrvH_toNNReal (y : HistorySpace nL nR) (r : ℝ) : regDrvH y ((r.toNNReal : ℝ≥0) : ℝ) = regDrvH y r := by
  simp only [regDrvH, Ito.rpath, Real.toNNReal_coe]

theorem measurable_regDrvH_apply (r : ℝ) : Measurable fun y : HistorySpace nL nR => regDrvH y r :=
  (Sec4.measurable_regPath_apply r.toNNReal).sub (Sec4.measurable_regPath_apply (0 : ℝ).toNNReal)

/-- **The chart `R ∘ f_s` of the field**, read from a (stopped) flow history: the identity chart, the Loewner stage of
the regularized driver up to `s`, then the infinity-source chart `R`. -/
def fChartH (s : ℝ≥0) (y : HistorySpace nL nR) : Chart :=
  (Chart.id.loewner (regDrvH y) s).trans infinitySourceChart

variable {s : ℝ≥0}

theorem fChartH_fst (y : HistorySpace nL nR) (z : ℂ) :
    (fChartH s y).1 z = negInv (fwdMap (regDrvH y) s z) := rfl

theorem fChartH_inv (y : HistorySpace nL nR) (w : ℂ) :
    (fChartH s y).2.1 w = fwdMapInv (regDrvH y) s (negInv w) := rfl

theorem fChartH_lift (y : HistorySpace nL nR) (z : ℂ) :
    (fChartH s y).2.2 z = (-2 * log (fwdMap (regDrvH y) s z)).im + (logDerivFwd (regDrvH y) s z).im := by
  simp only [fChartH, Chart.trans_lift, Chart.loewner, Chart.id, infinitySourceChart, add_zero]

theorem isConformal_fChartH (y : HistorySpace nL nR) : (fChartH s y).IsConformal :=
  (Chart.isConformal_id.loewner (continuous_regDrvH y) (regDrvH_zero y) s.coe_nonneg).trans
    Chart.isConformal_infinitySourceChart

theorem negInv_image_H : negInv '' H = H := by
  refine Subset.antisymm (fun _ ⟨w, hw, e⟩ => e ▸ WangWu.negInv_mem_H hw) fun z hz =>
    ⟨negInv z, WangWu.negInv_mem_H hz, WangWu.negInv_negInv z⟩

/-- The domain of the chart is `ℍ ∖ K_s`. -/
theorem coe_dom_fChartH (y : HistorySpace nL nR) :
    ((fChartH s y).dom : Set ℂ) = H \ fwdHull (regDrvH y) s := by
  rw [(isConformal_fChartH y).coe_dom]
  change (fun w => fwdMapInv (regDrvH y) s (negInv w)) '' H = _
  rw [show (fun w => fwdMapInv (regDrvH y) s (negInv w)) = fwdMapInv (regDrvH y) s ∘ negInv from rfl,
    image_comp, negInv_image_H, QuantumZipper.RS.image_fwdMapInv_H (continuous_regDrvH y) (regDrvH_zero y)
      s.coe_nonneg]

theorem mem_dom_fChartH_iff (y : HistorySpace nL nR) {z : ℂ} :
    z ∈ (fChartH s y).dom ↔ z ∈ H ∧ z ∉ fwdHull (regDrvH y) s := by
  rw [← SetLike.mem_coe, coe_dom_fChartH]
  rfl

/-- **The lift of the chart is continuous on its domain.** -/
theorem continuousOn_lift_fChartH (y : HistorySpace nL nR) :
    ContinuousOn (fChartH s y).2.2 (fChartH s y).dom := by
  have hw := continuous_regDrvH y
  have hs := s.coe_nonneg
  rw [coe_dom_fChartH]
  have hf : ContinuousOn (fwdMap (regDrvH y) s) (H \ fwdHull (regDrvH y) s) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn
  have hlog : ContinuousOn (fun z => log (fwdMap (regDrvH y) s z)) (H \ fwdHull (regDrvH y) s) := by
    intro z hz
    have hH : fwdMap (regDrvH y) s z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hz
    exact (continuousAt_clog (Complex.mem_slitPlane_iff.2 (Or.inr hH.ne'))).comp_continuousWithinAt (hf z hz)
  have hL : ContinuousOn (logDerivFwd (regDrvH y) s) (H \ fwdHull (regDrvH y) s) :=
    (isDerivLog_fwdMap hw hs).1.continuousOn
  have hc : ContinuousOn (fun z => (-2 * log (fwdMap (regDrvH y) s z)).im + (logDerivFwd (regDrvH y) s z).im)
      (H \ fwdHull (regDrvH y) s) :=
    (continuous_im.comp_continuousOn ((continuousOn_const (c := (-2 : ℂ))).mul hlog)).add
      (continuous_im.comp_continuousOn hL)
  exact hc.congr fun z _ => fChartH_lift y z

end Chart

/-! ### Measurability in the history -/

section Meas

variable {nL nR : ℕ} {s : ℝ≥0}

/-- The regularized driver as a process on histories. -/
def regProc : ℝ≥0 → HistorySpace nL nR → ℝ := fun t y => regDrvH y t

/-- The constant filtration at the σ-algebra of histories. -/
abbrev histFilt : Filtration ℝ≥0 (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
  Filtration.const ℝ≥0 inferInstance le_rfl

theorem adapted_regProc : Adapted (histFilt (nL := nL) (nR := nR)) regProc := fun t =>
  measurable_regDrvH_apply (t : ℝ)

theorem continuous_regProc (y : HistorySpace nL nR) : Continuous fun t => regProc t y :=
  (continuous_regDrvH y).comp NNReal.continuous_coe

theorem regProc_zero (y : HistorySpace nL nR) : regProc 0 y = 0 := regDrvH_zero y

theorem rpath_regProc (y : HistorySpace nL nR) : Ito.rpath (regProc · y) = regDrvH y := by
  funext r
  exact regDrvH_toNNReal y r

theorem loewnerChartAt_regProc (y : HistorySpace nL nR) :
    Chart.loewnerChartAt regProc s y = Chart.id.loewner (regDrvH y) s := by
  rw [Chart.loewnerChartAt, rpath_regProc]

theorem setOf_mem_dom_fChartH (z : ℂ) :
    {y : HistorySpace nL nR | z ∈ (fChartH s y).dom} = {y | z ∈ (Chart.loewnerChartAt regProc s y).dom} := by
  ext y
  rw [mem_ofPred_eq, mem_ofPred_eq, mem_dom_fChartH_iff, loewnerChartAt_regProc, ← SetLike.mem_coe,
    (Chart.isConformal_id.loewner (continuous_regDrvH y) (regDrvH_zero y) s.coe_nonneg).coe_dom]
  change _ ↔ z ∈ fwdMapInv (regDrvH y) s '' H
  rw [QuantumZipper.RS.image_fwdMapInv_H (continuous_regDrvH y) (regDrvH_zero y) s.coe_nonneg]
  rfl

/-- **The domain events of the chart are measurable in the history.** -/
theorem measurableSet_mem_dom_fChartH (z : ℂ) :
    MeasurableSet {y : HistorySpace nL nR | z ∈ (fChartH s y).dom} := by
  rw [setOf_mem_dom_fChartH]
  exact Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := histFilt) adapted_regProc continuous_regProc
    regProc_zero _ _

/-- **The forward map of the chart is measurable in the history** (on its domain). -/
theorem measurable_indicator_fwd_fChartH (z : ℂ) :
    Measurable ({y : HistorySpace nL nR | z ∈ (fChartH s y).dom}.indicator fun y => (fChartH s y).1 z) := by
  classical
  have h := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := histFilt (nL := nL) (nR := nR)) adapted_regProc
    continuous_regProc regProc_zero s z
  have e : ({y : HistorySpace nL nR | z ∈ (fChartH s y).dom}.indicator fun y => (fChartH s y).1 z) =
      negInv ∘ ({y | z ∈ (Chart.loewnerChartAt regProc s y).dom}.indicator
        fun y => (Chart.loewnerChartAt regProc s y).1 z) := by
    rw [setOf_mem_dom_fChartH]
    funext y
    by_cases hy : y ∈ {y : HistorySpace nL nR | z ∈ (Chart.loewnerChartAt regProc s y).dom}
    · rw [indicator_of_mem hy, Function.comp_apply, indicator_of_mem hy, fChartH_fst, loewnerChartAt_regProc]
      rfl
    · rw [indicator_of_notMem hy, Function.comp_apply, indicator_of_notMem hy]
      simp [negInv]
  rw [e]
  exact measurable_negInv.comp h

/-- **The lift of the chart is measurable in the history** (on its domain). -/
theorem measurable_indicator_lift_fChartH (z : ℂ) :
    Measurable ({y : HistorySpace nL nR | z ∈ (fChartH s y).dom}.indicator fun y => (fChartH s y).2.2 z) := by
  classical
  set D := {y : HistorySpace nL nR | z ∈ (Chart.loewnerChartAt regProc s y).dom} with hD
  have hDm : MeasurableSet D :=
    Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := histFilt) adapted_regProc continuous_regProc regProc_zero _ _
  have hf := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := histFilt (nL := nL) (nR := nR)) adapted_regProc
    continuous_regProc regProc_zero s z
  have hl := Chart.measurable_indicator_lift_loewnerChartAt (𝓖 := histFilt (nL := nL) (nR := nR)) adapted_regProc
    continuous_regProc regProc_zero s z
  set F : ℂ → ℝ := fun v => (-2 * log v).im with hF
  have hFm : Measurable F := continuous_im.measurable.comp (measurable_const.mul measurable_log)
  have e : ({y : HistorySpace nL nR | z ∈ (fChartH s y).dom}.indicator fun y => (fChartH s y).2.2 z) =
      D.indicator fun y => F (D.indicator (fun y => (Chart.loewnerChartAt regProc s y).1 z) y) +
        D.indicator (fun y => (Chart.loewnerChartAt regProc s y).2.2 z) y := by
    rw [setOf_mem_dom_fChartH]
    refine indicator_congr fun y hy => ?_
    rw [indicator_of_mem hy, indicator_of_mem hy, fChartH_lift, loewnerChartAt_regProc]
    simp only [hF, Chart.loewner, Chart.id, add_zero]
  rw [e]
  exact ((hFm.comp hf).add hl).indicator hDm

/-- **The closed-ball domain events of the chart are measurable in the history.** -/
theorem measurableSet_closedBall_subset_dom_fChartH (z : ℂ) (ρ : ℝ) :
    MeasurableSet {y : HistorySpace nL nR | closedBall z ρ ⊆ ((fChartH s y).dom : Set ℂ)} := by
  classical
  have hc : ∀ y : HistorySpace nL nR, ContinuousOn (fun t => regProc t y)
      {t : ℝ≥0 | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) y} := fun y => (continuous_regProc y).continuousOn
  have h := Sec7.Lemma71M.measurableSet_lt_subset_H_diff_fwdHull (Chart.adaptedBefore_top adapted_regProc) hc s
    (isCompact_closedBall z ρ)
  have e : {y : HistorySpace nL nR | closedBall z ρ ⊆ ((fChartH s y).dom : Set ℂ)} =
      {y | (s : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) y ∧ closedBall z ρ ⊆
        H \ fwdHull (fun t : ℝ => regProc t.toNNReal y) (s : ℝ)} := by
    ext y
    have hrp : (fun t : ℝ => regProc t.toNNReal y) = regDrvH y := rpath_regProc y
    simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, hrp, coe_dom_fChartH]
  rw [e]
  exact h

end Meas

/-! ### The chart of a glued sample, read from the stopped flow history -/

section Glue

variable {Ω : Type*} {nL nR mL mR : ℕ}

/-- **The chart of the field in the image coordinate** of a glued sample: `R ∘ f_s` for the flow driver regularized
from the flow history stopped at `s`. -/
def fChart (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : Chart :=
  fChartH s (flowStop W VL VR ζ s p)

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0}
  {p : Ω × HistorySpace 0 0}

theorem fReg_eq_regDrvH : fReg W VL VR ζ s p = regDrvH (flowStop W VL VR ζ s p) := rfl

theorem isConformal_fChart (p : Ω × HistorySpace 0 0) : (fChart W VL VR ζ s p).IsConformal :=
  isConformal_fChartH _

theorem continuousOn_lift_fChart (p : Ω × HistorySpace 0 0) :
    ContinuousOn (fChart W VL VR ζ s p).2.2 (fChart W VL VR ζ s p).dom :=
  continuousOn_lift_fChartH _

theorem coe_dom_fChart (p : Ω × HistorySpace 0 0) :
    ((fChart W VL VR ζ s p).dom : Set ℂ) = H \ fwdHull (fReg W VL VR ζ s p) s :=
  coe_dom_fChartH _

/-- On a good sample the chart's forward map is `Ψ ∘ R` with the flow driver. -/
theorem fChart_fst_eq (hg : IsGood47 W VL VR ζ p) (z : ℂ) :
    (fChart W VL VR ζ s p).1 z = revChart (fDrv W p) s (negInv z) := by
  rw [fChart, fChartH_fst, ← fReg_eq_regDrvH, revChart, WangWu.negInv_negInv,
    Ito.fwdMap_congr_of_eqOn (eqOn_fReg hg)]

/-- On a good sample the chart's domain is `ℍ ∖ K_s` with the flow driver. -/
theorem coe_dom_fChart_of_good (hg : IsGood47 W VL VR ζ p) :
    ((fChart W VL VR ζ s p).dom : Set ℂ) = H \ fwdHull (fDrv W p) s := by
  rw [coe_dom_fChart, YuanCorollary13.fwdHull_eq_of_eqOn_Icc continuous_fReg (continuous_fDrv hg) s.coe_nonneg
    (fun r hr => eqOn_fReg hg hr)]

/-- On a good sample the chart's inverse map is `R ∘ Ψ⁻¹` on `ℍ`. -/
theorem fChart_inv_eq (hg : IsGood47 W VL VR ζ p) {w : ℂ} (hw : w ∈ H) :
    (fChart W VL VR ζ s p).2.1 w = fwdMapInv (fDrv W p) s (negInv w) := by
  rw [fChart, fChartH_inv, ← fReg_eq_regDrvH]
  exact LP.fwdMapInv_eq_of_eqOn_Icc continuous_fReg (continuous_fDrv hg) fReg_zero (fDrv_zero hg) s.coe_nonneg
    (fun r hr => eqOn_fReg hg hr) (WangWu.negInv_mem_H hw)

/-- **On a good sample the chart's lift is `Im L_Ψ(R z) − 2 arg z`** (`z ∈ ℍ`), the lift of PROVE-CFRESTART3's mean
formula (`arg(−1/z) = π − arg z`). -/
theorem fChart_lift_eq (hg : IsGood47 W VL VR ζ p) {z : ℂ} (hz : z ∈ H) :
    (fChart W VL VR ζ s p).2.2 z = (GlueImg.logDerivPsi (fDrv W p) s (negInv z)).im - 2 * arg z := by
  rw [fChart, fChartH_lift, ← fReg_eq_regDrvH, Ito.fwdMap_congr_of_eqOn (eqOn_fReg hg),
    Ito.logDerivFwd_congr_of_eqOn (eqOn_fReg hg) s.coe_nonneg le_rfl]
  have ha := GlueImg.arg_negInv_of_mem_H hz
  simp only [GlueImg.logDerivPsi, WangWu.negInv_negInv, add_im, mul_im, neg_re, neg_im, re_ofNat, im_ofNat,
    log_im, ofReal_re, ofReal_im, I_re, I_im, ha, mul_re]
  ring

end Glue

/-! ### Measurability through the stopped flow history -/

section GlueMeas

variable {Ω : Type*} {nL nR mL mR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)} {xL : Fin mL → ℝ}
  {xR : Fin mR → ℝ}

/-- The flow history stopped at `s` is known at every time of the raw image filtration. -/
theorem measurable_flowStop_qRaw [MeasurableSpace Ω] (hX : IsMeasurableKilledDriving W VL VR ζ) (r : ℝ≥0) :
    Measurable[qRaw xL xR W VL VR ζ s E r] (flowStop W VL VR ζ s) := fun B hB =>
  measurableSet_qRaw_of_gen ⟨0, zero_le, Or.inr (Or.inr (Or.inr ⟨B, hB, rfl⟩))⟩ ((measurable_stopFlow hX s) hB)

variable {𝓜 : MeasurableSpace (Ω × HistorySpace 0 0)}

theorem measurableSet_mem_dom_fChart_of (hY : Measurable[𝓜] (flowStop W VL VR ζ s)) (z : ℂ) :
    MeasurableSet[𝓜] {p | z ∈ (fChart W VL VR ζ s p).dom} :=
  hY (measurableSet_mem_dom_fChartH (s := s) z)

theorem measurable_indicator_fwd_fChart_of (hY : Measurable[𝓜] (flowStop W VL VR ζ s)) (z : ℂ) :
    Measurable[𝓜] ({p | z ∈ (fChart W VL VR ζ s p).dom}.indicator fun p => (fChart W VL VR ζ s p).1 z) :=
  (measurable_indicator_fwd_fChartH (s := s) z).comp hY

theorem measurable_indicator_lift_fChart_of (hY : Measurable[𝓜] (flowStop W VL VR ζ s)) (z : ℂ) :
    Measurable[𝓜] ({p | z ∈ (fChart W VL VR ζ s p).dom}.indicator fun p => (fChart W VL VR ζ s p).2.2 z) :=
  (measurable_indicator_lift_fChartH (s := s) z).comp hY

theorem measurableSet_closedBall_subset_dom_fChart_of (hY : Measurable[𝓜] (flowStop W VL VR ζ s)) (z : ℂ)
    (ρ : ℝ) : MeasurableSet[𝓜] {p | closedBall z ρ ⊆ ((fChart W VL VR ζ s p).dom : Set ℂ)} :=
  hY (measurableSet_closedBall_subset_dom_fChartH (s := s) z ρ)

end GlueMeas

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
