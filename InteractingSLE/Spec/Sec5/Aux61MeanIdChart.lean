/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61RestartBdry
import InteractingSLE.Spec.Sec5.Aux61ChLocRestart

/-!
# The glued instantiation: the restart chart's lift is harmonic, and the chart is measurable for the marks

Packet PROVE-AUX61-MEAN, the two small items of the glued instantiation (`planning/handoffs/PROVE-AUX61-CHARTLOC.md`,
"What remains" (I)/(II)): `Aux61ChLoc.hasFibreLocalCover_of_restart_marked` needs

* `hlift`: the lift of the restart chart `c i x` is harmonic on its domain. R1's chart
  (`Aux61Restart.HasOriginalTargetRestartChart`) has the lift `Im physicalRestartLog (stripTargetHull D)` on its domain
  `D` (the selected retained component); that is the imaginary part of a holomorphic logarithm of the derivative of
  `mapOut ∘ stripRightRetarget` (`Aux61Restart.isDerivLog_physicalRestartLog`), once `stripTargetHull D` is a hull,
  i.e. once `D` is open, simply connected, in `ℍ` and contains a collar of the original target `1`
  (`Aux61Restart.isHPHull_stripTargetHull`). The collar follows from `1 ∈ closure D` and the target's protection
  (`Aux61Restart.exists_original_right_target_component_collar`). Results: **`harmonicOnNhd_im_physicalRestartLog`**,
  **`harmonicOnNhd_lift_of_restartComponent`**, and for the chart output itself
  **`HasOriginalTargetRestartChartH`** with **`hasOriginalTargetRestartChartH_of_protection`** (R1's chart with the
  harmonic-lift clause added, under the hypotheses of `has_original_target_restart_chart_of_protection`).
* `hEℋ`, `hcℋ`: the restart event and chart are measurable for the marks `ℋ`. R1's charts are built over measurable
  clearance pieces (subtypes); **`extendChart`** extends a chart family from a measurable event `E` (identity chart off
  `E`), and **`IsMeasChart.extendChart`** shows it is `IsMeasChart` for any σ-algebra in which `E` is measurable and the
  chart on `E` is measurable for the induced σ-algebra (so for the marks, when R1's construction is run with the marks
  as the ambient σ-algebra: its measurability hypotheses are the history's). **`isMeasChart_of_clauses`** reads
  `IsMeasChart` off R1's three measurability clauses.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61MeanId

open Aux61Restart
open Aux61FibData (IsMeasChart)

/-! ### The lift of R1's restart chart is harmonic -/

/-- **The imaginary part of the inherited physical logarithm is harmonic** on a retained domain `D` that is open, simply
connected, contained in `ℍ` and contains a collar of the original target `1`. -/
theorem harmonicOnNhd_im_physicalRestartLog {D : Set ℂ} (hDo : IsOpen D) (hDs : IsSimplyConnected D) (hDH : D ⊆ H)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D) :
    InnerProductSpace.HarmonicOnNhd (fun z => (physicalRestartLog (stripTargetHull D) z).im) D := by
  have hB := isHPHull_stripTargetHull hDo hDs hDH htarget
  have hmaps : MapsTo stripRightRetarget D (H \ stripTargetHull D) := fun z hz => by
    rw [H_diff_stripTargetHull hDH]
    exact mem_image_of_mem _ hz
  have hL := (isDerivLog_physicalRestartLog hDo hB hDH hmaps).1
  intro z hz
  exact (hL.analyticAt (hDo.mem_nhds hz)).harmonicAt_im

/-- A function agreeing on an open set with a harmonic function is harmonic there. -/
theorem harmonicOnNhd_of_eqOn {D : Set ℂ} (hDo : IsOpen D) {f g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g D) (hfg : EqOn f g D) : InnerProductSpace.HarmonicOnNhd f D := by
  intro z hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 (hg z hz)
  filter_upwards [hDo.mem_nhds hz] with w hw
  exact (hfg hw).symm

/-- **The lift of a restart chart of a retained component is harmonic** (deterministic form): the component of
`ℍ ∖ (K ∪ η[0, r])` selected by `b` is open, simply connected and in `ℍ` (`historyComponent_properties`), it has `1` in
its closure while `1 ∉ closure K` (so it contains a collar of `1`), and the chart's lift is
`Im physicalRestartLog (stripTargetHull D)` on its domain `D`. -/
theorem harmonicOnNhd_lift_of_restartComponent {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b : ℂ}
    (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0) (hH : MapsTo η (Ioc 0 r) H) (hK : (1 : ℂ) ∉ closure K)
    (hmark : (1 : ℂ) ∈ closure (restartComponent K η r b)) (hDo : IsOpen (restartComponent K η r b))
    (hDs : IsSimplyConnected (restartComponent K η r b)) (hDH : restartComponent K η r b ⊆ H)
    {c : Chart} (hdom : (c.dom : Set ℂ) = restartComponent K η r b)
    (hlift : ∀ z ∈ restartComponent K η r b,
      c.2.2 z = (physicalRestartLog (stripTargetHull (restartComponent K η r b)) z).im) :
    InnerProductSpace.HarmonicOnNhd c.2.2 c.dom := by
  rw [hdom]
  exact harmonicOnNhd_of_eqOn hDo (harmonicOnNhd_im_physicalRestartLog hDo hDs hDH
    (exists_original_right_target_component_collar hc h0 hH hK hmark)) hlift

/-- **R1's restart chart with the harmonic-lift clause**: `HasOriginalTargetRestartChart` with, in addition, the lift
harmonic on the chart's domain (the input `hlift` of `Aux61ChLoc.hasFibreLocalCover_of_restart_marked`). -/
def HasOriginalTargetRestartChartH {Ω : Type*} [MeasurableSpace Ω]
    (s r : ℝ≥0) (q : ℚ) (Y : Ω → LawUnique.HistorySpace 0 0) (η : Ω → ℝ → ℂ)
    (U : ℝ≥0 → Ω → ℝ) (e : ℕ → ℂ) : Prop :=
  ∃ N : Ω → ℕ, Measurable N ∧
    (∀ ω, e (N ω) ∈ retainedDomain (historyHull s Y ω) (η ω) q) ∧
    let D := historyComponent s q Y η (fun ω => e (N ω))
    (∀ ω, (1 : ℂ) ∈ closure (D ω)) ∧
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = D ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (D ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω z, z ∈ D ω →
        (c ω).2.2 z = (physicalRestartLog (stripTargetHull (D ω)) z).im) ∧
      (∀ ω, Tendsto ((c ω).1 ∘ (ownHistoryChart U r ω).2.1) (𝓝[H] 0) (𝓝 0) ∧
        Tendsto (fun w : ℂ => ‖(c ω).1 (w + 1)‖) (𝓝[H] 0) atTop) ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)

/-- **R1's restart chart has a harmonic lift**: under the hypotheses of
`Aux61Restart.has_original_target_restart_chart_of_protection` (R1), the chart exists with the harmonic-lift clause. -/
theorem hasOriginalTargetRestartChartH_of_protection
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    (hrq : (r : ℝ) = q) (hq : 0 < (q : ℝ)) {Y : Ω → LawUnique.HistorySpace 0 0}
    (hY : Measurable fun ω => GlueCond.cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hi : ∀ ω, InjOn (η ω) (Icc (0 : ℝ) q))
    (hH : ∀ ω, MapsTo (η ω) (Ioc (0 : ℝ) q) H)
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    (hclear : ∀ ω, 0 < infDist (η ω q) (historyHull s Y ω))
    (hprotected : ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω))
    (hincident : ∀ ω, ∃ b : ℂ,
      (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
      ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈
        restartComponent (historyHull s Y ω) (η ω) q b)
    {e : ℕ → ℂ} (he : DenseRange e) :
    HasOriginalTargetRestartChartH s r q Y η U e := by
  obtain ⟨N, hNm, hb, hmark, c, hc, hdom, hbij, hdm, hfm, hlm, hlc, hphase, hlimits⟩ :=
    has_original_target_restart_chart_of_protection hrq hq hY hUc hU0 hUm hη hi hH hm hclear hprotected hincident he
  have hprops := historyComponent_properties hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) (fun ω => (hη ω).1) hm hNm hb
  refine ⟨N, hNm, hb, hmark, c, hc, hdom, hbij, hdm, hfm, hlm, hlc, hphase, hlimits, fun ω => ?_⟩
  obtain ⟨hDo, -, hDs, hDH⟩ := hprops.1 ω
  exact harmonicOnNhd_lift_of_restartComponent ((hη ω).2.1.mono Icc_subset_Ici_self) (hη ω).1 (hH ω)
    (hprotected ω) (hmark ω) hDo hDs hDH (hdom ω) (hphase ω)

/-! ### Measurability of the chart for the marks -/

section Meas

variable {X : Type*}

/-- R1's three measurability clauses are exactly `IsMeasChart` (for whatever σ-algebra they are stated in). -/
theorem isMeasChart_of_clauses [MeasurableSpace X] {c : X → Chart} (hdm : ∀ z, MeasurableSet {x | z ∈ (c x).dom})
    (hfm : ∀ z, Measurable ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hlm : ∀ z, Measurable ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z)) : IsMeasChart c :=
  ⟨hdm, hfm, hlm⟩

open scoped Classical in
/-- **A chart family on an event, extended by the identity chart.** -/
def extendChart (E : Set X) (c : E → Chart) (x : X) : Chart :=
  if hx : x ∈ E then c ⟨x, hx⟩ else Chart.id

theorem extendChart_of_mem {E : Set X} {c : E → Chart} {x : X} (hx : x ∈ E) : extendChart E c x = c ⟨x, hx⟩ := by
  simp only [extendChart, hx, ↓reduceDIte]

theorem extendChart_of_notMem {E : Set X} {c : E → Chart} {x : X} (hx : x ∉ E) : extendChart E c x = Chart.id := by
  simp only [extendChart, hx, ↓reduceDIte]

theorem isConformal_extendChart {E : Set X} {c : E → Chart} (hc : ∀ x, (c x).IsConformal) (x : X) :
    (extendChart E c x).IsConformal := by
  by_cases hx : x ∈ E
  · rw [extendChart_of_mem hx]; exact hc _
  · rw [extendChart_of_notMem hx]; exact Chart.isConformal_id

/-- **The extended chart is measurable** for every σ-algebra `m` in which `E` is measurable and for which the chart on
`E` is measurable (for the induced σ-algebra on `E`). Applied with `m` the marks `ℋ`, this is `hcℋ`. -/
theorem IsMeasChart.extendChart {m : MeasurableSpace X} {E : Set X} (hE : MeasurableSet[m] E) {c : E → Chart}
    (hc : @IsMeasChart E (MeasurableSpace.comap Subtype.val m) c) :
    @IsMeasChart X m (extendChart E c) := by
  classical
  have hdom : ∀ z, {x | z ∈ (Aux61MeanId.extendChart E c x).dom} =
      Subtype.val '' {y : E | z ∈ (c y).dom} ∪ (Eᶜ ∩ {_x | z ∈ H}) := by
    intro z; ext x
    by_cases hx : x ∈ E
    · simp only [mem_ofPred_eq, Aux61MeanId.extendChart_of_mem hx, mem_union, mem_image, Subtype.exists,
        exists_and_right, exists_eq_right, hx, exists_true_left, mem_inter_iff, mem_compl_iff, not_true_eq_false,
        false_and, or_false]
    · simp only [mem_ofPred_eq, Aux61MeanId.extendChart_of_notMem hx, mem_union, mem_image, Subtype.exists,
        exists_and_right, exists_eq_right, hx, IsEmpty.exists_iff, mem_inter_iff, mem_compl_iff, not_false_eq_true,
        true_and, false_or]
      rw [← SetLike.mem_coe, Aux61FibData.coe_dom_id]
  have hdm : ∀ z, MeasurableSet {x | z ∈ (Aux61MeanId.extendChart E c x).dom} := fun z => by
    rw [hdom z]
    exact (hE.subtype_image (hc.dom z)).union (hE.compl.inter (MeasurableSet.const _))
  -- an indicator over the extended domain, as a `dite` on `E`
  have hind : ∀ (z : ℂ) (F : Chart → ℂ → ℂ)
      (_ : Measurable ({y : E | z ∈ (c y).dom}.indicator fun y => F (c y) z)),
      Measurable ({x | z ∈ (Aux61MeanId.extendChart E c x).dom}.indicator fun x =>
        F (Aux61MeanId.extendChart E c x) z) := by
    intro z F hF
    have e : ({x | z ∈ (Aux61MeanId.extendChart E c x).dom}.indicator fun x =>
        F (Aux61MeanId.extendChart E c x) z) = fun x =>
        if hx : x ∈ E then ({y : E | z ∈ (c y).dom}.indicator fun y => F (c y) z) ⟨x, hx⟩
        else ({x : X | z ∈ H}.indicator fun _ => F Chart.id z) x := by
      funext x
      by_cases hx : x ∈ E
      · simp only [hx, ↓reduceDIte, indicator, mem_ofPred_eq, Aux61MeanId.extendChart_of_mem hx]
      · simp only [hx, ↓reduceDIte, indicator, mem_ofPred_eq, Aux61MeanId.extendChart_of_notMem hx]
        rw [← SetLike.mem_coe, Aux61FibData.coe_dom_id]
    rw [e]
    exact Measurable.dite hF ((measurable_const.indicator (MeasurableSet.const _)).comp measurable_subtype_coe) hE
  have hindR : ∀ (z : ℂ) (F : Chart → ℂ → ℝ)
      (_ : Measurable ({y : E | z ∈ (c y).dom}.indicator fun y => F (c y) z)),
      Measurable ({x | z ∈ (Aux61MeanId.extendChart E c x).dom}.indicator fun x =>
        F (Aux61MeanId.extendChart E c x) z) := by
    intro z F hF
    have e : ({x | z ∈ (Aux61MeanId.extendChart E c x).dom}.indicator fun x =>
        F (Aux61MeanId.extendChart E c x) z) = fun x =>
        if hx : x ∈ E then ({y : E | z ∈ (c y).dom}.indicator fun y => F (c y) z) ⟨x, hx⟩
        else ({x : X | z ∈ H}.indicator fun _ => F Chart.id z) x := by
      funext x
      by_cases hx : x ∈ E
      · simp only [hx, ↓reduceDIte, indicator, mem_ofPred_eq, Aux61MeanId.extendChart_of_mem hx]
      · simp only [hx, ↓reduceDIte, indicator, mem_ofPred_eq, Aux61MeanId.extendChart_of_notMem hx]
        rw [← SetLike.mem_coe, Aux61FibData.coe_dom_id]
    rw [e]
    exact Measurable.dite hF ((measurable_const.indicator (MeasurableSet.const _)).comp measurable_subtype_coe) hE
  exact ⟨hdm, fun z => hind z (fun c₀ w => c₀.1 w) (hc.fwd z), fun z => hindR z (fun c₀ w => c₀.2.2 w) (hc.lift z)⟩

end Meas

end InteractingSLE.Sec5.Aux61MeanId
