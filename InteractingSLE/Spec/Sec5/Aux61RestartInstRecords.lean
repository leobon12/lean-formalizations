import InteractingSLE.Spec.Sec5.Aux61RestartInstChart

/-!
# Access charts read from the stopped records

Packet PROVE-AUX61-R1. The current access uses the original own Loewner
chart. The original right-target access uses the counterflow inverse chart
at `junR`, translated to zero. Its collar and its identification as the
original target remain explicit geometric premises in the assembly theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu WangWu.ImgWord LawUnique GlueCond CrossCond.Word49
open Sec7.Lemma71E

/-- The current-access chart in the original own capacity parameter. -/
abbrev ownHistoryChart {Ω : Type*} (U : ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) : Chart :=
  Chart.loewnerChartAtTime U (fun _ => r) ω

/-- The original right-target junction, read from the stopped counterflow. -/
def historyRightJunction {Ω : Type*} (s : ℝ≥0) (Y : Ω → HistorySpace 0 0) (ω : Ω) : ℝ :=
  junR (cfDrv0 s (Y ω)) s

/-- The target access in counterflow coordinates, translated to zero. -/
def historyTargetMap {Ω : Type*} (s : ℝ≥0) (Y : Ω → HistorySpace 0 0)
    (ω : Ω) (z : ℂ) : ℂ := (cfChart s (Y ω)).1 z - (historyRightJunction s Y ω : ℂ)

/-- The same original-target access in physical coordinates. -/
def historyTargetInv {Ω : Type*} (s : ℝ≥0) (Y : Ω → HistorySpace 0 0)
    (ω : Ω) (w : ℂ) : ℂ := (cfChart s (Y ω)).2.1 (w + (historyRightJunction s Y ω : ℂ))

/-- The original junction is measurable in the stopped record itself. -/
theorem measurable_historyRightJunction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {s : ℝ≥0} {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω)) : Measurable (historyRightJunction s Y) := by
  have hm : ∀ t : ℝ, Measurable fun ω => cfDrv0 s (Y ω) t :=
    fun t => measurable_comp_of_stopSigma (measurable_cfDrv0_apply s t) hY
  have h := Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable
    (𝓕 := Chart.constFiltration (le_refl mΩ))
    (W := fun t ω => -cfDrv0 s (Y ω) t) (fun t => (hm t).neg)
    (fun ω => ((continuous_cfDrv0 s (Y ω)).comp NNReal.continuous_coe).neg)
    (x := fun _ => (0 : ℝ)) measurable_const s
  have heq : ∀ ω, Bessel.realPath (fun t ω => -cfDrv0 s (Y ω) t) ω =
      fun t => -cfDrv0 s (Y ω) t := by
    intro ω
    funext t
    simp only [Bessel.realPath, cfDrv0_toNNReal]
  simp_rw [heq] at h
  exact measurable_const.div (h.neg.sub (hm s))

/-- Restricting a chart evaluation to a smaller recorded domain preserves
measurability. This is used for both actual history charts. -/
theorem measurable_indicator_restrict_domain
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [Zero β]
    {D E : Ω → Set ℂ} {f : Ω → ℂ → β}
    (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω}) (hDE : ∀ ω, D ω ⊆ E ω)
    (hm : ∀ z, Measurable ({ω | z ∈ E ω}.indicator fun ω => f ω z)) (z : ℂ) :
    Measurable ({ω | z ∈ D ω}.indicator fun ω => f ω z) := by
  classical
  have h := (hm z).indicator (hDm z)
  convert h using 1
  ext ω
  by_cases hz : z ∈ D ω
  · have hωD : ω ∈ {ω | z ∈ D ω} := hz
    have hωE : ω ∈ {ω | z ∈ E ω} := hDE ω hz
    simp only [indicator_of_mem hωD, indicator_of_mem hωE]
  · have hωD : ω ∉ {ω | z ∈ D ω} := hz
    simp only [indicator_of_notMem hωD]

/-- The own chart is measurable from its driver through `r` only. The driver
can have arbitrary continuation after `r`; no future values are required. -/
theorem measurable_indicator_ownHistoryChart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ} {r : ℝ≥0}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t)) (z : ℂ) :
    Measurable ({ω | z ∈ (ownHistoryChart U r ω).dom}.indicator
      fun ω => (ownHistoryChart U r ω).1 z) := by
  exact Chart.measurable_indicator_fwd_loewnerChartAtTime (le_refl mΩ) hUc hU0
    measurable_const (fun t => hUm (min t r) (min_le_right _ _)) z

/-- The translated counterflow target chart retains both inverse identities
and maps the retained component to the half-plane. -/
theorem historyTarget_access_properties
    {Ω : Type*} {s : ℝ≥0} {Y : Ω → HistorySpace 0 0} {D : Ω → Set ℂ}
    (hD : ∀ ω, D ω ⊆ H \ historyHull s Y ω) (ω : Ω) :
    ContinuousOn (historyTargetMap s Y ω) (D ω) ∧
      MapsTo (historyTargetMap s Y ω) (D ω) H ∧
      (∀ w ∈ H, historyTargetMap s Y ω (historyTargetInv s Y ω w) = w) ∧
      (∀ z ∈ D ω, historyTargetInv s Y ω (historyTargetMap s Y ω z) = z) := by
  have hc := isConformal_cfChart (s := s) (Y ω)
  have hsub : D ω ⊆ (cfChart s (Y ω)).dom := by
    rw [coe_dom_cfChart]
    exact hD ω
  have hreal (z : ℂ) (a : ℝ) : z - (a : ℂ) ∈ H ↔ z ∈ H := by
    change 0 < (z - (a : ℂ)).im ↔ 0 < z.im
    rw [sub_im, ofReal_im, sub_zero]
  refine ⟨(hc.differentiableOn_fwd.continuousOn.mono hsub).sub continuousOn_const,
    fun z hz => (hreal _ _).2 (hc.fwd_mem (hsub hz)), ?_, ?_⟩
  · intro w hw
    have hshift : w + (historyRightJunction s Y ω : ℂ) ∈ H := by
      change 0 < (w + (historyRightJunction s Y ω : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using (show 0 < w.im from hw)
    unfold historyTargetMap historyTargetInv
    rw [hc.2.2 _ hshift, add_sub_cancel_right]
  · intro z hz
    unfold historyTargetInv historyTargetMap
    rw [sub_add_cancel, hc.inv_fwd (hsub hz)]

/-- The original-target coordinate is measurable on any recorded subdomain of
the counterflow complement. The junction shift uses the same stopped record. -/
theorem measurable_indicator_historyTargetMap
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω)) {D : Ω → Set ℂ}
    (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω})
    (hD : ∀ ω, D ω ⊆ H \ historyHull s Y ω) (z : ℂ) :
    Measurable ({ω | z ∈ D ω}.indicator fun ω => historyTargetMap s Y ω z) := by
  have hsub : ∀ ω, D ω ⊆ (cfChart s (Y ω)).dom := by
    intro ω
    rw [coe_dom_cfChart]
    exact hD ω
  have hf := measurable_indicator_restrict_domain hDm hsub
    (measurable_indicator_fwd_cfChart_comp hY) z
  have hj := Complex.measurable_ofReal.comp (measurable_historyRightJunction hY)
  have h := (hf.sub hj).indicator (hDm z)
  classical
  convert h using 1
  ext ω
  by_cases hz : z ∈ D ω
  · have hωD : ω ∈ {ω | z ∈ D ω} := hz
    simp only [indicator_of_mem hωD, Pi.sub_apply, Function.comp_apply, historyTargetMap]
  · have hωD : ω ∉ {ω | z ∈ D ω} := hz
    simp only [indicator_of_notMem hωD]

end InteractingSLE.Sec5.Aux61Restart
