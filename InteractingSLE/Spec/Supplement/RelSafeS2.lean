/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS1
import InteractingSLE.Spec.Sec5.CfGivenChart
import InteractingSLE.Spec.Supplement.BW1ChainChart

/-!
# GB6's relative safe law, part 2: the relative chart of a record

Packet PROVE-GB6-RELSAFE2. K2's lines step (`BW1Lines.hasSafeLaw_life_of_lineKernel`) reads a field `h` in a random
chart `c` that is conformal for EVERY sample and measurable in the time-zero σ-algebra. For GB6 the field is the
counterflow-frame field `h′ = R_*h` and the chart is GB6's relative chart `Ψ = R ∘ f_s ∘ R`
(`GW2JointKernel.jointChart`, forward map `relMap`, inverse `relInv`), read from the RECORD of the flow prefix:

* `relChart r = R.trans (CfGiven.cfChart r)` (the inversion followed by the image chart of the record, which is the
  own-component chart of the record driver); conformal for every record, domain `{z | −1/z ∈ dom (cfChart r)}`,
  domain / forward map / lift measurable in the record (`measurableSet_mem_dom_relChart`,
  `measurable_indicator_fwd_relChart`, `measurable_indicator_lift_relChart`), lift continuous and harmonic on the
  domain;
* `relChart_eq_jointChart`: at a record of time `s` it is `jointChart (rdrv r) s`;
* **`ae_eq_chartTransport_relChart`**: almost surely on the interior-tip event, GB6's chart field `Hc` is the
  transport of `h′` through the relative chart of the record with coefficients `1, 2πχ(16/κ), χ(16/κ)`
  (`BW1Chain.chartTransport_jointChart_eq_cfField`: the inversion is an involution whose lift adds `−2π`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.RelSafeS

open Exist.StagedLaw Supp8.GB6 Sec5.CfGiven Theorem14.GW2JointKernel

/-! ### The chart -/

/-- **GB6's relative chart of a record**: the inversion `R(w) = −1/w` followed by the image chart of the record. -/
def relChart (r : RecData) : Chart := infinitySourceChart.trans (cfChart r)

theorem isConformal_relChart (r : RecData) : (relChart r).IsConformal :=
  Chart.isConformal_infinitySourceChart.trans (isConformal_cfChart r)

theorem negInv_involutive : Function.Involutive fun z : ℂ => -z⁻¹ := fun z => by
  simp only [inv_neg, inv_inv, neg_neg]

theorem mem_dom_relChart_iff (r : RecData) (z : ℂ) : z ∈ (relChart r).dom ↔ -z⁻¹ ∈ (cfChart r).dom := by
  rw [← SetLike.mem_coe, (isConformal_relChart r).coe_dom, ← SetLike.mem_coe, (isConformal_cfChart r).coe_dom]
  change z ∈ (infinitySourceChart.trans (cfChart r)).2.1 '' H ↔ _
  rw [Chart.trans_image]
  change z ∈ (fun z : ℂ => -z⁻¹) '' _ ↔ _
  rw [Set.image_eq_preimage_of_inverse negInv_involutive.leftInverse negInv_involutive.rightInverse]
  rfl

theorem setOf_mem_dom_relChart (z : ℂ) :
    {r : RecData | z ∈ (relChart r).dom} = {r : RecData | -z⁻¹ ∈ (cfChart r).dom} := by
  ext r
  exact mem_dom_relChart_iff r z

theorem measurableSet_mem_dom_relChart (z : ℂ) : MeasurableSet {r : RecData | z ∈ (relChart r).dom} := by
  rw [setOf_mem_dom_relChart]
  exact measurableSet_mem_dom_cfChart (-z⁻¹)

theorem measurable_indicator_fwd_relChart (z : ℂ) :
    Measurable ({r : RecData | z ∈ (relChart r).dom}.indicator fun r => (relChart r).1 z) := by
  rw [setOf_mem_dom_relChart]
  exact measurable_indicator_fwd_cfChart (-z⁻¹)

theorem measurable_indicator_lift_relChart (z : ℂ) :
    Measurable ({r : RecData | z ∈ (relChart r).dom}.indicator fun r => (relChart r).2.2 z) := by
  rw [setOf_mem_dom_relChart]
  have e : ({r : RecData | -z⁻¹ ∈ (cfChart r).dom}.indicator fun r => (relChart r).2.2 z) =
      ({r : RecData | -z⁻¹ ∈ (cfChart r).dom}.indicator fun r => (cfChart r).2.2 (-z⁻¹)) +
        {r : RecData | -z⁻¹ ∈ (cfChart r).dom}.indicator fun _ => infinitySourceChart.2.2 z := by
    funext r
    by_cases hr : r ∈ {r : RecData | -z⁻¹ ∈ (cfChart r).dom}
    · simp only [Pi.add_apply, indicator_of_mem hr]
      rfl
    · simp only [Pi.add_apply, indicator_of_notMem hr, add_zero]
  rw [e]
  exact (measurable_indicator_lift_cfChart (-z⁻¹)).add
    (measurable_const.indicator (measurableSet_mem_dom_cfChart (-z⁻¹)))

theorem dom_relChart_subset_H (r : RecData) : ((relChart r).dom : Set ℂ) ⊆ H :=
  (isConformal_relChart r).dom_subset

theorem negInv_mapsTo_dom (r : RecData) :
    MapsTo (fun z : ℂ => -z⁻¹) ((relChart r).dom : Set ℂ) ((cfChart r).dom : Set ℂ) := fun z hz =>
  (mem_dom_relChart_iff r z).1 hz

theorem differentiableOn_negInv : DifferentiableOn ℂ (fun z : ℂ => -z⁻¹) H := fun _ hz =>
  (differentiableAt_inv (ne_zero_of_mem_H hz)).neg.differentiableWithinAt

theorem continuousOn_lift_relChart (r : RecData) : ContinuousOn (relChart r).2.2 (relChart r).dom := by
  have h1 : ContinuousOn (fun z : ℂ => (cfChart r).2.2 (-z⁻¹)) (relChart r).dom :=
    (continuousOn_lift_cfChart r).comp (differentiableOn_negInv.continuousOn.mono (dom_relChart_subset_H r))
      (negInv_mapsTo_dom r)
  have h2 : ContinuousOn infinitySourceChart.2.2 (relChart r).dom :=
    Sec7.StripSysField.continuousOn_infinitySourceChart_lift'.mono (dom_relChart_subset_H r)
  exact h1.add h2

theorem harmonicOnNhd_lift_relChart (r : RecData) :
    InnerProductSpace.HarmonicOnNhd (relChart r).2.2 (relChart r).dom := by
  have h1 : InnerProductSpace.HarmonicOnNhd ((cfChart r).2.2 ∘ fun z : ℂ => -z⁻¹) (relChart r).dom :=
    LQGMetric.harmonicOnNhd_comp_holo (cfChart r).dom.isOpen (relChart r).dom.isOpen (harmonicOnNhd_lift_cfChart r)
      (differentiableOn_negInv.mono (dom_relChart_subset_H r)) (negInv_mapsTo_dom r)
  intro z hz
  exact (h1 z hz).add (Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift z (dom_relChart_subset_H r hz))

/-- At a record of time `s`, the relative chart is GB6's joint chart of the record driver. -/
theorem relChart_eq_jointChart {r : RecData} {s : ℝ} (hr : rtime r = s) :
    relChart r = jointChart (rdrv r) s := by
  unfold relChart cfChart jointChart ownComponentChart
  congr 2
  unfold recChart LocalExt.histChart
  congr 1

/-! ### The chart field is the transport of `h′` -/

section Field

variable {κ : ℝ}

/-- **The own-component chart field is `cfField`**: reading `h` in the Loewner chart (`1, 0, χ`) and then in the
inversion (`−1, −πχ, χ(16/κ)`) is reading it in the own-component chart with `−1, −πχ, χ(16/κ)`. -/
theorem isChartTransport_own_cfField (hκ : 0 < κ) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport (ownComponentChart w s) (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f
      (Theorem14.BW1Chain.cfField κ (isConformal_loewner hw hw0 hs) f) := by
  have hL := isConformal_loewner hw hw0 hs
  have hR := Chart.isConformal_infinitySourceChart
  have hℓL := continuousOn_loewner_lift hw hw0 hs
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have hχ : chiC (16 / κ) = -1 * chiC κ := by rw [Sec4.chiC_sixteen_div hκ]; ring
  have h5 := Chart.isChartTransport_chartTransport hL (Chart.locallyIntegrableOn_of_continuousOn hℓL) 1 0
    (chiC κ) f
  have h6 := Theorem14.BW1Chain.isChartTransport_cfField κ hL f
  rw [hχ] at h6
  have h7 := isChartTransport_trans_sign hL hR hℓL hℓR h5 h6
  have e₃ : (-1 : ℝ) * 1 = -1 := by ring
  have e₄ : (-1 : ℝ) * 0 + -(Real.pi * chiC κ) = -(Real.pi * chiC κ) := by ring
  rw [e₃, e₄, ← hχ] at h7
  exact h7

/-- **The chart identity, for one record.** If `Hc` is `h` read in the own-component chart of a continuous driver
`w` from `0` at time `s` and `h′` is the `R`-transport of `h`, then `Hc` is `h′` read in `jointChart w s` with
`1, 2πχ(16/κ), χ(16/κ)`. -/
theorem eq_chartTransport_jointChart (hκ : 0 < κ) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) {f f' Hc : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f f')
    (hHc : IsChartTransport (ownComponentChart w s) (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f Hc) :
    Hc = Chart.chartTransport (isConformal_jointChart hw hw0 hs) 1 (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ))
      f' := by
  have hR := Chart.isConformal_infinitySourceChart
  have hown : (ownComponentChart w s).IsConformal :=
    (isConformal_loewner hw hw0 hs).trans Chart.isConformal_infinitySourceChart
  have e1 : Hc = Theorem14.BW1Chain.cfField κ (isConformal_loewner hw hw0 hs) f :=
    hHc.unique hown (isChartTransport_own_cfField hκ hw hw0 hs f)
  have e2 : f' = Chart.chartTransport hR (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f :=
    hT.eq_chartTransport hR (Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift)
  rw [e1, e2, Theorem14.BW1Chain.chartTransport_jointChart_eq_cfField hκ hw hw0 hs f]

/-- The chart transport through equal conformal charts. -/
theorem chartTransport_congr_chart {c c' : Chart} (e : c = c') (hc : c.IsConformal) (hc' : c'.IsConformal)
    (σ a k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc σ a k f = Chart.chartTransport hc' σ a k f := by
  subst e
  rfl

/-- **The chart identity for a record of time `s`.** -/
theorem eq_chartTransport_relChart (hκ : 0 < κ) {r : RecData} {s : ℝ≥0} (hr : rtime r = s)
    {f f' Hc : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f f')
    (hHc : IsChartTransport (ownComponentChart (rdrv r) s) (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f Hc) :
    Hc = Chart.chartTransport (isConformal_relChart r) 1 (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ)) f' := by
  rw [eq_chartTransport_jointChart hκ (continuous_rdrv r) (rdrv_zero r) s.coe_nonneg hT hHc]
  exact chartTransport_congr_chart (relChart_eq_jointChart hr).symm _ _ _ _ _ _

/-- **GB6's chart field is the transport of `h′` through the relative chart of the record**, almost surely on the
event `{s < ζα, α(s) ∈ ℍ}`. -/
theorem ae_eq_chartTransport_relChart {θ : ℝ} (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h h' Hc : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    {α : Ω → ℝ≥0 → ℂ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (s : ℝ≥0)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω)) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      Hc ω = Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h' ω) := by
  filter_upwards [ae_gb6RecGood hfl hα s, hHc] with ω hg hHcω hs hsH
  obtain ⟨⟨-, hch, -⟩, -, hr⟩ := hg hs
  have hHc' := hHcω hs hsH
  rw [← hch] at hHc'
  exact eq_chartTransport_relChart hκ hr (hT ω) hHc'

end Field

end InteractingSLE.Supp8.RelSafeS
