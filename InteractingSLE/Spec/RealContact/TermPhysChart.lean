/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermGoodAe
import InteractingSLE.Spec.Supplement.WalkInfMeas
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Supplement.CondDriverBridge
import InteractingSLE.Spec.Supplement.BR4aPathField
import InteractingSLE.Spec.Supplement.OrdFstShift
import InteractingSLE.Spec.Restart.RetFinGlue

/-!
# The physical chart of the completed second path

Packet PROVE-RC-TERM, second run (ruling R124). The chart in which K2 is applied to the first path: for a record `r`
of the second path (driver `U`, time `T`), the second seed `x₂` and a real number `τ` (the chart position of the first
seed),

`physChart x₂ r τ = ((Chart.id.recenter x₂).trans (recChart r)).recenter τ`,

that is `z ↦ f_T(z − x₂) − τ` with inverse `v ↦ f_T⁻¹(v + τ) + x₂` and lift `arg f_T′(· − x₂)`.

* `physChart_fst`, `physChart_inv`, `physChart_lift`, `isConformal_physChart`, `coe_dom_physChart`;
* **`isMeasChart_physChart`**: for a σ-algebra measuring the record and `τ`, it is a measurable random chart
  (`Theorem14.WalkInf.IsMeasChart`: conformal, continuous harmonic lift, measurable domain events, masked forward
  maps and masked lifts);
* **`chartTransport_physChart`**: the field read in it with the constant `a` is
  `flowField 0 a (flowField τ 0 (termField κ x₂ r f))`, the field of `RLC.OrdModel.AStopSourceInputs` at the seed `τ`.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Exist.Staged Exist.StagedLaw

/-- **The physical chart of a record of the second path**, recentred at `τ`. -/
def physChart (x₂ : ℝ) (r : RecData) (τ : ℝ) : Chart := ((Chart.id.recenter x₂).trans (recChart r)).recenter τ

theorem isConformal_physChart₀ (x₂ : ℝ) (r : RecData) : ((Chart.id.recenter x₂).trans (recChart r)).IsConformal :=
  (Chart.isConformal_id.recenter x₂).trans (isConformal_recChart r)

theorem isConformal_physChart (x₂ : ℝ) (r : RecData) (τ : ℝ) : (physChart x₂ r τ).IsConformal :=
  (isConformal_physChart₀ x₂ r).recenter τ

theorem physChart₀_fst (x₂ : ℝ) (r : RecData) (z : ℂ) :
    ((Chart.id.recenter x₂).trans (recChart r)).1 z = fwdMap (rdrv r) (rtime r) (z - (x₂ : ℂ)) := by
  rw [recChart_eq r]
  rfl

theorem physChart₀_inv (x₂ : ℝ) (r : RecData) (v : ℂ) :
    ((Chart.id.recenter x₂).trans (recChart r)).2.1 v = fwdMapInv (rdrv r) (rtime r) v + (x₂ : ℂ) := by
  rw [recChart_eq r]
  rfl

theorem physChart₀_lift (x₂ : ℝ) (r : RecData) (z : ℂ) :
    ((Chart.id.recenter x₂).trans (recChart r)).2.2 z = (logDerivFwd (rdrv r) (rtime r) (z - (x₂ : ℂ))).im := by
  rw [recChart_eq r]
  change ((logDerivFwd (rdrv r) (rtime r) (z - (x₂ : ℂ))).im + 0) + 0 = _
  rw [add_zero, add_zero]

/-- The domain of the unrecentred physical chart is the translated complement of the hull of the record. -/
theorem coe_dom_physChart₀ (x₂ : ℝ) (r : RecData) :
    (((Chart.id.recenter x₂).trans (recChart r)).dom : Set ℂ) =
      (fun z : ℂ => z + (x₂ : ℂ)) '' (H \ fwdHull (rdrv r) (rtime r)) := by
  rw [(isConformal_physChart₀ x₂ r).coe_dom,
    ← QuantumZipper.RS.image_fwdMapInv_H (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r), image_image]
  exact image_congr fun v _ => physChart₀_inv x₂ r v

theorem physChart_fst (x₂ : ℝ) (r : RecData) (τ : ℝ) (z : ℂ) :
    (physChart x₂ r τ).1 z = fwdMap (rdrv r) (rtime r) (z - (x₂ : ℂ)) - (τ : ℂ) := by
  unfold physChart
  rw [recChart_eq r]
  rfl

theorem physChart_inv (x₂ : ℝ) (r : RecData) (τ : ℝ) (v : ℂ) :
    (physChart x₂ r τ).2.1 v = fwdMapInv (rdrv r) (rtime r) (v + (τ : ℂ)) + (x₂ : ℂ) := by
  unfold physChart
  rw [recChart_eq r]
  rfl

theorem physChart_lift (x₂ : ℝ) (r : RecData) (τ : ℝ) (z : ℂ) :
    (physChart x₂ r τ).2.2 z = (logDerivFwd (rdrv r) (rtime r) (z - (x₂ : ℂ))).im := by
  unfold physChart
  rw [recChart_eq r]
  change ((logDerivFwd (rdrv r) (rtime r) (z - (x₂ : ℂ))).im + 0) + 0 = _
  rw [add_zero, add_zero]

/-- The domain of the physical chart is the translated complement of the hull of the record. -/
theorem coe_dom_physChart (x₂ : ℝ) (r : RecData) (τ : ℝ) :
    ((physChart x₂ r τ).dom : Set ℂ) = (fun z : ℂ => z + (x₂ : ℂ)) '' (H \ fwdHull (rdrv r) (rtime r)) := by
  rw [(isConformal_physChart x₂ r τ).coe_dom,
    ← QuantumZipper.RS.image_fwdMapInv_H (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)]
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvτ : v + (τ : ℂ) ∈ H := by
      show 0 < (v + (τ : ℂ)).im
      have : 0 < v.im := hv
      simpa using this
    exact ⟨_, ⟨_, hvτ, rfl⟩, (physChart_inv x₂ r τ v).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hwτ : w - (τ : ℂ) ∈ H := by
      show 0 < (w - (τ : ℂ)).im
      have : 0 < w.im := hw
      simpa using this
    exact ⟨_, hwτ, by rw [physChart_inv, sub_add_cancel]⟩

/-- **The physical chart of a measurable record at a measurable position is a measurable random chart.** -/
theorem isMeasChart_physChart {Ω : Type u} {m : MeasurableSpace Ω} {rec : Ω → RecData} (hr : Measurable[m] rec)
    {τ : Ω → ℝ} (hτ : Measurable[m] τ) (x₂ : ℝ) :
    Theorem14.WalkInf.IsMeasChart m fun ω => physChart x₂ (rec ω) (τ ω) :=
  (((Theorem14.WalkInf.isMeasChart_id m).recenter (measurable_const (a := x₂))).trans_recChart hr).recenter hτ

/-- **The unrecentred physical chart of a measurable record is a measurable random chart.** -/
theorem isMeasChart_physChart₀ {Ω : Type u} {m : MeasurableSpace Ω} {rec : Ω → RecData} (hr : Measurable[m] rec)
    (x₂ : ℝ) : Theorem14.WalkInf.IsMeasChart m fun ω => (Chart.id.recenter x₂).trans (recChart (rec ω)) :=
  ((Theorem14.WalkInf.isMeasChart_id m).recenter (measurable_const (a := x₂))).trans_recChart hr

theorem continuousOn_lift_inv_physChart₀ (x₂ : ℝ) (r : RecData) :
    ContinuousOn (fun w => ((Chart.id.recenter x₂).trans (recChart r)).2.2
      (((Chart.id.recenter x₂).trans (recChart r)).2.1 w)) H := by
  refine Theorem14.GW2JointKernel.continuousOn_trans_lift (Chart.isConformal_id.recenter x₂)
    (isConformal_recChart r) ?_ (continuousOn_recChart_lift r)
  exact continuousOn_const

/-- **The chart field of a record is the field read in the unrecentred physical chart.** -/
theorem isChartTransport_termField (κ x₂ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport ((Chart.id.recenter x₂).trans (recChart r)) 1 0 (chiC κ) f (termField κ x₂ r f) := by
  have ht₁ := Theorem14.BR4aPath.isChartTransport_recField (chiC κ) x₂ f
  have ht₂ : IsChartTransport (recChart r) 1 0 (1 * chiC κ) (Exist.flowField x₂ 0 f)
      (recField κ r (Exist.flowField x₂ 0 f)) := by
    rw [one_mul]
    exact isChartTransport_recField κ r _
  have ht := Theorem14.GW2JointKernel.isChartTransport_trans_sign (Chart.isConformal_id.recenter x₂)
    (isConformal_recChart r) continuousOn_const (continuousOn_recChart_lift r) ht₁ ht₂
  rw [one_mul, mul_zero, add_zero, one_mul] at ht
  exact ht

/-- **The field read in the physical chart** is the recentred chart field of the record, shifted by the constant. -/
theorem chartTransport_physChart (κ x₂ : ℝ) (r : RecData) (τ a : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport (isConformal_physChart x₂ r τ) 1 a (chiC κ) f =
      Exist.flowField 0 a (Exist.flowField τ 0 (termField κ x₂ r f)) := by
  have hc₀ := isConformal_physChart₀ x₂ r
  have hℓ₀ := continuousOn_lift_inv_physChart₀ x₂ r
  have h1 : Chart.chartTransport hc₀ 1 0 (chiC κ) f = termField κ x₂ r f :=
    (Chart.isChartTransport_chartTransport hc₀
      (Chart.locallyIntegrableOn_of_continuousOn hℓ₀) 1 0 (chiC κ) f).unique hc₀
      (isChartTransport_termField κ x₂ r f)
  rw [← Restart.RetFin.flowField_chartTransport,
    show Chart.chartTransport (isConformal_physChart x₂ r τ) 1 0 (chiC κ) f =
      Exist.flowField τ 0 (Chart.chartTransport hc₀ 1 0 (chiC κ) f) from
      RLC.OrdDet.chartTransport_recenter_eq_flowField hc₀ hℓ₀ τ 1 0 (chiC κ) f, h1]

end Term

end InteractingSLE.RealContact
