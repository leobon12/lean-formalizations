/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuSeed
import InteractingSLE.Spec.Supplement.OrdFstShift

/-!
# The retained law read in the hull chart with an offset

Packet PROVE-SB2-LCMEAN, round 13 (step 1 of the induction, handoff §R13.5). The retained kernel law
(`Qr.RetainedLawAt`, F3) is stated in the canonical hull chart with offset `0`; F2b′'s versions use the hull chart with
the offset `x₀` placing B's launch point at `0`. The hull chart with offset `x₀` is the recentred one
(`hullChart_eq_recenter`), so its chart field is the translate of the offset-`0` field (`flowField x₀ 0`), and if `x₀`
is measurable for the marks, the conditional law moves to the shifted word `BoundaryWord.shiftW x₀ β`:

* `hullChart_eq_recenter`, `continuousOn_lift_inv_hullChart`;
* **`ae_isGFF_hullChart_shift`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist Exist.StagedLaw

/-- The hull chart with offset `x₀` is the offset-`0` hull chart recentred at `x₀`. -/
theorem hullChart_eq_recenter (A : Set ℂ) (x₀ : ℝ) : Mo.hullChart A x₀ = (Mo.hullChart A 0).recenter x₀ := by
  simp only [Mo.hullChart, Chart.recenter, Complex.ofReal_zero, sub_zero, add_zero]

/-- The lift of the hull chart read through its inverse is continuous on `ℍ`. -/
theorem continuousOn_lift_inv_hullChart {A : Set ℂ} (hA : IsHPHull A) (x₀ : ℝ) :
    ContinuousOn (fun w => (Mo.hullChart A x₀).2.2 ((Mo.hullChart A x₀).2.1 w)) H :=
  (Mo.isDomainChart_hullChart hA x₀).continuousOn_lift_inv

/-- **The retained law read in the hull chart with an offset**: if, on a `𝒢`-event, the field read in the offset-`0`
canonical hull chart of `fill K` is conditionally a GFF with the data of `β`, and the offset `x₀` is `𝒢`-measurable,
then the field read in the hull chart with offset `x₀` is conditionally a GFF with the data of `shiftW x₀ β`. -/
theorem ae_isGFF_hullChart_shift {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {G : Set Ω}
    {K : Ω → Set ℂ} (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    {x₀ : Ω → ℝ} (hx₀ : Measurable[𝒢] x₀) {κ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {β : Ω → BoundaryWord} (hYm : Measurable fun ω =>
      Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀)
      (fun ω => Chart.chartTransport (isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω) 1 0 (chiC κ) (h ω))
      (β ω₀).fn (β ω₀).jumps) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀)
      (fun ω => Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).jumps := by
  have hA : ∀ ω, IsHPHull (fillH (K ω)) := Mo.isHPHull_fillH hKc hKp
  filter_upwards [hlaw, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hx₀] with ω₀ hl hxeq hG
  have hg := hl hG
  have hrec := Supp9.IsGFFWithBoundaryData.recenter (β ω₀).isPiecewiseConstantBoundaryData (x₀ ω₀) hg
  rw [BoundaryWord.jumps_shiftW,
    show (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).fn = fun y => (β ω₀).fn (y + x₀ ω₀) from
      funext (BoundaryWord.fn_shiftW _ _)]
  refine isGFFWithBoundaryData_congr_ae hrec hYm ?_
  filter_upwards [hxeq] with ω hω
  have hc0 := isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω
  have e := RLC.OrdDet.chartTransport_recenter_eq_flowField hc0 (continuousOn_lift_inv_hullChart (hA ω) 0)
    (x₀ ω) 1 0 (chiC κ) (h ω)
  have hch : Mo.hullChart (fillH (K ω)) (x₀ ω) = (Mo.hullChart (fillH (K ω)) 0).recenter (x₀ ω) :=
    hullChart_eq_recenter _ _
  show Exist.flowField (x₀ ω₀) 0 (Chart.chartTransport hc0 1 0 (chiC κ) (h ω)) =
    Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)
  rw [← hω, ← e]
  congr 1
  exact hch.symm

end InteractingSLE.Theorem14.SB.Mu
