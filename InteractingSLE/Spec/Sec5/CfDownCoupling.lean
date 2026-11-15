/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfDownWord
import InteractingSLE.WangWu.ReverseContactLocal

/-!
# The image chart and the chart coupling clause under the reflection `σ(z) = −z̄`

Packet PROVE-CFDOWN. The image chart `cfChart r = recChart r ∘ R` (`R(z) = −1/z`) of the reflected record is the
reflected image chart, except that its lift carries the offset `−2π` (`R7Outer.lift_reflectC`: `L(σ z) = −L(z) − 2π`).
In the chart coupling clause the lift enters as `a + k · lift` with `(a, k) = (−πχ, −χ)`; since `a = πk` the offset
turns `a + k · lift` into `−(a + k · lift ∘ σ)`, which is exactly the sign change of the reflected field. Hence:

* `cfChart_negRec_fwd`, `cfChart_negRec_inv`, `cfChart_negRec_lift`, `image_cfChart_negRec`;
* **`isChartCouplingCharFunConst_reflect`**: the chart coupling clause (fixed times,
  `Lemma71D.IsChartCouplingCharFunConst`)
  of the reflected configuration (driver `W`, word `(xL; xR)`, charts `cfChart (negRec R)`, field `−(−h ∘ σ)`) gives
  the clause of the original configuration (driver `−W`, word `(−xR; −xL)` with exchanged weights, charts `cfChart R`,
  field `−h`). Test function `−φ ∘ σ`, harmonic extension `−u ∘ σ`; means by `FlowReflect.couplingMean_reflect`,
  variances by `FlowReflect.zeroGFFTestCov_image_reflectC` and `WangWu.zeroGFFTestCov_neg_neg`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfDown

open Exist.StagedLaw CfGiven
open LP (reflectC reflectC_reflectC)
open WangWu (negInv)
open Sec7.FlowReflect (reflField reflTest reflData reflJumps)
open Sec7.PocketTraversal (geomLW geomRW)

/-! ### The image chart of the reflected record -/

theorem cfChart_negRec_fwd (r : RecData) (z : ℂ) :
    (cfChart (negRec r)).1 z = reflectC ((cfChart r).1 (reflectC z)) := by
  change -((recChart (negRec r)).1 z)⁻¹ = reflectC (-((recChart r).1 (reflectC z))⁻¹)
  rw [recChart_negRec_fwd]
  exact Sec7.R7Outer.negInv_reflectC _

theorem cfChart_negRec_inv (r : RecData) {w : ℂ} (hw : w ∈ H) :
    (cfChart (negRec r)).2.1 w = reflectC ((cfChart r).2.1 (reflectC w)) := by
  change (recChart (negRec r)).2.1 (-w⁻¹) = reflectC ((recChart r).2.1 (-(reflectC w)⁻¹))
  rw [recChart_negRec_inv r (Sec7.StripSysField.negInv_mem_H hw)]
  rw [show reflectC (-w⁻¹) = -(reflectC w)⁻¹ from (Sec7.R7Outer.negInv_reflectC w).symm]

/-- **The lift of the reflected image chart** carries the offset `−2π`. -/
theorem cfChart_negRec_lift (r : RecData) {z : ℂ} (hz : (recChart r).1 (reflectC z) ∈ H) :
    (cfChart (negRec r)).2.2 z = -(cfChart r).2.2 (reflectC z) - 2 * π := by
  change infinitySourceChart.2.2 ((recChart (negRec r)).1 z) + (recChart (negRec r)).2.2 z =
    -(infinitySourceChart.2.2 ((recChart r).1 (reflectC z)) + (recChart r).2.2 (reflectC z)) - 2 * π
  rw [recChart_negRec_fwd, recChart_negRec_lift, Sec7.R7Outer.lift_reflectC hz]
  ring

theorem image_cfChart_negRec (r : RecData) {S : Set ℂ} (hS : S ⊆ H) :
    (cfChart (negRec r)).2.1 '' S = reflectC '' ((cfChart r).2.1 '' (reflectC '' S)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(cfChart r).2.1 (reflectC w), ⟨reflectC w, mem_image_of_mem _ hw, rfl⟩,
      (cfChart_negRec_inv r (hS hw)).symm⟩
  · rintro ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨v, hv, cfChart_negRec_inv r (hS hv)⟩

/-! ### The chart coupling clause -/

section Coupling

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓐 : Filtration ℝ≥0 mΩ}

/-- **The chart coupling clause under the reflection** (for `a = πk`, the image chart's constants `(−πχ, −χ)`). -/
theorem isChartCouplingCharFunConst_reflect {κ' a k : ℝ} (hak : a = π * k) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {R : Ω → RecData}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : Sec7.Lemma71D.IsChartCouplingCharFunConst κ' ρL ρR P 𝓐 W (geomLW W xL) (geomRW W xR) (fun _ => ⊤)
      (fun ω => cfChart (negRec (R ω))) a k (fun ω => -reflField (h ω))) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst κ' ρR ρL P 𝓐 (-W) (geomLW (-W) (fun ω i => -xR ω i))
      (geomRW (-W) (fun ω j => -xL ω j)) (fun _ => ⊤) (fun ω => cfChart (R ω)) a k (fun ω => -h ω) := by
  intro t u hu φ
  have hu' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ' ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω))
      (fun z => -u ω (reflectC z)) := by
    intro ω
    have e1 : (fun i => geomLW (-W) (fun ω i => -xR ω i) i t ω - (-W) t ω) =
        fun i => -(geomRW W xR i t ω - W t ω) := funext fun i => by rw [geomLW_neg]; simp only [Pi.neg_apply]; ring
    have e2 : (fun j => geomRW (-W) (fun ω j => -xL ω j) j t ω - (-W) t ω) =
        fun j => -(geomLW W xL j t ω - W t ω) := funext fun j => by rw [geomRW_neg]; simp only [Pi.neg_apply]; ring
    have h1 := hu ω
    rw [e1, e2] at h1
    exact Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect_force h1
  filter_upwards [hC t (fun ω z => -u ω (reflectC z)) hu' (-reflTest φ)] with ω hω htζ hsupp
  have hwn : (fun s : ℝ => (-W) s.toNNReal ω) = -fun s : ℝ => W s.toNNReal ω := rfl
  have hK : fwdHull (fun s : ℝ => (-W) s.toNNReal ω) (t : ℝ) =
      reflectC '' fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by rw [hwn, LP.fwdHull_neg]
  have hU : (cfChart (negRec (R ω))).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) =
      reflectC '' ((cfChart (R ω)).2.1 '' (H \ fwdHull (fun s : ℝ => (-W) s.toNNReal ω) (t : ℝ))) := by
    rw [image_cfChart_negRec _ sdiff_subset, hK, LP.H_diff_reflectC_image]
  have hsupp' : tsupport ⇑(-reflTest φ) ⊆
      (cfChart (negRec (R ω))).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) := by
    have e : ⇑(-reflTest φ) = -⇑(reflTest φ) := rfl
    rw [hU, e, tsupport_neg, Sec7.FlowReflect.tsupport_reflTest]
    exact image_mono hsupp
  have key := hω htζ hsupp'
  have e1 : (fun ω' => Complex.exp (Complex.I * ((-h ω' φ : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * (((-reflField (h ω')) (-reflTest φ) : ℝ) : ℂ)) := by
    funext ω'
    simp only [neg_apply, Sec7.FlowReflect.reflField_apply, map_neg,
      Sec7.FlowReflect.reflTest_reflTest, neg_neg]
  have hmean : ∫ z, (couplingMean κ' (fun s : ℝ => W s.toNNReal ω) (t : ℝ) (fun z => -u ω (reflectC z))
        ((cfChart (negRec (R ω))).1 z) - a - k * (cfChart (negRec (R ω))).2.2 z) * (-reflTest φ) z =
      ∫ z, (couplingMean κ' (fun s : ℝ => (-W) s.toNNReal ω) (t : ℝ) (u ω) ((cfChart (R ω)).1 z) - a -
        k * (cfChart (R ω)).2.2 z) * φ z := by
    rw [← Sec7.FlowReflect.integral_comp_reflectC]
    congr 1
    funext z
    have hφσ : (-reflTest φ) (reflectC z) = -φ z := by
      change -(reflTest φ (reflectC z)) = -φ z
      rw [Sec7.FlowReflect.reflTest_apply, reflectC_reflectC]
    rw [hφσ]
    by_cases hz : z ∈ tsupport φ
    · obtain ⟨w, hw, hwz⟩ := hsupp hz
      have hH : (recChart (R ω)).1 (reflectC (reflectC z)) ∈ H := by
        rw [reflectC_reflectC, ← hwz]
        change (recChart (R ω)).1 ((recChart (R ω)).2.1 (-w⁻¹)) ∈ H
        rw [(isConformal_recChart (R ω)).2.2 _ (Sec7.StripSysField.negInv_mem_H hw.1)]
        exact Sec7.StripSysField.negInv_mem_H hw.1
      rw [cfChart_negRec_fwd, cfChart_negRec_lift _ hH, reflectC_reflectC]
      have hcm := Sec7.FlowReflect.couplingMean_reflect κ' (-(fun s : ℝ => W s.toNNReal ω))
        (NNReal.coe_nonneg t) (fun z => -u ω (reflectC z)) ((cfChart (R ω)).1 z)
      simp only [neg_neg, reflectC_reflectC] at hcm
      rw [hcm, hwn, hak]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hz, neg_zero, mul_zero, mul_zero]
  have hcov : zeroGFFTestCov ((cfChart (negRec (R ω))).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)))
        ⇑(-reflTest φ) ⇑(-reflTest φ) =
      zeroGFFTestCov ((cfChart (R ω)).2.1 '' (H \ fwdHull (fun s : ℝ => (-W) s.toNNReal ω) (t : ℝ))) φ φ := by
    rw [hU, Sec7.FlowReflect.zeroGFFTestCov_image_reflectC]
    have e : (fun z => (-reflTest φ) (reflectC z)) = -⇑φ := funext fun z => by
      change -(reflTest φ (reflectC z)) = -φ z
      rw [Sec7.FlowReflect.reflTest_apply, reflectC_reflectC]
    rw [e, WangWu.zeroGFFTestCov_neg_neg]
  change condExp (𝓐 t) P (fun ω' => Complex.exp (Complex.I * ((-h ω' φ : ℝ) : ℂ))) ω = _
  rw [e1, key, hmean, hcov]

end Coupling

end InteractingSLE.Sec5.CfDown
