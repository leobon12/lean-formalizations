/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedBase
import InteractingSLE.Spec.Sec7.StripWallInputsReflDet
import InteractingSLE.Spec.Supplement.CounterflowNoReturnBack
import InteractingSLE.Spec.Sec7.R7OuterReflect

/-!
# The retained record, its chart and its field under the reflection `σ(z) = −z̄`

Packet PROVE-CFDOWN. A launched piece with driver `e` is retained through its record `recOf t e` (`Exist.StagedLaw`).
The reflected piece has driver `−e` (`Sec7.StripWall.negDrv`). This file proves that every record object is
reflection covariant:

* `negRec` (the record with negated driver samples), a measurable involution; **`recOf_negDrv`**:
  `recOf t (negDrv e) = negRec (recOf t e)`; **`comap_negRec`**: both records generate the same σ-algebra;
* `histDrv_recHist_negRec`: the driver read from the reflected record is the negated driver;
* **`recChart_negRec_fwd`**, **`recChart_negRec_inv`** (on `ℍ`), **`recChart_negRec_lift`**: the record chart of the
  reflected record is the reflected chart `(σ ∘ fwd ∘ σ, σ ∘ inv ∘ σ, −lift ∘ σ)` (`LP.fwdMap_neg`,
  `CfNoReturn.fwdMapInv_neg`, `LP.im_logDerivFwd_neg`);
* `deriv_reflectC_comp`: `(σ ∘ f ∘ σ)′ = conj (f′ ∘ σ)`;
* **`IsChartTransport.reflect_of`**: the chart transport commutes with the reflection (the constant changes sign);
* **`recField_negRec`**: `recField κ (negRec r) (reflField f) = reflField (recField κ r f)`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real ComplexConjugate

namespace InteractingSLE.Sec5.CfDown

open Exist.StagedLaw LocalExt
open LP (reflectC reflectC_reflectC)
open Sec7.FlowReflect (reflField reflTest)
open Sec7.StripWall (negDrv)

/-! ### The reflected record -/

/-- **The reflected record**: the driver samples negated, the stop time and the threshold flag kept. -/
def negRec (r : RecData) : RecData := (fun q => -r.1 q, r.2.1, r.2.2)

@[simp] theorem negRec_negRec (r : RecData) : negRec (negRec r) = r := by
  simp only [negRec, neg_neg]

theorem negRec_involutive : Function.Involutive negRec := negRec_negRec

theorem measurable_negRec : Measurable negRec :=
  (measurable_pi_iff.2 fun q => ((measurable_pi_apply q).comp measurable_fst).neg).prodMk measurable_snd

/-- **The record of the reflected driver is the reflected record.** -/
theorem recOf_negDrv (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : recOf t (negDrv e) = negRec (recOf t e) := rfl

/-- **A record and its reflection generate the same σ-algebra.** -/
theorem comap_negRec {Ω : Type*} (R : Ω → RecData) :
    MeasurableSpace.comap (fun ω => negRec (R ω)) inferInstance = MeasurableSpace.comap R inferInstance := by
  refine le_antisymm (measurable_negRec.comp (comap_measurable R)).comap_le ?_
  have h := measurable_negRec.comp (comap_measurable (fun ω => negRec (R ω)))
  have e : negRec ∘ (fun ω => negRec (R ω)) = R := funext fun ω => negRec_negRec (R ω)
  rw [e] at h
  exact h.comap_le

/-! ### The driver and the chart read from the reflected record -/

theorem isDrvGood_recHist_negRec_iff (r : RecData) : IsDrvGood (recHist (negRec r)) ↔ IsDrvGood (recHist r) := by
  simp only [IsDrvGood, recHist, negRec, neg_eq_zero, neg_sub_neg, abs_sub_comm]

/-- The driver read from the reflected record is the negated driver. -/
theorem histDrv_recHist_negRec (r : RecData) (t : ℝ≥0) :
    histDrv (recHist (negRec r)) t = -histDrv (recHist r) t := by
  by_cases hg : IsDrvGood (recHist r)
  · have h1 := tendsto_drvSample_histDrv ((isDrvGood_recHist_negRec_iff r).2 hg) t
    have h2 := (tendsto_drvSample_histDrv hg t).neg
    exact tendsto_nhds_unique h1 h2
  · rw [histDrv_of_not hg, histDrv_of_not (mt (isDrvGood_recHist_negRec_iff r).1 hg), neg_zero]

theorem rpath_histDrv_negRec (r : RecData) :
    Ito.rpath (histDrv (recHist (negRec r))) = -Ito.rpath (histDrv (recHist r)) := by
  funext s
  simp only [Ito.rpath, histDrv_recHist_negRec, Pi.neg_apply]

theorem histTime_recHist_negRec (r : RecData) : histTime (recHist (negRec r)) = histTime (recHist r) := rfl

theorem continuous_rpath_histDrv (r : RecData) : Continuous (Ito.rpath (histDrv (recHist r))) :=
  (continuous_histDrv _).comp continuous_real_toNNReal

theorem rpath_histDrv_zero (r : RecData) : Ito.rpath (histDrv (recHist r)) 0 = 0 := by
  simp only [Ito.rpath, Real.toNNReal_zero, histDrv_zero]

/-- **The forward map of the reflected record chart** is `σ ∘ fwd ∘ σ`. -/
theorem recChart_negRec_fwd (r : RecData) (z : ℂ) :
    (recChart (negRec r)).1 z = reflectC ((recChart r).1 (reflectC z)) := by
  change QuantumZipper.fwdMap (Ito.rpath (histDrv (recHist (negRec r)))) (histTime (recHist (negRec r))) z =
    reflectC (QuantumZipper.fwdMap (Ito.rpath (histDrv (recHist r))) (histTime (recHist r)) (reflectC z))
  rw [rpath_histDrv_negRec, histTime_recHist_negRec, ← LP.fwdMap_neg _ (histTime (recHist r)).coe_nonneg,
    reflectC_reflectC]

/-- **The inverse map of the reflected record chart** is `σ ∘ inv ∘ σ` on `ℍ`. -/
theorem recChart_negRec_inv (r : RecData) {w : ℂ} (hw : w ∈ H) :
    (recChart (negRec r)).2.1 w = reflectC ((recChart r).2.1 (reflectC w)) := by
  change QuantumZipper.fwdMapInv (Ito.rpath (histDrv (recHist (negRec r)))) (histTime (recHist (negRec r))) w =
    reflectC (QuantumZipper.fwdMapInv (Ito.rpath (histDrv (recHist r))) (histTime (recHist r)) (reflectC w))
  rw [rpath_histDrv_negRec, histTime_recHist_negRec]
  have h := CfNoReturn.fwdMapInv_neg (continuous_rpath_histDrv r) (rpath_histDrv_zero r)
    (histTime (recHist r)).coe_nonneg (LP.reflectC_mem_H_iff.2 hw)
  rwa [reflectC_reflectC] at h

/-- **The lift of the reflected record chart** is `−lift ∘ σ`. -/
theorem recChart_negRec_lift (r : RecData) (z : ℂ) :
    (recChart (negRec r)).2.2 z = -(recChart r).2.2 (reflectC z) := by
  change (QuantumZipper.logDerivFwd (Ito.rpath (histDrv (recHist (negRec r)))) (histTime (recHist (negRec r)))
      z).im + 0 =
    -((QuantumZipper.logDerivFwd (Ito.rpath (histDrv (recHist r))) (histTime (recHist r)) (reflectC z)).im + 0)
  rw [rpath_histDrv_negRec, histTime_recHist_negRec]
  have h := LP.im_logDerivFwd_neg (Ito.rpath (histDrv (recHist r))) (histTime (recHist r)).coe_nonneg
    (reflectC z)
  rw [reflectC_reflectC] at h
  rw [h, add_zero, add_zero]

/-! ### Chart transport under the reflection -/

/-- **The derivative of `σ ∘ f ∘ σ`** is `conj (f′ ∘ σ)` (also where `f` is not differentiable: both are `0`). -/
theorem deriv_reflectC_comp (f : ℂ → ℂ) (z : ℂ) :
    deriv (fun w => reflectC (f (reflectC w))) z = conj (deriv f (reflectC z)) := by
  have e : (fun w => reflectC (f (reflectC w))) = conj ∘ (-(fun w => f (-w))) ∘ conj := by
    funext w
    simp only [LP.reflectC, Function.comp_apply, map_neg, Pi.neg_apply]
  rw [e, deriv_conj_conj, Function.comp_apply, Function.comp_apply, deriv.neg, deriv_comp_neg, neg_neg]
  rfl

theorem norm_deriv_reflectC_comp (f : ℂ → ℂ) (z : ℂ) :
    ‖deriv (fun w => reflectC (f (reflectC w))) z‖ = ‖deriv f (reflectC z)‖ := by
  rw [deriv_reflectC_comp, Complex.norm_conj]

/-- The image of `ℍ` under the reflected inverse map. -/
theorem image_inv_reflect_of {c c' : Chart} (hinv : ∀ w ∈ H, c'.2.1 w = reflectC (c.2.1 (reflectC w))) :
    c'.2.1 '' H = reflectC '' (c.2.1 '' H) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨c.2.1 (reflectC w), ⟨reflectC w, LP.reflectC_mem_H_iff.2 hw, rfl⟩, (hinv w hw).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨reflectC v, LP.reflectC_mem_H_iff.2 hv, ?_⟩
    rw [hinv _ (LP.reflectC_mem_H_iff.2 hv), reflectC_reflectC]

/-- **The chart transport commutes with the reflection.** If `c′ = (σ ∘ fwd ∘ σ, σ ∘ inv ∘ σ, −lift ∘ σ)` (the
inverse only on `ℍ`) and `g` is the transport of `σ f + a` in `c`, then `−g ∘ σ` is the transport of
`σ (−f ∘ σ) − a` in `c′`, with the same lift coefficient. -/
theorem IsChartTransport.reflect_of {c c' : Chart} (hfwd : ∀ z, c'.1 z = reflectC (c.1 (reflectC z)))
    (hinv : ∀ w ∈ H, c'.2.1 w = reflectC (c.2.1 (reflectC w))) (hlift : ∀ z, c'.2.2 z = -c.2.2 (reflectC z))
    {s a k : ℝ} {f g : DistOn upperHalfPlaneOpens} (hT : IsChartTransport c s a k f g) :
    IsChartTransport c' s (-a) k (reflField f) (reflField g) := by
  have himg := image_inv_reflect_of hinv
  have hfwd' : c'.1 = fun z => reflectC (c.1 (reflectC z)) := funext hfwd
  intro φ φ' hsupp hφ
  have hsupp' : tsupport (reflTest φ) ⊆ c.2.1 '' H := by
    rw [Sec7.FlowReflect.tsupport_reflTest]
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hsupp hz
    rw [himg] at h1
    obtain ⟨v, hv, e⟩ := h1
    rw [← e, reflectC_reflectC]
    exact hv
  have hrel : ∀ z ∈ c.2.1 '' H, reflTest φ z = reflTest φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2 := by
    intro z hz
    have hσz : reflectC z ∈ c'.2.1 '' H := by
      rw [himg]
      exact mem_image_of_mem _ hz
    rw [Sec7.FlowReflect.reflTest_apply, Sec7.FlowReflect.reflTest_apply, hφ _ hσz, hfwd']
    simp only [reflectC_reflectC, norm_deriv_reflectC_comp]
  have key := hT (reflTest φ) (reflTest φ') hsupp' hrel
  have hI1 : ∫ w, reflTest φ' w = ∫ w, φ' w := Sec7.FlowReflect.integral_comp_reflectC (fun w => φ' w)
  have hI2 : ∫ w, c'.2.2 (c'.2.1 w) * φ' w = -∫ w, c.2.2 (c.2.1 w) * reflTest φ' w := by
    have e1 : ∫ w, c.2.2 (c.2.1 w) * reflTest φ' w = ∫ w, c.2.2 (c.2.1 (reflectC w)) * φ' w := by
      rw [← Sec7.FlowReflect.integral_comp_reflectC (fun w => c.2.2 (c.2.1 (reflectC w)) * φ' w)]
      congr 1
      funext w
      simp only [reflectC_reflectC, Sec7.FlowReflect.reflTest_apply]
    rw [e1, ← integral_neg]
    congr 1
    funext w
    by_cases hw : w ∈ H
    · rw [hinv w hw, hlift, reflectC_reflectC, neg_mul]
    · have h0 : φ' w = 0 := φ'.zero_on_compl (show w ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hw)
      rw [h0, mul_zero, mul_zero, neg_zero]
  rw [Sec7.FlowReflect.reflField_apply, Sec7.FlowReflect.reflField_apply, key, hI1, hI2]
  ring

/-- **The field read in the reflected record chart is the reflected field read in the record chart.** -/
theorem recField_negRec (κ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    recField κ (negRec r) (reflField f) = reflField (recField κ r f) := by
  have h := IsChartTransport.reflect_of (recChart_negRec_fwd r) (fun w hw => recChart_negRec_inv r hw)
    (recChart_negRec_lift r) (isChartTransport_recField κ r f)
  rw [neg_zero] at h
  exact (isChartTransport_recField κ (negRec r) (reflField f)).unique (isConformal_recChart _) h

end InteractingSLE.Sec5.CfDown
