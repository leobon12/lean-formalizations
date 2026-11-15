/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernel
import InteractingSLE.Spec.Jordan.Transport
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Sec4.Heights
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Spec.Exist.StagedLaw2Flow

/-!
# The field in the joint chart is the counterflow's chart field returned through `R`

Packet PROVE-T14-TIP10. The joint chart of a counterflow stop is `jointChart w s = (R.trans L).trans R`
(`R` the infinity-source chart, `L = Chart.id.loewner w s` the counterflow's own centred Loewner chart). The flow field
`h` read in it (coefficients `1, 0, χ(κ)`, as in `GW2JointKernelStatement`) is therefore obtained from the counterflow
parameter field `h′` (the `R`-transport of `h`, coefficients `−1, −πχ(κ), χ(16/κ)`, as in
`IsCenteredCounterflowDriver`) read in `L` (coefficients `1, 0, χ(16/κ)`, the record field of the counterflow), by one
more transport through `R` with sign `−1`: it is `StripSysField.returnField a l` of that field, `a = −πχ(κ) +
2πχ(16/κ)`, `l = χ(16/κ)`.

* `IsChartTransport.trans_sign`: composition of chart transports when the second one flips the sign (the lift
  coefficients compose as `σ₂ k₁`), the general form of `IsChartTransport.trans`;
* `isChartTransport_infinitySourceChart_returnField`: `returnField a k Y` is the `R`-transport of `Y` with
  coefficients `−1, a − 2πk, −k` (the source lift at `R w` is `−2π` minus the source lift at `w` on `ℍ`);
* `jointChart_eq`, `isConformal_jointChart`, `continuousOn_jointChart_lift`;
* **`isChartTransport_jointChart_returnField`**: the field read in the joint chart (any offset `a₀`) is the returned
  record field;
* **`eq_returnField_of_isChartTransport`**: hence every version of it (uniqueness of chart transports);
* **`jointChart_zero_lift`**, `isChartTransport_jointChart_zero`: at own time `0` the joint chart is the identity with
  the constant lift `−2π`, so the field read in it with the coefficients `1, 0, χ` of `GW2JointKernelStatement` is
  `h − 2πχ` (the normalization defect recorded in `GW2JointKernelProof`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Theorem14

namespace GW2JointKernel

open Sec7.StripSysField

/-! ### Composition with a sign flip -/

section Sign

variable {c₁ c₂ : Chart} {σ₁ a₁ k₁ σ₂ a₂ : ℝ} {h h₁ h₂ : DistOn upperHalfPlaneOpens}

/-- **Composition of chart transports with a sign**: reading `h` in `c₁` (`σ₁, a₁, k₁`) and then the result in `c₂`
(`σ₂, a₂, σ₂ k₁`) is reading `h` in `c₁.trans c₂` with `σ₂ σ₁, σ₂ a₁ + a₂, σ₂ k₁`. -/
theorem isChartTransport_trans_sign (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal)
    (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H) (hℓ₂ : ContinuousOn (fun w => c₂.2.2 (c₂.2.1 w)) H)
    (ht₁ : IsChartTransport c₁ σ₁ a₁ k₁ h h₁) (ht₂ : IsChartTransport c₂ σ₂ a₂ (σ₂ * k₁) h₁ h₂) :
    IsChartTransport (c₁.trans c₂) (σ₂ * σ₁) (σ₂ * a₁ + a₂) (σ₂ * k₁) h h₂ := by
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest (hc₁.trans hc₂) hsupp hφ, Chart.pushTest_trans hc₁ hc₂,
    ht₂.apply_eq hc₂ φ', ht₁.apply_eq hc₁ (Chart.pushTest hc₂ φ'), Chart.integral_pushTest hc₂,
    Chart.integral_mul_pushTest hc₂ φ' (fun z => c₁.2.2 (c₁.2.1 z)),
    IsChartTransport.integral_trans_lift hc₁ hc₂ hℓ₁ hℓ₂ φ']
  ring

/-- The lift of a composed chart, read in the coordinate of `ℍ`, is continuous when both lifts are. -/
theorem continuousOn_trans_lift (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal)
    (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H) (hℓ₂ : ContinuousOn (fun w => c₂.2.2 (c₂.2.1 w)) H) :
    ContinuousOn (fun w => (c₁.trans c₂).2.2 ((c₁.trans c₂).2.1 w)) H := by
  have hc : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 (c₂.2.1 w))) H :=
    hℓ₁.comp hc₂.1.continuousOn hc₂.2.1
  refine (hℓ₂.add hc).congr fun w hw => ?_
  exact IsChartTransport.trans_lift_inv hc₁ (hc₂.2.1 hw)

end Sign

/-! ### The source chart and the return field -/

section Return

/-- On `ℍ`, the infinity-source lift at `R w = −1/w` is `−2π` minus the lift at `w`
(`arg (−1/w) = π − arg w`). -/
theorem infinitySourceChart_lift_negInv {w : ℂ} (hw : w ∈ H) :
    infinitySourceChart.2.2 (-w⁻¹) = -(2 * Real.pi) - infinitySourceChart.2.2 w := by
  rw [infinitySourceChart_lift, infinitySourceChart_lift]
  have hw0 : w ≠ 0 := mem_H_ne_zero hw
  have hargπ : Complex.arg w ≠ Real.pi := fun h => by
    have : (0 : ℝ) < w.im := hw
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h.2]
  have hinv : Complex.arg w⁻¹ = -Complex.arg w := by simp only [Complex.arg_inv, hargπ, ite_false]
  have him : (w⁻¹).im < 0 := by
    rw [Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hw) (Complex.normSq_pos.2 hw0)
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him, hinv]
  ring

/-- The pushed test function of the return chart is that of the source chart (same forward and inverse maps). -/
theorem pushTest_return_eq (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest isConformal_infinityReturnChart φ = Chart.pushTest Chart.isConformal_infinitySourceChart φ := by
  ext z
  rw [Chart.coe_pushTest, Chart.coe_pushTest]
  rfl

/-- **`returnField a k Y` is the `R`-transport of `Y`** with coefficients `−1, a − 2πk, −k`. -/
theorem isChartTransport_infinitySourceChart_returnField (a k : ℝ) (Y : DistOn upperHalfPlaneOpens) :
    IsChartTransport infinitySourceChart (-1) (a - 2 * Real.pi * k) (-k) Y (returnField a k Y) := by
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest Chart.isConformal_infinitySourceChart hsupp hφ, returnField_apply, pushTest_return_eq]
  have hint : ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w =
      -(2 * Real.pi) * (∫ w, φ' w) - ∫ w, infinitySourceChart.2.2 w * φ' w := by
    have hi1 : Integrable fun w => φ' w :=
      φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
    have hi2 : Integrable fun w => infinitySourceChart.2.2 w * φ' w :=
      integrable_mul_testOn_of_continuousOn continuousOn_infinitySourceChart_lift' φ'
    rw [← integral_const_mul, ← integral_sub (hi1.const_mul _) hi2]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    change infinitySourceChart.2.2 (-w⁻¹) * φ' w = -(2 * Real.pi) * φ' w - infinitySourceChart.2.2 w * φ' w
    by_cases hw : w ∈ H
    · rw [infinitySourceChart_lift_negInv hw]
      ring
    · rw [testOn_eq_zero_of_notMem_H φ' hw]
      ring
  rw [hint]
  ring

end Return

/-! ### The joint chart -/

section Joint

variable {w : ℝ → ℝ} {s : ℝ}

/-- The joint chart is `(R.trans L).trans R`. -/
theorem jointChart_eq (w : ℝ → ℝ) (s : ℝ) :
    jointChart w s = (infinitySourceChart.trans (Chart.id.loewner w s)).trans infinitySourceChart := by
  unfold jointChart ownComponentChart
  rw [Chart.trans_assoc]

theorem isConformal_loewner (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    (Chart.id.loewner w s).IsConformal :=
  Chart.isConformal_id.loewner hw hw0 hs

theorem continuousOn_loewner_lift (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    ContinuousOn (fun z => (Chart.id.loewner w s).2.2 ((Chart.id.loewner w s).2.1 z)) H :=
  Chart.isConformal_id.continuousOn_loewner_lift Chart.continuousOn_id_lift hw hw0 hs

theorem isConformal_jointChart (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    (jointChart w s).IsConformal := by
  rw [jointChart_eq]
  exact (Chart.isConformal_infinitySourceChart.trans (isConformal_loewner hw hw0 hs)).trans
    Chart.isConformal_infinitySourceChart

/-- **The field read in the joint chart is the returned record field.** If `h′` is the counterflow parameter field of
`h` (`R`-transport with `−1, −πχ(κ), χ(16/κ)`) and `Y` is `h′` read in the counterflow's Loewner chart at `s`
(`1, 0, χ(16/κ)`), then `returnField (−πχ(κ) + 2πχ(16/κ) + a₀) χ(16/κ) Y` is `h` read in the joint chart with
`1, a₀, χ(κ)`. -/
theorem isChartTransport_jointChart_returnField {κ : ℝ} (hκ : 0 < κ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (a₀ : ℝ) {h h' Y : DistOn upperHalfPlaneOpens}
    (h₁ : IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) h h')
    (h₂ : IsChartTransport (Chart.id.loewner w s) 1 0 (QuantumZipper.chiC (16 / κ)) h' Y) :
    IsChartTransport (jointChart w s) 1 a₀ (QuantumZipper.chiC κ) h
      (returnField (-(Real.pi * QuantumZipper.chiC κ) + 2 * Real.pi * QuantumZipper.chiC (16 / κ) + a₀)
        (QuantumZipper.chiC (16 / κ)) Y) := by
  have hR := Chart.isConformal_infinitySourceChart
  have hL := isConformal_loewner hw hw0 hs
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have hℓL := continuousOn_loewner_lift hw hw0 hs
  have hRL := IsChartTransport.trans hR hL hℓR hℓL h₁ h₂
  have h₃ := isChartTransport_infinitySourceChart_returnField
    (-(Real.pi * QuantumZipper.chiC κ) + 2 * Real.pi * QuantumZipper.chiC (16 / κ) + a₀)
    (QuantumZipper.chiC (16 / κ)) Y
  have e₁ : -(Real.pi * QuantumZipper.chiC κ) + 2 * Real.pi * QuantumZipper.chiC (16 / κ) + a₀ -
      2 * Real.pi * QuantumZipper.chiC (16 / κ) = -(Real.pi * QuantumZipper.chiC κ) + a₀ := by ring
  have e₂ : -QuantumZipper.chiC (16 / κ) = -1 * QuantumZipper.chiC (16 / κ) := by ring
  rw [e₁, e₂] at h₃
  have h₄ := isChartTransport_trans_sign (hR.trans hL) hR (continuousOn_trans_lift hR hL hℓR hℓL) hℓR hRL h₃
  have e₃ : (-1 : ℝ) * -1 = 1 := by ring
  have e₄ : (-1 : ℝ) * -(Real.pi * QuantumZipper.chiC κ) + (-(Real.pi * QuantumZipper.chiC κ) + a₀) = a₀ := by
    ring
  have e₅ : (-1 : ℝ) * QuantumZipper.chiC (16 / κ) = QuantumZipper.chiC κ := by
    rw [Sec4.chiC_sixteen_div hκ]
    ring
  rw [e₃, e₄, e₅] at h₄
  rw [jointChart_eq]
  exact h₄

/-- **Every version of the field read in the joint chart is the returned record field.** -/
theorem eq_returnField_of_isChartTransport {κ : ℝ} (hκ : 0 < κ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (a₀ : ℝ) {h h' Y Hc : DistOn upperHalfPlaneOpens}
    (h₁ : IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) h h')
    (h₂ : IsChartTransport (Chart.id.loewner w s) 1 0 (QuantumZipper.chiC (16 / κ)) h' Y)
    (hHc : IsChartTransport (jointChart w s) 1 a₀ (QuantumZipper.chiC κ) h Hc) :
    Hc = returnField (-(Real.pi * QuantumZipper.chiC κ) + 2 * Real.pi * QuantumZipper.chiC (16 / κ) + a₀)
      (QuantumZipper.chiC (16 / κ)) Y :=
  hHc.unique (isConformal_jointChart hw hw0 hs) (isChartTransport_jointChart_returnField hκ hw hw0 hs a₀ h₁ h₂)

end Joint

/-! ### The lift of the joint chart at time `0` -/

section Zero

variable {w : ℝ → ℝ}

/-- At own time `0` the joint chart is the identity on `ℍ`. -/
theorem jointChart_zero_fst (hw0 : w 0 = 0) (z : ℂ) : (jointChart w 0).1 z = z := by
  change -(QuantumZipper.fwdMap w 0 (-z⁻¹))⁻¹ = z
  rw [Exist.StagedLaw.fwdMap_zero_time hw0, negInv_negInv]

/-- **At own time `0` the lift of the joint chart is the constant `−2π` on `ℍ`**, not `0`: the chain-rule lift of
`R ∘ id ∘ R` adds the two infinity-source lifts `Im(−2 Log(−1/z)) + Im(−2 Log z) = −2π`. So the field read in the
joint chart with the coefficients `1, 0, χ` (as in `GW2JointKernelStatement`) is `h − 2πχ` at time `0`
(`isChartTransport_jointChart_zero`), and in general it differs by the constant `−2πχ` from the joint-chart field of
the specification (GB9, p. 525: "the continuously inherited integer argument starts at zero and stays zero"). -/
theorem jointChart_zero_lift (hw0 : w 0 = 0) {z : ℂ} (hz : z ∈ H) : (jointChart w 0).2.2 z = -(2 * Real.pi) := by
  change infinitySourceChart.2.2 (QuantumZipper.fwdMap w 0 (-z⁻¹)) +
    ((QuantumZipper.logDerivFwd w 0 (-z⁻¹)).im + 0) + infinitySourceChart.2.2 z = -(2 * Real.pi)
  rw [Exist.StagedLaw.fwdMap_zero_time hw0, infinitySourceChart_lift_negInv hz,
    show QuantumZipper.logDerivFwd w 0 (-z⁻¹) = 0 by simp [QuantumZipper.logDerivFwd]]
  simp

/-- **At own time `0` the field read in the joint chart (coefficients `1, 0, χ`) is `h − 2πχ`.** -/
theorem isChartTransport_jointChart_zero (hw : Continuous w) (hw0 : w 0 = 0) (k : ℝ)
    (h : DistOn upperHalfPlaneOpens) :
    IsChartTransport (jointChart w 0) 1 0 k h (h - (2 * Real.pi * k) • Chart.oneDist) := by
  have hc := isConformal_jointChart hw hw0 le_rfl
  have hinv : ∀ v ∈ H, (jointChart w 0).2.1 v = v := by
    intro v hv
    change -(QuantumZipper.fwdMapInv w 0 (-v⁻¹))⁻¹ = v
    rw [fwdMapInv_zero_time hw hw0 (negInv_mem_H hv), negInv_negInv]
  have himg : (jointChart w 0).2.1 '' H = H := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hinv u hu]
      exact hu
    · intro hv
      exact ⟨v, hv, hinv v hv⟩
  intro φ φ' hsupp hφ
  have hderiv : ∀ z ∈ H, deriv (jointChart w 0).1 z = 1 := by
    intro z hz
    have he : (jointChart w 0).1 =ᶠ[𝓝 z] id :=
      Filter.Eventually.of_forall fun y => jointChart_zero_fst hw0 y
    rw [he.deriv_eq, deriv_id]
  have hφφ : φ = φ' := by
    ext z
    by_cases hz : z ∈ H
    · rw [hφ z (himg.symm ▸ hz), hderiv z hz, jointChart_zero_fst hw0, norm_one, one_pow, mul_one]
    · rw [testOn_eq_zero_of_notMem_H φ hz, testOn_eq_zero_of_notMem_H φ' hz]
  have hlift : ∫ v, (jointChart w 0).2.2 ((jointChart w 0).2.1 v) * φ' v = -(2 * Real.pi) * ∫ v, φ' v := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ H
    · change (jointChart w 0).2.2 ((jointChart w 0).2.1 v) * φ' v = -(2 * Real.pi) * φ' v
      rw [hinv v hv, jointChart_zero_lift hw0 hv]
    · change (jointChart w 0).2.2 ((jointChart w 0).2.1 v) * φ' v = -(2 * Real.pi) * φ' v
      rw [testOn_eq_zero_of_notMem_H φ' hv]
      ring
  rw [hlift, hφφ, sub_apply, smul_apply, Chart.oneDist_apply, smul_eq_mul]
  ring

end Zero

end GW2JointKernel

end Theorem14

end InteractingSLE
