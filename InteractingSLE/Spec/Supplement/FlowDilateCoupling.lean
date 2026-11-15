/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.FlowDilate
import InteractingSLE.Spec.Sec7.Lemma725RefFullDil

/-!
# The optional hull coupling under a dilation: the bridge to Aux. lemma 126

Packet PROVE-RLC-J, item (g) (Lemma G8's affine normalization). The dilation of a whole optional hull coupling is
already proved (PROVE-LEMMA725REF2, `Sec7.Lemma725RefFull.IsOptionalHullCoupling.dilate`, Aux. lemma 126), with the
dilated field `Sec7.Lemma725RefFull.dilField hr h = h(· / r)` (the field read in the dilation chart). This file only
identifies that field with `FlowDilate.affField 0 hr h` (both test `h` against `φ ↦ r² φ(r ·)`), and restates the
coupling dilation with it (`isOptionalHullCoupling_dilate_affField`), for `IsFlowLine.affine`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace FlowDilate

open Sec7.Dilation

/-- **The dilated field of Aux. lemma 126 is `affField 0`.** -/
theorem dilField_eq_affField {r : ℝ} (hr : 0 < r) (h : DistOn upperHalfPlaneOpens) :
    Sec7.Lemma725RefFull.dilField hr h = affField 0 hr h := by
  ext φ
  rw [Sec7.Lemma725RefFull.dilField_apply, affField_apply]
  congr 1
  ext z
  rw [Sec7.Lemma725RefFull.pushTest_dilation_apply hr, affTest_apply]
  congr 2
  simp only [aff, Complex.ofReal_zero, add_zero, Complex.real_smul]

/-- **The optional hull coupling under dilation** (`Sec7.Lemma725RefFull.IsOptionalHullCoupling.dilate`, with the
field written `affField 0`): for `c > 0`, `s = c^{-1/2}`, the dilated evolution `s (W, V, B)(c ·)` with lifetime `ζ/c`
and the field `h(· / s)` satisfy the frozen optional hull specification of the word `s (x_L; x_R)`. -/
theorem isOptionalHullCoupling_dilate_affField {Ω : Type u} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ : ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : ℝ≥0} (hc : c ≠ 0)
    (hs : 0 < (√(c : ℝ))⁻¹) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ (fun i => (√(c : ℝ))⁻¹ * xL i) (fun i => (√(c : ℝ))⁻¹ * xR i) ρL ρR P
      (dilFiltration c 𝓕) (dilProc c W) (fun i => dilProc c (VL i)) (fun i => dilProc c (VR i)) (dilProc c B)
      (fun ω => ζ ω / c) (fun ω => affField 0 hs (h ω)) := by
  have h1 := Sec7.Lemma725RefFull.IsOptionalHullCoupling.dilate hc hC
  simp only [dilField_eq_affField] at h1
  exact h1

end FlowDilate

end InteractingSLE
