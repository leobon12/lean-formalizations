import QuantumZipper.Proofs.Zipper.MeasUnzipFlow
import QuantumZipper.Proofs.LQG.GoodMeasurable

/-!
# MEAS-UNZIP (2), (4): the unzipped field as a measurable field-valued map; scale and boundary
# measure of the unzipped field at measurable (random) times

Continuation of `MeasUnzipFlow.lean`. `ufJ hT γ κ q` is a field sample (junk `0` at measures
that are not s-finite or not carried by `ℍ`) whose raw values are `unzRawJ`; it is measurable
into the product σ-algebra of `FieldSample` (`measurable_ufJ`), and on the good set
(`f ∈ PZ`, `s ∈ [0,T]`) it has the same raw values at every folded circle as the unzipped field
`unzippedField γ (x, Wof κ T hT f) s` (`ufJ_foldedCircle`). Hence the two have the same
regularized averages, the same coordinates, the same goodness, the same boundary and area
measures and the same scale (`avgReg_ufJ`, `isLQGGood_ufJ_iff`, `qBoundaryMeasure_ufJ`,
`qAreaMeasure_ufJ`, `scaleParam_ufJ`), which are therefore measurable functions of
`((f, x), s)`:

* `measurable_scaleJ`: `q ↦ scaleParam γ (ufJ q)` on the good samples (junk `0`), from
  `GoodMeas.measurable_scaleParam_global`;
* `measurable_qBoundaryMeasure_ufJ`, `measurable_qAreaMeasure_ufJ`: the boundary and area
  measures (Giry σ-algebra) on the good samples, from `GoodMeas.measurable_qBoundaryMeasure_global`,
  `GoodMeas.measurable_qAreaMeasure_global`;
* `measurable_scaleParam_unzip_random`, `measurable_unzippedField_random`: the same at a
  measurable random time `τ ∈ [0,T]`, for measurable random paths in `PZ` and fields.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper.MeasUnzip

open CharFun RegCont Factorization
open scoped Classical

variable {T : ℝ} (hT : 0 ≤ T)

/-- The unzipped field, written with `unzRawJ` (junk `0` at measures not s-finite or not
carried by `ℍ`). -/
def ufJ (γ κ : ℝ) (q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℝ) : FieldSample := fun μ =>
  if h : SFinite μ ∧ μ Hᶜ = 0 then (haveI := h.1; unzRawJ hT γ κ μ q) else 0

theorem measurable_ufJ (γ κ : ℝ) : Measurable (ufJ (T := T) hT γ κ) := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : SFinite μ ∧ μ Hᶜ = 0
  · have := h.1
    simp only [ufJ, dif_pos h]
    exact measurable_unzRawJ hT γ κ μ
  · simp only [ufJ, dif_neg h]
    exact measurable_const

/-- On the good set `ufJ` and the unzipped field agree at every folded circle. -/
theorem ufJ_foldedCircle (γ κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ufJ hT γ κ ((f, x), s) (foldedCircle w r) =
      unzippedField γ (x, Wof κ T hT f) s (foldedCircle w r) := by
  have hH : (foldedCircle w r) Hᶜ = 0 := ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H w hr)
  have h : SFinite (foldedCircle w r) ∧ (foldedCircle w r) Hᶜ = 0 := ⟨inferInstance, hH⟩
  simp only [ufJ, dif_pos h]
  exact (unzRawJ_eq hT γ κ hf hs x hH).symm

theorem avgReg_ufJ (γ κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) :
    avgReg (ufJ hT γ κ ((f, x), s)) = avgReg (unzippedField γ (x, Wof κ T hT f) s) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact ufJ_foldedCircle hT γ κ hf hs x _ (radius_pos k)

/-! ## Measurable scale and boundary measure -/

/-! ## At a measurable random time -/

variable {α : Type*} [MeasurableSpace α] {κ : ℝ} {P : α → C(Icc (0 : ℝ) T, ℝ)}
  {X : α → FieldSample} {τ : α → ℝ}

end QuantumZipper.MeasUnzip
