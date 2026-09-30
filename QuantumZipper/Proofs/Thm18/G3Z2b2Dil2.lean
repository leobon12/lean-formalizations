import QuantumZipper.Proofs.Thm18.G3Z2b2Dil
import QuantumZipper.Proofs.Thm18.G1Z2MeasScale
import QuantumZipper.Proofs.Thm18.R18G3Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (9): the dilation step for the two-point Palm-window integral of `G3TCurveStmt`

`wedgePalm2_rescale`: the joint Palm-window integrand of `g3zWedgePalmCyl` (zoom at `x` through
`g true x`, zoom at the length partner `R(x)` through `g false (R(x))`) for the dilated field
`rescale y Q b` equals that of `y` through the target-dilated maps `b · g true (x/b)` and
`b · g false (R(x)/b)`. The length partner is dilation covariant:
`R_{rescale y Q b}(x/b) = R_y(x)/b` (`g3zPartner_rescale`, from
`GoodTransforms.qBoundaryMeasure_rescale` and `g1z2_lenRight_map_div`). With
`b = scaleParam γ W` this passes the integral of `wedgeRep = canonical W` to the unscaled wedge
`W`. Own bookkeeping (as `wedgePalm_rescale`).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus

theorem g3zPartner_rescale {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} (hy : IsLQGGood γ y) {b : ℝ}
    (hb : 0 < b) (x : ℝ) :
    R18.g3zPartner γ (rescale y (Qc γ) b) (x / b) = R18.g3zPartner γ y x / b := by
  have hν' := GoodTransforms.qBoundaryMeasure_rescale hy hγ hb
  have hmeas : Measurable fun u : ℝ => u / b := measurable_id.div_const b
  have hseg : (qBoundaryMeasure γ y).map (fun u => u / b) (Icc (x / b) 0) =
      qBoundaryMeasure γ y (Icc x 0) := by
    rw [Measure.map_apply hmeas measurableSet_Icc]
    have := preimage_div_seg hb true x
    simp only [g1SideSeg, ite_true] at this
    rw [this]
  unfold R18.g3zPartner
  rw [hν', hseg, g1z2_lenRight_map_div _ hb]

/-- **The joint Palm-window integral of a dilated field through the curve maps.** -/
theorem wedgePalm2_rescale {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} (hy : IsLQGGood γ y) {b : ℝ}
    (hb : 0 < b) (U L : ℝ) (s t : Set LawD) (g : Bool → ℝ → ℂ → ℂ)
    (hg : ∀ side x, Measurable (g side x))
    (hreg1 : ∀ x ∈ g1SideHalf true, DilReg γ y b x (g true (x / b)))
    (hreg2 : ∀ x ∈ g1SideHalf true,
      DilReg γ y b (R18.g3zPartner γ y x) (g false (R18.g3zPartner γ y x / b))) :
    ∫⁻ x in g1zWedgeWin γ true (rescale y (Qc γ) b) U,
        s.indicator 1 (WedgeMeas.dataFull H (canonical γ
          (zoomFieldVia γ L (rescale y (Qc γ) b) x (g true x)))) *
        t.indicator 1 (WedgeMeas.dataFull H (canonical γ
          (zoomFieldVia γ L (rescale y (Qc γ) b) (R18.g3zPartner γ (rescale y (Qc γ) b) x)
            (g false (R18.g3zPartner γ (rescale y (Qc γ) b) x)))))
        ∂((qBoundaryMeasure γ (rescale y (Qc γ) b)).restrict (g1SideHalf true)) =
      ∫⁻ x in g1zWedgeWin γ true y U,
        s.indicator 1 (WedgeMeas.dataFull H (canonical γ
          (zoomFieldVia γ L y x (fun w => (b : ℂ) * g true (x / b) w)))) *
        t.indicator 1 (WedgeMeas.dataFull H (canonical γ
          (zoomFieldVia γ L y (R18.g3zPartner γ y x)
            (fun w => (b : ℂ) * g false (R18.g3zPartner γ y x / b) w))))
        ∂((qBoundaryMeasure γ y).restrict (g1SideHalf true)) := by
  set ν := qBoundaryMeasure γ y with hν
  have hν' : qBoundaryMeasure γ (rescale y (Qc γ) b) = ν.map fun u => u / b :=
    GoodTransforms.qBoundaryMeasure_rescale hy hγ hb
  have hdiv : (fun u : ℝ => u / b) = fun u => u * b⁻¹ := funext fun u => div_eq_mul_inv u b
  have hemb : MeasurableEmbedding fun u : ℝ => u / b := by
    rw [hdiv]; exact (MeasurableEquiv.mulRight₀ b⁻¹ (inv_ne_zero hb.ne')).measurableEmbedding
  have hwin : (fun u : ℝ => u / b) ⁻¹' g1zWedgeWin γ true (rescale y (Qc γ) b) U =
      g1zWedgeWin γ true y U := by
    ext u
    show (u / b ∈ g1SideHalf true ∧ qBoundaryMeasure γ (rescale y (Qc γ) b)
        (g1SideSeg true (u / b)) ≤ ENNReal.ofReal U) ↔
      (u ∈ g1SideHalf true ∧ ν (g1SideSeg true u) ≤ ENNReal.ofReal U)
    rw [hν', hemb.map_apply, preimage_div_seg hb]
    exact and_congr_left' (Set.ext_iff.1 (preimage_div_half hb true) u)
  have hhalf : MeasurableSet (g1SideHalf true) := measurableSet_Iio
  have hpart : ∀ x, R18.g3zPartner γ (rescale y (Qc γ) b) (x / b) =
      R18.g3zPartner γ y x / b := g3zPartner_rescale hγ hy hb
  rw [hν', hemb.restrict_map, hemb.restrict_map, hemb.lintegral_map, preimage_div_half hb, hwin]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (s := g1zWedgeWin γ true y U) (ae_restrict_mem hhalf)]
    with x hx
  have hR : R18.g3zPartner γ y x / b * b = R18.g3zPartner γ y x := by field_simp
  rw [hpart x, canonical_zoomFieldVia_rescale y hb L x (hg _ _) (hreg1 x hx)]
  have e2 := canonical_zoomFieldVia_rescale y hb L (R18.g3zPartner γ y x) (hg false _)
    (hreg2 x hx)
  rw [e2]

end G3Z2b2
end Thm18Asm
end QuantumZipper
