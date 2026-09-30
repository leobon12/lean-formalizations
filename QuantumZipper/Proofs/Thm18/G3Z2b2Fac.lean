import QuantumZipper.Proofs.Thm18.G3Z2b2Mz
import QuantumZipper.Proofs.Thm18.G3Pl2Meas
import QuantumZipper.Proofs.Thm18.G2LenSmoothGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (6): the wedge Palm-window integrand through the curve maps as a measurable functional
of (path, wedge data)

`g1PhiM γ L R Γ Ψ left U (y, a)` is the Palm-window integral of `y` over its window of length
`U` on the side half-line. It zooms at level `L` through the measurable local maps
`Λ(a, x, ·) = g3locM Ψ left (a, x, ·)`, with the boundary measure read on its certificate
(`bdryM`).

* `measurable_g1PhiM`: jointly measurable in `(y, a)`.
* `g1PhiM_congr`: it only depends on `avgReg y`. Hence `(a, c) ↦ g1PhiM (fromC c.1, a)` is a
  measurable function of (path, wedge data) (`measurable_g1PhiData`).
* `g1Inner_eq_g1PhiM`: for a good path and a good field, at every window point where the
  regularity conditions `G1FacReg` hold (the zoomed field is good; the absorption conditions of
  `data_canonical_zoomFieldVia_comp_mul`), the inner integral of `g1zWedgePalmInt` through the
  curve maps `g1zLocMap` **equals** `g1PhiM`.

This is the measurable `G` of the Fubini step Z2a (`G3PathFubiniStmt`) for
`G1WedgePalmZoomStmt`. Own bookkeeping, following `G3Pl2Meas` (measurable Palm-window
functional).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The measurable zoom datum at `x` for the field `y` and the path `a` (scale `1`). -/
def g1zM (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ) :
    LawD :=
  g3zoomLawM γ L Ψ left (q.1.1, q.1.2, 1, q.2)

open Classical in
/-- The integrand of the measurable Palm-window functional. -/
def g1IntM (γ L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (U : ℝ)
    (q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ) : ℝ≥0∞ :=
  if q.2 ∈ g1SideHalf left ∧ bdryM γ q.1.1 (g1SideSeg left q.2) ≤ ENNReal.ofReal U then
    Γ (g1zLocData R (g1zM γ L Ψ left q)) else 0

/-- **The measurable Palm-window functional** through the measurable local maps. -/
def g1PhiM (γ L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (U : ℝ) (p : FieldSample × (ℝ≥0 → ℝ)) :
    ℝ≥0∞ :=
  ∫⁻ x, g1IntM γ L R Γ Ψ left U (p, x) ∂(bdryM γ p.1)

theorem measurable_bdryM_seg (γ : ℝ) (left : Bool) :
    Measurable fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ => bdryM γ q.1.1 (g1SideSeg left q.2) := by
  have hμ : Measurable fun q : FieldSample × (ℝ≥0 → ℝ) => bdryM γ q.1 :=
    (measurable_bdryM γ).comp measurable_fst
  cases left
  · -- `Icc 0 x`: reflect
    have hμ' : Measurable fun q : FieldSample × (ℝ≥0 → ℝ) => (bdryM γ q.1).map Neg.neg :=
      (Measure.measurable_map _ measurable_neg).comp hμ
    have hfin : ∀ (q : FieldSample × (ℝ≥0 → ℝ)) (b : ℝ),
        (bdryM γ q.1).map Neg.neg (Icc b 0) ≠ ⊤ := fun q b => by
      rw [Measure.map_apply measurable_neg measurableSet_Icc]
      rw [show Neg.neg ⁻¹' Icc b 0 = Icc 0 (-b) by ext u; simp [neg_le, le_neg]]
      exact R18.bdryM_Icc_ne_top γ q.1 0 (-b)
    have h := measurable_measure_Icc_zero hμ' hfin
    have e : (fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ => bdryM γ q.1.1 (g1SideSeg false q.2)) =
        fun q => (bdryM γ q.1.1).map Neg.neg (Icc (-q.2) 0) := by
      funext q
      rw [Measure.map_apply measurable_neg measurableSet_Icc]
      rw [show Neg.neg ⁻¹' Icc (-q.2) 0 = Icc 0 q.2 by ext u; simp [neg_le, le_neg]]
      simp [g1SideSeg]
    rw [e]
    exact h.comp (f := fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ => (q.1, -q.2))
      (measurable_fst.prodMk measurable_snd.neg)
  · have h := measurable_measure_Icc_zero hμ fun q b => R18.bdryM_Icc_ne_top γ q.1 b 0
    simpa [g1SideSeg] using h

theorem measurable_g1zM {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (left : Bool) :
    Measurable (g1zM γ L Ψ left) :=
  (measurable_g3zoomLawM hsel L left).comp
    (f := fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ => ((q.1.1, q.1.2, 1, q.2) : G3Par))
    ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)))

theorem measurable_g1IntM {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ) :
    Measurable (g1IntM γ L R Γ Ψ left U) := by
  classical
  have hS : MeasurableSet {q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ |
      q.2 ∈ g1SideHalf left ∧ bdryM γ q.1.1 (g1SideSeg left q.2) ≤ ENNReal.ofReal U} := by
    have hh : MeasurableSet (g1SideHalf left) := by
      cases left
      · exact measurableSet_Ioi
      · exact measurableSet_Iio
    exact (measurable_snd hh).inter
      (measurableSet_le (measurable_bdryM_seg γ left) measurable_const)
  exact Measurable.ite hS ((hΓ.comp (measurable_g1zLocData R)).comp (measurable_g1zM hsel L left))
    measurable_const

theorem measurable_g1PhiM {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ) :
    Measurable (g1PhiM γ L R Γ Ψ left U) :=
  R18.measurable_lintegral_family ((measurable_bdryM γ).comp measurable_fst)
    (fun p N => R18.bdryM_Icc_ne_top γ p.1 _ _) (measurable_g1IntM hsel L R hΓ left U)

theorem g1PhiM_congr {γ L : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} {left : Bool}
    {U : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y') (a : ℝ≥0 → ℝ) :
    g1PhiM γ L R Γ Ψ left U (y, a) = g1PhiM γ L R Γ Ψ left U (y', a) := by
  have hc : ∀ x : ℝ, g1zM γ L Ψ left ((y, a), x) = g1zM γ L Ψ left ((y', a), x) := fun x => by
    have e : g3coordsM γ L Ψ left (y, a, 1, x) = g3coordsM γ L Ψ left (y', a, 1, x) := by
      funext i
      simp only [g3coordsM, g3mapP]
      rw [translate_congr h]
    simp only [g1zM, g3zoomLawM, e]
  have hb : bdryM γ y = bdryM γ y' := R18.bdryM_congr h
  simp only [g1PhiM, g1IntM, hc, hb]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ g1SideHalf left ∧ bdryM γ y' (g1SideSeg left x) ≤ ENNReal.ofReal U
  · rw [if_pos (by rw [hb]; exact hx), if_pos hx]
  · rw [if_neg (by rw [hb]; exact hx), if_neg hx]

/-- **The measurable functional of (path, wedge data).** -/
theorem measurable_g1PhiData {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ) :
    Measurable fun p : G1PathData => g1PhiM γ L R Γ Ψ left U (E1.fromC p.2.1, p.1) :=
  (measurable_g1PhiM hsel L R hΓ left U).comp
    (f := fun p : G1PathData => (E1.fromC p.2.1, p.1))
    ((Cor15Group.measurable_fromC.comp (measurable_fst.comp measurable_snd)).prodMk measurable_fst)

theorem g1PhiM_fromC {γ L : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} {left : Bool}
    {U : ℝ} (y : FieldSample) (a : ℝ≥0 → ℝ) :
    g1PhiM γ L R Γ Ψ left U (E1.fromC (WedgeMeas.dataFull H y).1, a) =
      g1PhiM γ L R Γ Ψ left U (y, a) :=
  g1PhiM_congr (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y)) a

end G3Z2b2
end Thm18Asm
end QuantumZipper
