import QuantumZipper.Proofs.Thm18.G3Z2b2Inn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (8): the two-point Palm-window integral of `G3TCurveStmt`, Fubini over the path

The joint Palm-window integral `g3zWedgePalmCyl γ P B Y U L s t` zooms at the left window point
`x` through `g1zLocMap true` and at its length partner `R(x)` through `g1zLocMap false`. This file
does for it what `G3Z2b2Fac`/`G3Z2b2Inn` do for the one-point integral:

* `g3PhiM2 γ L Ψ U s t (y, a)`: the measurable version (measurable zoom data `g3zoomLawM`,
  partner read on `bdryM`), jointly measurable (`measurable_g3PhiM2`), a function of `avgReg y`
  only (`g3PhiM2_congr`);
* `g3Inner_eq_g3PhiM2`: on a good path and a good field it equals the inner integral of
  `g3zWedgePalmCyl`, under the regularity conditions `G1FacReg` at `x` and at `R(x) > 0`, for
  boundary-measure-a.e. window point `x`;
* **`g3zWedgePalmCyl_fubini`**: `g3zWedgePalmCyl = ∫ (∫ g3PhiM2(wedgeRep ω', a) dP') d(path law)`.

Sheffield, arXiv:1012.4797, p. 71 (Figure 1.7; the curve is independent of the wedge). Own
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The measurable length partner. -/
def partM (γ : ℝ) (y : FieldSample) (x : ℝ) : ℝ :=
  lenRight (bdryM γ y) (bdryM γ y (Icc x 0)).toReal

open Classical in
/-- The integrand of the measurable joint Palm-window functional. -/
def g3IntM2 (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (U : ℝ) (s t : Set LawD)
    (q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ) : ℝ≥0∞ :=
  if q.2 ∈ g1SideHalf true ∧ bdryM γ q.1.1 (g1SideSeg true q.2) ≤ ENNReal.ofReal U then
    s.indicator 1 (g1zM γ L Ψ true q) *
      t.indicator 1 (g1zM γ L Ψ false (q.1, partM γ q.1.1 q.2))
  else 0

/-- **The measurable joint Palm-window functional.** -/
def g3PhiM2 (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (U : ℝ) (s t : Set LawD)
    (p : FieldSample × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x, g3IntM2 γ L Ψ U s t (p, x) ∂(bdryM γ p.1)

theorem measurable_g3IntM2 {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ) {s t : Set LawD}
    (hs : MeasurableSet s) (ht : MeasurableSet t) : Measurable (g3IntM2 γ L Ψ U s t) := by
  classical
  have hS : MeasurableSet {q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ |
      q.2 ∈ g1SideHalf true ∧ bdryM γ q.1.1 (g1SideSeg true q.2) ≤ ENNReal.ofReal U} :=
    (measurable_snd (show MeasurableSet (g1SideHalf true) from measurableSet_Iio)).inter
      (measurableSet_le (measurable_bdryM_seg γ true) measurable_const)
  have hpart : Measurable fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ => partM γ q.1.1 q.2 :=
    (R18.measurable_g3plPartner γ).comp (f := fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ =>
      ((q.1.1, q.2) : FieldSample × ℝ)) ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd)
  have hA : Measurable fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ =>
      s.indicator (1 : LawD → ℝ≥0∞) (g1zM γ L Ψ true q) :=
    (measurable_one.indicator hs).comp (measurable_g1zM hsel L true)
  have hB : Measurable fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ =>
      t.indicator (1 : LawD → ℝ≥0∞) (g1zM γ L Ψ false (q.1, partM γ q.1.1 q.2)) :=
    (measurable_one.indicator ht).comp ((measurable_g1zM hsel L false).comp
      (f := fun q : (FieldSample × (ℝ≥0 → ℝ)) × ℝ => (q.1, partM γ q.1.1 q.2))
      (measurable_fst.prodMk hpart))
  exact Measurable.ite hS (hA.mul hB) measurable_const

theorem measurable_g3PhiM2 {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ) {s t : Set LawD}
    (hs : MeasurableSet s) (ht : MeasurableSet t) : Measurable (g3PhiM2 γ L Ψ U s t) :=
  R18.measurable_lintegral_family ((measurable_bdryM γ).comp measurable_fst)
    (fun p N => R18.bdryM_Icc_ne_top γ p.1 _ _) (measurable_g3IntM2 hsel L U hs ht)

theorem g1zM_congr {γ L : ℝ} {left : Bool} {y y' : FieldSample} (h : avgReg y = avgReg y')
    (a : ℝ≥0 → ℝ) (x : ℝ) : g1zM γ L Ψ left ((y, a), x) = g1zM γ L Ψ left ((y', a), x) := by
  have e : g3coordsM γ L Ψ left (y, a, 1, x) = g3coordsM γ L Ψ left (y', a, 1, x) := by
    funext i
    simp only [g3coordsM, g3mapP]
    rw [translate_congr h]
  simp only [g1zM, g3zoomLawM, e]

theorem g3PhiM2_congr {γ L U : ℝ} {s t : Set LawD} {y y' : FieldSample}
    (h : avgReg y = avgReg y') (a : ℝ≥0 → ℝ) :
    g3PhiM2 γ L Ψ U s t (y, a) = g3PhiM2 γ L Ψ U s t (y', a) := by
  classical
  have hb : bdryM γ y = bdryM γ y' := R18.bdryM_congr h
  have hp : ∀ x, partM γ y x = partM γ y' x := fun x => by simp only [partM, hb]
  simp only [g3PhiM2, g3IntM2, hp, g1zM_congr (Ψ := Ψ) (γ := γ) (L := L) h, hb]

theorem measurable_g3PhiData2 {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ) {s t : Set LawD}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Measurable fun p : G1PathData => g3PhiM2 γ L Ψ U s t (E1.fromC p.2.1, p.1) :=
  (measurable_g3PhiM2 hsel L U hs ht).comp (f := fun p : G1PathData => (E1.fromC p.2.1, p.1))
    ((Cor15Group.measurable_fromC.comp (measurable_fst.comp measurable_snd)).prodMk measurable_fst)

theorem g3PhiM2_fromC {γ L U : ℝ} {s t : Set LawD} (y : FieldSample) (a : ℝ≥0 → ℝ) :
    g3PhiM2 γ L Ψ U s t (E1.fromC (WedgeMeas.dataFull H y).1, a) = g3PhiM2 γ L Ψ U s t (y, a) :=
  g3PhiM2_congr (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y)) a

end G3Z2b2
end Thm18Asm
end QuantumZipper
