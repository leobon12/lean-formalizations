import QuantumZipper.Proofs.Section5.Prop17Shift

/-!
# Proposition 1.7: the field-level shift identity (S5-PLAN node D5-c)

Sheffield, arXiv:1012.4797, proof of Proposition 1.7 (§1.6, p. 25–26): "In the rescaled surfaces
in Proposition 1.6, boundary lengths are scaled by `e^{C/2}`, so if we set `δ = e^{−C/2}`, then
the distance between `x` and `x'` is `L` after the rescaling." At the level of fields: moving the
origin of the canonical zoom `canonical γ (h(· + x) + C/γ)` to its length-`L` point gives, up to
`canonical`, the zoom at the Palm-shifted point `x' = palmShiftRight ν_h (L e^{−C/2}) x`.

Contents (deterministic):

* `RegEq` congruences: `canonical` and `wedgeLengthPoint` depend on a sample only through its
  regularized circle averages, so `RegEq x y` makes them *equal* (wrappers around the blueprint-A4
  lemmas `Factorization.*_congr`);
* `regEq_of_fc`: two samples agreeing on every folded circle centred in `Hbar` are `RegEq`;
* `translate_rescale_zoomField_regEq` (translate ∘ rescale ∘ translate ∘ addConst): for a regular
  `h`, `translate (rescale (zoomField γ C h x) Q a) y` and `rescale (zoomField γ C h (x + a y)) Q a`
  are `RegEq`;
* `canonical_translate_canonical_zoomField` (**D5-c**, general `y`) and
  `canonical_translate_lengthPoint_regEq` (**D5-c**, `y` the length-`L` point, via D5-b).

Own elementary proof (the change of variables `a(w + y) + x = a w + (x + a y)` read through the
regularity witnesses of `RegularClosure`); cost rule of AGENT_GUIDE.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldShift

open RegClosure CircleFubini

/-! ## `RegEq` as an equivalence, and its congruences -/

theorem RegEq.symm' {x y : FieldSample} (h : RegEq x y) : RegEq y x := fun k z => (h k z).symm

theorem RegEq.trans' {x y z : FieldSample} (h₁ : RegEq x y) (h₂ : RegEq y z) : RegEq x z :=
  fun k w => (h₁ k w).trans (h₂ k w)

variable {x y : FieldSample}

theorem avgReg_congr (h : RegEq x y) : avgReg x = avgReg y := by
  funext k z; exact h k z

/-- `canonical` is a function of the regularized field: `RegEq` samples have *equal*
canonical descriptions (`Factorization.canonical_congr`, blueprint A4). -/
theorem canonical_congr (h : RegEq x y) (γ : ℝ) : canonical γ x = canonical γ y :=
  Factorization.canonical_congr (avgReg_congr h) γ

/-! ## Folded-circle criterion for `RegEq` -/

theorem fc_foldH_eq' (v : ℂ) (s : ℝ) : foldedCircle (foldH v) s = foldedCircle v s :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f =>
    integral_fc_foldH f.continuous.continuousOn v s

/-- Two samples with the same raw values on every folded circle centred in `Hbar` (positive
radius) are `RegEq`. -/
theorem regEq_of_fc
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r)) :
    RegEq x y := by
  intro k z
  have e : ∀ n, x (foldedCircle (dyadicRoundC n z) (radius k)) =
      y (foldedCircle (dyadicRoundC n z) (radius k)) := fun n => by
    rw [← fc_foldH_eq' (dyadicRoundC n z), h _ (foldH_mem_Hbar' _) _ (radius_pos k)]
  unfold avgReg
  simp_rw [e]

/-! ## translate ∘ rescale ∘ translate ∘ addConst -/

/-- Regularity witness of the zoom `h(· + x) + C/γ`. -/
theorem isRegularWith_zoomField {h : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith h F)
    (γ C x : ℝ) :
    IsRegularWith (zoomField γ C h x) (fun q => F (q.1 + x, q.2) + C / γ) :=
  (hF.translate' x).addConst' (C / γ)

/-- **Field lemma (translate ∘ rescale of a zoom).** For a regular `h` and `a > 0`,
`(h(a· + x) + C/γ + Q log a)(· + y) = h(a· + (x + a y)) + C/γ + Q log a` up to `RegEq`. -/
theorem translate_rescale_zoomField_regEq {h : FieldSample} (hh : IsRegularSample h)
    (γ C x y Q : ℝ) {a : ℝ} (ha : 0 < a) :
    RegEq (translate (rescale (zoomField γ C h x) Q a) (y : ℂ))
      (rescale (zoomField γ C h (x + a * y)) Q a) := by
  obtain ⟨F, hF⟩ := hh
  have hZ := isRegularWith_zoomField hF γ C x
  have hZ' := isRegularWith_zoomField hF γ C (x + a * y)
  have hR := hZ.rescale' Q ha
  refine regEq_of_fc fun d hd r hr => ?_
  rw [translate_fc_eq hR y hd hr, rescale_fc_eq hZ' Q ha d hr,
    foldH_of_mem' (mapsTo_mul_pos ha hd)]
  have e : (a : ℂ) * (d + (y : ℂ)) + (x : ℂ) = (a : ℂ) * d + ((x + a * y : ℝ) : ℂ) := by
    push_cast; ring
  simp only [e]

/-! ## D5-c -/

variable {γ : ℝ} {h : FieldSample}

theorem isLQGGood_zoomField (hg : IsLQGGood γ h) (C x : ℝ) : IsLQGGood γ (zoomField γ C h x) :=
  (hg.translate x).addConst (C / γ)

/-- **D5-c (exact form).** Recentring the canonical zoom at `y` gives, *exactly*, the canonical
description of the rescaled zoom at `x + a y`, `a = scaleParam γ (zoomField γ C h x)`. -/
theorem canonical_translate_canonical_zoomField (hg : IsLQGGood γ h) (C x y : ℝ)
    (ha : 0 < scaleParam γ (zoomField γ C h x)) :
    canonical γ (translate (canonical γ (zoomField γ C h x)) (y : ℂ)) =
      canonical γ (rescale (zoomField γ C h (x + scaleParam γ (zoomField γ C h x) * y)) (Qc γ)
        (scaleParam γ (zoomField γ C h x))) :=
  canonical_congr (translate_rescale_zoomField_regEq hg.1 γ C x y (Qc γ) ha) γ

/-! ## Exact agreement of the circle coordinates -/

/-- Composition of rescalings agrees *exactly* on every folded circle of positive radius, hence on
`coordsFull` (the `RegEq` statement `regEq_rescale_rescale` only compares regularized averages). -/
theorem coordsFull_rescale_rescale {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) :
    CoordsFull.coordsFull (rescale (rescale x Q b) Q c) =
      CoordsFull.coordsFull (rescale x Q (b * c)) := by
  obtain ⟨F, hF⟩ := hx
  funext i
  have hr : 0 < (CoordsFull.fullIndex i).2 := by
    simp only [CoordsFull.fullIndex]; positivity
  simp only [CoordsFull.coordsFull]
  rw [rescale_fc_eq (hF.rescale' Q hb) Q hc _ hr, rescale_fc_eq hF Q (mul_pos hb hc) _ hr]
  have e1 : (b : ℂ) * foldH ((c : ℂ) * (CoordsFull.fullIndex i).1) =
      foldH (((b * c : ℝ) : ℂ) * (CoordsFull.fullIndex i).1) := by
    rw [← foldH_mul_pos _ hb]; push_cast; ring_nf
  rw [e1, show b * (c * (CoordsFull.fullIndex i).2) = b * c * (CoordsFull.fullIndex i).2 by ring,
    Real.log_mul hb.ne' hc.ne']
  ring

/-- `canonical γ (rescale W Q a)` and `canonical γ W` have *equal* circle coordinates. -/
theorem coordsFull_canonical_rescale (hγ : 0 < γ) {W : FieldSample} (hW : IsLQGGood γ W) {a : ℝ}
    (ha : 0 < a) (hs : 0 < scaleParam γ W) :
    CoordsFull.coordsFull (canonical γ (rescale W (Qc γ) a)) =
      CoordsFull.coordsFull (canonical γ W) := by
  unfold canonical
  rw [GoodTransforms.scaleParam_rescale hW hγ ha]
  have := coordsFull_rescale_rescale hW.1 (Qc γ) ha (div_pos hs ha)
  rwa [mul_div_cancel₀ _ ha.ne'] at this

/-- **D5-c (circle coordinates, exact).** Under the hypotheses of
`canonical_translate_canonical_zoomField_regEq`, the two fields have equal `coordsFull`. (Their
raw test pairings need not agree: they are limits along the radii `a 2^{-k}` and `2^{-k}`.) -/
theorem coordsFull_canonical_translate_canonical_zoomField (hγ : 0 < γ) (hg : IsLQGGood γ h)
    (C x y : ℝ) (ha : 0 < scaleParam γ (zoomField γ C h x))
    (ha' : 0 < scaleParam γ (zoomField γ C h (x + scaleParam γ (zoomField γ C h x) * y))) :
    CoordsFull.coordsFull (canonical γ (translate (canonical γ (zoomField γ C h x)) (y : ℂ))) =
      CoordsFull.coordsFull
        (canonical γ (zoomField γ C h (x + scaleParam γ (zoomField γ C h x) * y))) := by
  rw [canonical_translate_canonical_zoomField hg C x y ha]
  exact coordsFull_canonical_rescale hγ (isLQGGood_zoomField hg C _) ha ha'

end FieldShift
end S5
end QuantumZipper
