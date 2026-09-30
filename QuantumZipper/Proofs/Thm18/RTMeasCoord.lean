import QuantumZipper.Proofs.Thm18.R18RTMeasDrv
import QuantumZipper.Proofs.Zipper.LocLenR2bReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS, part 1: Borel readings of the unzipped pieces from the data

For data `p = (c, w)` (circle coordinates, driver on `[0,∞)`), the unzipping of the pieces
`configOfData γ d` (with `πd d = p`) at a time `t ≥ 0` has circle coordinates

  `ucoord γ (readOffField d) (w ∘ dyNN) t`

(`ucoord_eq_coordsFull`): the unzipped field `h ∘ f_t⁻¹ + Q log |(f_t⁻¹)'|` (Sheffield,
arXiv:1012.4797, p. 26, "well defined by unzipping") read through the jointly measurable reverse
flow `G4Core.Psi` of the dyadic code of the driver (the D81/G4CMeas4 chain). This is
`G4Core.vcoord` with the field of the pieces (`readOffField`) in place of the reconstructed wedge
field. The rescaling (1.8) of a field by a scale `A` has circle coordinates `rescCoord γ x A`,
jointly measurable in `(x, A)` and depending on `x` only through its circle coordinates.

Own elementary bookkeeping (measurability the paper leaves implicit), copied from
`G4Core.measurable_vcoord` / `G4Core.vcoord_lcode` (G4CMeas4Fld.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core CoordsFull

/-- The data space `(circle coordinates, driver)`. -/
abbrev PX : Type := (ℕ → ℝ) × (ℝ≥0 → ℝ)

/-- Full data with the (unused) test-function pairings set to `0`. -/
def dfull (p : PX) : E6.FullData := ((p.1, fun _ => 0), p.2)

theorem measurable_dfull : Measurable dfull :=
  (measurable_fst.prodMk measurable_const).prodMk measurable_snd

theorem readOffField_dfull (d : E6.FullData) : readOffField (dfull (πd d)) = readOffField d := rfl

/-- The dyadic code of the driver. -/
def pcode (p : PX) : LCode := (p.1, fun n => p.2 (dyNN n))

theorem measurable_pcode : Measurable pcode :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd)

theorem pcode_πd (d : E6.FullData) : pcode (πd d) = lcode d := rfl

/-- The circle coordinates of the field `x` unzipped along the coded driver `a` at time `t`. -/
def ucoord (γ : ℝ) (x : FieldSample) (a : ℕ → ℝ) (t : ℝ) : ℕ → ℝ := fun i =>
  limUnder atTop (fun m => ∫ z, avgReg x m (Psi a t z) ∂circI i) +
    Qc γ * ∫ z, LD a t z ∂circI i

theorem measurable_ucoord (γ : ℝ) :
    Measurable fun q : (FieldSample × (ℕ → ℝ)) × ℝ => ucoord γ q.1.1 q.1.2 q.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  have hA : ∀ m : ℕ, StronglyMeasurable fun q : (FieldSample × (ℕ → ℝ)) × ℝ =>
      ∫ z, avgReg q.1.1 m (Psi q.1.2 q.2 z) ∂circI i := by
    intro m
    refine StronglyMeasurable.integral_prod_right' (f := fun p : ((FieldSample × (ℕ → ℝ)) × ℝ) × ℂ =>
      avgReg p.1.1.1 m (Psi p.1.1.2 p.1.2 p.2)) ?_
    refine ((measurable_avgReg m).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_Psi.comp (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))).stronglyMeasurable
  have hL : StronglyMeasurable fun q : (FieldSample × (ℕ → ℝ)) × ℝ =>
      ∫ z, LD q.1.2 q.2 z ∂circI i := by
    refine StronglyMeasurable.integral_prod_right' (f := fun p : ((FieldSample × (ℕ → ℝ)) × ℝ) × ℂ =>
      LD p.1.1.2 p.1.2 p.2) ?_
    exact (measurable_LD.comp (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hA).measurable.add (hL.measurable.const_mul _)

/-- **On good drivers at `t ≥ 0`, `ucoord` gives the circle coordinates of the unzipped field.** -/
theorem ucoord_eq_coordsFull (γ : ℝ) (x : FieldSample) {d : E6.FullData}
    (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t) :
    ucoord γ x (lcode d).2 t = coordsFull (unzippedField γ (x, F1.readDrv d.2) t) := by
  funext i
  have e : coordsFull (unzippedField γ (x, F1.readDrv d.2) t) i =
      evalReg x ((circI i).map (fwdMapInv (F1.readDrv d.2) t)) +
        Qc γ * ∫ z, Real.log ‖deriv (fwdMapInv (F1.readDrv d.2) t) z‖ ∂circI i := by
    simp only [coordsFull, unzippedField, coordChange]
  rw [e, evalReg_eq_code hp ht, logInt_eq_code hp ht]
  rfl

/-- A continuous driver is recovered from its values on `[0,∞)`. -/
theorem drvOfData_eq_readDrv {d : E6.FullData} (hc : Continuous d.2) :
    drvOfData d = F1.readDrv d.2 := by
  have hW : Continuous (drvOfData d) := by
    unfold drvOfData
    exact hc.comp (Continuous.subtype_mk (by fun_prop) _)
  have hW0 : ∀ s : ℝ, drvOfData d s = drvOfData d (s.toNNReal : ℝ) := by
    intro s
    simp only [drvOfData, Real.coe_toNNReal', max_eq_left (le_max_right s 0)]
  have e : (fun r : ℝ≥0 => drvOfData d r) = d.2 := by
    funext r
    simp only [drvOfData]
    simp
    rfl
  have h := F1.readDrv_eq hW hW0
  rw [e] at h
  exact h.symm

/-- The field unzipped from the data, in terms of `ucoord`. -/
theorem coordsFull_unzipped_configOfData (γ : ℝ) {d : E6.FullData} (hc : Continuous d.2)
    (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t) :
    coordsFull (unzippedField γ (configOfData γ d).toPair t) =
      ucoord γ (readOffField (dfull (πd d))) (pcode (πd d)).2 t := by
  rw [readOffField_dfull, pcode_πd, ucoord_eq_coordsFull γ _ hp ht]
  show coordsFull (unzippedField γ (readOffField d, drvOfData d) t) = _
  rw [drvOfData_eq_readDrv hc]

/-! ## The rescaling (1.8) on circle coordinates -/

/-- The circle coordinates of the rescaled field `x(A·) + Q log A`. -/
def rescCoord (γ : ℝ) (x : FieldSample) (A : ℝ) : ℕ → ℝ :=
  coordsFull (rescale x (Qc γ) A)

theorem rescCoord_congr (γ : ℝ) {x x' : FieldSample} (h : coordsFull x = coordsFull x') (A : ℝ) :
    rescCoord γ x A = rescCoord γ x' A := by
  funext i
  simp only [rescCoord, coordsFull, rescale, coordChange, NuMeas.evalReg_congr_coordsFull h]

theorem measurable_rescCoord (γ : ℝ) :
    Measurable fun q : FieldSample × ℝ => rescCoord γ q.1 q.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  have hd : ∀ (A : ℝ) (z : ℂ), deriv (fun w : ℂ => (A : ℂ) * w) z = (A : ℂ) := by
    intro A z; simp
  have hmA : ∀ A : ℝ, Measurable fun w : ℂ => (A : ℂ) * w := fun A => measurable_const.mul measurable_id
  have e : (fun q : FieldSample × ℝ => rescCoord γ q.1 q.2 i) = fun q =>
      limUnder atTop (fun k => ∫ z, avgReg q.1 k ((q.2 : ℂ) * z) ∂circI i) +
        Qc γ * ∫ _z, Real.log ‖(q.2 : ℂ)‖ ∂circI i := by
    funext q
    simp only [rescCoord, coordsFull, rescale, coordChange, hd, evalReg]
    congr 2
    funext k
    exact integral_map (hmA q.2).aemeasurable
      ((measurable_avgReg k).comp (f := fun w : ℂ => (q.1, w))
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [e]
  have hA : ∀ k : ℕ, StronglyMeasurable fun q : FieldSample × ℝ =>
      ∫ z, avgReg q.1 k ((q.2 : ℂ) * z) ∂circI i := by
    intro k
    refine StronglyMeasurable.integral_prod_right' (f := fun p : (FieldSample × ℝ) × ℂ =>
      avgReg p.1.1 k ((p.1.2 : ℂ) * p.2)) ?_
    exact ((measurable_avgReg k).comp ((measurable_fst.comp measurable_fst).prodMk
      ((Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).mul
        measurable_snd))).stronglyMeasurable
  have hL : Measurable fun q : FieldSample × ℝ => ∫ _z, Real.log ‖(q.2 : ℂ)‖ ∂circI i := by
    simp only [integral_const, smul_eq_mul]
    exact measurable_const.mul
      (Real.measurable_log.comp (Complex.measurable_ofReal.comp measurable_snd).norm)
  exact (StronglyMeasurable.limUnder hA).measurable.add (hL.const_mul _)

end RTMeas
end R18
end QuantumZipper
