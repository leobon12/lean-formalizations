import QuantumZipper.Proofs.Thm18.G3Reduce
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.Proofs.Section5.Prop16MeasCoords

/-!
# G3 concrete scheme (part 2): the measurable maps (M1 lengths and points, M2 zooms)

Deterministic, measurable building blocks of the concrete G3 scheme (Sheffield,
arXiv:1012.4797, proof of Theorem 1.8, §5.4, pp. 70–71, and Figure 1.7):

* `bdryM γ y`: the boundary measure `qBoundaryMeasure γ y` on the countable certificate `BCert`
  for the existence of its vague limit (junk `0` off it); Giry-measurable
  (`E1.M4.measurable_qBoundaryMeasure_bCert`). Unlike the `IsLQGGood` guard, `BCert` does not
  ask for regularity of `y`, so it does not discard the junk-extended region fields.
* `lenLeft m ℓ`, `lenRight m ℓ`: the points `x ≤ 0 ≤ R` with `m[x, 0] = ℓ`, `m[0, R] = ℓ`
  (Palm point by length and its length partner); jointly measurable in `(m, ℓ)`.
* `scaleProxy γ y`: a measurable version of `scaleParam γ y`, through the pre-limit functionals
  `areaFun` (the measurable candidates for `∫ f dqAreaMeasure`) and rational radii;
  `canonProxy γ y = rescale y Q (scaleProxy γ y)` (the canonical description (1.8)).
* `zoomLaw γ C y s`: the law data (`lawData`) of `canonProxy γ (zoomField γ C y s)`, the canonical
  description of the zoomed field `y(· + s) + C/γ`; jointly measurable in `(y, s)`
  (`measurable_zoomLaw`, via the countable raw coordinates, as in `Prop16MeasCoords`).

Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

open Factorization CoordsFull

/-! ## Boundary measure on its certificate -/

open Classical in
/-- The boundary measure on its existence certificate (junk `0` off it). -/
def bdryM (γ : ℝ) (y : FieldSample) : Measure ℝ :=
  if E1.M4.BCert γ y then qBoundaryMeasure γ y else 0

theorem measurable_bdryM (γ : ℝ) : Measurable (bdryM γ) :=
  E1.M4.measurable_qBoundaryMeasure_bCert γ

theorem measurable_measure_add {α : Type*} {mα : MeasurableSpace α} {f g : α → Measure ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a + g a :=
  Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.add_apply]
    exact ((Measure.measurable_coe hs).comp hf).add ((Measure.measurable_coe hs).comp hg)

/-! ## Points by length -/

/-- The point `R ≥ 0` with `m[0, R] = ℓ` (first such point). -/
def lenRight (m : Measure ℝ) (ℓ : ℝ) : ℝ :=
  sInf {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc 0 y)}

/-- The point `x ≤ 0` with `m[x, 0] = ℓ` (first such point to the left of `0`). -/
def lenLeft (m : Measure ℝ) (ℓ : ℝ) : ℝ :=
  -sInf {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc (-y) 0)}

theorem measurable_lenRight : Measurable fun p : Measure ℝ × ℝ => lenRight p.1 p.2 := by
  refine LQGMeas.measurable_sInf_upClosed (fun p : Measure ℝ × ℝ =>
    {y : ℝ | 0 < y ∧ ENNReal.ofReal p.2 ≤ p.1 (Icc 0 y)}) (fun q => ?_) ?_ (fun _ _ h => h.1)
  · exact (MeasurableSet.const _).inter (measurableSet_le
      (ENNReal.measurable_ofReal.comp measurable_snd)
      ((Measure.measurable_coe measurableSet_Icc).comp measurable_fst))
  · exact fun p a b ha hab => ⟨ha.1.trans_le hab,
      ha.2.trans (measure_mono (Icc_subset_Icc_right hab))⟩

theorem measurable_lenLeft : Measurable fun p : Measure ℝ × ℝ => lenLeft p.1 p.2 := by
  refine (LQGMeas.measurable_sInf_upClosed (fun p : Measure ℝ × ℝ =>
    {y : ℝ | 0 < y ∧ ENNReal.ofReal p.2 ≤ p.1 (Icc (-y) 0)}) (fun q => ?_) ?_
    (fun _ _ h => h.1)).neg
  · exact (MeasurableSet.const _).inter (measurableSet_le
      (ENNReal.measurable_ofReal.comp measurable_snd)
      ((Measure.measurable_coe measurableSet_Icc).comp measurable_fst))
  · exact fun p a b ha hab => ⟨ha.1.trans_le hab,
      ha.2.trans (measure_mono (Icc_subset_Icc_left (neg_le_neg hab)))⟩

/-! ## The measurable scale parameter and the zoom law -/

/-- The measurable candidate for `qAreaMeasure γ y (B_a(0) ∩ ℍ)`. -/
def areaProxy (γ : ℝ) (y : FieldSample) (a : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (LQGMeas.areaFun γ
    (LQGMeas.openBump (Metric.ball (0 : ℂ) a ∩ H) n) y)

/-- A measurable version of `scaleParam γ y` (rational radii, `areaProxy`). -/
def scaleProxy (γ : ℝ) (y : FieldSample) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ 1 ≤ areaProxy γ y q}

/-- The canonical description (1.8) with the measurable scale `scaleProxy`. -/
def canonProxy (γ : ℝ) (y : FieldSample) : FieldSample := rescale y (Qc γ) (scaleProxy γ y)

/-- The law data of a single field sample (`lawData` at a point). -/
def lawOf (y : FieldSample) : LawD := (coordsFull y, fun ρ => pairRaw y ρ.1)

/-- The law data of the canonical description of the zoomed field `y(· + s) + C/γ`. -/
def zoomLaw (γ C : ℝ) (y : FieldSample) (s : ℝ) : LawD :=
  lawOf (canonProxy γ (zoomField γ C y s))

theorem measurable_areaProxy (γ a : ℝ) : Measurable fun y => areaProxy γ y a :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    (LQGMeas.measurable_areaFun γ (LQGMeas.continuous_openBump _ n).measurable)

theorem measurable_scaleProxy (γ : ℝ) : Measurable (scaleProxy γ) := by
  refine LQGMeas.measurable_sInf_upClosed (fun y => {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧
    (q : ℝ) ≤ a ∧ 1 ≤ areaProxy γ y q}) (fun b => ?_) ?_ (fun _ _ h => h.1)
  · refine measurableSet_setOfPred.2 (measurable_const.and (Measurable.exists fun q => ?_))
    exact measurable_const.and (measurable_const.and
      (measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_areaProxy γ q))))
  · rintro y a b ⟨ha, q, hq, hqa, h1⟩ hab
    exact ⟨ha.trans_le hab, q, hq, hqa.trans hab, h1⟩

theorem scaleProxy_recon (γ : ℝ) (y : FieldSample) :
    scaleProxy γ (reconstruct (coords y)) = scaleProxy γ y := by
  have h : ∀ f, LQGMeas.areaFun γ f (reconstruct (coords y)) = LQGMeas.areaFun γ f y := by
    intro f
    unfold LQGMeas.areaFun
    rw [show reconstruct (coords y) = Prop16Area.recon y from rfl, Prop16Area.areaApprox_recon]
  simp only [scaleProxy, areaProxy, h]

theorem canonProxy_recon (γ : ℝ) (y : FieldSample) :
    canonProxy γ y = rescale (reconstruct (coords y)) (Qc γ)
      (scaleProxy γ (reconstruct (coords y))) := by
  rw [scaleProxy_recon, Prop16Area.rescale_reconstruct_coords]
  rfl

/-- The canonical description rebuilt from the raw coordinates `c`. -/
def canonOfCoords (γ : ℝ) (c : ℕ → ℝ) : FieldSample :=
  rescale (reconstruct c) (Qc γ) (scaleProxy γ (reconstruct c))

theorem measurable_canonOfCoords_apply (γ : ℝ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun c : ℕ → ℝ => canonOfCoords γ c ν := by
  unfold canonOfCoords
  exact Measurable.comp (g := fun q : FieldSample × ℝ => rescale q.1 (Qc γ) q.2 ν)
    (f := fun c : ℕ → ℝ => (reconstruct c, scaleProxy γ (reconstruct c)))
    (Prop16Area.measurable_rescale_apply_joint (Qc γ) ν)
    (measurable_reconstruct.prodMk ((measurable_scaleProxy γ).comp measurable_reconstruct))

theorem measurable_lawOf_canon (γ : ℝ) :
    Measurable fun c : ℕ → ℝ => lawOf (canonOfCoords γ c) := by
  unfold lawOf
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · exact measurable_canonOfCoords_apply γ (foldedCircle (fullIndex i).1 (fullIndex i).2)
  · exact (measurable_canonOfCoords_apply γ
      (volume.withDensity fun z => ENNReal.ofReal (ρ.1 z))).sub
      (measurable_canonOfCoords_apply γ (volume.withDensity fun z => ENNReal.ofReal (-ρ.1 z)))

theorem measurable_coords_zoomField_joint (γ C : ℝ) :
    Measurable fun q : FieldSample × ℝ => coords (zoomField γ C q.1 q.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  have e : (fun q : FieldSample × ℝ => coords (zoomField γ C q.1 q.2) i) = fun q =>
      coords (translate q.1 (q.2 : ℂ)) i +
        C / γ * ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) univ).toReal := by
    funext q
    rfl
  rw [e]
  exact ((measurable_pi_apply i).comp IndepParams.measurable_coords_translate).add
    measurable_const

/-- **M2.** The zoom law is jointly measurable in the field and the zoom point. -/
theorem measurable_zoomLaw (γ C : ℝ) :
    Measurable fun q : FieldSample × ℝ => zoomLaw γ C q.1 q.2 := by
  have e : (fun q : FieldSample × ℝ => zoomLaw γ C q.1 q.2) = fun q =>
      lawOf (canonOfCoords γ (coords (zoomField γ C q.1 q.2))) := by
    funext q
    rw [zoomLaw, canonProxy_recon]
    rfl
  rw [e]
  exact (measurable_lawOf_canon γ).comp (measurable_coords_zoomField_joint γ C)

end Thm18Asm
end QuantumZipper
