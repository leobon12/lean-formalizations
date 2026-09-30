import QuantumZipper.Proofs.Zipper.FSMeasBasic
import QuantumZipper.Proofs.Zipper.F2Unscaled
import QuantumZipper.Proofs.Zipper.F1B4dBasic

/-!
# FS-MEAS (D27) applied to F2 step (2a): the canonical `P_*` sample of an unscaled wedge

`F2.UnscaledCanonIndepStmt` asks for `(canonical γ Z, scaleParam γ Z)` (`Z` the unscaled wedge
field) to be an a.e.-measurable `FieldSample × ℝ`-valued random variable independent of the
driver. Its `FieldSample` component has uncontrolled coordinates at non-s-finite measures, so we
do not prove it; following D27 we replace the canonical field by its measurable version
`xiU = canonVer γ (coords of Z)`, where the coordinates of `Z` are read as a *measurable*
function of `(X', A)` (`F1.B4d.coordsW`, valid on the a.s. event that `A` is continuous). Then

* `xiU` is a.e.-measurable, independent of the driver `B''` (it is a measurable function of
  `(X', A)`), and a.s. equal to `(sfTrunc (canonical γ Z), scaleParam γ Z)` (`xiU_spec`);
* `(xiU.1, B')`, `B'` the Brownian rescaling of `B''` by `scaleParam γ Z`, is a `P_*` sample
  (`pstar_of_unscaled_fs`), whose configuration agrees with `canonConfig γ (Z, √κ B'')` up to
  the truncation, which `unzipLengths` does not see;
* hence **F2 step (2a) holds with the single open input `F2.UnscaledB3dStmt`**
  (`f2Unscaled_of_B3d`); the input `UnscaledCanonIndepStmt` is no longer needed.

Source of the step: Sheffield, arXiv:1012.4797, §5.1 (pp. 60–62) and §5.4 (pp. 70–72), as in
`F2Unscaled.lean`. The measurability bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace QuantumZipper
namespace FSMeas

open Factorization CoordsFull F2

/-- The dyadic coordinates of the wedge field, as a measurable function of the lateral
coordinates of the GFF sample and of the radial path (read at dyadic times). -/
def wedgeCoordsM (Q : ℝ) (q : FieldSample × (ℝ → ℝ)) : ℕ → ℝ :=
  F1.B4d.coordsW Q (F1.B4d.latId q.1, q.2)

theorem measurable_wedgeCoordsM (Q : ℝ) : Measurable (wedgeCoordsM Q) :=
  (F1.B4d.measurable_coordsW Q).comp
    ((F1.B4d.measurable_latId.comp measurable_fst).prodMk measurable_snd)

/-- The measurable version of `(canonical γ Z, scaleParam γ Z)` for the unscaled wedge field
`Z = zU γ X' A`. -/
def xiU (γ : ℝ) {Ω : Type*} (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (ω : Ω) : FieldSample × ℝ :=
  canonVer γ (wedgeCoordsM (Qc γ) (X' ω, fun t => A t ω))

/-- **The measurable canonical data of the unscaled wedge field.** -/
theorem xiU_spec {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X' : Ω → FieldSample}
    {A : ℝ → Ω → ℝ} {β : Type*} [MeasurableSpace β] {V : Ω → β}
    (hX : IsFreeGFFModConstH X' P) (hA : IsWedgeProcess α (Qc γ) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P)
    (hIV : IndepFun (fun ω => (X' ω, fun t => A t ω)) V P) :
    AEMeasurable (xiU γ X' A) P ∧ IndepFun (xiU γ X' A) V P ∧
      ∀ᵐ ω ∂P, xiU γ X' A ω = (sfTrunc (canonical γ (zU γ X' A ω)), scaleParam γ (zU γ X' A ω)) := by
  have hc : AEMeasurable (fun ω => wedgeCoordsM (Qc γ) (X' ω, fun t => A t ω)) P :=
    (measurable_wedgeCoordsM _).comp_aemeasurable
      ((WedgeTK.measurable_X_pi hX).aemeasurable.prodMk (ZoomRadial.aemeasurable_wedgePath hA))
  have hcW : ∀ᵐ ω ∂P, wedgeCoordsM (Qc γ) (X' ω, fun t => A t ω) = coords (zU γ X' A ω) := by
    filter_upwards [WedgeCan4.ae_continuous_wedgeProcess hA] with ω hω
    exact (F1.B4d.coords_wedgeField_eq _ hω _).symm
  have hIc : IndepFun (fun ω => wedgeCoordsM (Qc γ) (X' ω, fun t => A t ω)) V P :=
    hIV.comp (measurable_wedgeCoordsM _) measurable_id
  exact canonVer_spec hc hcW
    (LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω _ P X' A inferInstance hX hA hI) hIc

/-- **The canonical `P_*` sample hidden in an unscaled configuration, measurable form** (replaces
`F2.pstar_of_unscaled` and its input `UnscaledCanonIndepStmt`). With `B'` the Brownian rescaling
of `B''` by the (measurable version of the) scale `a = scaleParam γ Z`, `(xiU.1, B')` is a `P_*`
sample; a.s. `a > 0`, `xiU.1 = sfTrunc (canonical γ Z)`, and the driver of `B'` is the driver of
`canonConfig γ (Z, √κ B'')`. -/
theorem pstar_of_unscaled_fs {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ}
    {B'' : ℝ≥0 → Ω → ℝ} (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    Thm13Asm.IsPStarSample κ P (fun ω => (xiU (Real.sqrt κ) X' A ω).1)
        (rscale (sqScale ∘ xiU (Real.sqrt κ) X' A) B'') ∧
      ∀ᵐ ω ∂P, 0 < scaleParam (Real.sqrt κ) (zU (Real.sqrt κ) X' A ω) ∧
        (xiU (Real.sqrt κ) X' A ω).1 = sfTrunc (canonical (Real.sqrt κ) (zU (Real.sqrt κ) X' A ω)) ∧
        drive κ (rscale (sqScale ∘ xiU (Real.sqrt κ) X' A) B'') ω =
          (canonConfig (Real.sqrt κ) (zU (Real.sqrt κ) X' A ω, drive κ B'' ω)).2 := by
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hγ2 : γ < 2 := sqrt_lt_two_of' hκ hκ4
  have hα : γ - 2 / γ < Qc γ := alpha_lt_Qc' hγ hγ2
  set Z := zU γ X' A with hZ
  obtain ⟨hξm, hξI, hξae⟩ := xiU_spec hγ hγ2 hα hX hA hI hIB
  obtain ⟨hBr, hBI⟩ := randScale_of_aemeasurable hB hξm measurable_sqScale sqScale_ne_zero hξI
  have hYI : IndepFun (fun ω => (xiU γ X' A ω).1)
      (pathOf (rscale (sqScale ∘ xiU γ X' A) B'')) P :=
    hBI.comp measurable_fst measurable_id
  have hW : IsQuantumWedge γ (γ - 2 / γ) (fun ω => (xiU γ X' A ω).1) P := by
    refine (isQuantumWedge_congr_sfTrunc (Y' := fun ω => canonical γ (Z ω)) ?_).2
      ⟨hα, Ω, _, P, X', A, inferInstance, hX, hA, hI, rfl⟩
    filter_upwards [hξae] with ω h
    rw [h]
  refine ⟨⟨hκ, hκ4, hW, hBr, hYI⟩, ?_⟩
  filter_upwards [hξae, Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI] with ω h hspec
  have ha : 0 < scaleParam γ (Z ω) := hspec.1
  refine ⟨ha, by rw [h], ?_⟩
  rw [canonConfig_eq_drive γ κ (Z ω) B'' ω ha]
  have ha' : 0 < scaleParam γ (zU γ X' A ω) := ha
  funext r
  simp only [drive, rscale, Function.comp, h, sqScale, ha', ↓reduceIte]
  rfl

end FSMeas
end QuantumZipper
