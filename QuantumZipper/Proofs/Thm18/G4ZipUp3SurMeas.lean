import QuantumZipper.Proofs.Thm18.G4ZipUpReadMeas
import QuantumZipper.Proofs.Thm18.G1RegRepMeas
import QuantumZipper.Proofs.LQG.WedgeMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: measurability of the surrogate zip-up data

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4ZIPUP-INPUTS, input (2): `G4SurrogateZipDataMeasStmt` (`G4ZipUpReadMeas.lean`) is **proved**
(`g4SurrogateZipDataMeasStmt_holds`).

No evalReg transfer identity is needed: every quantity only reads `avgReg`, and
* the coordinates `coords X_z` of the pulled-back field `X_z = coordChange (y z) (ψ z) Q` are
  measurable in `z` (each is `evalReg (y z) (μ.map (ψ z)) + Q ∫ log ‖ψ_z'‖ dμ`, by
  `G1Meas.measurable_evalReg_map_param`);
* `X_z` has the same `avgReg` as the *measurable* family `reconstruct (coords X_z)`
  (`Factorization.avgReg_reconstruct_coords`), so the second coordinate change may be taken on
  that family (`Factorization.coordChange_congr`), where `measurable_evalReg_map_param` applies;
* the good-set scale is `WedgeMeas.scaleG γ (coords X_z)` (`WedgeMeas.measurable_scaleG`).

**Own elementary argument** (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- Evaluation of a coordinate change of a measurable family at a fixed s-finite measure. -/
theorem measurable_coordChange_apply_param {Z : Type} [MeasurableSpace Z] {y : Z → FieldSample}
    (hy : Measurable y) {ψ : Z → ℂ → ℂ} (hψ : Measurable fun q : Z × ℂ => ψ q.1 q.2)
    (hψd : Measurable fun q : Z × ℂ => Real.log ‖deriv (ψ q.1) q.2‖) (Q : ℝ)
    (μ : Measure ℂ) [SFinite μ] :
    Measurable fun z => coordChange (y z) (ψ z) Q μ := by
  show Measurable fun z => evalReg (y z) (μ.map (ψ z)) + Q * ∫ w, Real.log ‖deriv (ψ z) w‖ ∂μ
  exact (G1Meas.measurable_evalReg_map_param hy hψ μ).add (measurable_const.mul
    (StronglyMeasurable.integral_prod_right' (f := fun q : Z × ℂ =>
      Real.log ‖deriv (ψ q.1) q.2‖) hψd.stronglyMeasurable).measurable)

open Classical in
/-- The good-set scale only reads the coordinates. -/
theorem goodScale_eq_scaleG (γ : ℝ) (x : FieldSample) :
    (if IsLQGGood γ x then scaleParam γ x else 0) = WedgeMeas.scaleG γ (Factorization.coords x) := by
  unfold WedgeMeas.scaleG
  by_cases hx : IsLQGGood γ x
  · have hx' := (GoodSample.isLQGGood_iff_reconstruct γ x).2 hx
    rw [if_pos hx, if_pos hx']
    exact (Factorization.scaleParam_congr (Factorization.avgReg_reconstruct_coords x) γ).symm
  · have hx' : ¬ IsLQGGood γ (Factorization.reconstruct (Factorization.coords x)) :=
      fun h => hx ((GoodSample.isLQGGood_iff_reconstruct γ x).1 h)
    rw [if_neg hx, if_neg hx']

/-- **Input (2) of `g4ZipUpFieldReadStmt_of_zip2`, proved.** -/
theorem g4SurrogateZipDataMeasStmt_holds : G4SurrogateZipDataMeasStmt := by
  intro γ Z _ y ψ sc hy hψ hψd hsc
  classical
  set X : Z → FieldSample := fun z => coordChange (y z) (ψ z) (Qc γ) with hXdef
  have hc : Measurable fun z => Factorization.coords (X z) :=
    measurable_pi_iff.2 fun i =>
      measurable_coordChange_apply_param hy hψ hψd (Qc γ) _
  set Y : Z → FieldSample := fun z => Factorization.reconstruct (Factorization.coords (X z))
    with hYdef
  have hY : Measurable Y := Factorization.measurable_reconstruct.comp hc
  set m : Z → ℂ → ℂ := fun z w => (sc z : ℂ) * w with hmdef
  have hm : Measurable fun q : Z × ℂ => m q.1 q.2 :=
    (Complex.measurable_ofReal.comp (hsc.comp measurable_fst)).mul measurable_snd
  have hmd' : ∀ z, deriv (m z) = fun _ => (sc z : ℂ) := by
    intro z; funext w; simp [hmdef]
  have hmd : Measurable fun q : Z × ℂ => Real.log ‖deriv (m q.1) q.2‖ := by
    simp only [hmd']
    exact Real.measurable_log.comp (measurable_norm.comp
      (Complex.measurable_ofReal.comp (hsc.comp measurable_fst)))
  have hXY : ∀ z, coordChange (X z) (m z) (Qc γ) = coordChange (Y z) (m z) (Qc γ) := fun z =>
    Factorization.coordChange_congr (Factorization.avgReg_reconstruct_coords (X z)).symm _ _
  have hW : ∀ (μ : Measure ℂ) [SFinite μ],
      Measurable fun z => coordChange (X z) (m z) (Qc γ) μ := by
    intro μ _
    simp only [hXY]
    exact measurable_coordChange_apply_param hY hm hmd (Qc γ) μ
  refine ⟨Measurable.prodMk (measurable_pi_iff.2 fun i => hW _) ?_, ?_⟩
  · refine measurable_pi_iff.2 fun ρ => ?_
    exact (hW _).sub (hW _)
  · convert (WedgeMeas.measurable_scaleG γ).comp hc using 1
    funext z
    convert goodScale_eq_scaleG γ (X z)
    rfl

end Thm18Asm
end QuantumZipper
