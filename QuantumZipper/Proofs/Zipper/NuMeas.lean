import QuantumZipper.Proofs.Zipper.E1TransferRep3
import QuantumZipper.Proofs.Zipper.E1ZFinBasic
import QuantumZipper.Proofs.Zipper.E3Palm

/-!
# NU-MEAS: the Palm boundary measure `ν_ω` is a random measure

`handoff/E-PLAN-2.md`, node NU-MEAS. Notation of `B2Defs`/`E1Defs`:
`ν_ω = nuPalm κ T B X ϖ ω = qBoundaryMeasure γ (h⁰ − m)`, `m = evalReg h⁰ ϖ`.

* `coordsFull_nuField_eq` (deterministic): if `RegShift y ϖ`, the coordinates of `y − evalReg y ϖ`
  are those of `nuField ϖ (coordsFull (nrm y))`, where `nuField ϖ c = fromC c − evalReg (fromC c) ϖ`
  is a measurable function of the coordinates `c`.
* **`aemeasurable_nuPalm`** (NU-MEAS): `ω ↦ ν_ω` is a.e. measurable.
* `exists_kernel_nuPalm`: a kernel `K` with `K ω = ν_ω` a.s.
* `e3_pos'`: E3-POS (`E3.e3_pos`) without the measurability hypothesis.

Source: Sheffield, arXiv:1012.4797, §5.2 and Lemma 5.6 (pp. 57–59, 66–68), where `ν` is used as a
random measure without comment. The measurability argument is **own bookkeeping**: `ν_ω` depends
only on the circle coordinates of `h⁰ − m` (`qBoundaryMeasure_congr_of_coordsFull`), which are a
measurable function of the (a.e.-measurable, `B2.aemeasurable_data_unzip`) coordinates of `nrm h⁰`
because `evalReg` commutes with constants under `RegShift` (`E1.evalReg_addConst_of_regShift`);
then `LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace NuMeas

open B2 E1 B1Full CoordsFull UnzipFull

/-- Each value of the field rebuilt from coordinates is measurable in the coordinates. -/
theorem measurable_fromC_apply (μ : Measure ℂ) : Measurable fun c : ℕ → ℝ => fromC c μ := by
  classical
  unfold fromC
  by_cases h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

/-- `evalReg` depends only on the circle coordinates. -/
theorem evalReg_congr_coordsFull {x x' : FieldSample} (h : coordsFull x = coordsFull x')
    (ν : Measure ℂ) : evalReg x ν = evalReg x' ν := by
  unfold evalReg; rw [avgReg_congr_full h]

/-- `bdryApprox` depends only on the circle coordinates. -/
theorem bdryApprox_congr_coordsFull (γ : ℝ) {x x' : FieldSample}
    (h : coordsFull x = coordsFull x') : bdryApprox γ x = bdryApprox γ x' := by
  funext k; unfold bdryApprox; rw [avgReg_congr_full h]

/-- The normalized field rebuilt from coordinates `c`: `fromC c − evalReg (fromC c) ϖ`. -/
def nuField (ϖ : Measure ℂ) (c : ℕ → ℝ) : FieldSample :=
  addConst (fromC c) (-(evalReg (fromC c) ϖ))

theorem measurable_nuField_apply (ϖ : Measure ℂ) [SFinite ϖ] (μ : Measure ℂ) :
    Measurable fun c => nuField ϖ c μ := by
  unfold nuField addConst
  refine (measurable_fromC_apply μ).add (Measurable.mul ?_ measurable_const)
  exact ((measurable_evalReg ϖ).comp (measurable_pi_iff.2 measurable_fromC_apply)).neg

/-- Deterministic core: under `RegShift y ϖ`, `y − evalReg y ϖ` and `nuField ϖ (coordsFull (nrm y))`
have the same circle coordinates. -/
theorem coordsFull_nuField_eq {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {y : FieldSample}
    (hR : RegShift y ϖ) :
    coordsFull (nuField ϖ (coordsFull (nrm y))) = coordsFull (addConst y (-(evalReg y ϖ))) := by
  have h1 : coordsFull (fromC (coordsFull (nrm y))) = coordsFull (nrm y) := coordsFull_fromC _
  have h2 : evalReg (fromC (coordsFull (nrm y))) ϖ = evalReg y ϖ + -(y (foldedCircle 0 1)) := by
    rw [evalReg_congr_coordsFull h1, nrm, evalReg_addConst_of_regShift hR]
  funext i
  rw [nuField, coordsFull_addConst, congrFun h1 i, h2, coordsFull_addConst, nrm,
    coordsFull_addConst]
  ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **NU-MEAS.** The Palm boundary measure `ω ↦ ν_ω` is a.e. measurable. -/
theorem aemeasurable_nuPalm (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ) :
    AEMeasurable (fun ω => nuPalm κ T B X ϖ ω) P := by
  have := hϖ.prob
  obtain ⟨K, hK, hKH, hϖK⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  have hcm : AEMeasurable (fun ω => coordsFull (nrm (h0f κ T B X ω))) P :=
    (aemeasurable_data_unzip (κ := κ) hB hX hind (s := T - 0) (by linarith)).fst.fst
  have hco : ∀ᵐ ω ∂P, coordsFull (nuField ϖ (hcm.mk _ ω)) =
      coordsFull (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω))) := by
    filter_upwards [hcm.ae_eq_mk, hB.cont,
      ae_regShift_Yf_compact κ hB hX hind le_rfl hT.le hK hKH hϖK hF hα] with ω hcω hc hR
    have hv : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
    rw [varpiT_zero hv (vrev_zero hT.le) hϖ.ae_mem_H] at hR
    rw [← hcω]
    exact coordsFull_nuField_eq hR
  have hae : AEMeasurable (fun ω => qBoundaryMeasure (Real.sqrt κ) (nuField ϖ (hcm.mk _ ω))) P := by
    refine LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae
      (fun μ => (measurable_nuField_apply ϖ μ).comp hcm.measurable_mk) ?_
    filter_upwards [hco, ae_exists_isVagueLimitR_nuPalm hReg hκ hκ4 hT hB hX hind ϖ]
      with ω h ⟨l, hl⟩
    show IsVagueLimitR (bdryApprox _ (nuField ϖ (hcm.mk _ ω)))
      (qBoundaryMeasure _ (nuField ϖ (hcm.mk _ ω)))
    rw [bdryApprox_congr_coordsFull _ h, qBoundaryMeasure_congr_of_coordsFull _ h,
      qBoundaryMeasure_eq hl]
    exact hl
  refine hae.congr ?_
  filter_upwards [hco] with ω h
  exact qBoundaryMeasure_congr_of_coordsFull _ h

/-- **NU-MEAS, kernel form.** -/
theorem exists_kernel_nuPalm (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ) :
    ∃ K : Kernel Ω ℝ, ∀ᵐ ω ∂P, K ω = nuPalm κ T B X ϖ ω := by
  have h := aemeasurable_nuPalm hReg hκ hκ4 hT hB hX hind hϖ
  refine ⟨⟨h.mk _, h.measurable_mk⟩, ?_⟩
  filter_upwards [h.ae_eq_mk] with ω hω
  exact hω.symm

/-- **E3-POS**, unconditional form (NU-MEAS discharged). -/
theorem e3_pos' (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {δ : ℝ} (hδ : 0 < δ) (hTδ : 4 * δ ^ 2 / (4 - κ) ≤ T) :
    0 < ∫⁻ ω, nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P :=
  E3.e3_pos hReg hκ hκ4 hT hB hX hind (aemeasurable_nuPalm hReg hκ hκ4 hT hB hX hind hϖ) hδ hTδ

end NuMeas
end QuantumZipper
