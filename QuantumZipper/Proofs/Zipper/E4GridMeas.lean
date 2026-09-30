import QuantumZipper.Proofs.Zipper.E4GridSet
import QuantumZipper.Proofs.Zipper.E1TransferFinal
import QuantumZipper.Proofs.Zipper.E1Nu
import QuantumZipper.Proofs.Zipper.NuMeas

/-!
# E4-GRID, G2: a.e.-measurability of the grid summands

`handoff/E4-A.md`, sub-statement G2 (the outer `∫⁻ ∂P` of a finite sum splits only with
a.e.-measurable summands).

* `qBoundaryMeasure_Icc_lt_top`: a boundary measure is finite on compact intervals (it is a vague
  limit, hence locally finite, or the junk `0`);
* `aemeasurable_setLIntegral_family`: `ω ↦ ∫⁻_{[a,b]} g(x, D ω) dν_ω` is a.e.-measurable for an
  a.e.-measurable family `ν` finite on `[a,b]`, a.e.-measurable `D` and measurable `g`
  (truncation, `E1.M4.measurable_setLIntegral_of_measurable_measure`);
* `aemeasurable_data`: `(lawData (nrm Y_t), (V^t, W⁰))` is a.e.-measurable (`B2.data_eq_comp`,
  `B2.aemeasurable_data_unzip`);
* **`aemeasurable_field`**: `ω ↦ coordsFull (Y_t − m)` is a.e.-measurable for `0 ≤ t < T`: a.s. it is
  `M4.measurable_coords_shift` applied to the data (M3 at the level of coordinates, as in
  `E1.ae_goodQ`, and `m = evalReg Y_t ϖ_t + q_t`, `B2.b2_evalReg_split`).

Own bookkeeping (Sheffield, arXiv:1012.4797, uses these random variables without comment).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 E1.M4 CharFun CoordsFull B1Full

theorem qBoundaryMeasure_Icc_lt_top (γ : ℝ) (y : FieldSample) (a b : ℝ) :
    qBoundaryMeasure γ y (Icc a b) < ⊤ := by
  classical
  unfold qBoundaryMeasure
  split_ifs with h
  · have := h.choose_spec.1
    exact measure_Icc_lt_top
  · simp

theorem aemeasurable_setLIntegral_family {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ν : Ω → Measure ℝ} (hν : AEMeasurable ν P) {a b : ℝ} (hfin : ∀ ω, ν ω (Icc a b) < ⊤)
    {E : Type*} [MeasurableSpace E] {D : Ω → E} (hD : AEMeasurable D P) {g : ℝ × E → ℝ≥0∞}
    (hg : Measurable g) : AEMeasurable (fun ω => ∫⁻ x in Icc a b, g (x, D ω) ∂ν ω) P := by
  classical
  set M : Ω → Measure ℝ := fun ω => if hν.mk ν ω (Icc a b) < ⊤ then hν.mk ν ω else 0 with hMdef
  have hM : Measurable M := Measurable.ite (measurableSet_lt ((Measure.measurable_coe
    measurableSet_Icc).comp hν.measurable_mk) measurable_const) hν.measurable_mk measurable_const
  have hMfin : ∀ ω, M ω (Icc a b) < ⊤ := fun ω => by
    simp only [hMdef]
    split_ifs with h
    · exact h
    · simp
  have hm := measurable_setLIntegral_of_measurable_measure hM measurableSet_Icc hMfin
    (f := fun p : Ω × ℝ => g (p.2, hD.mk D p.1))
    (hg.comp (measurable_snd.prodMk (hD.measurable_mk.comp measurable_fst)))
  refine hm.aemeasurable.congr ?_
  filter_upwards [hν.ae_eq_mk, hD.ae_eq_mk] with ω h1 h2
  have hMω : M ω = ν ω := by
    simp only [hMdef, ← h1, hfin ω, ite_true]
  simp only [hMω, h2]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

theorem aemeasurable_data (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) :
    AEMeasurable (fun ω => (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
      (Vstop κ T t B ω, W0p κ T B ω))) P := by
  rw [data_eq_comp ht htT]
  exact (measurable_id.prodMap (measurable_splitAt t)).comp_aemeasurable
    (aemeasurable_data_unzip hB hX hind (sub_nonneg.2 htT))

/-- **G2, field factor.** -/
theorem aemeasurable_field (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ) (ht : 0 ≤ t) (htT : t < T) :
    AEMeasurable (fun ω => coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω)))) P := by
  have := hϖ.prob
  obtain ⟨K, hK, hKH, hϖK⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  have hϖH : ∀ᵐ z ∂ϖ, z ∈ H := ae_iff.2 (measure_mono_null (fun z hz hzK => hz (hKH hzK)) hϖK)
  have hG := (measurable_coords_shift κ ht ϖ hϖH).comp (measurable_pq t)
  refine (hG.comp_aemeasurable (aemeasurable_data (κ := κ) hB hX hind ht htT.le)).congr ?_
  filter_upwards [hB.cont, ae_regShift_Yf_compact κ hB hX hind ht htT.le hK hKH hϖK hF hα,
    b2_evalReg_split (κ := κ) hB hX hind ht htT.le hK hKH hϖK hF hα] with ω hc h1 hm
  have hrev : revMap (Wof 1 t ht (extC t (Vstop κ T t B ω))) t = revMap (Vr κ T B ω) t :=
    funext fun z => ReverseFlow.revMap_congr_drive z (eqOn_Wof_extC_Vstop ht hc)
  have := hϖ.prob
  have : IsProbabilityMeasure (varpiT (Vr κ T B ω) t ϖ) := by unfold varpiT; infer_instance
  have hc1 := coordsFull_fromC (nrm (Yf κ T t B X ω))
  have e1 : evalReg (fromC (coordsFull (nrm (Yf κ T t B X ω)))) (varpiT (Vr κ T B ω) t ϖ) =
      evalReg (Yf κ T t B X ω) (varpiT (Vr κ T B ω) t ϖ) +
        -(Yf κ T t B X ω (foldedCircle 0 1)) := by
    rw [NuMeas.evalReg_congr_coordsFull hc1, nrm, evalReg_addConst_of_regShift h1]
  simp only [Function.comp_apply, pq, mC, lawData]
  unfold varpiT at e1
  simp only [varpiT, qt, hrev, e1]
  funext i
  rw [coordsFull_addConst, coordsFull_addConst, congrFun hc1 i, nrm, coordsFull_addConst, mReg,
    hm]
  simp only [qt]
  ring

end E4Grid
end QuantumZipper
