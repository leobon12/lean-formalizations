import QuantumZipper.Proofs.Zipper.F1CanonLaw

/-!
# WEDGE-ADDCONST (1): field-level B4(c) from the reference wedge

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6 (canonical description
(1.8) of a quantum wedge); Duplantier–Miller–Sheffield, *Liouville quantum gravity as a mating
of trees*, arXiv:1409.7055, Def. 4.5 / Prop. 4.6 (the circle-average embedding; adding a constant
and re-embedding preserves the law).

`F1.WedgeAddConstLawStmt` quantifies over every `α`-wedge `Y`. Since `IsQuantumWedge` only fixes
the law `fieldLawFull H Y P`, and (`F1.canonAddFactor`) the joint law of the canonical data of
`Y + k` and of the scale `scaleParam γ (Y + k)` is a measurable image of that law (on the a.s.
event that `Y` is good), the statement reduces to the **reference wedge**
`WedgeMeas.wedgeRef γ X A = canonical γ (wedgeField (lateralPart X) A Q)`:
`WedgeRefAddConstStmt` (this file) implies `F1.WedgeAddConstLawStmt`
(`wedgeAddConstLawStmt_of_ref`).

Own bookkeeping argument (push-forwards of a.e.-measurable maps, `ae_map_iff`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace F1

open Factorization CoordsFull

/-- **B4(c) for the reference wedge.** For the reference data `(X, A)` of `IsQuantumWedge`, a.s.
the canonical scale of `W + k` is positive (`W = wedgeRef γ X A`), and `canonical γ (W + k)` has
the field law of `W`. -/
def WedgeRefAddConstStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' → ∀ k : ℝ,
      (∀ᵐ ω ∂P', 0 < scaleParam γ (addConst (WedgeMeas.wedgeRef γ X A ω) k)) ∧
        fieldLawFull H (fun ω => canonical γ (addConst (WedgeMeas.wedgeRef γ X A ω) k)) P' =
          fieldLawFull H (WedgeMeas.wedgeRef γ X A) P'

/-- The canonical data of `x + k` and its scale, read from the full data of `x`. -/
def canonAddData (γ k : ℝ) (p : (ℕ → ℝ) × (TestFun H → ℝ)) :
    ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  canonAddFactor γ k p.1

theorem measurable_canonAddData (γ k : ℝ) : Measurable (canonAddData γ k) :=
  (measurable_canonAddFactor γ k).comp measurable_fst

theorem canonAddData_of_good {γ : ℝ} (k : ℝ) {x : FieldSample} (hx : IsLQGGood γ x) :
    canonAddData γ k (WedgeMeas.dataFull H x) =
      (WedgeMeas.dataFull H (canonical γ (addConst x k)), scaleParam γ (addConst x k)) := by
  show canonAddFactor γ k (coordsFull x) = _
  rw [canonAddFactor_coordsFull, canonData_of_good (hx.addConst k)]

/-- The joint law of the canonical data of `V + k` and its scale is the image of the law of `V`. -/
theorem map_canonAdd_eq {γ : ℝ} (k : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : Ω → FieldSample} (hVm : AEMeasurable (fun ω => WedgeMeas.dataFull H (V ω)) P)
    (hVg : ∀ᵐ ω ∂P, IsLQGGood γ (V ω)) :
    AEMeasurable (fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (V ω) k)),
        scaleParam γ (addConst (V ω) k))) P ∧
      P.map (fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (V ω) k)),
        scaleParam γ (addConst (V ω) k))) = (fieldLawFull H V P).map (canonAddData γ k) := by
  have hae : (fun ω => canonAddData γ k (WedgeMeas.dataFull H (V ω))) =ᵐ[P]
      fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (V ω) k)),
        scaleParam γ (addConst (V ω) k)) := by
    filter_upwards [hVg] with ω h
    exact canonAddData_of_good k h
  have hm : AEMeasurable (fun ω => canonAddData γ k (WedgeMeas.dataFull H (V ω))) P :=
    (measurable_canonAddData γ k).comp_aemeasurable hVm
  refine ⟨hm.congr hae, ?_⟩
  rw [← Measure.map_congr hae]
  exact (AEMeasurable.map_map_of_aemeasurable
    (measurable_canonAddData γ k).aemeasurable hVm).symm

/-- **Field-level B4(c) from the reference wedge.** -/
theorem wedgeAddConstLawStmt_of_ref
    (href : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeRefAddConstStmt γ α) :
    WedgeAddConstLawStmt := by
  intro γ α hγ hγ2 hα Ω _ P _ Y hY k
  have hY' := hY
  obtain ⟨-, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hY'
  have := hP'
  set W : Ω' → FieldSample := WedgeMeas.wedgeRef γ X A with hWdef
  have hW : IsQuantumWedge γ α W P' := ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have hlaw' : fieldLawFull H Y P = fieldLawFull H W P' := hlaw
  obtain ⟨hpos, hlawW⟩ := href γ α hγ hγ2 hα P' X A hX hA hI k
  have hYm := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hY
  have hWm := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have hYg := Wire2.wedgeGoodStmt hγ hγ2 hα P Y hY
  have hWg := Wire2.wedgeGoodStmt hγ hγ2 hα P' W hW
  obtain ⟨hgY, hJY⟩ := map_canonAdd_eq (γ := γ) k hYm hYg
  obtain ⟨hgW, hJW⟩ := map_canonAdd_eq (γ := γ) k hWm hWg
  have hJ : P.map (fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (Y ω) k)),
        scaleParam γ (addConst (Y ω) k))) =
      P'.map (fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (W ω) k)),
        scaleParam γ (addConst (W ω) k))) := by
    rw [hJY, hJW, hlaw']
  have hSm : MeasurableSet {q : ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ | 0 < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  refine ⟨?_, ?_⟩
  · have h1 := (ae_map_iff hgW hSm).2 hpos
    rw [← hJ] at h1
    exact ae_of_ae_map hgY h1
  · have e1 : fieldLawFull H (fun ω => canonical γ (addConst (Y ω) k)) P =
        (P.map (fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (Y ω) k)),
          scaleParam γ (addConst (Y ω) k)))).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hgY).symm
    have e2 : fieldLawFull H (fun ω => canonical γ (addConst (W ω) k)) P' =
        (P'.map (fun ω => (WedgeMeas.dataFull H (canonical γ (addConst (W ω) k)),
          scaleParam γ (addConst (W ω) k)))).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hgW).symm
    rw [e1, hJ, ← e2, hlawW, hlaw']

end F1
end QuantumZipper
