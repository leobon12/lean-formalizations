import QuantumZipper.Proofs.Section5.Prop17PalmABId

/-!
# Proposition 1.7, node D4⁺ (Palm zoom), node B assembled, and the wiring (PALM-AB)

* `compProd_map_zoomCoords`: the unnormalized Palm identity
  `(P ⊗ ν|[a,b]).map (zoomCoords γ C h) = (P ⊗ ρ_ϖ dx|[a,b]).map (palmRep γ C ϖ X)`, from the
  Palm formula (Duplantier–Sheffield, arXiv:0808.1560, §3.3, p. 22; `palm_free_Ioo`) applied to
  `φ = 1_E ∘ zoomRep γ C` (the representation of node A), endpoints being null;
* `prop17FreePalmIdStmt_of_adm`: **node B** (`Prop17FreePalmIdStmt γ ϖ a b`) for every admissible
  probability normalizer `ϖ`; the normalizations agree (`E ν[a,b] = ∫_a^b ρ_ϖ`, the case `E = univ`);
* `prop17FreePalmIdStmt_holds`: node B for `ϖ = foldedCircle 0 3`, `[a, b] = [0, 1]`;
* `theorem1_7_of_freeNodesAC`, `theorem1_7_of_fixedZoom`: Proposition 1.7 from the free-field
  nodes, through the corrected shift locality (`theorem1_7_of_palmZoom'`, which uses the proved
  `prop17ShiftDetStmt'_holds`); only node C (`Prop17FreeFixedZoomStmt`) remains.

Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull PalmNorm PalmShift

section
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The unnormalized Palm point intensity `ρ_ϖ(x) dx` on `[a, b]`. -/
def palmLam (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity fun x => ENNReal.ofReal (rhoNorm γ (0 : ℂ → ℝ) ϖ x)

/-- The test function `1_E ∘ zoomRep γ C`. -/
def zoomφ (γ C : ℝ) (E : Set (ℕ → ℝ)) (c : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  E.indicator 1 (zoomRep γ C (c, x))

instance sFinite_palmLam (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : SFinite (palmLam γ ϖ a b) := by
  unfold palmLam; infer_instance

theorem measurable_zoomφ (γ C : ℝ) {E : Set (ℕ → ℝ)} (hE : MeasurableSet E) :
    Measurable (Function.uncurry (zoomφ γ C E)) :=
  (measurable_one.indicator hE).comp (measurable_zoomRep γ C)

/-- **Unnormalized Palm identity for the zoom coordinates.** -/
theorem compProd_map_zoomCoords [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ} (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1)
    {a b : ℝ} {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) {h : Ω → FieldSample}
    {ν : Kernel Ω ℝ} [IsSFiniteKernel ν]
    (hae : ∀ᵐ ω ∂P, h ω = freeFieldN ϖ X ω ∧ ν ω = qBoundaryMeasure γ (h ω))
    {C : ℝ} (hZ : Measurable (zoomCoords γ C h)) :
    (P ⊗ₘ ν.restrict (measurableSet_Icc (a := a) (b := b))).map (zoomCoords γ C h) =
      (P.prod (palmLam γ ϖ a b)).map (palmRep γ C ϖ X) := by
  haveI : IsProbabilityMeasure ϖ := ⟨hϖ1⟩
  have hF := measurable_palmRep hX γ C ϖ
  ext E hE
  have hL : ∀ᵐ ω ∂P, ν.restrict (measurableSet_Icc (a := a) (b := b)) ω
      (Prod.mk ω ⁻¹' (zoomCoords γ C h ⁻¹' E)) =
      ∫⁻ x in Ioo a b, zoomφ γ C E (coords (freeFieldN ϖ X ω)) x
        ∂(qBoundaryMeasure γ (freeFieldN ϖ X ω)) := by
    filter_upwards [hae, ae_freeFieldN_bdry hX hγ hγ2 ϖ] with ω h1 h2
    haveI : NullSingletonClass (qBoundaryMeasure γ (freeFieldN ϖ X ω)) := ⟨h2.2.1⟩
    set S : Set ℝ := {x | zoomRep γ C (coords (freeFieldN ϖ X ω), x) ∈ E} with hSdef
    have hS : MeasurableSet S :=
      (measurable_zoomRep γ C).comp (measurable_const.prodMk measurable_id) hE
    have hpre : Prod.mk ω ⁻¹' (zoomCoords γ C h ⁻¹' E) = S := by
      ext x
      show coordsFull (canonical γ (zoomField γ C (h ω) x)) ∈ E ↔ _
      rw [h1.1, zoomCoords_eq_zoomRep h2.1]
      rfl
    have hind : ∀ x, zoomφ γ C E (coords (freeFieldN ϖ X ω)) x = S.indicator 1 x := fun x => by
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        exact indicator_of_mem (show zoomRep γ C (coords (freeFieldN ϖ X ω), x) ∈ E from hx) _
      · rw [indicator_of_notMem hx]
        exact indicator_of_notMem (show zoomRep γ C (coords (freeFieldN ϖ X ω), x) ∉ E from hx) _
    rw [Kernel.restrict_apply, hpre, h1.2, h1.1, lintegral_congr hind, lintegral_indicator_one hS,
      Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := qBoundaryMeasure γ (freeFieldN ϖ X ω)))]
  rw [Measure.map_apply hZ hE, Measure.compProd_apply (hZ hE), lintegral_congr_ae hL,
    palm_free_Ioo hX hγ hγ2 hϖ hϖ1 hab (measurable_zoomφ γ C hE),
    Measure.map_apply hF hE, Measure.prod_apply_symm (hF hE), palmLam,
    lintegral_withDensity_eq_lintegral_mul _
      (E1.measurable_rhoNorm (γ := γ) (h := (0 : ℂ → ℝ)) measurable_const ϖ).ennreal_ofReal
      (measurable_measure_prodMk_right (μ := P) (hF hE)),
    Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  congr 1
  have hmx : MeasurableSet ((fun ω => (ω, x)) ⁻¹' (palmRep γ C ϖ X ⁻¹' E)) :=
    (hF hE).preimage measurable_prodMk_right
  rw [← lintegral_indicator_one hmx]
  refine lintegral_congr fun ω => ?_
  by_cases hω : zoomRep γ C (coords (palmFreeField γ ϖ X x ω), x) ∈ E
  · rw [zoomφ, indicator_of_mem hω,
      indicator_of_mem (show ω ∈ (fun ω => (ω, x)) ⁻¹' (palmRep γ C ϖ X ⁻¹' E) from hω)]
    rfl
  · rw [zoomφ, indicator_of_notMem hω,
      indicator_of_notMem (show ω ∉ (fun ω => (ω, x)) ⁻¹' (palmRep γ C ϖ X ⁻¹' E) from hω)]

end

/-- **Node B (`Prop17FreePalmIdStmt γ ϖ a b`), proved for admissible probability `ϖ`.** -/
theorem prop17FreePalmIdStmt_of_adm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ}
    (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1) {a b : ℝ} {N : ℕ}
    (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) : Prop17FreePalmIdStmt γ ϖ a b := by
  intro Ω _ P X hP hX h ν hν hae hmeas
  haveI := hP
  haveI := hν
  haveI : IsProbabilityMeasure ϖ := ⟨hϖ1⟩
  have hF := fun C => measurable_palmRep hX γ C ϖ
  have hU := fun C => compProd_map_zoomCoords hX hγ hγ2 hϖ hϖ1 hab hae (hmeas C)
  have hR : ((P.prod (palmLam γ ϖ a b)).map (palmRep γ 0 ϖ X)) univ =
      ∫⁻ x in Icc a b, ENNReal.ofReal (rhoNorm γ 0 ϖ x) := by
    rw [Measure.map_apply (hF 0) MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod, measure_univ, one_mul, palmLam, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  have hLm : ((P ⊗ₘ ν.restrict (measurableSet_Icc (a := a) (b := b))).map
      (zoomCoords γ 0 h)) univ = palmMass P ν a b := by
    rw [Measure.map_apply (hmeas 0) MeasurableSet.univ, preimage_univ,
      Measure.compProd_apply MeasurableSet.univ, palmMass]
    refine lintegral_congr fun ω => ?_
    rw [preimage_univ, Kernel.restrict_apply, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
  have hM : palmMass P ν a b = ∫⁻ x in Icc a b, ENNReal.ofReal (rhoNorm γ 0 ϖ x) := by
    rw [← hLm, hU 0, hR]
  refine ⟨fun C => palmRep γ C ϖ X, hF, ?_, fun C => ?_⟩
  · have hg := ae_palmFreeField_good (P := P) hX hγ hγ2 hϖ hϖ1 hab
    have hac : palmIntensity γ ϖ a b ≪ volume.restrict (Icc a b) :=
      Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
    filter_upwards [hac.ae_le hg] with x hx C
    filter_upwards [hx] with ω hω
    exact (zoomCoords_eq_zoomRep hω C x).symm
  · rw [palmLaw, Measure.map_smul _ (hmeas C).aemeasurable, hU C, palmIntensity,
      Measure.prod_smul_right, Measure.map_smul _ (hF C).aemeasurable, hM, palmLam]

/-- **Node B for the instance used in Proposition 1.7** (`ϖ = foldedCircle 0 3`, `[0, 1]`). -/
theorem prop17FreePalmIdStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Prop17FreePalmIdStmt γ (foldedCircle 0 3) 0 1 := by
  have habN : Icc (0 : ℝ) 1 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by
    intro t ht; simp only [Nat.cast_one, mem_Icc] at ht ⊢; constructor <;> linarith [ht.1, ht.2]
  exact prop17FreePalmIdStmt_of_adm hγ hγ2
    (isAdmissibleH_foldedCircle (by simp [Hbar]) (by norm_num)) measure_univ habN

/-- **Proposition 1.7 from the three free-field nodes A, B, C**, through the corrected shift
locality (`theorem1_7_of_palmZoom'`, which uses the proved `prop17ShiftDetStmt'_holds`). -/
theorem theorem1_7_of_freeNodesAC
    (hA : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreeModStmt γ (foldedCircle 0 3))
    (hB : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreePalmIdStmt γ (foldedCircle 0 3) 0 1)
    (hC : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1) :
    theorem1_7 :=
  theorem1_7_of_palmZoom' fun γ hγ hγ2 => prop17PalmZoomStmt_of_freeNodes hγ hγ2
    (prop17FreeRegRestStmt_of_mod hγ hγ2 (hA γ hγ hγ2)) (hB γ hγ hγ2) (hC γ hγ hγ2)

/-- **Proposition 1.7 from node C alone** (nodes A and B are proved). -/
theorem theorem1_7_of_fixedZoom
    (hC : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1) :
    theorem1_7 :=
  theorem1_7_of_freeNodesAC (fun _ hγ hγ2 => prop17FreeModStmt_holds hγ hγ2 _)
    (fun _ hγ hγ2 => prop17FreePalmIdStmt_holds hγ hγ2) hC

end Raw
end FieldLaw
end S5
end QuantumZipper
