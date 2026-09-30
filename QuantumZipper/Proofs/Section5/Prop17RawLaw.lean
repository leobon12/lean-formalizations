import QuantumZipper.Proofs.Section5.Prop17RawAS

/-!
# Proposition 1.7, node D5-e: reduction of `Prop17RefShiftStmt` to circle coordinates

`fieldLawFull H Y P` is the law of `(coordsFull (Y ω), ρ ↦ pairRaw (Y ω) ρ)`. When, for every
test function, `pairRaw = pairTest` almost surely (and the data is a.e.-measurable), the second
component is a fixed measurable function `pairOfCoords` of the first
(`fieldLawFull_eq_map_coordsFull`), so the law is determined by the law of `coordsFull`.
`Prop17RawAS` proves `pairRaw = pairTest` a.s. for the reference wedge and for its shift, hence

* `prop17RefShiftStmt_of_coords`: `Prop17RefShiftStmt γ L` follows from
  `WedgeDataAEMeasStmt γ γ`, `WedgeGoodStmt γ γ`, the a.s. positivity of the two scale parameters
  (`Prop17ScalePosStmt γ L`) and the **stationarity of the law of `coordsFull`** of the reference
  wedge under the shift (`Prop17RefCoordsShiftStmt γ L`), which is the level at which D5-c's
  shift identity is exact.

Own elementary argument (law of a pair whose second coordinate is a.s. a function of the first,
through the finite-dimensional distributions, `map_eq_iff_forall_finset_map_restrict_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## 1. Laws of pairs whose coordinates agree a.s. one by one -/

theorem map_eq_of_ae_coord {ι : Type*} [IsFiniteMeasure P] {f g : Ω → ι → ℝ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) (h : ∀ i, ∀ᵐ ω ∂P, f ω i = g ω i) :
    P.map f = P.map g := by
  classical
  refine (map_eq_iff_forall_finset_map_restrict_eq (X := fun i ω => f ω i)
    (Y := fun i ω => g ω i) hf hg).2 fun I => ?_
  refine Measure.map_congr ?_
  filter_upwards [ae_all_iff.2 fun i : I => h i.1] with ω hω
  funext i
  exact hω i

theorem map_prod_eq_of_ae {ι : Type*} [IsFiniteMeasure P] {f g : Ω → (ℕ → ℝ) × (ι → ℝ)}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) (h1 : ∀ᵐ ω ∂P, (f ω).1 = (g ω).1)
    (h2 : ∀ i, ∀ᵐ ω ∂P, (f ω).2 i = (g ω).2 i) : P.map f = P.map g := by
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ℕ ⊕ ι => ℝ) with he
  have key : ∀ F : Ω → (ℕ → ℝ) × (ι → ℝ), AEMeasurable F P →
      P.map F = (P.map (e.symm ∘ F)).map e := by
    intro F hF
    rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable
      (e.symm.measurable.comp_aemeasurable hF)]
    congr 1
  rw [key f hf, key g hg, map_eq_of_ae_coord (e.symm.measurable.comp_aemeasurable hf)
    (e.symm.measurable.comp_aemeasurable hg) ?_]
  rintro (i | i)
  · filter_upwards [h1] with ω hω
    change (f ω).1 i = (g ω).1 i
    rw [hω]
  · filter_upwards [h2 i] with ω hω
    exact hω

/-! ## 2. Test pairings as a measurable function of the circle coordinates -/

/-- The regularized test pairings read off the full circle coordinates. -/
def pairOfCoords (c : ℕ → ℝ) : TestFun H → ℝ := fun ρ => pairTest (reconstruct (proj c)) ρ.1

theorem measurable_pairOfCoords : Measurable pairOfCoords :=
  measurable_pi_iff.2 fun ρ =>
    (measurable_pairTest ρ.1).comp (measurable_reconstruct.comp measurable_proj)

theorem pairOfCoords_coordsFull (x : FieldSample) (ρ : TestFun H) :
    pairOfCoords (coordsFull x) ρ = pairTest x ρ.1 := by
  simp only [pairOfCoords, ← coords_eq_proj]
  rw [Factorization.pairTest_congr (avgReg_reconstruct_coords x)]

/-- **Law through the coordinates.** If the data is a.e.-measurable and, for each test function,
`pairRaw = pairTest` a.s., then `fieldLawFull H Y P` is the push-forward of the law of
`coordsFull ∘ Y` under the graph of `pairOfCoords`. -/
theorem fieldLawFull_eq_map_coordsFull [IsFiniteMeasure P] {Y : Ω → FieldSample}
    (hm : AEMeasurable (fun ω => dataFull H (Y ω)) P)
    (hp : ∀ ρ : TestFun H, ∀ᵐ ω ∂P, pairRaw (Y ω) ρ.1 = pairTest (Y ω) ρ.1) :
    fieldLawFull H Y P =
      (P.map fun ω => coordsFull (Y ω)).map fun c => (c, pairOfCoords c) := by
  have hc : AEMeasurable (fun ω => coordsFull (Y ω)) P := hm.fst
  have hgr : Measurable fun c : ℕ → ℝ => (c, pairOfCoords c) :=
    measurable_id.prodMk measurable_pairOfCoords
  rw [AEMeasurable.map_map_of_aemeasurable hgr.aemeasurable hc]
  show P.map (fun ω => dataFull H (Y ω)) = _
  refine map_prod_eq_of_ae hm (hgr.comp_aemeasurable hc) (ae_of_all _ fun ω => rfl)
    fun ρ => ?_
  filter_upwards [hp ρ] with ω hω
  show pairRaw (Y ω) ρ.1 = pairOfCoords (coordsFull (Y ω)) ρ
  rw [pairOfCoords_coordsFull, hω]

/-! ## 3. The reduction of D5-e -/

/-- The reference wedge field of a reference tuple. -/
def refField (γ : ℝ) {Ω' : Type*} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ω : Ω') :
    FieldSample :=
  canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))

/-- **Scale positivity (hypothesis).** A.s. the reference wedge and its translate by the
length-`L` point have positive scale parameters (so both are genuine rescalings). The first half
is `Wire3.wedgeRef_scaleParam_pos_and_data_aemeasurable`. -/
def Prop17ScalePosStmt (γ L : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) ∧
      0 < scaleParam γ (translate (refField γ X A ω) (wedgeLengthPoint γ L (refField γ X A ω)))

/-- **D5-e at the level of circle coordinates (remaining).** The law of `coordsFull` of the
reference wedge is invariant under the shift map `shiftL γ L`. -/
def Prop17RefCoordsShiftStmt (γ L : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    P'.map (fun ω => coordsFull (shiftL γ L (refField γ X A ω))) =
      P'.map (fun ω => coordsFull (refField γ X A ω))

theorem gamma_lt_Qc' {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < Qc γ := by
  unfold Qc
  have h1 : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ]; nlinarith
  linarith

/-- **D5-e, raw pairings settled.** `Prop17RefShiftStmt γ L` from the wedge data measurability
and goodness, the a.s. positivity of the two scale parameters, and the stationarity of the law
of `coordsFull` of the reference wedge. -/
theorem prop17RefShiftStmt_of_coords {γ L : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hmeas : WedgeDataAEMeasStmt γ γ) (hgood : WedgeGoodStmt γ γ)
    (hpos : Prop17ScalePosStmt γ L) (hcoords : Prop17RefCoordsShiftStmt γ L) :
    Prop17RefShiftStmt γ L := by
  intro Ω' _ P' X A hP hX hA hI
  have hW : IsQuantumWedge γ γ (refField γ X A) P' :=
    ⟨gamma_lt_Qc' hγ hγ2, Ω', _, P', X, A, hP, hX, hA, hI, rfl⟩
  have hm : AEMeasurable (fun ω => dataFull H (refField γ X A ω)) P' := hmeas P' _ hW
  have hg := hgood P' _ hW
  have hm' : AEMeasurable (fun ω => dataFull H (shiftL γ L (refField γ X A ω))) P' :=
    ((measurable_shiftData γ L).comp_aemeasurable hm).congr
      (hg.mono fun ω h => (dataFull_shiftL h).symm)
  have hpr := fun ρ : TestFun H =>
    ae_pairRaw_eq_pairTest_wedge hX (WedgeCan4.ae_continuous_wedgeProcess hA) (Qc γ) ρ
  have hpos' := hpos Ω' _ P' X A hP hX hA hI
  have h1 : ∀ ρ : TestFun H, ∀ᵐ ω ∂P',
      pairRaw (refField γ X A ω) ρ.1 = pairTest (refField γ X A ω) ρ.1 := fun ρ => by
    filter_upwards [hpr ρ, hpos'] with ω h hp
    exact (h _ hp.1).1
  have h2 : ∀ ρ : TestFun H, ∀ᵐ ω ∂P', pairRaw (shiftL γ L (refField γ X A ω)) ρ.1 =
      pairTest (shiftL γ L (refField γ X A ω)) ρ.1 := fun ρ => by
    filter_upwards [hpr ρ, hpos'] with ω h hp
    exact (h _ hp.1).2 _ _ hp.2
  show fieldLawFull H (fun ω => shiftL γ L (refField γ X A ω)) P' = fieldLawFull H (refField γ X A) P'
  rw [fieldLawFull_eq_map_coordsFull hm' h2, fieldLawFull_eq_map_coordsFull hm h1,
    hcoords Ω' _ P' X A hP hX hA hI]

end Raw
end FieldLaw
end S5
end QuantumZipper
