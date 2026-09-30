import QuantumZipper.Proofs.LQG.WedgeBdryInfB2
import QuantumZipper.Proofs.LQG.WedgeBoundary
import QuantumZipper.Proofs.Section5.Prop17Point

/-!
# WEDGE-BDRY 4 (b), 3/3: clause 3 of `S5.WedgeBoundaryRegularStmt` for a `γ`-quantum wedge

`InfMassIci γ x` is `qBoundaryMeasure γ x [0,∞) = ⊤` (infinite boundary length; Sheffield
arXiv:1012.4797 §1.6, p. 21: "an infinite amount in each neighborhood of ∞"). This file
transfers the reference-field statement `ae_qBoundaryMeasure_Ici_top_wedgeField` (file
`WedgeBdryInfB2`) first to the canonical description of the reference field (a rescaling by
`scaleParam > 0`, which preserves `ν[0,∞) = ⊤` because `ν` is pushed forward by `u ↦ u/a`) and
then to every quantum wedge through the law identity of `IsQuantumWedge`
(`ae_of_fieldLawFull_eq`), and assembles clause 3 with clauses 1–2
(`ae_atomless_pos_of_isQuantumWedge`) into `S5.WedgeBoundaryRegularStmt γ γ`, conditional only on
`WedgeBdryFreeInfStmt` (item 4 (a)) and the two conditions of the handoff (R23 (b): a.s.
`0 < scaleParam` for the reference field, and a.e.-measurability of the two full-coordinate maps).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace WedgeBdry

/-- **Infinite boundary mass on `[0,∞)`.** -/
def InfMassIci (γ : ℝ) (x : FieldSample) : Prop := qBoundaryMeasure γ x (Ici (0 : ℝ)) = ⊤

/-- Infinite boundary mass together with goodness (a measurable event of the sample). -/
def InfMassGood (γ : ℝ) (x : FieldSample) : Prop := InfMassIci γ x ∧ IsLQGGood γ x

theorem measurableSet_infMassGood (γ : ℝ) : MeasurableSet {x : FieldSample | InfMassGood γ x} := by
  classical
  set g : FieldSample → Measure ℝ :=
    fun x => if IsLQGGood γ x then qBoundaryMeasure γ x else 0 with hg_def
  have hg : Measurable g := GoodMeas.measurable_qBoundaryMeasure_global γ
  have hcomp : Measurable fun x : FieldSample => (g x) (Ici (0 : ℝ)) :=
    (Measure.measurable_coe measurableSet_Ici).comp hg
  have he : {x : FieldSample | InfMassGood γ x} = {x | IsLQGGood γ x} ∩
      {x | (g x) (Ici (0 : ℝ)) = ⊤} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, InfMassGood, InfMassIci]
    constructor
    · rintro ⟨hI, hG⟩
      exact ⟨hG, by simpa only [hg_def, if_pos hG] using hI⟩
    · rintro ⟨hG, hI⟩
      exact ⟨by simpa only [hg_def, if_pos hG] using hI, hG⟩
  rw [he]
  exact (GoodMeas.measurableSet_isLQGGood γ).inter (hcomp (measurableSet_singleton ⊤))

theorem infMassGood_reconstruct (γ : ℝ) (x : FieldSample) :
    InfMassGood γ (Factorization.reconstruct (Factorization.coords x)) ↔ InfMassGood γ x := by
  simp only [InfMassGood, InfMassIci, qBoundaryMeasure_reconstruct,
    GoodSample.isLQGGood_iff_reconstruct]

/-- Rescaling by `a > 0` pushes `ν` forward by `u ↦ u/a`, which preserves `ν[0,∞) = ⊤`. -/
theorem infMassIci_rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsLQGGood γ x)
    {a : ℝ} (ha : 0 < a) : InfMassIci γ (rescale x (Qc γ) a) ↔ InfMassIci γ x := by
  have hm : Measurable fun u : ℝ => u / a := measurable_id.div_const a
  rw [InfMassIci, InfMassIci, GoodTransforms.qBoundaryMeasure_rescale hx hγ ha,
    Measure.map_apply hm measurableSet_Ici]
  have e : (fun u : ℝ => u / a) ⁻¹' Ici (0 : ℝ) = Ici (0 : ℝ) := by
    ext u
    simp only [mem_preimage, mem_Ici, div_nonneg_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, h2⟩) <;> linarith
    · intro h; exact Or.inl ⟨h, ha.le⟩
  rw [e]

/-- **The canonical description of the reference wedge field has infinite boundary mass.** -/
theorem ae_infMassGood_canonical_wedgeField (hInf : WedgeBdryFreeInfStmt) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα : α < Qc γ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess α (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P')
    (hscale : ∀ᵐ ω ∂P',
      0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) :
    ∀ᵐ ω ∂P',
      InfMassGood γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) := by
  obtain ⟨α'', hαα'', hα''Q⟩ : ∃ α'' : ℝ, α < α'' ∧ α'' < Qc γ :=
    ⟨(α + Qc γ) / 2, by linarith, by linarith⟩
  filter_upwards [ae_qBoundaryMeasure_Ici_top_wedgeField hInf hγ hγ2 hαα'' hα''Q Ω' P' X A
      inferInstance hX hA hI, ae_bReg_wedgeField hγ hγ2 hα hX hA hI, hscale]
    with ω h1 h2 h3
  exact ⟨(infMassIci_rescale hγ h2.1 h3).2 h1, h2.1.rescale hγ h3⟩

/-- **Clause 3 of `WedgeBoundaryRegularStmt` for a quantum wedge**, given the free-field
statement (a), the a.s. positivity of `scaleParam` for the reference field and the
a.e.-measurability of the two full-coordinate maps. -/
theorem ae_infMassIci_of_isQuantumWedge (hInf : WedgeBdryFreeInfStmt) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample) (hY : IsQuantumWedge γ γ Y P)
    (hYm : AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
      fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P)
    (href : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
      IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      AEMeasurable (fun ω => (CoordsFull.coordsFull
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))),
        fun ρ : TestFun H => pairRaw
          (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ρ.1)) P') :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (Y ω) (Ici (0 : ℝ)) = ⊤ := by
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hY
  obtain ⟨hsc, hm⟩ := href Ω' P' X A hP' hX hA hI
  filter_upwards [ae_of_fieldLawFull_eq hlaw hYm hm (InfMassGood γ)
    (measurableSet_infMassGood γ) (infMassGood_reconstruct γ)
    (ae_infMassGood_canonical_wedgeField hInf hγ hγ2 hα hX hA hI hsc)] with ω hω
  exact hω.1

/-- **Clause 3 of `S5.WedgeBoundaryRegularStmt γ γ`**, conditional on the free-field statement
(item 4 (a)) and the two handoff conditions (R23 (b) and the a.e.-measurability of the
full-coordinate maps); clauses 1–2 come from `ae_atomless_pos_of_isQuantumWedge`. -/
theorem wedgeBoundaryRegularStmt_of_freeInf (hInf : WedgeBdryFreeInfStmt) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hYm : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Ω → FieldSample), IsQuantumWedge γ γ Y P →
      AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
        fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P)
    (href : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
      IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      AEMeasurable (fun ω => (CoordsFull.coordsFull
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))),
        fun ρ : TestFun H => pairRaw
          (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ρ.1)) P') :
    S5.WedgeBoundaryRegularStmt γ γ := by
  intro Ω _ P _ Y hY
  filter_upwards [ae_atomless_pos_of_isQuantumWedge hγ hγ2 P Y hY (hYm P Y hY) href,
    ae_infMassIci_of_isQuantumWedge hInf hγ hγ2 P Y hY (hYm P Y hY) href] with ω h1 h2
  exact ⟨h1.1, h1.2, h2⟩

end WedgeBdry

end QuantumZipper
