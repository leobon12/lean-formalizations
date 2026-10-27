import MatedCRTHarmonic.MoTInput.CellCoupling
import MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import MatedCRTHarmonic.CellFamily.Interfaces

/-!
# The dyadic cellular family, on a full-measure standard-Borel subspace
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The full-measure event on which every dyadic mesh has its curve-cell embedding. -/
def MeshEmbeddingGood (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (ω : Ω) : Prop :=
  (∃ h : IsLocallyFinite 1 (bm ω),
    ∃ H : CellularEmbedding (MatedCRT.graph 1 (bm ω) h) 0,
      H.cell = fun x : ℤ => η ω '' Icc ((x : ℝ) - 1) x) ∧
  ∀ k, ∃ h : IsLocallyFinite (CellFamily.mesh k) (bm ω),
    ∃ H : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) (bm ω) h) 0,
      H.cell = fun x : ℤ => η ω '' Icc
        (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)

/-- A measurable subset of the full-measure geometric event, used as the probability space for
the total random-cell family. -/
noncomputable def meshGoodSetData
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    {S : Set Ω // MeasurableSet S ∧ (∀ ω, ω ∈ S → MeshEmbeddingGood D ω) ∧
      ∀ᵐ ω ∂P, ω ∈ S} := by
  classical
  let A : Set Ω := {ω | MeshEmbeddingGood D ω}
  have hA : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [ae_unitCellularEmbedding D, ae_meshCellularEmbeddings D] with ω hunit hmesh
    exact ⟨hunit, hmesh⟩
  have hbad : P Aᶜ = 0 := by
    have hset : {ω | ¬ ω ∈ A} = Aᶜ := by ext ω; simp
    rw [← hset]
    exact ae_iff.mp hA
  let N := Classical.choose (exists_measurable_superset_of_null hbad)
  have hN := Classical.choose_spec (exists_measurable_superset_of_null hbad)
  have hbadN : Aᶜ ⊆ N := hN.1
  have hNmeas : MeasurableSet N := hN.2.1
  have hNzero : P N = 0 := hN.2.2
  refine ⟨Nᶜ, hNmeas.compl, ?_, ?_⟩
  · intro ω hω
    have hnotbad : ω ∉ Aᶜ := fun h => hω (hbadN h)
    simpa [A] using hnotbad
  · rw [ae_iff]
    have hset : {ω | ¬ ω ∈ Nᶜ} = N := by ext ω; simp
    rw [hset]
    exact hNzero

/-- The measurable full-measure subtype underlying the mesh family. -/
abbrev MeshSpace
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :=
  {ω : Ω // ω ∈ (meshGoodSetData D).val}

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)

/-- Inclusion of the good subtype preserves the original probability measure. -/
theorem meshSpace_inclusion_measurePreserving :
    MeasurePreserving (Subtype.val : MeshSpace D → Ω) (P.comap Subtype.val) P := by
  have hS := (meshGoodSetData D).property
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe hS.1]
  exact Measure.restrict_eq_self_of_ae_mem hS.2.2

theorem meshSpace_probability : IsProbabilityMeasure (P.comap (Subtype.val : MeshSpace D → Ω)) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hMP := meshSpace_inclusion_measurePreserving D
  haveI : IsProbabilityMeasure ((P.comap (Subtype.val : MeshSpace D → Ω)).map Subtype.val) := by
    rw [hMP.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map hMP.measurable.aemeasurable

/-- The chosen local-finiteness witness on the geometric full-measure event. -/
noncomputable def meshLocal (ω : MeshSpace D) (k : ℕ) :
    IsLocallyFinite (CellFamily.mesh k) (bm ω.1) :=
  Classical.choose (((meshGoodSetData D).property.2.1 ω.1 ω.2).2 k)

/-- The chosen cellular embedding on the geometric full-measure event. -/
noncomputable def meshEmbedding (ω : MeshSpace D) (k : ℕ) :
    CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) (bm ω.1) (meshLocal D ω k)) 0 :=
  Classical.choose (Classical.choose_spec (((meshGoodSetData D).property.2.1 ω.1 ω.2).2 k))

theorem meshEmbedding_cell (ω : MeshSpace D) (k : ℕ) :
    (meshEmbedding D ω k).cell = fun x : ℤ => η ω.1 '' Icc
      (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) :=
  Classical.choose_spec (Classical.choose_spec (((meshGoodSetData D).property.2.1 ω.1 ω.2).2 k))

noncomputable def meshUnitLocal (ω : MeshSpace D) : IsLocallyFinite 1 (bm ω.1) :=
  Classical.choose ((meshGoodSetData D).property.2.1 ω.1 ω.2).1

noncomputable def meshUnitEmbedding (ω : MeshSpace D) :
    CellularEmbedding (MatedCRT.graph 1 (bm ω.1) (meshUnitLocal D ω)) 0 :=
  Classical.choose (Classical.choose_spec ((meshGoodSetData D).property.2.1 ω.1 ω.2).1)

theorem meshUnitEmbedding_cell (ω : MeshSpace D) :
    (meshUnitEmbedding D ω).cell = fun x : ℤ => η ω.1 '' Icc ((x : ℝ) - 1) x :=
  Classical.choose_spec (Classical.choose_spec ((meshGoodSetData D).property.2.1 ω.1 ω.2).1)

/-- The random-cell family uses the exact edge subtype and mated-CRT graph at each dyadic mesh. -/
noncomputable def meshRandomCellFamily : CellFamily.RandomCellFamily := by
  letI : MeasurableSpace (MeshSpace D) := inferInstance
  let μ : Measure (MeshSpace D) := P.comap Subtype.val
  letI : IsProbabilityMeasure μ := meshSpace_probability D
  exact
    { Ω := MeshSpace D
      P := μ
      E := fun k ω => MatedCRT.Edge (CellFamily.mesh k) (bm ω.1)
      G := fun k ω => MatedCRT.graph (CellFamily.mesh k) (bm ω.1) (meshLocal D ω k)
      H := fun k ω => meshEmbedding D ω k }

theorem meshRandomCellFamily_meshGraph_identity (k : ℕ) :
    ∀ ω : MeshSpace D,
      (meshRandomCellFamily D).E k ω = MatedCRT.Edge (CellFamily.mesh k) (bm ω.1) ∧
      (meshRandomCellFamily D).G k ω =
        MatedCRT.graph (CellFamily.mesh k) (bm ω.1) (meshLocal D ω k) := by
  intro ω
  exact ⟨rfl, rfl⟩

theorem meshRandomCellFamily_meshCell_identity (k : ℕ) :
    ∀ ω : MeshSpace D, ∀ x : ℤ,
      ((meshRandomCellFamily D).H k ω).cell x =
        η ω.1 '' Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) := by
  intro ω x
  exact congrArg (fun f : ℤ → Set ℂ => f x) (meshEmbedding_cell D ω k)

/-- The restricted family map to Brownian path space has exactly the original law. -/
theorem meshSpace_bm_map_eq :
    (P.comap (Subtype.val : MeshSpace D → Ω)).map (fun ω => bm ω.1) = P.map bm := by
  change (P.comap (Subtype.val : MeshSpace D → Ω)).map (bm ∘ Subtype.val) = P.map bm
  rw [← Measure.map_map D.measurable_curves.2.2.2 measurable_subtype_coe]
  rw [(meshSpace_inclusion_measurePreserving D).map_eq]

/-- The whole dyadic curve-cell family, with its exact multigraph identity to mated-CRT. -/
noncomputable def matedMeshFamily : CellFamily.MultigraphCoupledRandomFamily γ := by
  let F := meshRandomCellFamily D
  let b : F.Ω → MatedCRT.Path2 := fun ω => bm ω.1
  let c : F.Ω → ℤ → Set ℂ := fun ω x => η ω.1 '' Icc ((x : ℝ) - 1) x
  have hLaw : IsCorrelatedBM2 γ ((P.comap (Subtype.val : MeshSpace D → Ω)).map b) := by
    change IsCorrelatedBM2 γ ((P.comap (Subtype.val : MeshSpace D → Ω)).map
      (fun ω : MeshSpace D => bm ω.1))
    rw [meshSpace_bm_map_eq D]
    exact D.boundaryLawBM
  have hCoupling : IsCellCoupling γ F.P b c := by
    refine ⟨?_, hLaw, ?_⟩
    · change Measurable (fun ω : MeshSpace D => bm ω.1)
      exact D.measurable_curves.2.2.2.comp measurable_subtype_coe
    · filter_upwards [] with ω
      refine ⟨meshUnitLocal D ω, meshUnitEmbedding D ω, ?_⟩
      funext x
      exact congrArg (fun f : ℤ → Set ℂ => f x) (meshUnitEmbedding_cell D ω)
  have hGraph : CellFamily.MatedCRTMultigraphIdentification F b := by
    intro k
    exact Filter.Eventually.of_forall fun ω =>
      ⟨rfl, meshLocal D ω k, rfl⟩
  exact CellFamily.MultigraphCoupledRandomFamily.ofMultigraph F b c hCoupling hGraph

/-- The restricted realization maps measure-preservingly to the original mating bundle. -/
theorem matedMeshFamily_modelMap_measurePreserving :
    MeasurePreserving (Subtype.val : (matedMeshFamily D).family.Ω → Ω)
      (matedMeshFamily D).family.P P := by
  change MeasurePreserving (Subtype.val : MeshSpace D → Ω)
    (P.comap Subtype.val) P
  exact meshSpace_inclusion_measurePreserving D

end MatedCRTHarmonic.MoTInput
