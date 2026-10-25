import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.CircleAverageShift
import LQGMetric.Meas.UM




set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

 


theorem invariant_borel_proxy_two_laws
    (μ₀ μ₁ : Measure DistC) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (E : Set DistC) (hE : LQGMetric.UMeasurableSet E)
    (N : DistC → DistC) (hN : Measurable N)
    (hNconst : ∀ g : DistC, ∀ c : ℝ,
      N (LQGMetric.addConst g c) = N g)
    (hEN : ∀ g : DistC, g ∈ E ↔ N g ∈ E)
    {ι : Type} (Z : Finset ι) (F : ι → Set DistC)
    (hFm : ∀ i ∈ Z, MeasurableSet (F i))
    (hFc : ∀ i ∈ Z, ∀ g : DistC, ∀ c : ℝ,
      g ∈ F i ↔ LQGMetric.addConst g c ∈ F i)
    (hEF : ∀ g ∈ E, ∀ i ∈ Z, g ∈ F i) :
    ∃ B : Set DistC,
      MeasurableSet B ∧
      (∀ g : DistC, ∀ c : ℝ,
        g ∈ B ↔ LQGMetric.addConst g c ∈ B) ∧
      (∀ g ∈ B, ∀ i ∈ Z, g ∈ F i) ∧
      E =ᵐ[μ₀] B ∧ E =ᵐ[μ₁] B := by
  let ν : Measure DistC := μ₀.map N + μ₁.map N
  have : IsFiniteMeasure ν := inferInstance
  let E₀ : Set DistC := toMeasurable ν E
  have hE₀m : MeasurableSet E₀ := measurableSet_toMeasurable _ _
  have hae : E =ᵐ[ν] E₀ :=
    (hE.nullMeasurableSet ν).toMeasurable_ae_eq.symm
  have hae₀ : E =ᵐ[μ₀.map N] E₀ := (ae_add_measure_iff.mp hae).1
  have hae₁ : E =ᵐ[μ₁.map N] E₀ := (ae_add_measure_iff.mp hae).2
  let B : Set DistC := {g | N g ∈ E₀ ∧ ∀ i ∈ Z, g ∈ F i}
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · have hsite : MeasurableSet {g : DistC | ∀ i ∈ Z, g ∈ F i} := by
      convert Z.measurableSet_biInter hFm using 1
      ext g
      simp
    exact (hE₀m.preimage hN).inter hsite
  · intro g c
    simp only [B, Set.mem_ofPred_eq, hNconst]
    constructor
    · rintro ⟨he, hf⟩
      exact ⟨he, fun i hi => (hFc i hi g c).1 (hf i hi)⟩
    · rintro ⟨he, hf⟩
      exact ⟨he, fun i hi => (hFc i hi g c).2 (hf i hi)⟩
  · intro g hg i hi
    exact hg.2 i hi
  · have hmap := ae_of_ae_map hN.aemeasurable hae₀
    filter_upwards [hmap] with g hg
    apply propext
    change (g ∈ E) ↔ (N g ∈ E₀ ∧ ∀ i ∈ Z, g ∈ F i)
    constructor
    · intro he
      exact ⟨(hg.mp ((hEN g).mp he)), hEF g he⟩
    · intro hb
      exact (hEN g).mpr (hg.mpr hb.1)
  · have hmap := ae_of_ae_map hN.aemeasurable hae₁
    filter_upwards [hmap] with g hg
    apply propext
    change (g ∈ E) ↔ (N g ∈ E₀ ∧ ∀ i ∈ Z, g ∈ F i)
    constructor
    · intro he
      exact ⟨(hg.mp ((hEN g).mp he)), hEF g he⟩
    · intro hb
      exact (hEN g).mpr (hg.mpr hb.1)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
