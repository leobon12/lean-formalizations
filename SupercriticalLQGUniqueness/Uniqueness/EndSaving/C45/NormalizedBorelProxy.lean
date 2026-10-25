import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.NormalizedShiftAC




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
open LQGMetric (DistC)

 

theorem normalized_borel_proxy_two_laws
    (μ₀ μ₁ : Measure DistC)
    (Eraw : Set DistC) (hraw : NullMeasurableSet Eraw μ₀)
    (N : DistC → DistC) (hN : Measurable N)
    (hNconst : ∀ g : DistC, ∀ c : ℝ,
      N (LQGMetric.addConst g c) = N g)
    (hfix : μ₀.map N = μ₀) (hAC : μ₁.map N ≪ μ₀)
    {ι : Type} (Z : Finset ι) (F : ι → Set DistC)
    (hFm : ∀ i ∈ Z, MeasurableSet (F i))
    (hFc : ∀ i ∈ Z, ∀ g : DistC, ∀ c : ℝ,
      g ∈ F i ↔ LQGMetric.addConst g c ∈ F i)
    (hEF : ∀ g : DistC, N g ∈ Eraw → ∀ i ∈ Z, g ∈ F i) :
    ∃ B : Set DistC,
      MeasurableSet B ∧
      (∀ g : DistC, ∀ c : ℝ,
        g ∈ B ↔ LQGMetric.addConst g c ∈ B) ∧
      (∀ g ∈ B, ∀ i ∈ Z, g ∈ F i) ∧
      (∀ᵐ g ∂μ₀, (N g ∈ Eraw) = (g ∈ B)) ∧
      (∀ᵐ g ∂μ₁, (N g ∈ Eraw) = (g ∈ B)) := by
  let E₀ : Set DistC := toMeasurable μ₀ Eraw
  have hE₀m : MeasurableSet E₀ := measurableSet_toMeasurable _ _
  have hAE : Eraw =ᵐ[μ₀] E₀ := hraw.toMeasurable_ae_eq.symm
  have hAE₀ : Eraw =ᵐ[μ₀.map N] E₀ := by
    rw [hfix]
    exact hAE
  have hAE₁ : Eraw =ᵐ[μ₁.map N] E₀ := hAC.ae_le hAE
  have hmap₀ : ∀ᵐ g ∂μ₀, (N g ∈ Eraw) = (N g ∈ E₀) :=
    ae_of_ae_map hN.aemeasurable hAE₀
  have hmap₁ : ∀ᵐ g ∂μ₁, (N g ∈ Eraw) = (N g ∈ E₀) :=
    ae_of_ae_map hN.aemeasurable hAE₁
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
  · filter_upwards [hmap₀] with g hg
    apply propext
    change (N g ∈ Eraw) ↔ (N g ∈ E₀ ∧ ∀ i ∈ Z, g ∈ F i)
    exact ⟨fun he => ⟨(Iff.of_eq hg).mp he, hEF g he⟩,
      fun hb => (Iff.of_eq hg).mpr hb.1⟩
  · filter_upwards [hmap₁] with g hg
    apply propext
    change (N g ∈ Eraw) ↔ (N g ∈ E₀ ∧ ∀ i ∈ Z, g ∈ F i)
    exact ⟨fun he => ⟨(Iff.of_eq hg).mp he, hEF g he⟩,
      fun hb => (Iff.of_eq hg).mpr hb.1⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
