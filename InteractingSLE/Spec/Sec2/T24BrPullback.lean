import InteractingSLE.Spec.Sec2.MartingaleExtract
import MathFin.Probability.Martingales.MartingaleSetIntegral

/-!
# Theorem 2.4: restriction to a conull subspace

Pulling a filtration and its local martingales back along a measure-preserving measurable
embedding allows the converse to discard exceptional paths before adding independent noise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'}

/-- The inverse-image filtration of a measurable map. -/
def pullbackFiltration (𝓕 : Filtration ℝ≥0 mΩ) (π : Ω' → Ω) (hπ : Measurable π) :
    Filtration ℝ≥0 mΩ' where
  seq t := (𝓕 t).comap π
  mono' _ _ h := MeasurableSpace.comap_mono (𝓕.mono h)
  le' t := (MeasurableSpace.comap_mono (𝓕.le t)).trans hπ.comap_le

/-- Martingales pull back along measure-preserving measurable embeddings. -/
theorem martingale_pullback [IsFiniteMeasure P] [IsFiniteMeasure Q] {π : Ω' → Ω}
    (hπ : MeasurePreserving π Q P) (hemb : MeasurableEmbedding π)
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) :
    Martingale (fun t ω => X t (π ω)) (pullbackFiltration 𝓕 π hπ.measurable) Q := by
  refine martingale_iff_setIntegral_eq.2 ⟨?_, ?_, ?_⟩
  · intro t
    exact (hX.stronglyMeasurable t).comp_measurable
      (measurable_iff_comap_le.2 le_rfl)
  · exact fun t => hπ.integrable_comp_of_integrable (hX.integrable t)
  · intro s t hst A hA
    obtain ⟨B, hB, rfl⟩ := hA
    rw [hπ.setIntegral_preimage_emb hemb, hπ.setIntegral_preimage_emb hemb]
    exact hX.setIntegral_eq hst hB

/-- Local martingales before a random time pull back with the time and filtration. -/
theorem isLocalMartingaleBefore_pullback [IsFiniteMeasure P] [IsFiniteMeasure Q] {π : Ω' → Ω}
    (hπ : MeasurePreserving π Q P) (hemb : MeasurableEmbedding π)
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0}
    (hX : MartChar.IsLocalMartingaleBefore 𝓕 P ζ X) :
    MartChar.IsLocalMartingaleBefore (pullbackFiltration 𝓕 π hπ.measurable) Q
      (ζ ∘ π) (fun t ω => X t (π ω)) := by
  obtain ⟨σ, hσ, hσζ, hex, hmart⟩ := hX
  refine ⟨fun n => σ n ∘ π, ?_, fun n ω => hσζ n (π ω),
    hπ.quasiMeasurePreserving.ae hex, ?_⟩
  · exact fun n t => ⟨_, hσ n t, rfl⟩
  · intro n
    exact martingale_pullback hπ hemb (hmart n)

/-- Inclusion of a measurable conull set preserves its pulled-back probability measure. -/
theorem measurePreserving_conull_subtype {G : Set Ω} (hG : MeasurableSet G)
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) :
    MeasurePreserving ((↑) : G → Ω) (P.comap ((↑) : G → Ω)) P := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe hG, Measure.restrict_eq_self_of_ae_mem hGae]

end InteractingSLE.Sec2.T24Bridge
