import QuantumZipper.Proofs.Thm18.R18G3TXSide2
import QuantumZipper.Proofs.Thm18.R18G3TXSide3
import QuantumZipper.Proofs.Thm18.R18G3TJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (R-b): the `x`-side of `B → C` (`G3TCutToProfXStmt`)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71. Assembly: the change of variables
`Φ` (`g3pPalm_cv`) maps outside events to outside events (`measurableSet_g3Φ_preimage`), carries
the margin event of `B` to that of `C` and the region-1 zoom of `B` to that of `C`; the full zooms
agree with the region zooms off the area-failure events (`g3p_symmDiff_subset_area₁`,
`g3TCutAreaStmt_holds`, `g3TProfAreaStmt_holds`). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- `Φ` maps outside events to outside events. -/
theorem measurableSet_g3Φ_preimage (γ : ℝ) (i : G3Idx) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G) :
    MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] (g3Φ γ i ⁻¹' G) := by
  set O := outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂
  have hfst : ∀ f : Ω₀ → ℝ, Measurable[outsideSigma2 gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] f →
      Measurable[O] fun p : Ω₀ × ℝ => f p.1 := fun f hf =>
    measurable_iff_comap_le.2 (by
      show MeasurableSpace.comap (f ∘ Prod.fst) _ ≤ O
      rw [← MeasurableSpace.comap_comp]
      exact (MeasurableSpace.comap_mono (measurable_iff_comap_le.1 hf)).trans le_sup_left)
  have hsnd : Measurable[O] fun p : Ω₀ × ℝ => p.2 := measurable_iff_comap_le.2 le_sup_right
  have h2 : Measurable[O] fun p : Ω₀ × ℝ =>
      p.2 + (g3pc γ (g3wProf γ) i p.1 - g3pc γ (g3wCut γ i.η) i p.1) :=
    hsnd.add ((hfst _ (measurable_g3pc_out γ _ i)).sub (hfst _ (measurable_g3pc_out γ _ i)))
  have hΦ : Measurable[O, O] (g3Φ γ i) := by
    refine measurable_iff_comap_le.2 ?_
    show MeasurableSpace.comap (g3Φ γ i)
      ((outsideSigma2 gffBase.X i.t₁ i.r₁ i.t₂ i.r₂).comap Prod.fst ⊔
        (inferInstance : MeasurableSpace ℝ).comap Prod.snd) ≤ O
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    refine sup_le ?_ ?_
    · exact le_sup_left
    · exact measurable_iff_comap_le.1 h2
  exact hΦ hG

/-- A.s. statements on the base transfer to every Palm law. -/
theorem ae_palm_of_ae (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) {Q : Ω₀ → Prop}
    (h : ∀ᵐ ω ∂gffBase.P, Q ω) : ∀ᵐ p ∂(g3pPalmLaw γ g i), Q p.1 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (Measure.quasiMeasurePreserving_fst.ae h)

/-- On good samples the Palm points agree under `Φ`. -/
theorem g3pX_Φ {γ : ℝ} {i : G3Idx} {p : Ω₀ × ℝ}
    (h0B : g3pν₀ γ (g3wCut γ i.η) i p.1 (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (h0C : g3pν₀ γ (g3wProf γ) i p.1 (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (h1z : g3pν₁ γ (g3wProf γ) i p.1 (Icc (i.t₁ + i.r₁) 0) = 0)
    (hx : g3pX γ (g3wCut γ i.η) i p ∈ reg1 i) :
    g3pX γ (g3wProf γ) i (g3Φ γ i p) = g3pX γ (g3wCut γ i.η) i p := by
  have h1 := g3pν₁_cut_eq γ i p.1
  have h1zB : g3pν₁ γ (g3wCut γ i.η) i p.1 (Icc (i.t₁ + i.r₁) 0) = 0 := by rw [h1]; exact h1z
  have e := g3pX_transfer (ℓ := p.2) h1 h1zB h0B h0C (g3pν₀_le_m γ _ i p.1 _ _)
    (g3pν₀_le_m γ _ i p.1 _ _) hx
  rw [show p.2 - g3pc γ (g3wCut γ i.η) i p.1 + g3pc γ (g3wProf γ) i p.1 =
    p.2 + (g3pc γ (g3wProf γ) i p.1 - g3pc γ (g3wCut γ i.η) i p.1) by ring] at e
  exact e

/-- Pointwise locality of the zoom. -/
theorem zoom_iff_of_not_fail {s : Set LawD} {R : ℝ} {U Uf : Ω₀ × ℝ → LawD} {E F : Set (Ω₀ × ℝ)}
    (h : (U ⁻¹' s ∩ E) ∆ (Uf ⁻¹' s ∩ E) ⊆ F) {p : Ω₀ × ℝ} (hE : p ∈ E) (hF : p ∉ F) :
    (U p ∈ s ↔ Uf p ∈ s) := by
  have _ := R
  by_contra hc
  refine hF (h ?_)
  rw [mem_symmDiff]
  by_cases hU : U p ∈ s
  · exact Or.inl ⟨⟨hU, hE⟩, fun h' => hc ⟨fun _ => h'.1, fun _ => hU⟩⟩
  · exact Or.inr ⟨⟨(not_iff.1 hc).1 hU |> fun h => by
      by_contra h'; exact hc ⟨fun h'' => absurd h'' hU, fun h'' => absurd h'' h'⟩, hE⟩,
      fun h' => hU h'.1⟩

theorem g3pZ_congr {γ : ℝ} {g : ℂ → ℝ} {i i' : G3Idx} (h₁ : i.1.1 = i'.1.1)
    (h₂ : i.1.2.1 = i'.1.2.1) : g3pZ γ g i = g3pZ γ g i' := by
  have hM : g3pMass γ g i = g3pMass γ g i' := by
    funext ω
    simp only [g3pMass, G3Idx.δ, h₁, g3pν₁_congr (γ := γ) (g := g) h₁ h₂,
      g3pν₀_congr (γ := γ) (g := g) h₁ h₂]
  have h0 : g3pW0 γ g i = g3pW0 γ g i' := by
    funext p
    simp only [g3pW0, hM]
  unfold g3pZ
  rw [h0]

end R18
end QuantumZipper
