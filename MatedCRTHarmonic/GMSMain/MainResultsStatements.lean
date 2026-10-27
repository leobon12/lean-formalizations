import MatedCRTHarmonic.GMSMain.MainResultsDraft

/-!
# Seven main-result statements, factored per coupling

The seven theorem statements all have the shape

`∀ γ, 0 < γ → γ < 2 → ∀ Ω [MeasurableSpace Ω] [StandardBorelSpace Ω] P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm,
  MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm → Body P η bm`,

where the body only mentions the probability `P`, the curve `η` and the Brownian path `bm` of the coupling. This file
records each body VERBATIM (with the local names of `MainResultsDraft`: `MainResults.energyOn G` for `G.energyOn`, etc.) as a
definition `…Body P η bm`, so that inputs and adapters can be stated per coupling. The theorems in
`MainResultsAnchors.lean` are stated with the full verbatim anchor types; they unfold to `∀ … → …Body P η bm` by `rfl`.

| draft anchor | body |
|---|---|
| `matedCRT_energy_le_add_of_matingOfTrees` ([18] Theorem 3.2) | `Theorem32Body` |
| `matedCRT_energy_le_of_matingOfTrees` ([18] Theorem 1.3, repaired) | `Theorem13Body` |
| `matedCRT_green_and_recurrent_of_matingOfTrees` ([18] Theorem 1.4) | `Theorem14GreenBody ∧ RecurrentBody` |
| `matedCRT_holder_of_matingOfTrees` ([18] Theorem 1.5, main, (a)) | `Theorem15Body` |
| `matedCRT_holder_of_matingOfTrees_simplyConnected` (literal, (b)) | `Theorem15SCBody` |
| `matedCRT_tutte_edge_le_of_matingOfTrees` ([18] Corollary 1.6, main) | `Corollary16Body` |
| `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected` (literal) | `Corollary16SCBody` |
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

variable {Ω : Type} [MeasurableSpace Ω]

/-- The body of the draft anchor `matedCRT_energy_le_add_of_matingOfTrees` ([18] Theorem 3.2), verbatim. -/
def Theorem32Body (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C →
    ∃ A : ℝ, 0 < A ∧ ∃ Cr : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ D : Set ℂ, ∀ hD : IsOpen D, D ⊆ ball (0 : ℂ) ρ →
      (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
      HasBoundedConvexity C D →
      ∀ f : ℂ → ℝ, ∀ hf : DifferentiableOn ℝ f D,
        (∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z - fderiv ℝ f w‖ ≤ ε ^ (-β) * dist z w) →
        (∀ z ∈ D, |f z| ≤ ε ^ (-β)) → (∀ z ∈ D, ‖fderiv ℝ f z‖ ≤ ε ^ (-β)) →
        ContinuousOn f (closure D) →
          P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
            (∃ g : ℤ → ℝ,
              IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
            ∀ g : ℤ → ℝ,
              IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
              energyOn (MatedCRT.graph ε (bm ω) h) (verticesMeeting (cell ε (η ω)) D) g ≤
                ENNReal.ofReal A * dirichletEnergy f D hD hf + ENNReal.ofReal (ε ^ α)} ≤
            ENNReal.ofReal (Cr * ε ^ α)

/-- The body of the draft anchor `matedCRT_energy_le_of_matingOfTrees` ([18] Theorem 1.3, repaired), verbatim. -/
def Theorem13Body (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ C : ℝ, 1 ≤ C → ∃ A : ℝ, 0 < A ∧
    ∀ D : Set ℂ, ∀ hD : IsOpen D, D ⊆ ball (0 : ℂ) ρ → HasBoundedConvexity C D →
    (∀ r ∈ Ioo (0 : ℝ) 1, volume (thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) →
    ∀ f : ℂ → ℝ, ∀ hf : DifferentiableOn ℝ f D, ContinuousOn (fderiv ℝ f) D →
      (∃ L : ℝ≥0, LipschitzOnWith L (fderiv ℝ f) D) → ContinuousOn f (closure D) →
      ∃ Cf : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
          (∃ g : ℤ → ℝ,
            IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
          ∀ g : ℤ → ℝ,
            IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
            energyOn (MatedCRT.graph ε (bm ω) h) (verticesMeeting (cell ε (η ω)) D) g ≤
              ENNReal.ofReal A * dirichletEnergy f D hD hf} ≤
          ENNReal.ofReal (Cf * ε ^ α)

/-- The first conjunct of the draft anchor `matedCRT_green_and_recurrent_of_matingOfTrees` ([18] Theorem 1.4,
(1.8)), verbatim. -/
def Theorem14GreenBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ,
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        ENNReal.ofReal (1 / A * Real.log ε⁻¹) ≤
          exitGreen (MatedCRT.graph ε (bm ω) h)
              (verticesMeeting (cell ε (η ω)) (ball (0 : ℂ) ρ)) 0 0 /
            ((MatedCRT.graph ε (bm ω) h).deg 0 : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * ε ^ α)

/-- The second conjunct of the draft anchor `matedCRT_green_and_recurrent_of_matingOfTrees` ([18] Theorem 1.4,
recurrence), verbatim. -/
def RecurrentBody (P : Measure Ω) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), (MatedCRT.graph ε (bm ω) h).Recurrent

/-- The body of the draft anchor `matedCRT_holder_of_matingOfTrees` ([18] Theorem 1.5, main form), verbatim. -/
def Theorem15Body (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
    ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
    ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
        ∀ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
          ∀ x ∈ verticesMeeting (cell ε (η ω)) D,
            ∀ y ∈ verticesMeeting (cell ε (η ω)) D,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
        ENNReal.ofReal (C * ε ^ α)

/-- The body of the draft anchor `matedCRT_holder_of_matingOfTrees_simplyConnected` ([18] Theorem 1.5, literal
form), verbatim. -/
def Theorem15SCBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
    ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
    ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g) ∧
        ∀ g : ℤ → ℝ,
          IsHarmonicExtension (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D f g →
          ∀ x ∈ verticesMeeting (cell ε (η ω)) D,
            ∀ y ∈ verticesMeeting (cell ε (η ω)) D,
              |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
        ENNReal.ofReal (C * ε ^ α)

/-- The body of the draft anchor `matedCRT_tutte_edge_le_of_matingOfTrees` ([18] Corollary 1.6, main form),
verbatim. -/
def Corollary16Body (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
    ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
    ∃ C : ℝ, Tendsto (fun ε : ℝ =>
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ Φ : ℤ → ℂ,
          IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ) ∧
        ∀ Φ : ℤ → ℂ,
          IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ →
          ∀ e : MatedCRT.Edge ε (bm ω),
            (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cell ε (η ω)) D →
            (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cell ε (η ω)) D →
              ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0)

/-- The body of the draft anchor `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected` ([18] Corollary 1.6,
literal form), verbatim. -/
def Corollary16SCBody (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
    ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
    ∃ C : ℝ, Tendsto (fun ε : ℝ =>
      P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
        (∃ Φ : ℤ → ℂ,
          IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ) ∧
        ∀ Φ : ℤ → ℂ,
          IsTutteEmbedding (MatedCRT.graph ε (bm ω) h) (cell ε (η ω)) D Φ →
          ∀ e : MatedCRT.Edge ε (bm ω),
            (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (cell ε (η ω)) D →
            (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (cell ε (η ω)) D →
              ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0)

end MatedCRTHarmonic.GMSMain.MainResults
