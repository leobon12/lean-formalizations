import MatedCRTHarmonic.GMSMain.MainResultsTheorem13
import MatedCRTHarmonic.BundleSec4.MesoModelFinal
import MatedCRTHarmonic.MesoModel.CloseCellModel

/-!
# Seven main-result statements from three inputs

The seven theorem anchors of the draft surface v5,
stated **verbatim** (with the local names of `MainResultsDraft` for the seven draft definitions; retargeted to the frozen
names by `rfl` for the corresponding declarations), each proved from the fewest named inputs of `MainResultsInputs`:

| anchor | theorem | inputs |
|---|---|---|
| [18] Theorem 3.2 | `matedCRT_energy_le_add_of_matingOfTrees_of_inputs` | `Theorem32Input` |
| [18] Theorem 1.3, repaired | `matedCRT_energy_le_of_matingOfTrees_of_inputs` | `Theorem32Input` |
| [18] Theorem 1.4 | `matedCRT_green_and_recurrent_of_matingOfTrees_of_inputs` | `Theorem14GreenInput` |
| [18] Theorem 1.5, main | `matedCRT_holder_of_matingOfTrees_of_inputs` | `Theorem15Input` |
| [18] Theorem 1.5, literal | `matedCRT_holder_of_matingOfTrees_simplyConnected_of_inputs` | `Theorem15Input` |
| [18] Corollary 1.6, main | `matedCRT_tutte_edge_le_of_matingOfTrees_of_inputs` | `Theorem15Input` |
| [18] Cor. 1.6, literal | `matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected_of_inputs` | `Theorem15Input` |

Proved here outright (no input):
* `recurrentBody_of_coupling` — the recurrence half of Theorem 1.4, for every real `ε > 0` (  `exists_cellModel_of_matingOfTrees_holds`, REC's transfer `MesoModel.matedCRTRecurrenceInput_of_cellModel` at the
  law `P.map bm`, and a.s. local finiteness).

Statement-level implications between the anchors (independent of how the inputs are proved):
* `theorem13Body_of_theorem32Body` (`MainResultsTheorem13`): Theorem 3.2 ⇒ repaired Theorem 1.3;
* `theorem15SCBody_of_theorem15Body`: main ⇒ literal Theorem 1.5 (`isConnected_compl_of_simplyConnected`);
* `corollary16Body_of_theorem15Body`: Theorem 1.5 ⇒ Corollary 1.6 (`corollary16_tendsto_of_theorem15`:
  `f = Re, Im` and [18] Lemma 2.7 at every real `ε`, T16D's `lemma27_cellAt`);
* `corollary16SCBody_of_corollary16Body`: main ⇒ literal Corollary 1.6 (TOPO).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Theorem 1.4, recurrence, for every frozen coupling, at every real mesh, with no input**: for every `ε > 0`,
almost surely `MatedCRT.graph ε (bm ω)` is locally finite and recurrent. -/
theorem recurrentBody_of_coupling (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ0 : 0 < γ) (hγ2 : γ < 2) : RecurrentBody P bm := by
  have hMI : MatedCRT.MatingOfTreesInput γ :=
    ⟨Ω, inferInstance, hstd, P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D⟩
  have hrec := MesoModel.matedCRTRecurrenceInput_of_cellModel
    (BundleSec4.exists_cellModel_of_matingOfTrees_holds γ hγ0 hγ2 hMI)
  intro ε hε
  have hlf : ∀ᵐ ω ∂P, MatedCRT.IsLocallyFinite ε (bm ω) :=
    ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
      (MatedCRTHarmonic.ae_isLocallyFinite_holds γ (P.map bm) D.boundaryLawBM ε hε)
  have hr : ∀ᵐ ω ∂P, ∀ h : MatedCRT.IsLocallyFinite ε (bm ω), (MatedCRT.graph ε (bm ω) h).Recurrent :=
    ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable (hrec ε hε (P.map bm) D.boundaryLawBM)
  filter_upwards [hlf, hr] with ω h hrω
  exact ⟨h, hrω h⟩

omit [MeasurableSpace Ω] in
/-- A bounded simply connected open `D` is a domain with connected complement (TOPO). -/
theorem isConnected_and_compl_of_simplyConnected {ρ : ℝ} {Dom : Set ℂ} (hDo : IsOpen Dom)
    (hDsub : Dom ⊆ ball (0 : ℂ) ρ) (hsc : SimplyConnectedSpace Dom) : IsConnected Dom ∧ IsConnected Domᶜ := by
  have hconnD : IsConnected Dom := isConnected_iff_connectedSpace.mpr inferInstance
  exact ⟨hconnD, isConnected_compl_of_simplyConnected hDo (isBounded_ball.subset hDsub) hconnD.nonempty⟩

/-- **Theorem 1.5: main form ⇒ literal form** ( (b); TOPO). -/
theorem theorem15SCBody_of_theorem15Body (h15 : Theorem15Body P η bm) : Theorem15SCBody P η bm := by
  obtain ⟨α, hα, h15⟩ := h15
  refine ⟨α, hα, fun ρ hρ0 hρ1 χ hχ => ?_⟩
  obtain ⟨ξ, hξ, h15⟩ := h15 ρ hρ0 hρ1 χ hχ
  refine ⟨ξ, hξ, fun Dom hDo hDsub hsc => ?_⟩
  obtain ⟨hc, hcc⟩ := isConnected_and_compl_of_simplyConnected hDo hDsub hsc
  exact h15 Dom hDo hDsub hc hcc

/-- **Corollary 1.6: main form ⇒ literal form** ( (b); TOPO). -/
theorem corollary16SCBody_of_corollary16Body (h16 : Corollary16Body P η bm) : Corollary16SCBody P η bm := by
  intro ρ hρ0 hρ1
  obtain ⟨ξ', hξ', h16⟩ := h16 ρ hρ0 hρ1
  refine ⟨ξ', hξ', fun Dom hDo hDsub hsc => ?_⟩
  obtain ⟨hc, hcc⟩ := isConnected_and_compl_of_simplyConnected hDo hDsub hsc
  exact h16 Dom hDo hDsub hc hcc

/-- **Theorem 1.5 ⇒ Corollary 1.6** for one frozen coupling (`corollary16_tendsto_of_theorem15`; its local
copies `IsHarmonicExtension`, `IsTutteEmbedding`, `cellAt` are the draft definitions by `rfl`). -/
theorem corollary16Body_of_theorem15Body
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hstd : StandardBorelSpace Ω)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (h15 : Theorem15Body P η bm) : Corollary16Body P η bm :=
  T16D.corollary16_tendsto_of_theorem15 D hstd hγ h15

end Coupling

/-! ### The seven draft anchors (verbatim statements, local names of `MainResultsDraft`) -/

/-- **[18] Theorem 3.2 on every mating-of-trees coupling**, from named input 1 (Theorem 3.2 at real `ε`). -/
theorem matedCRT_energy_le_add_of_matingOfTrees_of_inputs (h32 : Theorem32Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
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
                  ENNReal.ofReal (Cr * ε ^ α) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    theorem32Body_of_raw (h32 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

/-- **[18] Theorem 1.3 (repaired) on every mating-of-trees coupling**, from named input 1 (via Theorem 3.2
and `theorem13Body_of_theorem32Body`). -/
theorem matedCRT_energy_le_of_matingOfTrees_of_inputs (h32 : Theorem32Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
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
                ENNReal.ofReal (Cf * ε ^ α) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    theorem13Body_of_theorem32Body D
      (theorem32Body_of_raw (h32 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D))

/-- **[18] Theorem 1.4 on every mating-of-trees coupling**: (1.8) from named input 2 ((1.8) at real `ε`), and
recurrence with no input (`recurrentBody_of_coupling`). -/
theorem matedCRT_green_and_recurrent_of_matingOfTrees_of_inputs (h14 : Theorem14GreenInput) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        (∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ,
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              ENNReal.ofReal (1 / A * Real.log ε⁻¹) ≤
                exitGreen (MatedCRT.graph ε (bm ω) h)
                    (verticesMeeting (cell ε (η ω)) (ball (0 : ℂ) ρ)) 0 0 /
                  ((MatedCRT.graph ε (bm ω) h).deg 0 : ℝ≥0∞)} ≤
              ENNReal.ofReal (C * ε ^ α)) ∧
        ∀ ε : ℝ, 0 < ε →
          ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite ε (bm ω), (MatedCRT.graph ε (bm ω) h).Recurrent :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    ⟨theorem14GreenBody_of_raw (h14 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D),
      recurrentBody_of_coupling D hstd hγ0 hγ2⟩

/-- **[18] Theorem 1.5 (main form, (a)) on every mating-of-trees coupling**, from named input 3. -/
theorem matedCRT_holder_of_matingOfTrees_of_inputs (h15 : Theorem15Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
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
              ENNReal.ofReal (C * ε ^ α) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    h15 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D

/-- **[18] Theorem 1.5 (literal form, (b)) on every mating-of-trees coupling**, from named input 3 (via the main
form and TOPO). -/
theorem matedCRT_holder_of_matingOfTrees_simplyConnected_of_inputs (h15 : Theorem15Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
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
              ENNReal.ofReal (C * ε ^ α) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    theorem15SCBody_of_theorem15Body (h15 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

/-- **[18] Corollary 1.6 (main form, (a)) on every mating-of-trees coupling**, from named input 3 (via T16D). -/
theorem matedCRT_tutte_edge_le_of_matingOfTrees_of_inputs (h15 : Theorem15Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
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
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    corollary16Body_of_theorem15Body D hstd ⟨hγ0, hγ2⟩
      (h15 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

/-- **[18] Corollary 1.6 (literal form, (b)) on every mating-of-trees coupling**, from named input 3 (via the
main form and TOPO). -/
theorem matedCRT_tutte_edge_le_of_matingOfTrees_simplyConnected_of_inputs (h15 : Theorem15Input) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
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
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) :=
  fun γ hγ0 hγ2 Ω _ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    corollary16SCBody_of_corollary16Body (corollary16Body_of_theorem15Body D hstd ⟨hγ0, hγ2⟩
      (h15 γ ⟨hγ0, hγ2⟩ Ω hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D))

end MatedCRTHarmonic.GMSMain.MainResults
