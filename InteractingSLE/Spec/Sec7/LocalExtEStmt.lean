/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtBStep8
import InteractingSLE.Spec.Sec7.LocalExtCTwoSeed

/-!
# Aux. lemmas 53 and 55 at own-filtration stops: the corrected restart statement and Theorem 1.2

Packet PROVE-LOCEXT-E. Specification p. 251 (Aux. lemma 53 applied after every own-filtration stop, with the countable
reference family of Aux. lemma 55) and Lemma 7.5's proof, p. 252 ("The finitely many possible amalgamated seed-weight
pairs and countably many chosen radii supply a measurable restart rule").

LOCEXT-B's named input `RestartReferenceExtensionStatement κ` has two defects, both corrected here:

* **measurability** (found by PROVE-LOCEXT-C): it asks for an extended reference pair over `(h, 𝒳_τ)`, whose field
  `p ↦ T (h p.1, 𝒳_τ p.1)` must be `Measurable` (frozen `IsOptionalHullCoupling`), while the recorded history
  `𝒳_τ = stoppedHistory (completedState …) τ` is only almost everywhere measurable. The corrected statement uses a
  **measurable version** `K` of `𝒳_τ`;
* **null cells**: it asks for an extended reference pair on **every** cell, including cells of probability zero
  (for instance every cell when `τ = ζ` almost surely), where no conditional coupling exists to build one from. The
  corrected statement asks for it only on cells of positive probability (`P {K ∈ A i} = 0 ∨ …`), which is all the
  measurable patching of step 8 uses.

* `RestartCellExtensionStatement κ` (the corrected statement);
* **`hasFieldLocalExtensions_of_restartCellExtension`**: LOCEXT-B's step-8 assembly from it: every coupling of an
  ordered force word has the local extensions `Determination.HasFieldLocalExtensions`;
* `localExtensionStatement_of_restartCellExtension`: the named input `Determination.LocalExtensionStatement κ`;
* **`exists_measurable_lifetime_trace_eq_comp_field_of_restartCellExtension`**: the conclusion of the frozen
  Theorem 1.2 for every `κ > 0`, from the two-seed input and `RestartCellExtensionStatement κ`;
* `lemma75DeterminationStatement_of_restartCellExtension`: LP11's input `LP.Lemma75DeterminationStatement`.

`LocalExtECells.lean` proves `RestartCellExtensionStatement κ` from the per-cell restarted two-seed extension (Aux. 53
with the data-uniform time-`0` construction).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Determination

/-- **Aux. lemmas 53 and 55 at own-filtration stops, in cell form, with a measurable recorded history and only on
cells of positive probability** (the corrected form of LOCEXT-B's `RestartReferenceExtensionStatement`; specification
pp. 245–252). For every coupling of an ordered force word, every measurability witness `hX` and every stopping time
`τ ≤ ζ` of the frozen driving filtration `𝓓 = drivingFiltration P hX`:

* a `𝓓`-stopping time `σ` with `τ ≤ σ ≤ ζ` and `τ < σ` almost surely on `{τ < ζ}` (the restarted local stop);
* a measurable version `K` of the recorded history `𝒳_τ`;
* countably many measurable cells `A i` of recorded histories, with seed weights `r_L i, r_R i > −2` and radii `r i`
  ("the finitely many possible amalgamated seed-weight pairs and countably many chosen radii"), whose preimages
  under `K` cover `{τ < ζ}` almost surely;
* on each cell `D i = {K ∈ A i}` of positive probability, a probability measure `Q` with `Q ≪ P` and `P|_{D i} ≪ Q`
  carrying an extended reference pair over `(h, K)` that recovers `𝒳_σ`. -/
def RestartCellExtensionStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (τ : Ω → WithTop ℝ≥0),
        IsStoppingTime (drivingFiltration P hX) τ → (∀ ω, τ ω ≤ (ζ ω : WithTop ℝ≥0)) →
        ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime (drivingFiltration P hX) σ ∧ (∀ ω, τ ω ≤ σ ω) ∧
          (∀ ω, σ ω ≤ (ζ ω : WithTop ℝ≥0)) ∧ (∀ᵐ ω ∂P, τ ω < (ζ ω : WithTop ℝ≥0) → τ ω < σ ω) ∧
          ∃ K : Ω → DrivingHist nL nR, Measurable K ∧
            K =ᵐ[P] stoppedHistory (completedState W VL VR ζ) τ ∧
          ∃ (A : ℕ → Set (DrivingHist nL nR)) (rL rR r : ℕ → ℝ), (∀ i, MeasurableSet (A i)) ∧
            (∀ i, -2 < rL i ∧ -2 < rR i) ∧
            (∀ᵐ ω ∂P, τ ω < (ζ ω : WithTop ℝ≥0) → ∃ i, K ω ∈ A i) ∧
            ∀ i, P {ω | K ω ∈ A i} = 0 ∨
              ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P.restrict {ω | K ω ∈ A i} ≪ Q ∧
                HasReferenceExtension.{u} κ (rL i) (rR i) (r i) Q (fun ω => (h ω, K ω))
                  (stoppedHistory (completedState W VL VR ζ) σ)

section Step8

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The local extensions of Aux. lemmas 53 and 55 at every own-filtration stop, from the corrected statement**:
under the two-seed input and `RestartCellExtensionStatement`, every coupling of an ordered force word has the local
extensions `HasFieldLocalExtensions` in its frozen driving filtration. On a null cell the determination holds
vacuously; on the other cells it is the two-seed graph of the extended reference pair; the cells are patched by
`isAEDeterminedBy_of_cells`. -/
theorem hasFieldLocalExtensions_of_restartCellExtension (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ)
    (hrest : RestartCellExtensionStatement.{u} κ) (hF : IsOrderedForceWord xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ) :
    HasFieldLocalExtensions P (drivingFiltration P hX) h W VL VR ζ := by
  intro τ hτ hτζ
  obtain ⟨σ, hσ, hτσ, hσζ, hlt, K, hKm, hKae, A, rL, rR, r, hA, hrr, hcover, hcells⟩ :=
    hrest xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX τ hτ hτζ
  refine ⟨σ, hσ, hτσ, hσζ, hlt, ?_⟩
  set X := completedState W VL VR ζ with hXdef
  have hcont := ae_continuousOn_completedState hκ hC.1
  have hYm : AEMeasurable (stoppedHistory X σ) P := aemeasurable_stoppedHistory hX hcont hσ.measurable' hσζ
  have hHm : AEMeasurable (fun ω => (h ω, K ω)) P := (hC.2.1.prodMk hKm).aemeasurable
  -- the determination on each cell
  have hcell : ∀ i, ∃ g : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR → DrivingHist nL nR,
      Measurable g ∧ ∀ᵐ ω ∂P, K ω ∈ A i → stoppedHistory X σ ω = g (h ω, K ω) := by
    intro i
    rcases hcells i with h0 | ⟨Q, hQ, hQP, hPQ, hext⟩
    · refine ⟨fun _ => (⊤, fun _ => 0), measurable_const, ?_⟩
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      simp only [mem_ofPred_eq, not_imp] at hω
      exact hω.1
    · obtain ⟨g, hg, hgQ⟩ := hext.isAEDeterminedBy hκ h2 (hrr i).1 (hrr i).2 (hHm.mono_ac hQP)
        (hYm.mono_ac hQP)
      exact ⟨g, hg, ae_imp_of_ae_restrict (hPQ.ae_le hgQ)⟩
  choose g hg hgc using hcell
  -- off the cells, `τ = ζ`, hence `σ = τ` and `𝒳_σ = 𝒳_τ = K`
  have hoff : ∀ᵐ ω ∂P, (∀ i, K ω ∉ A i) → stoppedHistory X σ ω = id (K ω) := by
    filter_upwards [hcover, hKae] with ω hω hK hno
    have hτeq : τ ω = (ζ ω : WithTop ℝ≥0) := by
      by_contra hne
      obtain ⟨i, hi⟩ := hω (lt_of_le_of_ne (hτζ ω) hne)
      exact hno i hi
    have hστ : σ ω = τ ω := le_antisymm (hτeq ▸ hσζ ω) (hτσ ω)
    rw [id, hK]
    exact stoppedHistory_congr hστ
  obtain ⟨G, hG, hYG⟩ := isAEDeterminedBy_of_cells A hA g hg hgc id measurable_id hoff
  refine ⟨G, hG, ?_⟩
  filter_upwards [hYG, hKae] with ω h1 h2
  rw [h1]
  show G (h ω, K ω) = G (h ω, stoppedHistory X τ ω)
  rw [h2]

/-- **The named input `Determination.LocalExtensionStatement κ` from `RestartCellExtensionStatement`**. -/
theorem localExtensionStatement_of_restartCellExtension (hκ : 0 < κ)
    (hrest : RestartCellExtensionStatement.{u} κ) : LocalExtensionStatement.{u} κ := by
  intro h2 nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX
  exact hasFieldLocalExtensions_of_restartCellExtension hκ h2 hrest hF hC hX

/-- **The conclusion of the frozen Theorem 1.2 for every `κ > 0`** from the two-seed input and Aux. lemmas 53–55 in the
corrected cell form `RestartCellExtensionStatement`. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_restartCellExtension (hκ : 0 < κ)
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hrest : RestartCellExtensionStatement.{u} κ)
    (hF : IsOrderedForceWord xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_localExtension hκ h2
    (localExtensionStatement_of_restartCellExtension hκ hrest) hF hC

/-- **Lemma 7.5 with Aux. 52–55** (LP11's input `LP.Lemma75DeterminationStatement`) from Proposition 7.3 and
`RestartCellExtensionStatement` for `0 < κ < 4`. -/
theorem lemma75DeterminationStatement_of_restartCellExtension
    (h73d : Prop73DeterminationStatement.{u}) (h73t : Sec7.Prop73TraceStatement.{u})
    (hrest : ∀ κ : ℝ, 0 < κ → κ < 4 → RestartCellExtensionStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  lemma75DeterminationStatement_of_inputs h73d h73t fun κ hκ hκ4 =>
    localExtensionStatement_of_restartCellExtension hκ (hrest κ hκ hκ4)

end Step8

end LocalExt

end InteractingSLE
