/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtBStep7

/-!
# Aux. lemmas 53 and 55 at own-filtration stops: the local extensions, and Theorem 1.2's conclusion

Packet PROVE-LOCEXT-B (step 8 of the split in `planning/handoffs/PROVE-AUX52-55.md`, and the assembly). Specification
p. 251: "**Aux.** lemma 53 justifies applying the preceding local comparison conditionally after every own-filtration
stopping time strictly before the threshold. … If the previous stopped history is a function of `h`, its active
conformal map and the transformed active field are also measurable functions of `h`. Applying **Aux.** lemma 55
conditionally and using its countable reference family produces a strictly longer own-filtration stopped driving
history determined by `h`." Lemma 7.5's proof (p. 252): "The finitely many possible amalgamated seed-weight pairs and
countably many chosen radii supply a measurable restart rule."

* `RestartReferenceExtensionStatement κ` (**named input**: Aux. 53 with (HL1)–(HL9) of Aux. 55 and Aux. 54 at an
  own-filtration stop): at every stopping time `τ ≤ ζ` of the frozen driving filtration there is a stopping time
  `σ ∈ [τ, ζ]`, strictly later on `{τ < ζ}` (the restarted local stop), and a countable family of cells of the
  recorded history `𝒳_τ` (fixed current seed-weight pair and dyadic radius) covering `{τ < ζ}`, such that on each cell
  an equivalent measure carries an extended reference pair (`HasReferenceExtension`) over `(h, 𝒳_τ)` recovering `𝒳_σ`
  (the active chart and the transformed active field are measurable functions of `(h, 𝒳_τ)`);
* **`hasFieldLocalExtensions_of_restartReferenceExtension`**: under the two-seed input it gives the local extensions
  `Determination.HasFieldLocalExtensions` of every coupling (the two-seed graphs `twoSeed_exists_stoppedGraph` on each
  cell, and the measurable patching of the countable reference family);
* **`localExtensionStatement_of_restartReferenceExtension`**: the named input `Determination.LocalExtensionStatement κ`
  of `DeterminationRestart.lean`;
* **`exists_measurable_lifetime_trace_eq_comp_field_of_restartReferenceExtension`**: the conclusion of the frozen
  Theorem 1.2 for every `κ > 0` from the two-seed input and `RestartReferenceExtensionStatement`; with Proposition 7.3
  for `0 < κ < 4`, `lemma75DeterminationStatement_of_restartReferenceExtension`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Determination

/-- **Named input: Aux. lemmas 53 and 55 at own-filtration stops, in cell form** (specification pp. 245–252; §D.2.2 of
the follow-up note; steps 1–6 and 8 of the split in `planning/handoffs/PROVE-AUX52-55.md`). For every coupling of an
ordered force word, every measurability witness `hX` and every stopping time `τ ≤ ζ` of the frozen driving filtration
`𝓓 = drivingFiltration P hX`:

* a `𝓓`-stopping time `σ` with `τ ≤ σ ≤ ζ` and `τ < σ` almost surely on `{τ < ζ}` (the restarted local stop: Aux. 53
  restarts the specification in the active chart `f_τ`, where Aux. 55's stop of the current seed radius applies);
* countably many measurable cells `A i` of recorded histories, with seed weights `r_L i, r_R i > −2` and radii `r i`
  ("the finitely many possible amalgamated seed-weight pairs and countably many chosen radii"), whose preimages under
  `𝒳_τ` cover `{τ < ζ}` almost surely;
* on each cell `D i = {𝒳_τ ∈ A i}`, a probability measure `Q` with `Q ≪ P` and `P|_{D i} ≪ Q` ((HL3) applied
  conditionally) carrying an extended reference pair (`HasReferenceExtension`: (HL8)–(HL9) and Aux. 54 in the active
  chart) over the pair `(h, 𝒳_τ)` that recovers `𝒳_σ` ("If the previous stopped history is a function of `h`, its
  active conformal map and the transformed active field are also measurable functions of `h`"). -/
def RestartReferenceExtensionStatement (κ : ℝ) : Prop :=
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
          ∃ (A : ℕ → Set (DrivingHist nL nR)) (rL rR r : ℕ → ℝ), (∀ i, MeasurableSet (A i)) ∧
            (∀ i, -2 < rL i ∧ -2 < rR i) ∧
            (∀ᵐ ω ∂P, τ ω < (ζ ω : WithTop ℝ≥0) →
              ∃ i, stoppedHistory (completedState W VL VR ζ) τ ω ∈ A i) ∧
            ∀ i, ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧
              P.restrict {ω | stoppedHistory (completedState W VL VR ζ) τ ω ∈ A i} ≪ Q ∧
              HasReferenceExtension.{u} κ (rL i) (rR i) (r i) Q
                (fun ω => (h ω, stoppedHistory (completedState W VL VR ζ) τ ω))
                (stoppedHistory (completedState W VL VR ζ) σ)

/-! ### The measurable patching of a countable family of determinations -/

section Patch

variable {Ω γ β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace γ] [MeasurableSpace β] {P : Measure Ω}

/-- **Patching countably many cell-wise determinations** (Lemma 7.5's proof, p. 252: "The finitely many possible
amalgamated seed-weight pairs and countably many chosen radii supply a measurable restart rule"). Let `K` be a recorded
variable, `A i` measurable cells of its values, and suppose that on each cell `{K ∈ A i}` the variable `Y` is almost
surely a Borel function of `(H, K)`, and that off the union of the cells `Y` is almost surely a Borel function of `K`.
Then `Y` is almost surely a Borel function of `(H, K)`. -/
theorem isAEDeterminedBy_of_cells {H : Ω → γ} {K : Ω → β} {δ : Type*} [MeasurableSpace δ] {Y : Ω → δ}
    (A : ℕ → Set β) (hA : ∀ i, MeasurableSet (A i)) (g : ℕ → γ × β → δ) (hg : ∀ i, Measurable (g i))
    (hcell : ∀ i, ∀ᵐ ω ∂P, K ω ∈ A i → Y ω = g i (H ω, K ω)) (g₀ : β → δ) (hg₀ : Measurable g₀)
    (hoff : ∀ᵐ ω ∂P, (∀ i, K ω ∉ A i) → Y ω = g₀ (K ω)) :
    IsAEDeterminedBy P (fun ω => (H ω, K ω)) Y := by
  classical
  -- the cells `B 0 = (⋃ A)ᶜ`, `B (i + 1) = A i` cover every value
  let B : ℕ → Set β := fun n => if n = 0 then (⋃ i, A i)ᶜ else A (n - 1)
  let f : ℕ → γ × β → δ := fun n => if n = 0 then fun p => g₀ p.2 else g (n - 1)
  have hB : ∀ n, MeasurableSet {p : γ × β | p.2 ∈ B n} := by
    intro n
    by_cases hn : n = 0
    · simp only [B, hn, ↓reduceIte]
      exact measurable_snd (MeasurableSet.iUnion hA).compl
    · simp only [B, hn, ↓reduceIte]
      exact measurable_snd (hA (n - 1))
  have hf : ∀ n, Measurable (f n) := by
    intro n
    by_cases hn : n = 0
    · simp only [f, hn, ↓reduceIte]
      exact hg₀.comp measurable_snd
    · simp only [f, hn, ↓reduceIte]
      exact hg (n - 1)
  have hex : ∀ p : γ × β, ∃ n, p.2 ∈ B n := by
    intro p
    by_cases hp : p.2 ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hp
      exact ⟨i + 1, by simpa [B] using hi⟩
    · exact ⟨0, by simpa [B] using hp⟩
  have hdec : ∀ n, DecidablePred fun p : γ × β => p.2 ∈ B n := fun n => Classical.decPred _
  refine ⟨fun p : γ × β => f (Nat.find (hex p)) p,
    Measurable.find (p := fun n (x : γ × β) => x.2 ∈ B n) hf hB hex, ?_⟩
  filter_upwards [ae_all_iff.2 hcell, hoff] with ω hc ho
  have hspec := Nat.find_spec (hex (H ω, K ω))
  show Y ω = f (Nat.find (hex (H ω, K ω))) (H ω, K ω)
  generalize Nat.find (hex (H ω, K ω)) = n at hspec ⊢
  by_cases hn : n = 0
  · simp only [B, hn, ↓reduceIte, mem_compl_iff, mem_iUnion, not_exists] at hspec
    simp only [f, hn, ↓reduceIte]
    exact ho hspec
  · simp only [B, hn, ↓reduceIte] at hspec
    simp only [f, hn, ↓reduceIte]
    exact hc (n - 1) hspec

end Patch

/-! ### Step 8: the local extensions at every own-filtration stop -/

section Step8

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The local extensions of Aux. lemmas 53 and 55 at every own-filtration stop** (p. 251: "Applying Aux. lemma 55
conditionally and using its countable reference family produces a strictly longer own-filtration stopped driving
history determined by `h`"): under the two-seed input and `RestartReferenceExtensionStatement`, every coupling of an
ordered force word has the local extensions `HasFieldLocalExtensions` in its frozen driving filtration. -/
theorem hasFieldLocalExtensions_of_restartReferenceExtension (hκ : 0 < κ) (h2 : LP.TwoSeedGraphInput.{u} κ)
    (hrest : RestartReferenceExtensionStatement.{u} κ) (hF : IsOrderedForceWord xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ) :
    HasFieldLocalExtensions P (drivingFiltration P hX) h W VL VR ζ := by
  intro τ hτ hτζ
  obtain ⟨σ, hσ, hτσ, hσζ, hlt, A, rL, rR, r, hA, hrr, hcover, hcells⟩ :=
    hrest xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX τ hτ hτζ
  refine ⟨σ, hσ, hτσ, hσζ, hlt, ?_⟩
  set X := completedState W VL VR ζ with hXdef
  have hcont := ae_continuousOn_completedState hκ hC.1
  have hKm : AEMeasurable (stoppedHistory X τ) P := aemeasurable_stoppedHistory hX hcont hτ.measurable' hτζ
  have hYm : AEMeasurable (stoppedHistory X σ) P := aemeasurable_stoppedHistory hX hcont hσ.measurable' hσζ
  have hHm : AEMeasurable (fun ω => (h ω, stoppedHistory X τ ω)) P := hC.2.1.aemeasurable.prodMk hKm
  -- the determination on each cell
  have hcell : ∀ i, ∃ g : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR → DrivingHist nL nR, Measurable g ∧
      ∀ᵐ ω ∂P, stoppedHistory X τ ω ∈ A i → stoppedHistory X σ ω = g (h ω, stoppedHistory X τ ω) := by
    intro i
    obtain ⟨Q, hQ, hQP, hPQ, hext⟩ := hcells i
    obtain ⟨g, hg, hgQ⟩ := hext.isAEDeterminedBy hκ h2 (hrr i).1 (hrr i).2 (hHm.mono_ac hQP) (hYm.mono_ac hQP)
    exact ⟨g, hg, ae_imp_of_ae_restrict (hPQ.ae_le hgQ)⟩
  choose g hg hgc using hcell
  -- off the cells, `τ = ζ`, hence `σ = τ`
  have hoff : ∀ᵐ ω ∂P, (∀ i, stoppedHistory X τ ω ∉ A i) →
      stoppedHistory X σ ω = id (stoppedHistory X τ ω) := by
    filter_upwards [hcover] with ω hω hno
    have hτeq : τ ω = (ζ ω : WithTop ℝ≥0) := by
      by_contra hne
      obtain ⟨i, hi⟩ := hω (lt_of_le_of_ne (hτζ ω) hne)
      exact hno i hi
    have hστ : σ ω = τ ω := le_antisymm (hτeq ▸ hσζ ω) (hτσ ω)
    exact stoppedHistory_congr hστ
  exact isAEDeterminedBy_of_cells A hA g hg hgc id measurable_id hoff

/-- **The named input `Determination.LocalExtensionStatement κ` from `RestartReferenceExtensionStatement`** (Aux.
lemmas 53–55 at own-filtration stops, §D.2.2). -/
theorem localExtensionStatement_of_restartReferenceExtension (hκ : 0 < κ)
    (hrest : RestartReferenceExtensionStatement.{u} κ) : LocalExtensionStatement.{u} κ := by
  intro h2 nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX
  exact hasFieldLocalExtensions_of_restartReferenceExtension hκ h2 hrest hF hC hX

/-- **The conclusion of the frozen Theorem 1.2 for every `κ > 0`** from the two-seed input and Aux. lemmas 53–55 in the
form `RestartReferenceExtensionStatement` (with Aux. 52 and LP11's reconstruction of the full trace, through
`Determination.exists_measurable_lifetime_trace_eq_comp_field_of_localExtension`). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_restartReferenceExtension (hκ : 0 < κ)
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hrest : RestartReferenceExtensionStatement.{u} κ)
    (hF : IsOrderedForceWord xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_localExtension hκ h2
    (localExtensionStatement_of_restartReferenceExtension hκ hrest) hF hC

/-- **Lemma 7.5 with Aux. 52–55** (the named input `LP.Lemma75DeterminationStatement` of LP11) from Proposition 7.3 and
`RestartReferenceExtensionStatement` for `0 < κ < 4`. -/
theorem lemma75DeterminationStatement_of_restartReferenceExtension
    (h73d : Prop73DeterminationStatement.{u}) (h73t : Sec7.Prop73TraceStatement.{u})
    (hrest : ∀ κ : ℝ, 0 < κ → κ < 4 → RestartReferenceExtensionStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  lemma75DeterminationStatement_of_inputs h73d h73t fun κ hκ hκ4 =>
    localExtensionStatement_of_restartReferenceExtension hκ (hrest κ hκ hκ4)

end Step8

end LocalExt

end InteractingSLE
