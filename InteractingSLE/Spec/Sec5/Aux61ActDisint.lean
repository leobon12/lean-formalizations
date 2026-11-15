/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ActCut

/-!
# The disintegration of the glued space by regular conditional laws

Packet PROVE-AUX61-ACT, piece (D) (the disintegration and localization of the glued space). Astra's follow-up 4 §1.3
(`source/external/AstraIG1/ig1_followup4_audited.txt` L258–L262, ruling R71): "Disintegrate over the retained history
and integrate; no measurable choice of fresh couplings is necessary." The glued space is not standard Borel; the
fibres are the regular conditional laws (`ProbabilityTheory.condDistrib`) of a **code** `Y` (in a standard Borel space:
the field read in the restart chart and the restarted path) given the **retained history** `Z` (any measurable map).
The kernels of `HasDyActFibreCover` are then `x ↦ condDistrib Y Z μ (Z x)`, and the two measure-theoretic clauses of the
cover hold for any such disintegration:

* **`measure_inter_le_lintegral_condDistrib`** (the disintegration inequality): if the event forces the code into `L`
  on the history event `Z ∈ B`, then `μ({Z ∈ B} ∩ E) ≤ ∫⁻_{Z ∈ B} condDistrib Y Z μ (Z x) L`;
* **`ae_ae_condDistrib_of_ae`** (almost-sure facts pass to almost every fibre): if `Y ∈ G` almost surely, then for
  almost every `x`, the fibre at `Z x` gives `G` full mass;
* **`hasDyActFibreCover_of_condDistrib`**: `HasDyActFibreCover` from a countable family of histories, codes and
  history events covering the event, whose fibres (for almost every history value in the event) carry a `DyActFibre`.

What remains for PROVE-AUX61-R2C's target is exactly the last clause: for almost every retained history value, the
regular conditional law of the code is (the law of) a `DyActFibre` — its path data, the kernel at the countably many
stops `min(T_N, k/2ⁿ)` and the member identities at rational times.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Act

universe u

section Disint

variable {X : Type*} [MeasurableSpace X] {β : Type*} [MeasurableSpace β] {S : Type*} [MeasurableSpace S]
  [StandardBorelSpace S] [Nonempty S] {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} {Y : X → S}

/-- **The disintegration inequality**: if, on the history event `Z ∈ B`, the event `E` forces the code into `L`, then
`μ({Z ∈ B} ∩ E) ≤ ∫⁻_{Z ∈ B} condDistrib Y Z μ (Z x) L`. -/
theorem measure_inter_le_lintegral_condDistrib (hZ : Measurable Z) (hY : Measurable Y) {B : Set β}
    (hB : MeasurableSet B) {L : Set S} (hL : MeasurableSet L) {E : X → Prop}
    (hE : ∀ᵐ x ∂μ, Z x ∈ B → E x → Y x ∈ L) :
    μ (Z ⁻¹' B ∩ {x | E x}) ≤ ∫⁻ x in Z ⁻¹' B, condDistrib Y Z μ (Z x) L ∂μ := by
  have h1 : μ (Z ⁻¹' B ∩ {x | E x}) ≤ μ (Z ⁻¹' B ∩ Y ⁻¹' L) := by
    refine measure_mono_ae ?_
    filter_upwards [hE] with x hx hxE
    exact ⟨hxE.1, hx hxE.1 hxE.2⟩
  have h2 : μ (Z ⁻¹' B ∩ Y ⁻¹' L) = (μ.map fun a => (Z a, Y a)) (B ×ˢ L) := by
    rw [Measure.map_apply (hZ.prodMk hY) (hB.prod hL)]
    rfl
  have h3 : (μ.map fun a => (Z a, Y a)) (B ×ˢ L) = ∫⁻ b in B, condDistrib Y Z μ b L ∂(μ.map Z) := by
    rw [← compProd_map_condDistrib hZ.aemeasurable hY.aemeasurable, Measure.compProd_apply_prod hB hL]
  have h4 : ∫⁻ b in B, condDistrib Y Z μ b L ∂(μ.map Z) = ∫⁻ x in Z ⁻¹' B, condDistrib Y Z μ (Z x) L ∂μ :=
    setLIntegral_map hB ((condDistrib Y Z μ).measurable_coe hL) hZ
  rw [← h4, ← h3, ← h2]
  exact h1

/-- **Almost-sure facts of the code pass to almost every fibre.** -/
theorem ae_ae_condDistrib_of_ae (hZ : Measurable Z) (hY : Measurable Y) {G : Set S} (hG : MeasurableSet G)
    (h : ∀ᵐ x ∂μ, Y x ∈ G) : ∀ᵐ x ∂μ, ∀ᵐ s ∂(condDistrib Y Z μ (Z x)), s ∈ G := by
  have h0 : (μ.map fun a => (Z a, Y a)) (univ ×ˢ Gᶜ) = 0 := by
    rw [Measure.map_apply (hZ.prodMk hY) (MeasurableSet.univ.prod hG.compl)]
    have e : (fun a => (Z a, Y a)) ⁻¹' (univ ×ˢ Gᶜ) = {x | Y x ∉ G} := by
      ext x; simp
    rw [e]
    exact ae_iff.1 h
  rw [← compProd_map_condDistrib hZ.aemeasurable hY.aemeasurable,
    Measure.compProd_apply_prod MeasurableSet.univ hG.compl, Measure.restrict_univ,
    lintegral_eq_zero_iff ((condDistrib Y Z μ).measurable_coe hG.compl)] at h0
  have h1 : ∀ᵐ b ∂(μ.map Z), condDistrib Y Z μ b Gᶜ = 0 := h0
  filter_upwards [ae_of_ae_map hZ.aemeasurable h1] with x hx
  rw [ae_iff]
  exact hx

end Disint

/-! ### The cover from regular conditional laws -/

/-- **`HasDyActFibreCover` from regular conditional laws**: a countable family of retained histories `Z i` (any
measurable maps), codes `Y i` (in one standard Borel space `S`), measurable history events `B i` and code events
`L i`, such that the event `E` is covered by the history events, forces the code into `L i` on `B i`, and, for almost
every `x` with `Z i x ∈ B i`, the regular conditional law of the code at `Z i x` is the law of a `DyActFibre` whose
paths in `L i` visit the reference set before the clock. -/
theorem hasDyActFibreCover_of_condDistrib {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} {ι : Type} [Countable ι] {S : Type u}
    [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (Y : ι → X → S) (hY : ∀ i, Measurable (Y i))
    (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i)) (L : ι → Set S) (hL : ∀ i, MeasurableSet (L i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i) (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x → Y i x ∈ L i)
    (hfib : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → ∃ (D : DyActFibre S) (I : Set ℝ),
      D.CS.P = condDistrib (Y i) (Z i) μ (Z i x) ∧ Ref D.κ D.bR D.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.RC.e ω ∧ ∃ y ∈ I, D.CS.Γ ω v = (y : ℂ)) :
    HasDyActFibreCover μ E Ref := by
  refine ⟨ι, inferInstance, fun i => Z i ⁻¹' B i, S, inferInstance,
    fun i => (condDistrib (Y i) (Z i) μ).comap (Z i) (hZ i), L, fun i => hZ i (hB i), hcover,
    fun i => ?_, fun i => ?_⟩
  · simp only [Kernel.comap_apply]
    exact measure_inter_le_lintegral_condDistrib (hZ i) (hY i) (hB i) (hL i) (hE i)
  · filter_upwards [hfib i] with x hx hxB
    obtain ⟨D, I, hP, hRef, hLv⟩ := hx hxB
    exact ⟨D, I, by rw [hP, Kernel.comap_apply], hRef, hLv⟩

end InteractingSLE.Sec5.Aux61Act
