/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimPhase

/-!
# Propagating one phase anchor through the positive pocket lifetime

PROVE-STRIPSYS38. The continuity argument in Aux. 122 uses no upper seed-weight
bound. Countably many rational phase statements and one continuous version give
a simultaneous lattice phase; the landed connected-lattice theorem then
propagates one zero anchor. No uncountable intersection of probability-one
events is taken. Continuity of the actual common phase remains explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C PocketStop PhaseSel

/-- Rational times suffice to verify a lattice-valued continuous function on
an open subset of the nonnegative times. -/
theorem mem_lattice_of_continuousOn_rationals {S : Set ℝ≥0} (hS : IsOpen S)
    {d : ℝ≥0 → ℝ} (hd : ContinuousOn d S) {c : ℝ} (hc : c ≠ 0)
    (hrat : ∀ r : ℚ, (r : ℝ).toNNReal ∈ S → ∃ m : ℤ, d (r : ℝ).toNNReal = m * c) :
    ∀ t ∈ S, ∃ m : ℤ, d t = m * c := by
  have hsurj : Function.Surjective Real.toNNReal := fun t => ⟨t, Real.toNNReal_coe⟩
  have hDense : DenseRange (fun r : ℚ => (r : ℝ).toNNReal) :=
    hsurj.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
  let R : Set ℝ≥0 := (fun r : ℚ => (r : ℝ).toNNReal) ''
    ((fun r : ℚ => (r : ℝ).toNNReal) ⁻¹' S)
  have hRS : R ⊆ S := image_preimage_subset _ _
  have hmaps : MapsTo (fun t => d t / c) R (range ((↑) : ℤ → ℝ)) := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨m, hm⟩ := hrat r hr
    refine ⟨m, ?_⟩
    change (m : ℝ) = d (r : ℝ).toNNReal / c
    rw [hm, mul_div_cancel_right₀ _ hc]
  intro t ht
  have hcl := ((hd.div_const c t ht).mono hRS).mem_closure
    (hDense.subset_closure_image_preimage_of_isOpen hS ht) hmaps
  rw [Int.isClosedEmbedding_coe_real.isClosed_range.closure_eq] at hcl
  obtain ⟨m, hm⟩ := hcl
  exact ⟨m, (div_eq_iff hc).1 hm.symm⟩

/-- The source's common continuous lattice phase is zero throughout its
positive lifetime as soon as it has one positive zero-phase visit. -/
theorem phase_eq_zero_on_lifetime_of_anchor {κ : ℝ} (hκ : 4 < κ) {T : ℝ≥0∞}
    {d : ℝ≥0 → ℝ} (hcont : ContinuousOn d {t | 0 < t ∧ (t : ℝ≥0∞) < T})
    (hmem : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → ∃ m : ℤ, d t = m * phaseStep κ)
    (hanchor : ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < T ∧ d s = 0) :
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → d t = 0 := by
  obtain ⟨s, hs, hsT, hs0⟩ := hanchor
  have hS : OrdConnected {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < T} :=
    ⟨fun _ hx _ hy _ hz => ⟨hx.1.trans_le hz.1, (ENNReal.coe_le_coe.2 hz.2).trans_lt hy.2⟩⟩
  intro t ht htT
  exact (eq_of_isPreconnected_of_continuousOn_of_mem_zmultiples hS.isPreconnected hcont
    (phaseStep_ne_zero hκ) (fun r hr => hmem r hr.1 hr.2) ⟨ht, htT⟩ ⟨hs, hsT⟩).trans hs0

/-- A single R.6 visit can anchor every positive-time side limit. The exact
remaining time input is the common-version continuity `hPhaseContinuous`.
Phase at time zero need not be selected by this argument. -/
theorem pocketStopSideLimit_of_phase_continuous_anchor {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {a : ℝ} {h₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : ℝ≥0 → Ω → Set ℂ} {δ : ℝ≥0 → Ω → ℝ}
    (hPhase : ∀ q, PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) (δ q) q)
    (hPhaseContinuous : ∀ᵐ ω ∂P, ω ∈ A →
      ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)})
    (hAnchor : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0) :
    ∀ q : ℝ≥0, 0 < q → PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) q := by
  have hRat : ∀ᵐ ω ∂P, ∀ r : ℚ, ω ∈ A →
      ((r : ℝ).toNNReal : ℝ≥0∞) < capLife (γ ω) →
        ∃ m : ℤ, δ (r : ℝ).toNNReal ω = m * phaseStep κ :=
    ae_all_iff.2 fun r => (hPhase (r : ℝ).toNNReal).1
  intro q hq
  apply pocketStopSideLimit_of_phase_eq_zero (hPhase q)
  filter_upwards [hRat, hPhaseContinuous, hAnchor] with ω hrat hcont hanchor hω hqT
  have hS : IsOpen {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)} :=
    isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_coe continuous_const)
  have hmem := mem_lattice_of_continuousOn_rationals hS (hcont hω) (phaseStep_ne_zero hκ)
    (fun r hr => hrat r hω hr.2)
  exact phase_eq_zero_on_lifetime_of_anchor hκ (hcont hω)
    (fun t ht htT => hmem t ⟨ht, htT⟩)
    (hanchor hω ((ENNReal.coe_pos.2 hq).trans hqT)) q hq hqT

end InteractingSLE.Sec7.PocketStopSide
