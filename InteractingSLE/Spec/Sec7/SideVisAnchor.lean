/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimTime

/-!
# Rational zero-phase visits from one live zero-phase time

PROVE-SIDE-VISITS. A lattice-valued phase, continuous on the positive relative
lifetime, is constant there (`PocketStopSide.phase_eq_zero_on_lifetime_of_anchor`).
Hence one live positive time with zero phase gives a zero phase at **every**
positive rational live time, simultaneously on one almost-sure event. This is
the countable-candidate form `(s, E)` required by the shared-side visit binders,
with the deterministic candidate times `s r = r` and the candidate events
`E r = {phase r = 0}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideVis

open PocketStopSide PocketTraversal Lemma71C PhaseSel

/-- **Every positive rational live time has zero phase** once one live time has:
the lattice condition at the rational times and continuity on the positive lifetime
are intersected on one event before the anchor is used. -/
theorem ae_rat_phase_zero_of_anchor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {κ : ℝ} (hκ : 4 < κ) {δ : ℝ≥0 → Ω → ℝ}
    (hLattice : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ q ω = m * phaseStep κ)
    (hcont : ∀ᵐ ω ∂P, ω ∈ A →
      ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)})
    (hAnchor : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      (∃ r : ℚ, 0 < (r : ℝ).toNNReal ∧ ((r : ℝ).toNNReal : ℝ≥0∞) < capLife (γ ω)) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < capLife (γ ω) → δ t ω = 0 := by
  have hRat : ∀ᵐ ω ∂P, ∀ r : ℚ, ω ∈ A → ((r : ℝ).toNNReal : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ (r : ℝ).toNNReal ω = m * phaseStep κ :=
    ae_all_iff.2 fun r => hLattice (r : ℝ).toNNReal
  filter_upwards [hRat, hcont, hAnchor] with ω hrat hc hanchor hω hT
  obtain ⟨s, hs, hsT, hs0⟩ := hanchor hω hT
  have hS : IsOpen {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)} :=
    isOpen_Ioi.inter (isOpen_lt ENNReal.continuous_coe continuous_const)
  have hmem := mem_lattice_of_continuousOn_rationals hS (hc hω) (phaseStep_ne_zero hκ)
    (fun r hr => hrat r hω hr.2)
  have hzero := phase_eq_zero_on_lifetime_of_anchor hκ (hc hω)
    (fun t ht htT => hmem t ⟨ht, htT⟩) ⟨s, hs, hsT, hs0⟩
  obtain ⟨r, hr0, hrs⟩ := exists_rat_btwn (show (0 : ℝ) < s from hs)
  have hrpos : 0 < (r : ℝ).toNNReal := Real.toNNReal_pos.2 hr0
  have hrs' : (r : ℝ).toNNReal < s := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0.le]
    exact hrs
  exact ⟨⟨r, hrpos, (ENNReal.coe_lt_coe.2 hrs').trans hsT⟩, hzero⟩

/-- **The countable zero-phase visits with deterministic candidate times**: from one
live zero-phase time, the candidates `s r = r`, `E r = {δ r = 0}` satisfy both
shared-side visit conditions. -/
theorem rat_zero_visits_of_anchor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {κ : ℝ} (hκ : 4 < κ) {δ : ℝ≥0 → Ω → ℝ}
    (hLattice : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ q ω = m * phaseStep κ)
    (hcont : ∀ᵐ ω ∂P, ω ∈ A →
      ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)})
    (hAnchor : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0) :
    (∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ {ω | δ (r : ℝ).toNNReal ω = 0} → δ (r : ℝ).toNNReal ω = 0) ∧
      ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
        ∃ r : ℚ, 0 < (r : ℝ).toNNReal ∧ ((r : ℝ).toNNReal : ℝ≥0∞) < capLife (γ ω) ∧
          ω ∈ {ω | δ (r : ℝ).toNNReal ω = 0} := by
  refine ⟨fun r => Eventually.of_forall fun _ _ h => h, ?_⟩
  filter_upwards [ae_rat_phase_zero_of_anchor hκ hLattice hcont hAnchor] with ω h hω hT
  obtain ⟨⟨r, hr, hrT⟩, hzero⟩ := h hω hT
  exact ⟨r, hr, hrT, hzero _ hr hrT⟩

end InteractingSLE.Sec7.SideVis
