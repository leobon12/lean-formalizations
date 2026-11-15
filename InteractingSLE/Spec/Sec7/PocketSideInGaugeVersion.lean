/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseContR7

/-!
# Choosing a positive-time constant lattice version of the phase

PROVE-POCKET-SIDEIN. A fixed-time almost-sure constant phase and its
fixed-time lattice laws select one integer-valued function. The new
version preserves every fixed-time phase side limit and is literally
constant at positive times. No equality at a selected random time follows.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal PhaseSel Lemma71C

/-- The inherited initial phase, followed by a constant lattice phase at
positive times. Its zero-time value is retained exactly. -/
def positiveLatticePhase {Ω : Type*} (initial : Ω → ℝ) (n : Ω → ℤ) (step : ℝ)
    (q : ℝ≥0) (ω : Ω) : ℝ :=
  if q = 0 then initial ω else (n ω : ℝ) * step

/-- A fixed-time constant phase can be chosen in the lattice everywhere,
while preserving its value almost surely at each positive live time. -/
theorem exists_integer_phase_of_fixed_time_constant {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} {T : Ω → ℝ≥0∞} {δ : ℝ≥0 → Ω → ℝ}
    {c : Ω → ℝ} {step : ℝ}
    (hConst : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < T ω → δ q ω = c ω)
    (hLattice : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < T ω →
      ∃ m : ℤ, δ q ω = m * step) :
    ∃ n : Ω → ℤ, ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < T ω →
      δ q ω = (n ω : ℝ) * step := by
  classical
  let n : Ω → ℤ := fun ω => if h : ∃ m : ℤ, c ω = m * step then h.choose else 0
  refine ⟨n, fun q hq => ?_⟩
  filter_upwards [hConst q hq, hLattice q hq] with ω hC hL hω hqT
  have hc : ∃ m : ℤ, c ω = m * step := by
    obtain ⟨m, hm⟩ := hL hω hqT
    exact ⟨m, (hC hω hqT).symm.trans hm⟩
  have hn : c ω = (n ω : ℝ) * step := by
    dsimp only [n]
    rw [dite_eq_left hc]
    exact hc.choose_spec
  exact (hC hω hqT).trans hn

/-- The selected version keeps every fixed-time phase boundary statement,
including its lattice law, and is continuous pathwise at positive times.
This changes the version before any subsequent reference selection. -/
theorem exists_lattice_phase_version {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {chart : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : ℝ≥0 → Ω → Set ℂ} {δ : ℝ≥0 → Ω → ℝ} {c : Ω → ℝ}
    (hPhase : ∀ q : ℝ≥0, PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR chart a h₀ u
      (K q) (δ q) q)
    (hConst : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A →
      (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c ω) :
    ∃ n : Ω → ℤ,
      (∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        δ q ω = positiveLatticePhase (δ 0) n (phaseStep κ) q ω) ∧
      (∀ q : ℝ≥0, PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR chart a h₀ u
        (K q) (positiveLatticePhase (δ 0) n (phaseStep κ) q) q) ∧
      ∀ ω, ContinuousOn (fun q => positiveLatticePhase (δ 0) n (phaseStep κ) q ω)
        {q : ℝ≥0 | 0 < q ∧ (q : ℝ≥0∞) < capLife (γ ω)} := by
  obtain ⟨n, hn⟩ := exists_integer_phase_of_fixed_time_constant hConst (fun q _ => (hPhase q).1)
  have hEq (q : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      δ q ω = positiveLatticePhase (δ 0) n (phaseStep κ) q ω := by
    by_cases hq : q = 0
    · subst q
      exact Eventually.of_forall fun ω _ _ => by rw [positiveLatticePhase, ite_eq_left rfl]
    · filter_upwards [hn q (pos_iff_ne_zero.2 hq)] with ω hω hA hT
      rw [positiveLatticePhase, ite_eq_right hq]
      exact hω hA hT
  refine ⟨n, hEq, fun q => PhaseCont.pocketStopPhaseSideLimit_congr (hPhase q) (hEq q), ?_⟩
  intro ω
  refine (continuousOn_const (c := (n ω : ℝ) * phaseStep κ)).congr fun q hq => ?_
  rw [positiveLatticePhase, ite_eq_right (ne_of_gt hq.1)]

end InteractingSLE.Sec7.PocketStopSide
