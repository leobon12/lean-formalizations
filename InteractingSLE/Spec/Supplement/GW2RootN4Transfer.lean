/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootN4Family
import InteractingSLE.Spec.Supplement.GW2RootK3Kernel

/-!
# Root crossing from identified finite-force models

Continuation of PROVE-T14-GW2ROOT2. The named hypothesis
`HasNearCrossingModels` requires the concrete integrated evolutions and word
bounds in `NearCrossingFamily`, and their identification with available model
candidates. It does not assume an arbitrarily high probability estimate.
Constructing this family for each retained root history remains unproved.
No measurable choice of angles or buffers from the retained history is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.RootN4

/-- The exact outstanding finite-force identification hypothesis. For almost
every alive retained state, each buffer's sufficiently near-extreme evolution
has reach probability bounded by some available candidate's probability.
The family, the cutoff in the angle sequence, and the candidate may depend
on that state. Neither a crossing estimate nor a measurable selection is assumed. -/
def HasNearCrossingModels {Ω L : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (P : Measure Ω) (A : L → Set Ω)
    (p : L → ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ l, ∀ᵐ ω ∂P, ω ∈ A l → ∃ f : NearCrossingFamily.{u} κ,
    ∀ n, ∀ᶠ m in atTop, ∃ a, f.crossProb m n ≤ p l a ω

/-- TIP11 discharges the model crossing clause from concrete near-extreme
evolutions and their identification with the available candidates. -/
theorem HasNearCrossingModels.modelCross {Ω L : Type*} [MeasurableSpace Ω]
    {κ : ℝ} {P : Measure Ω} {A : L → Set Ω} {p : L → ℕ → Ω → ℝ≥0∞}
    (hNear : HasNearCrossingModels.{u} κ P A p)
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ l (δ : ℝ≥0∞), 0 < δ → ∀ᵐ ω ∂P,
      ω ∈ A l → ∃ a, 1 - δ < p l a ω := by
  intro l δ hδ
  filter_upwards [hNear l] with ω hω hωA
  obtain ⟨f, hf⟩ := hω hωA
  exact f.exists_lt_of_domination h13 hκ hκ4 hf hδ

section Transfer

variable {Ω Ξ L : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace Ξ] {P : Measure Ω} [IsFiniteMeasure P]
  {σ : L → MeasurableSpace Ω} {A : L → Set Ω}
  {U : L → ℕ → Ω → Ξ} {K : L → ℕ → Ω → Measure Ξ}
  {B : L → ℕ → Set Ξ} {E : L → ℕ → Set Ω}

/-- The same concrete finite-force inputs give crossing under the full
retained conditional law. The measurable sample, event, and complete law
identity are retained explicitly to rule out junk pushforward measures. -/
theorem ae_condExpKernel_crossing_of_nearModels
    (hσ : ∀ l, σ l ≤ mΩ) (hU : ∀ l a, Measurable (U l a))
    (hB : ∀ l a, MeasurableSet (B l a))
    (hLaw : ∀ l a, ∀ᵐ ω ∂P, ω ∈ A l →
      (condExpKernel P (σ l) ω).map (U l a) = K l a ω)
    (hident : ∀ l a, U l a ⁻¹' B l a =ᵐ[P] E l a)
    {κ : ℝ}
    (hNear : HasNearCrossingModels.{u} κ P A (fun l a ω => K l a ω (B l a)))
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ l (δ : ℝ≥0∞), 0 < δ → ∀ᵐ ω ∂P,
      ω ∈ A l → ∃ a, 1 - δ < condExpKernel P (σ l) ω (E l a) := by
  intro l δ hδ
  have heq := ae_all_iff.2 fun a =>
    RootK3.ae_condExpKernel_event_eq_of_map (hσ l) (hU l a) (hB l a)
      (hLaw l a) (hident l a)
  filter_upwards [heq, hNear.modelCross h13 hκ hκ4 l δ hδ]
    with ω hωeq hωcross hωA
  obtain ⟨a, ha⟩ := hωcross hωA
  exact ⟨a, (hωeq a hωA).symm ▸ ha⟩

end Transfer

end InteractingSLE.Theorem14.GW2TipSystem.RootN4
