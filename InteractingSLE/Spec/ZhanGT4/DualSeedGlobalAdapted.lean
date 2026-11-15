/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalExhaust

/-!
# Actual adapted map coefficients on an event-localized horizon

Packet PROVE-ZHAN-GT4-A22. Restrict the source alive force coordinates
to the band event and its shorter stopping horizon, then use the existing
Loewner measurability theorem for the actual map and D10 rate.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- No measurability of a Taylor remainder or map derivative is required:
the actual source driver and alive force coordinates supply it. -/
theorem seedMap_measurable_on_event {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {X : ℝ≥0 → Ω → ℝ} {d : Ω → SeedData n} {κ : ℝ} {rr : Fin n → ℝ}
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} {E : Set Ω} {ε : ℝ≥0} {S T : Ω → ℝ≥0}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hE : MeasurableSet[𝓕 ε] E) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hST : ∀ ω ∈ E, S ω ≤ T ω)
    (h : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω ∈ E, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    (hcl : ∀ ω ∈ E, ∀ (q : ℝ≥0), ε ≤ q → q ≤ S ω → ∀ m,
      ∃ ρ > 0, Disjoint (ball ((d ω).V m q : ℂ) ρ) (imgHull (d ω).W A q))
    (hVm : ∀ (q : ℝ≥0) m, ε ≤ q → Measurable[𝓕 q]
      ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q)) :
    ∀ q : ℝ≥0, ε ≤ q →
      (∀ k, Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).A k q)) ∧
        Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).d10Rate q) := by
  intro q hq
  have hG : MeasurableSet[𝓕 q] (E ∩ {ω | q ≤ S ω}) :=
    (𝓕.mono hq _ hE).inter (measurableSet_ge_of_isStoppingTime hS q)
  apply measurable_seed_map_inputs hXm hXc hdW hdφ hdζ hdκ hdr q hG
    (fun ω hω => NNReal.coe_le_coe.2 hω.2) (fun ω hω => h ω hω.1) (fun ω hω => hv₀ ω hω.1)
    (fun ω hω => hcl ω hω.1 q hq hω.2)
  intro m
  have he : (E ∩ {ω | q ≤ S ω}).indicator (fun ω => (d ω).V m q) =
      (E ∩ {ω | q ≤ S ω}).indicator
        ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q) := by
    have hsub : E ∩ {ω | q ≤ S ω} ⊆ {ω | q ≤ T ω} :=
      fun ω hω => hω.2.trans (hST ω hω.1)
    rw [indicator_indicator, inter_eq_left.2 hsub]
  rw [he]
  exact (hVm q m hq).indicator hG

end InteractingSLE.ZhanGT4
