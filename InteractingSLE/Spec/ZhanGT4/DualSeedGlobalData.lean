/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalActual
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseContinuity

/-!
# Global map-coefficient and entrance-integrability facts

Packet PROVE-ZHAN-GT4-A22. The protected real derivative supplies the
uniform bound one. The finite D10 entrance-integrability theorem is
reused directly from the landed `DualSeedCloseContinuity` module.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual first map derivative is adapted while alive, continuous
at positive alive times, and bounded by one from the protected enclosure. -/
theorem seedMap_alive_derivative_facts {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {d : Ω → SeedData n} {X : ℝ≥0 → Ω → ℝ} {κ : ℝ} {rr : Fin n → ℝ}
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} {T : Ω → ℝ≥0} {r ρm : ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hr : 0 < r) (hρm : 0 < ρm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).W t : ℂ) r) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hmclr : ∀ ω m t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hVm : ∀ (q : ℝ≥0) m, Measurable[𝓕 q]
      ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q)) :
    (∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (d ω).A 1 u)) ∧
    (∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (T ω))) ∧
    (∀ u ω, 0 < u → u ≤ T ω → |(d ω).A 1 u| ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hg : MeasurableSet[𝓕 u] {ω | u ≤ T ω} := measurableSet_ge_of_isStoppingTime hT u
    exact (measurable_seed_map_inputs hXm hXc hdW hdφ hdζ hdκ hdr u hg
      (fun ω hω => NNReal.coe_le_coe.2 hω) (fun ω _ => h ω) (fun ω _ => hv₀ ω)
      (fun ω hω m => ⟨ρm, hρm, hmclr ω m u ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hω⟩⟩)
      (hVm u)).1 1
  · intro ω
    exact ((h ω).continuousOn_frzA 1).comp continuous_subtype_val.continuousOn
      (fun u hu => ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu.2⟩)
  · intro u ω _ hu
    have ht : (u : ℝ) ∈ Icc (0 : ℝ) (T ω) := ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
    have hh := (h ω).deriv_ownExt_real ht hr (hclr ω u ht)
    have he : (d ω).A 1 u = (deriv (ownExt (d ω).W (d ω).W' (d ω).a (d ω).φ u)
        ((d ω).W u)).re := by simp only [SeedData.A, frzA, Function.iterate_one]
    rw [he, abs_of_pos hh.2.1]
    exact hh.2.2

end InteractingSLE.ZhanGT4
