/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedR80Drift

/-!
# Adaptedness of the actual mapped noise from protected source coordinates

Packet PROVE-ZHAN-GT4-A22. Actual Loewner measurability gives the map and
D10-rate values while alive. Protected moving force coordinates and seed
entrance integrals supply the remaining continuity and integrability.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The exact actual mapped noise is adapted from the source geometry;
its stochastic integral equality is not a measurability hypothesis. -/
theorem measurable_seedOwnMappedNoise_of_source {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {d : Ω → SeedData n} {X B : ℝ≥0 → Ω → ℝ} {κ : ℝ} {rr : Fin n → ℝ}
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} {T : Ω → ℝ≥0} {ρm : ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hρm : 0 < ρm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hmclr : ∀ ω m t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hVm : ∀ (q : ℝ≥0) m, Measurable[𝓕 q]
      ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (T ω)))
    (h20 : ∀ ω, ContinuousOn (d ω).A20 (Icc 0 (T ω)))
    (hsep : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → (d ω).A 0 t ≠ (d ω).A20 t)
    (hne : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) → ∀ m, (d ω).A 0 t ≠ (d ω).B0 t m)
    (hi : ∀ ω, (d ω).ImageEntranceIntegrable (T ω))
    (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0) :
    Measurable[𝓕 t] (seedOwnMappedNoise κ d T B t) := by
  have hinputs (u : ℝ≥0) := measurable_seed_map_inputs hXm hXc hdW hdφ hdζ hdκ hdr u
    (measurableSet_ge_of_isStoppingTime hT u)
    (fun ω hω => NNReal.coe_le_coe.2 hω) (fun ω _ => h ω) (fun ω _ => hv₀ ω)
    (fun ω hω m => ⟨ρm, hρm, hmclr ω m u ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hω⟩⟩) (hVm u)
  have hc (ω : Ω) : ContinuousOn (fun u : ℝ≥0 => (d ω).d10Rate u) (Ioc 0 (T ω)) :=
    ((d ω).continuousOn_d10Rate_of_clear (h ω) hρm (hVc ω) (hmclr ω) (h20 ω)
      (fun u hu => hsep ω u (Ioc_subset_Icc_self hu)) (hne ω)).comp
        continuous_subtype_val.continuousOn
        (fun u hu => ⟨NNReal.coe_pos.2 hu.1, NNReal.coe_le_coe.2 hu.2⟩)
  have hint (ω : Ω) : IntervalIntegrable (d ω).d10Rate volume 0 (T ω) :=
    (d ω).intervalIntegrable_d10Rate (fun i =>
      (d ω).imageWeightedGap_integrable (h ω) (h20 ω) (hsep ω) (hi ω) i ⟨(T ω).coe_nonneg, le_rfl⟩)
  exact measurable_seedOwnMappedNoise hT (fun u => (hinputs u).1 0)
    (fun ω => (h ω).continuousOn_frzA 0) (fun u => (hinputs u).2) hc hint hBm hBc t

end InteractingSLE.ZhanGT4
