/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartLawReference

/-!
# BW1: complete retained-past kernels from the stopped K2

Infinite relative lifetime supplies the announcing sequence automatically: use
the deterministic integer horizons. The stopped K2 then gives a complete optional
coupling under the retained-past kernels, with all-time agreement of the drivers.
The finite original contact time is not used as a relative lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1RestartLaw

open Restart.DomainMarkov.K2 Restart.StoppedK2

/-- The stopped K2 closes the entire optional-kernel step once the actual
relative evolution, safe mean/locality identities, and infinite lifetime are known. -/
theorem ae_isOptionalHullCoupling_of_stoppedK2_ae_top
    {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ}
    {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 𝓗' : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hE : IsRandomWordEvolutionUpTo κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B V)
    (hX : Measurable X) (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW : AdaptedBefore 𝓗' V W)
    (hVL : ∀ i, AdaptedBefore 𝓗' V (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X)
    (hmem : HasSafeMembers P 𝓗' F V W X)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    (hV : ∀ᵐ ω ∂P, ω ∈ F → V ω = ⊤) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
        (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR
          (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' V X ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧
          (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω := by
  let σ : ℕ → Ω → WithTop ℝ≥0 := fun n _ => ((n : ℝ≥0) : WithTop ℝ≥0)
  have hσ : ∀ n, IsStoppingTime (drivingFiltration P hXP) (σ n) :=
    fun n => isStoppingTime_const _ (n : ℝ≥0)
  have hσm : ∀ ω, Monotone fun n => σ n ω := by
    intro ω n m hnm
    change ((n : ℝ≥0) : WithTop ℝ≥0) ≤ ((m : ℝ≥0) : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.2 (by exact_mod_cast hnm)
  have hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω := by
    filter_upwards [hV] with ω hv hω n
    rw [hv hω]
    exact WithTop.coe_lt_top (n : ℝ≥0)
  have hσlim : ∀ᵐ ω ∂P, ω ∈ F →
      Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
    filter_upwards [hV] with ω hv hω
    rw [hv hω]
    change Tendsto (fun n : ℕ => (n : ℝ≥0∞)) atTop (𝓝 ⊤)
    exact ENNReal.tendsto_nat_nhds_top
  have hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ →
      ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
        (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧
        ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal) := by
    filter_upwards [hV] with ω hv hω hn
    exact (hn (hv hω)).elim
  have hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω := by
    filter_upwards [hV] with ω hv hω
    rw [hv hω]
    exact ENNReal.zero_lt_top
  have hK := ae_isStoppedHullCoupling_k hE hcont hX hV0 h𝒢' hW hVL hVR
    hlaw hmem hXP hσ hσm hσV hσlim
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢'.trans (𝓗'.le 0)
  filter_upwards [hK, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢m hV,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢m hE.2.1]
    with ω₀ hk hv hF hω₀
  have hvν : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), V ω = ⊤ := by
    filter_upwards [hv, hF hω₀] with ω h1 h2 using h1 h2
  obtain ⟨𝓕', W', VL', VR', B', hc, hag⟩ := hk hω₀
  refine ⟨𝓕', W', VL', VR', B', isOptionalHullCoupling_of_stopped_ae_top hc hvν, ?_⟩
  filter_upwards [hag, hvν] with ω ha ht t
  exact ha t (by rw [ht]; exact le_top)

end InteractingSLE.Theorem14.GW1RestartLaw
