/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalData

/-!
# Global stochastic D10 from the actual seeded source calculus

Packet PROVE-ZHAN-GT4-A22. Construct all positive-time gap bands under
the one fixed seeded Girsanov motion, remove them, pass to the entrance,
and append the post-horizon Brownian continuation. The assumptions are
actual source geometry, force calculus and seed entrance integrability;
no stochastic D10, map Itô identity or localized field is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open Girsanov
open QuantumZipper (fwdMap IsForwardSol)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Global stochastic D10 for the actual seeded mapped driver. Its exact
stable conclusion can be consumed by the landed capacity construction. -/
theorem seedOwnD10Integral_of_actual_source {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (rr : Fin n → ℝ) {d : Ω → SeedData n} {B D : ℝ≥0 → Ω → ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {φ : ℂ → ℂ} {ζ₀ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdWX : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    {T : Ω → ℝ≥0} {U : ℝ≥0} {M C : ℝ}
    (hTU : ∀ ω, T ω ≤ U)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hM : 0 ≤ M) (hC : 0 ≤ C)
    {A : Set ℂ} {r a₀ ρm : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ,
      IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).W t : ℂ) r) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω), a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω, ∀ m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA0 : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω), |(d ω).A 0 t| ≤ M)
    (hV₀ : ∀ ω, ∀ t ∈ Ioc (0 : ℝ) (T ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hV : ∀ ω, ∀ m, ∀ t ∈ Ioc (0 : ℝ) (T ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hD : ∀ ω, ∀ t ∈ Ioc (0 : ℝ) (T ω), HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hnc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ d T u.toNNReal ω) (Ioc 0 (T ω)))
    (hVm : ∀ (q : ℝ≥0) m, Measurable[𝓕 q]
      ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hBh : IsFilteredBrownianReal 𝓕 (girsanovProcess B (seedNoise κ d T)) Q)
    (hBc : ∀ ω, Continuous (B · ω))
    {Y : SeedGap n → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hYv : ∀ ω i (u : ℝ≥0), 0 < u → u ≤ T ω → Y i u ω = (d ω).gapVal i u)
    (hne : ∀ ω i (u : ℝ≥0), 0 < u → u ≤ T ω → Y i u ω ≠ 0)
    (hc20 : ∀ ω, ContinuousOn (d ω).A20 (Icc 0 (T ω)))
    (hne20 : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → (d ω).A 0 t ≠ (d ω).A20 t)
    (hi : ∀ ω, (d ω).ImageEntranceIntegrable (T ω)) :
    SeedOwnD10Integral Q 𝓕 (girsanovProcess B (seedNoise κ d T)) κ d T := by
  obtain ⟨hm, hcA, hbA⟩ := seedMap_alive_derivative_facts hXm hXc hdWX hdφ hdζ hdκ hdr hT hr hρm
    h hv₀ hclr hmclr hVm
  have hBhc (ω : Ω) : Continuous (girsanovProcess B (seedNoise κ d T) · ω) :=
    (hBc ω).add (Girsanov.continuous_drift hp hb ω)
  have hint (ω : Ω) : IntervalIntegrable (d ω).d10Rate volume 0 (T ω) :=
    (d ω).intervalIntegrable_d10Rate (fun i =>
      (d ω).imageWeightedGap_integrable (h ω) (hc20 ω) (hne20 ω) (hi ω) i ⟨(T ω).coe_nonneg, le_rfl⟩)
  apply seedOwnD10Integral_of_positive_map_calculus hκ
    (isFilteredPreBrownian_of_isFilteredBrownianReal hBh) hBhc hT h hint hm hcA (by norm_num) hbA
  intro ε t hε hεt
  exact seedMap_positive_integral_actual hκ rr hdW hdκ hdr hXm hXc hdWX hdφ hdζ hε hTU hT hM hC
    hr ha₀ hρm (fun ω _ => h ω) (fun ω _ => hv₀ ω) (fun ω _ => hclr ω) (fun ω _ => hA1 ω)
    (fun ω _ => hmclr ω) (fun ω _ => hA0 ω) (fun ω _ => hV₀ ω) (fun ω _ => hV ω)
    (fun ω _ => hD ω) hp hb hnc (fun q m _ => hVm q m) hBh hBc hm hcA (by norm_num) hbA
    hYc hYm (fun ω i u hu htu => hYv ω i u (hε.trans_le hu) htu)
    (fun ω i u hu htu => hne ω i u (hε.trans_le hu) htu) hεt

end InteractingSLE.ZhanGT4
