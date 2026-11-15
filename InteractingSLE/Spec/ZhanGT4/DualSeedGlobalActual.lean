/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalGeometry

/-!
# Actual stochastic mapped-driver D10 after removing all seed bands

Packet PROVE-ZHAN-GT4-A22. Construct every band field and its adapted
coefficients from protected source geometry, and exhaust the actual gaps
under the fixed Girsanov Brownian motion at the original density horizon.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open Girsanov
open QuantumZipper (fwdMap IsForwardSol)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The positive-time stochastic D10 identity follows from actual source
geometry and calculus. No band Itô identity or field is assumed. -/
theorem seedMap_positive_integral_actual {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (rr : Fin n → ℝ) {d : Ω → SeedData n} {B D : ℝ≥0 → Ω → ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {φ : ℂ → ℂ} {ζ₀ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdWX : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    {ε : ℝ≥0} (hε : 0 < ε) {T : Ω → ℝ≥0} {U : ℝ≥0} {M C : ℝ}
    (hTU : ∀ ω, T ω ≤ U)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hM : 0 ≤ M) (hC : 0 ≤ C)
    {A : Set ℂ} {r a₀ ρm : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, ε ≤ T ω → OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ε ≤ T ω → ∃ v₀ : ℝ → ℂ,
      IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).W t : ℂ) r) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω), a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA0 : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω), |(d ω).A 0 t| ≤ M)
    (hV₀ : ∀ ω, ε ≤ T ω → ∀ t ∈ Ioc (0 : ℝ) (T ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hV : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Ioc (0 : ℝ) (T ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hD : ∀ ω, ε ≤ T ω → ∀ t ∈ Ioc (0 : ℝ) (T ω), HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hnc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ d T u.toNNReal ω) (Ioc 0 (T ω)))
    (hVm : ∀ (q : ℝ≥0) m, ε ≤ q → Measurable[𝓕 q]
      ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hBh : IsFilteredBrownianReal 𝓕 (girsanovProcess B (seedNoise κ d T)) Q)
    (hBc : ∀ ω, Continuous (B · ω))
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (d ω).A 1 u))
    (hcA : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (T ω)))
    {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hbA : ∀ u ω, 0 < u → u ≤ T ω → |(d ω).A 1 u| ≤ Ca)
    {Y : SeedGap n → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hYv : ∀ ω i (u : ℝ≥0), ε ≤ u → u ≤ T ω → Y i u ω = (d ω).gapVal i u)
    (hne : ∀ ω i (u : ℝ≥0), ε ≤ u → u ≤ T ω → Y i u ω ≠ 0)
    {t : ℝ≥0} (hεt : ε ≤ t) :
    (fun ω => (d ω).A 0 (min t (T ω)) - (d ω).A 0 (min ε (T ω)) -
      (∫ u in (min ε (T ω) : ℝ≥0)..(min t (T ω) : ℝ≥0), (d ω).d10Rate u)) =ᵐ[Q]
    fun ω => stochIntegral Q 𝓕 (girsanovProcess B (seedNoise κ d T))
        (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T) t ω -
      stochIntegral Q 𝓕 (girsanovProcess B (seedNoise κ d T))
        (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T) ε ω := by
  let E := fun k : ℕ => bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
  let S := fun k : ℕ => bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε U T
  have hf k := exists_seedMap_gap_band_fields hκ rr hdW hdκ hdr hε
    (fun ω => NNReal.coe_le_coe.2 (hTU ω)) hM hC hr ha₀ hρm h hclr hA1 hmclr hA0 hV₀ hV hD
    hp hb hnc hYc hYv k U
  choose ρ K hρ hK hF using hf
  have hi k := seedMap_gap_band_inputs hXm hXc hdWX hdφ hdζ hdκ hdr hε hT hr ha₀ hρm
    h hv₀ hclr hA1 hmclr hVm hYc hYm hYv k U
  have hW (ω : Ω) : (d ω).W = driftDriver (Real.sqrt κ)
      (girsanovProcess B (seedNoise κ d T))
      (seedImageOffset (Real.sqrt κ) D (seedNoise κ d T)) ω :=
    (hdW ω).trans (seed_driver_girsanov_eq _ _ _ _ ω).symm
  have hBhc (ω : Ω) : Continuous (girsanovProcess B (seedNoise κ d T) · ω) :=
    (hBc ω).add (Girsanov.continuous_drift hp hb ω)
  refine seedMap_positive_integral_of_exhaustion hκ hε hW hdκ
    (fun k ω hω => bandExit_le hω.1) (fun k => (hi k).1) (fun k => (hi k).2.1)
    hF hρ hBh hBhc ?_ (fun k j q hq => ((hi k).2.2 q hq).1 j)
    (fun k q hq => ((hi k).2.2 q hq).2) hT hm hcA hCa hbA ?_ hεt
  · intro k
    exact isStoppingTime_onEvS (isStoppingTime_bandExit hYc hYm hT) le_bandExit
      (measurableSet_bandEv hYm hT)
  · intro ω hω
    exact eventually_bandEv_bandExit_eq hYc hω
      ((hTU ω).trans (le_add_of_nonneg_left (zero_le (a := ε)))) (hne ω)

end InteractingSLE.ZhanGT4
