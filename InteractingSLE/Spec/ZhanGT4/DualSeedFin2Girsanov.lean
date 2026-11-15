/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Source
import InteractingSLE.Spec.ZhanGT4.DualSeedImageGirsanov

/-!
# Seeded Girsanov from the actual protected geometry

Packet PROVE-ZHAN-GT4-A22. Discharge the positive-time logarithmic Itô
input of the existing Doléans/Girsanov theorem, with its entrance limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Under the actual normalized seeded density the compensated driving
coordinate is Brownian; no stochastic logarithm identity is assumed. -/
theorem seed_girsanov_of_protected_data
    (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω}
    {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (rr : Fin n → ℝ)
    {B D : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    {d : Ω → SeedData n}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ}
    (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    {Tm : ℝ} (hTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    {r a₀ ρm : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ,
      IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).W t : ℂ) r)
        ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω m t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).V m t : ℂ) ρm)
        ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hV₀ : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hG₀ : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (d ω).G₀
        (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Ioc 0 (T ω)) t)
    (hV : ∀ ω m t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (T ω)))
    (hD : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω)
        ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hVm : ∀ (q : ℝ≥0) m,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).G₀ q))
    (hgc : ∀ ω i, ContinuousOn ((d ω).gapVal i) (Icc 0 (T ω)))
    (hgn : ∀ ω i t, t ∈ Ioc (0 : ℝ) (T ω) → (d ω).gapVal i t ≠ 0)
    (hp : IsStronglyPredictable 𝓕 (seedNoise κ d T))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hreg : Girsanov.IsRiemannRegular P (seedNoise κ d T))
    (hnc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (T ω)))
    {U : ℝ≥0} (hTU : ∀ ω, T ω < U) :
    IsFilteredBrownianReal 𝓕 (Girsanov.girsanovProcess B (seedNoise κ d T)) (seedMeasure P d T) ∧
      MathFin.IsEquivProbMeasure P (seedMeasure P d T) := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hi := seedPositiveLogIto_of_protected_data 𝓕 hκ rr hB hBc hDm hDc hdW hdκ hdr hdφ hdζ
    hT hTm hr ha₀ hρm h hv₀ hclr hA1 hmclr hV₀ hG₀ hV hVc hD hVm hV₀m hG₀m hgc hgn
    hp.isStronglyProgressive hC hb hreg
  exact seed_girsanov_of_positiveIto hB hp hb hreg hnc hi hTU

end InteractingSLE.ZhanGT4
