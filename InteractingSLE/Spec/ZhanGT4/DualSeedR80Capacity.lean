/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedR80Adapted
import InteractingSLE.Spec.ZhanGT4.A1FamilyFilt

/-!
# Actual capacity noise with the named stochastic inputs discharged

Packet PROVE-ZHAN-GT4-A22. The source calculus proves global D10 and exact
mapped-noise adaptedness. The landed capacity theorem then gives Brownian
motion for the actual inverse-clock noise in the exposed capacity-time
filtration used by the frozen-family construction.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open Girsanov
open QuantumZipper (fwdMap IsForwardSol)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Actual source geometry supplies capacity Brownian noise in the exposed
family filtration, with no D10 or mapped-noise measurability premise. -/
theorem exists_seedCapacityBrownian_actual_source {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ)
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
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (T ω)))
    (hc20 : ∀ ω, ContinuousOn (d ω).A20 (Icc 0 (T ω)))
    (hne20 : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → (d ω).A 0 t ≠ (d ω).A20 t)
    (hi : ∀ ω, (d ω).ImageEntranceIntegrable (T ω))
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hρL : ∀ ω i, (d ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (d ω).imageCharge (e (.inr j)) = ρR j) :
    ∃ (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d T) ω))
      (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d T) ω))
      (hcm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => seedQuadClock (seedCapacityCoeff d T) ω u),
      SeedCapacityBrownian κ ρL ρR Q (A1Family.seedFilt 𝓕 d T hCc hCm hcm)
        (seedCapacityDriver d T) (fun i => seedCapacityForce d T (e (.inl i)))
        (fun j => seedCapacityForce d T (e (.inr j))) (seedCapacityHorizon d T)
        (A1Family.seedBh κ d T (girsanovProcess B (seedNoise κ d T))) ∧
      ∀ ω, Continuous (A1Family.seedBh κ d T (girsanovProcess B (seedNoise κ d T)) · ω) := by
  have hD10 := seedOwnD10Integral_of_actual_source hκ rr hdW hdκ hdr hXm hXc hdWX hdφ hdζ
    hTU hT hM hC hr ha₀ hρm h hv₀ hclr hA1 hmclr hA0 hV₀ hV hD hp hb hnc hVm hBh hBc
    hYc hYm hYv hne hc20 hne20 hi
  obtain ⟨hmA, hcA, hbA⟩ := seedMap_alive_derivative_facts hXm hXc hdWX hdφ hdζ hdκ hdr
    hT hr hρm h hv₀ hclr hmclr hVm
  have hm (u : ℝ≥0) : Measurable[𝓕 u]
      ({ω | u ≤ T ω}.indicator fun ω => (d ω).A 1 u - 1) := by
    have hE := measurableSet_ge_of_isStoppingTime hT u
    convert (hmA u).sub ((measurable_const (a := (1 : ℝ))).indicator hE) using 1
    funext ω
    by_cases hω : u ≤ T ω <;> simp [indicator, hω]
  have hlow (ω : Ω) (u : ℝ≥0) (_ : 0 < u) (hu : u ≤ T ω) : a₀ ≤ (d ω).A 1 u :=
    hA1 ω u ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
  have hBhc (ω : Ω) : Continuous (girsanovProcess B (seedNoise κ d T) · ω) :=
    (hBc ω).add (Girsanov.continuous_drift hp hb ω)
  have hneB (ω : Ω) (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) (T ω)) (m : Fin n) :
      (d ω).A 0 u ≠ (d ω).B0 u m := by
    intro he
    have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
    have huT : u.toNNReal ≤ T ω := Real.toNNReal_le_iff_le_coe.2 hu.2
    have hh := hne ω (Sum.inr (Sum.inl (0, m))) u.toNNReal hu0 huT
    rw [hYv ω _ u.toNNReal hu0 huT, Real.coe_toNNReal _ hu.1.le] at hh
    apply hh
    simp only [SeedData.gapVal, Matrix.cons_val_zero, he, sub_self]
  have hNm := measurable_seedOwnMappedNoise_of_source hXm hXc hdWX hdφ hdζ hdκ hdr hT hρm
    h hv₀ hmclr hVm hVc hc20 hne20 hneB hi (fun u => hBh.2.1 u) hBhc
  obtain ⟨hCc, hCs, hcm, -⟩ := A1Family.clock_props hm hcA ha₀
    (fun ω u => hbA u ω) hlow
  refine ⟨hCc, fun ω => (hCs ω).monotone, hcm, ?_⟩
  exact A1Family.seedCapacityBrownian_seedFilt e hBh hBhc h hm hcA ha₀
    (fun ω u => hbA u ω) hlow hdκ hρL hρR hc20 hne20 hi hNm hD10
    hCc (fun ω => (hCs ω).monotone) hcm

end InteractingSLE.ZhanGT4
