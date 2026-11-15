/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstAdapted

/-!
# The actual stopped Brownian seeded row

Packet PROVE-ZHAN-GT4-A22. All rectangle, clearance, alive-flow, D9,
scale and source-gap inputs are derived from the enclosures.
The original mirror charge is zero. Both the compensating adapted drift
and the measurable protected source version are constructed, not assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual chosen row has the martingale, continuity, boundedness and
entrance-one properties from the original force equation and enclosures. -/
theorem seedStopped_row_facts_of_enclosures {n : ℕ} {P : Measure Ω} {κ S p s δ q d Tm : ℝ}
    {H₁ H₂ : Set ℂ} (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q d) (hκ : 0 < κ)
    (rr : Fin n → ℝ) (W₁ Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ)
    (W₂ : Ω → ℝ → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (hS : 0 < S) (hT : ∀ ω, 0 < T ω) (hs : s ∈ Ioc (0 : ℝ) S)
    (hDriver : ∀ ω, W₂ ω = seedStoppedDriver (Real.sqrt (16 / κ)) p B T ω)
    (hW₁ : Continuous W₁) (hW₁0 : W₁ 0 = 0)
    (hK₁ : fwdHull W₁ S ⊆ H₁) (hK₂ : ∀ ω, fwdHull (W₂ ω) (T ω) ⊆ H₂)
    (hlo : IsSeedCoordinate W₁ Vlo S) (hhi : IsSeedCoordinate W₁ Vhi S)
    (hseed : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hVI : ∀ m, V m s ∈ uIcc (Vlo s) (Vhi s)) (hinj : Function.Injective fun m => V m s)
    (hSm : S ≤ Tm) (hTTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hCharge : mirrorSourceCharge κ rr = 0)
    (hStop : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    Martingale (fun (t : ℝ≥0) ω =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v)
        ω s (min (t : ℝ) (T ω))) 𝓕 P ∧
    (∀ ω, Continuous fun t : ℝ≥0 =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v)
        ω s (min (t : ℝ) (T ω))) ∧
    (∃ C : ℝ, ∀ (t : ℝ≥0) ω, |seedHeightField
      (fun v ω => seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v)
        ω s (min (t : ℝ) (T ω))| ≤ C) ∧
    ∀ ω, seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω)
      (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v) ω s 0 = 1 := by
  let σ := Real.sqrt (16 / κ)
  let D := seedStoppedDrift σ B T
  let X : ℝ≥0 → Ω → ℝ := fun u ω => σ * B (min u (T ω)) ω + p
  have h0 : ∀ ω, W₂ ω 0 = p := by
    intro ω
    rw [hDriver ω]
    simp only [seedStoppedDriver, Real.toNNReal_zero, min_eq_left (show (0 : ℝ≥0) ≤ T ω from bot_le),
      hB0 ω, mul_zero, zero_add]
  have hdW : ∀ ω, (fun u => W₂ ω u - W₂ ω 0) = driftDriver σ B D ω := by
    intro ω
    rw [h0 ω, hDriver ω]
    exact seedStoppedDriver_eq_driftDriver σ p B T ω
  have hW₂ : ∀ ω, Continuous (W₂ ω) := by
    intro ω
    rw [hDriver ω]
    exact continuous_seedStoppedDriver hBc σ p T ω
  have hDm : ∀ u, Measurable[𝓕 u] (D u) :=
    measurable_seedStoppedDrift hB.2.1 hBc hStop σ
  have hDc : ∀ ω, Continuous (D · ω) := continuous_seedStoppedDrift hBc σ T
  have hXm : Adapted 𝓕 X := by
    intro u
    convert ((measurable_const.mul (hB.2.1 u)).add (hDm u)).add measurable_const using 1
    funext ω
    change σ * B (min u (T ω)) ω + p = σ * B u ω + seedStoppedDrift σ B T u ω + p
    unfold seedStoppedDrift
    ring
  have hXc : ∀ ω, Continuous (X · ω) := fun ω =>
    (continuous_const.mul ((hBc ω).comp (continuous_id.min continuous_const))).add continuous_const
  have hWX : ∀ ω, W₂ ω = fun u => X u.toNNReal ω := hDriver
  have hD : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal ω)
        (mirrorSourceCharge κ rr / (W₂ ω t - (frzChart (W₂ ω) t 0).re))
        (Icc (0 : ℝ) (T ω)) t := by
    intro ω t ht
    rw [hCharge, zero_div]
    exact hasDerivWithinAt_seedStoppedDrift σ T ω ht
  exact seedSrc_row_facts_of_adapted_enclosures hp hκ rr W₁ Vlo Vhi V W₂ 𝓕 B D T
    hS hT hs h0 hdW hW₁ hW₁0 hW₂ hK₁ hK₂ hlo hhi hseed hVI hinj hSm hTTm
    hB hDm hBc hDc X hXm hXc hWX hStop hD

end InteractingSLE.ZhanGT4
