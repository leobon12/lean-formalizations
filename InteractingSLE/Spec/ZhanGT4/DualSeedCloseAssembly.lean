/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseContinuity

/-!
# Capacity Brownian motion for the actual seeded image coordinates

Packet PROVE-ZHAN-GT4-A22. Discharge the coordinate substitution, horizon
identity and continuity premises of `exists_SeedCapacityBrownian_seeded_D10`.
The own-time stochastic D10 identity remains named and unchanged. In
particular this theorem does not claim to prove that stochastic identity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

/-- The actual inverse-clock image driver has the capacity Brownian noise.
The only stochastic D10 premise is the existing `SeedOwnD10Integral`;
capacity agreement and continuity of the mapped noise are conclusions. -/
theorem exists_SeedCapacityBrownian_actual_coordinates
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {n nL nR : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hB : IsFilteredBrownianReal 𝓕 B Q) (hBc : ∀ ω, Continuous (B · ω))
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u - 1))
    (hcA : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω)))
    {C a₀ : ℝ} (ha : 0 < a₀)
    (hb : ∀ ω u, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C)
    (hlb : ∀ ω u, 0 < u → u ≤ S ω → a₀ ≤ (d ω).A 1 u)
    (hκ : ∀ ω, (d ω).κ = κ)
    (hρL : ∀ ω i, (d ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (d ω).imageCharge (e (.inr j)) = ρR j)
    (h20 : ∀ ω, ContinuousOn (d ω).A20 (Icc 0 (S ω)))
    (hsep : ∀ ω t, t ∈ Icc (0 : ℝ) (S ω) → (d ω).A 0 t ≠ (d ω).A20 t)
    (hseed : ∀ ω, (d ω).ImageEntranceIntegrable (S ω))
    (hYm : ∀ u, Measurable[𝓕 u] (seedOwnMappedNoise κ d S B u))
    (hD10 : SeedOwnD10Integral Q 𝓕 B κ d S) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (Bh : ℝ≥0 → Ω → ℝ),
      SeedCapacityBrownian κ ρL ρR Q 𝓗 (seedCapacityDriver d S)
        (fun i => seedCapacityForce d S (e (.inl i)))
        (fun j => seedCapacityForce d S (e (.inr j))) (seedCapacityHorizon d S) Bh ∧
      ∀ ω, Continuous (Bh · ω) := by
  have hprog := (seedCapacityCoeff_predictable 𝓕 hm hcA).isStronglyProgressive
  have hbound := abs_seedCapacityCoeff_le hb
  have hlow := seedCapacityCoeff_sq_ge ha hlb
  have hpos : 0 < min (a₀ ^ 2) 1 := lt_min (sq_pos_of_pos ha) zero_lt_one
  have hCc := continuous_seedQuadClock hprog hbound
  have hCs := strictMono_seedQuadClock hprog hbound hpos hlow
  have hClb := seedQuadClock_ge hprog hbound hlow
  have hi (ω : Ω) (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :=
    (d ω).imageWeightedGap_integrable (hown ω) (h20 ω) (hsep ω) (hseed ω) i ht
  have hW (ω : Ω) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityDriver d S ((d ω).a u).toNNReal ω = (d ω).A 0 u - (d ω).A 0 0 := by
    have hule : u.toNNReal ≤ S ω := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
    simpa only [Real.coe_toNNReal _ hu.1] using
      seedCapacityDriver_at_capacity hown hCc hCs hpos hClb ω hule
  have hV (ω : Ω) (i : Fin (n + 1)) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityForce d S i ((d ω).a u).toNNReal ω =
        (d ω).imageForce u i - (d ω).A 0 0 := by
    have hule : u.toNNReal ≤ S ω := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
    simpa only [Real.coe_toNNReal _ hu.1] using
      seedCapacityForce_at_capacity hown hCc hCs hpos hClb ω i hule
  apply exists_SeedCapacityBrownian_seeded_D10 hB hown hm hcA ha hb hlb
    (continuous_seedOwnMappedNoise hown hBc (fun ω i => hi ω i (S ω)
      ⟨(S ω).coe_nonneg, le_rfl⟩)) hYm hD10
  · intro ω
    apply Real.coe_toNNReal
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn ⟨le_rfl, (hown ω).pos.le⟩
      ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  · exact seed_capacityNoise_eq_ownMappedNoise e hown hκ hρL hρR hW hV hi

end InteractingSLE.ZhanGT4
