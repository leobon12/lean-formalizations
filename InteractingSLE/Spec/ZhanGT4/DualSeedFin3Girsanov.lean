/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3D10

/-!
# Stochastic D10 under the actual seeded Brownian change

Packet PROVE-ZHAN-GT4-A22. Use the landed seeded Girsanov motion and
its actual offset in the mapped-driver Itô formula. The original driver
and conformal records are retained exactly, and the offset derivative
is proved from its noise primitive rather than supplied as an image-law input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual Girsanov coordinate satisfies stochastic mapped-driver D10
on every protected positive band below the original density horizon. Its Brownian assertion is the conclusion
of `seeded_source_calculus_right`; no stochastic image-driver formula is assumed. -/
theorem seed_girsanov_map_d10_on_band {n : ℕ} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ) {d : Ω → SeedData n}
    {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} (hε : 0 < ε) {S T : Ω → ℝ≥0} (hST : ∀ ω, S ω ≤ T ω)
    {A : Set ℂ} {r a₀ γ Γ lam ρm L M Cb C : ℝ}
    (hle : ∀ ω, ε ≤ S ω) (hΓ : 0 ≤ Γ) (hM : 0 ≤ M) (hCb : 0 ≤ Cb)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ)
    (hown : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hc : ∀ ω, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (hL : ∀ ω, SeedScaleOK r a₀ γ Γ lam (S ω) L)
    (hA0 : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) → |(d ω).A 0 t| ≤ M)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hnc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ d T u.toNNReal ω) (Ioc 0 (T ω)))
    (hD : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) → HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hbc : ∀ ω, ContinuousOn (fun t => (d ω).drift t + κ * (d ω).ellX t ((d ω).W t))
      (Icc (ε : ℝ) (S ω)))
    (hbb : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) →
      |(d ω).drift t + κ * (d ω).ellX t ((d ω).W t)| ≤ Cb)
    (hBh : IsFilteredBrownianReal 𝓕 (Girsanov.girsanovProcess B (seedNoise κ d T)) Q)
    (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hmA : ∀ k (u : ℝ≥0), ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => (d ω).A k u))
    (hmRate : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => (d ω).d10Rate u))
    {t : ℝ≥0} (hεt : ε ≤ t) :
    (fun ω => (d ω).A 0 (min t (S ω)) - (d ω).A 0 ε -
      ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), (d ω).d10Rate u) =ᵐ[Q]
    fun ω => Girsanov.stochIntegral Q 𝓕 (Girsanov.girsanovProcess B (seedNoise κ d T))
        (fun u ω => if ε ≤ u ∧ u < S ω then Real.sqrt κ * (d ω).A 1 u else 0) t ω -
      Girsanov.stochIntegral Q 𝓕 (Girsanov.girsanovProcess B (seedNoise κ d T))
        (fun u ω => if ε ≤ u ∧ u < S ω then Real.sqrt κ * (d ω).A 1 u else 0) 0 ω := by
  have hW (ω : Ω) : (d ω).W = driftDriver (Real.sqrt κ)
      (Girsanov.girsanovProcess B (seedNoise κ d T))
      (seedImageOffset (Real.sqrt κ) D (seedNoise κ d T)) ω :=
    (hdW ω).trans (seed_driver_girsanov_eq _ _ _ _ ω).symm
  have hDc (ω : Ω) (t : ℝ) (ht : t ∈ Icc (ε : ℝ) (S ω)) : HasDerivWithinAt
      (fun u : ℝ => seedImageOffset (Real.sqrt κ) D (seedNoise κ d T) u.toNNReal ω)
      ((d ω).drift t + κ * (d ω).ellX t ((d ω).W t)) (Icc (ε : ℝ) (S ω)) t := by
    have ht0 : t ∈ Ioc (0 : ℝ) (T ω) :=
      ⟨(NNReal.coe_pos.2 hε).trans_le ht.1, ht.2.trans (hST ω)⟩
    have hA : (d ω).A 1 t ≠ 0 := (hown ω).frzA_one_pos
      ⟨ε.coe_nonneg.trans ht.1, ht.2⟩ |>.ne'
    have hh := (seedImageOffset_deriv_and_d10 hκ hdκ hp hb hnc hD ω ht0 hA).1
    have hn := (seedNoise_coordinate κ d T).1 ω t.toNNReal (Real.toNNReal_pos.2 ht0.1)
      (Real.toNNReal_le_iff_le_coe.2 ht0.2)
    rw [Real.coe_toNNReal _ ht0.1.le] at hn
    rw [hn] at hh
    have he : (d ω).drift t - Real.sqrt κ * (-Real.sqrt κ * (d ω).ellX t ((d ω).W t)) =
        (d ω).drift t + κ * (d ω).ellX t ((d ω).W t) := by
      calc _ = (d ω).drift t + (Real.sqrt κ) ^ 2 * (d ω).ellX t ((d ω).W t) := by ring
           _ = _ := by rw [Real.sq_sqrt hκ.le]
    rw [he] at hh
    exact hh.mono (fun u hu => ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2.trans (hST ω)⟩)
  have hBhc (ω : Ω) : Continuous (Girsanov.girsanovProcess B (seedNoise κ d T) · ω) :=
    (hBc ω).add (Girsanov.continuous_drift hp hb ω)
  exact seed_map_d10_of_protected_data hκ hle hΓ hM hCb hW hdκ hown hc hL hA0 hDc hbc hbb
    hBh hBhc hS hmA hmRate hεt

end InteractingSLE.ZhanGT4
