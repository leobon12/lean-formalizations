/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalSplice

/-!
# Actual event-localized map fields under one seeded measure

Packet PROVE-ZHAN-GT4-A22. Construct the regular map field from the
protected band geometry and the original source force equations. The
Girsanov noise keeps its original terminal horizon throughout localization.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual source offset rate after the fixed-horizon seeded Brownian change. -/
def seedMappedDrift {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (T : Ω → ℝ≥0) (ω : Ω) (t : ℝ) : ℝ :=
  (d ω).drift t - Real.sqrt κ * seedNoise κ d T t.toNNReal ω

/-- At positive times this is the source drift plus the seeded logarithmic correction. -/
theorem seedMappedDrift_eq {n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (d : Ω → SeedData n)
    (T : Ω → ℝ≥0) (ω : Ω) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (T ω)) :
    seedMappedDrift κ d T ω t = (d ω).drift t + κ * (d ω).ellX t ((d ω).W t) := by
  have hn := (seedNoise_coordinate κ d T).1 ω t.toNNReal (Real.toNNReal_pos.2 ht.1)
    (Real.toNNReal_le_iff_le_coe.2 ht.2)
  rw [Real.coe_toNNReal _ ht.1.le] at hn
  unfold seedMappedDrift
  rw [hn]
  calc _ = (d ω).drift t + (Real.sqrt κ) ^ 2 * (d ω).ellX t ((d ω).W t) := by ring
       _ = _ := by rw [Real.sq_sqrt hκ]

/-- Protected actual band data construct the event-localized regular map
field under the fixed Girsanov Brownian coordinate. -/
theorem seedMap_localized_field {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} {rr : Fin n → ℝ} {d : Ω → SeedData n} {B D : ℝ≥0 → Ω → ℝ}
    {ε : ℝ≥0} (hε : 0 < ε) {S T : Ω → ℝ≥0} {E : Set Ω}
    {A : Set ℂ} {r a₀ γ Γ lam ρm L M C Tm : ℝ}
    (hΓ : 0 ≤ Γ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hle : ∀ ω, ε ≤ S ω) (hST : ∀ ω ∈ E, S ω ≤ T ω) (hSTm : ∀ ω ∈ E, (S ω : ℝ) ≤ Tm)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hown : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hc : ∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (hL : SeedScaleOK r a₀ γ Γ lam Tm L)
    (hA0 : ∀ ω ∈ E, ∀ t ∈ Icc (ε : ℝ) (S ω), |(d ω).A 0 t| ≤ M)
    (hV₀ : ∀ ω ∈ E, ∀ t ∈ Icc (ε : ℝ) (S ω), HasDerivWithinAt (d ω).V₀
      (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hV : ∀ ω ∈ E, ∀ m, ∀ t ∈ Icc (ε : ℝ) (S ω), HasDerivWithinAt ((d ω).V m)
      (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hnc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ d T u.toNNReal ω) (Ioc 0 (T ω)))
    (hD : ∀ ω ∈ E, ∀ t ∈ Ioc (0 : ℝ) (T ω), HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t) (Ioc 0 (T ω)) t) :
    IsSeedDriftField (Real.sqrt κ) (3 * cutRad r a₀ γ / 4)
      (Real.exp L + Γ + M + (|κ| * (coefTot κ rr * scaleBound L) + Real.sqrt κ * C))
      (Girsanov.girsanovProcess B (seedNoise κ d T))
      (seedImageOffset (Real.sqrt κ) D (seedNoise κ d T))
      (onEvB E (seedMappedDrift κ d T)) ε (onEvS E ε S)
      (onEv E (fun ω => (d ω).F 0)) (onEv E (fun ω => (d ω).F 1))
      (onEv E (fun ω => (d ω).F 2)) (onEv E (fun ω => (d ω).F 3))
      (onEv E (fun ω => (d ω).mapTime)) := by
  have hcoef : 0 ≤ coefTot κ rr * scaleBound L :=
    mul_nonneg (coefTot_ge (κ := κ) (r := rr)).2.2.2
      (hL.base.L0.trans (le_scaleBound hL.base.L0).1)
  apply seedDriftField_localize (by positivity)
  intro ω hω
  have hLω := hL.mono (hc ω hω).r0 (hc ω hω).a0 (hSTm ω hω)
  have hsub : Icc (ε : ℝ) (S ω) ⊆ Ioc (0 : ℝ) (T ω) := fun u hu =>
    ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2.trans (hST ω hω)⟩
  have hd (t : ℝ) (ht : t ∈ Icc (ε : ℝ) (S ω)) : HasDerivWithinAt
      (fun u : ℝ => seedImageOffset (Real.sqrt κ) D (seedNoise κ d T) u.toNNReal ω)
      (seedMappedDrift κ d T ω t) (Icc (ε : ℝ) (S ω)) t :=
    ((hD ω hω t (hsub ht)).sub
      ((hasDerivWithinAt_seed_drift_pos hp hb hnc ω (hsub ht)).const_mul _)).mono hsub
  have hcont : ContinuousOn (seedMappedDrift κ d T ω) (Icc (ε : ℝ) (S ω)) :=
    ((d ω).continuousOn_drift (hown ω hω) (hc ω hω) (hV₀ ω hω) (hV ω hω)).sub
      (((hnc ω).mono hsub).const_mul (Real.sqrt κ))
  have hbound (t : ℝ) (ht : t ∈ Icc (ε : ℝ) (S ω)) :
      |seedMappedDrift κ d T ω t| ≤ |κ| * (coefTot κ rr * scaleBound L) + Real.sqrt κ * C := by
    have hd' := (d ω).abs_drift_le (hc ω hω) hLω ht
    rw [hdκ ω, hdr ω] at hd'
    have hn : |Real.sqrt κ * seedNoise κ d T t.toNNReal ω| ≤ Real.sqrt κ * C := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]
      exact mul_le_mul_of_nonneg_left (hb _ _) (Real.sqrt_nonneg κ)
    exact (abs_sub _ _).trans (add_le_add hd' hn)
  have hW : (d ω).W = driftDriver (Real.sqrt κ)
      (Girsanov.girsanovProcess B (seedNoise κ d T))
      (seedImageOffset (Real.sqrt κ) D (seedNoise κ d T)) ω :=
    (hdW ω).trans (seed_driver_girsanov_eq _ _ _ _ ω).symm
  exact seedMap_isSeedDriftField (Ω := Unit) (fun _ => hle ω) hΓ hM (by positivity)
    (fun _ => hW) (fun _ => hown ω hω) (fun _ => hc ω hω) (fun _ => hLω)
    (fun _ => hA0 ω hω) (fun _ => hd) (fun _ => hcont) (fun _ => hbound)

end InteractingSLE.ZhanGT4
