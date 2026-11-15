/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Ito

/-!
# The stochastic seeded mapped-driver D10 on a protected positive band

Packet PROVE-ZHAN-GT4-A22. Apply original-clock Itô to the actual
reflected map. The Brownian motion may be the seeded Girsanov Brownian
motion; its offset rate is the source drift plus `κ ℓ_x`. The map field,
Taylor pasting, and its D10 generator are conclusions of protected geometry.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Original-clock mapped-driver D10 on a protected seed band. The
coefficient is exactly `√κ A₁` between the restart and the band exit.
No map-field, Taylor, generator or stochastic-integral identity is an input. -/
theorem seed_map_d10_of_protected_data {n : ℕ} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ) {d : Ω → SeedData n}
    {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    {A : Set ℂ} {r a₀ γ Γ lam ρm L M Cb : ℝ}
    (hle : ∀ ω, ε ≤ S ω) (hΓ : 0 ≤ Γ) (hM : 0 ≤ M) (hCb : 0 ≤ Cb)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ)
    (hown : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hc : ∀ ω, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (hL : ∀ ω, SeedScaleOK r a₀ γ Γ lam (S ω) L)
    (hA0 : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) → |(d ω).A 0 t| ≤ M)
    (hD : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) → HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t + κ * (d ω).ellX t ((d ω).W t))
      (Icc (ε : ℝ) (S ω)) t)
    (hbc : ∀ ω, ContinuousOn (fun t => (d ω).drift t + κ * (d ω).ellX t ((d ω).W t))
      (Icc (ε : ℝ) (S ω)))
    (hbb : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) →
      |(d ω).drift t + κ * (d ω).ellX t ((d ω).W t)| ≤ Cb)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hmA : ∀ k (u : ℝ≥0), ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => (d ω).A k u))
    (hmRate : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => (d ω).d10Rate u))
    {t : ℝ≥0} (hεt : ε ≤ t) :
    (fun ω => (d ω).A 0 (min t (S ω)) - (d ω).A 0 ε -
      ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), (d ω).d10Rate u) =ᵐ[P]
    fun ω => Girsanov.stochIntegral P 𝓕 B
        (fun u ω => if ε ≤ u ∧ u < S ω then Real.sqrt κ * (d ω).A 1 u else 0) t ω -
      Girsanov.stochIntegral P 𝓕 B
        (fun u ω => if ε ≤ u ∧ u < S ω then Real.sqrt κ * (d ω).A 1 u else 0) 0 ω := by
  classical
  by_cases hne : Nonempty Ω
  swap
  · have : IsEmpty Ω := not_nonempty_iff.mp hne
    exact Eventually.of_forall fun ω => isEmptyElim ω
  have : Nonempty Ω := hne
  let b : Ω → ℝ → ℝ := fun ω t => (d ω).drift t + κ * (d ω).ellX t ((d ω).W t)
  have hF := seedMap_isSeedDriftField hle hΓ hM hCb hdW hown hc hL hA0 hD hbc hbb
  have hρ : 0 < 3 * cutRad r a₀ γ / 4 := by
    have hh := cutRad_pos (hc (Classical.arbitrary Ω)).r0
      (hc (Classical.arbitrary Ω)).a0 (hc (Classical.arbitrary Ω)).g0
    positivity
  have hmF (k : ℕ) (u : ℝ≥0) (hu : ε ≤ u) : Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => (d ω).F k u (driftDriver (Real.sqrt κ) B D ω u)) := by
    convert hmA k u hu using 1
    funext ω
    by_cases hs : u ≤ S ω
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hs)]
      rw [← hdW ω]
      exact (d ω).F_driver k u
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω} from hs)]
  have hG (ω : Ω) (u : ℝ) (hu : u ∈ Icc (ε : ℝ) (S ω)) :
      seedDriftGenerator (fun ω => (d ω).F 1) (fun ω => (d ω).F 2)
        (fun ω => (d ω).mapTime) b (Real.sqrt κ) B D ω u = (d ω).d10Rate u := by
    unfold seedDriftGenerator
    rw [← hdW ω, Real.sq_sqrt hκ.le]
    have hh := (d ω).map_generator_d10_of_const (hown ω) (hc ω) ε.coe_nonneg
      (by rw [hdκ ω]; exact hκ.ne') hu
    simpa only [hdκ ω] using hh
  have hmG (u : ℝ≥0) (hu : ε ≤ u) : Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => seedDriftGenerator (fun ω => (d ω).F 1)
        (fun ω => (d ω).F 2) (fun ω => (d ω).mapTime) b (Real.sqrt κ) B D ω u) := by
    convert hmRate u hu using 1
    funext ω
    by_cases hs : u ≤ S ω
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hs)]
      exact hG ω u ⟨hu, hs⟩
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω} from hs)]
  have he := hF.seed_original_fieldIto hB hBc (Real.sqrt_pos.2 hκ) hρ hS
    (hmF 0) (hmF 1) (hmF 2) hmG hεt
  have hcoef : seedEndCoef ε (Ito.stopCoef
      (seedRestartDeriv 1 (fun ω => (d ω).F 1) (Real.sqrt κ) B D ε)
      (shiftBM B ε) (fun ω => S ω - ε)) =
      fun u ω => if ε ≤ u ∧ u < S ω then Real.sqrt κ * (d ω).A 1 u else 0 := by
    funext u ω
    rw [seed_restart_coef_eq _ _ _ _ _ _ _ (hle ω)]
    rw [← hdW ω, (d ω).F_driver]
  rw [hcoef] at he
  filter_upwards [he] with ω hω
  have hi : (∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), seedDriftGenerator
      (fun ω => (d ω).F 1) (fun ω => (d ω).F 2) (fun ω => (d ω).mapTime) b
      (Real.sqrt κ) B D ω u) = ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), (d ω).d10Rate u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (show (ε : ℝ) ≤ (min t (S ω) : ℝ≥0) from le_min hεt (hle ω))] at hu
    exact hG ω u ⟨hu.1, hu.2.trans (by exact_mod_cast min_le_right t (S ω))⟩
  rw [hi, ← hdW ω, (d ω).F_driver, (d ω).F_driver] at hω
  exact hω

end InteractingSLE.ZhanGT4
