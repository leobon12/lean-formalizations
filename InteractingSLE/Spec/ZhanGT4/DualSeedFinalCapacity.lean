/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalCoeff
import InteractingSLE.Spec.ZhanGT4.DualSeedLawEvolution

/-!
# Construction of the capacity Brownian motion

Packet PROVE-ZHAN-GT4-A22. Start with the own-time compensated mapped
driver as an integral against the Girsanov Brownian motion. Doléans,
optional sampling and the landed Lévy characterization construct the
capacity Brownian motion, including its continuation after the horizon.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w Y : ℝ≥0 → Ω → ℝ}

/-- The actual seeded compensated image driver, spliced with the driving
Brownian motion after the own-time horizon. The subtraction at zero fixes
the image driver's spatial origin. -/
def seedOwnMappedNoise {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ((d ω).A 0 (min u (S ω)) - (d ω).A 0 0 -
      (∫ r in (0 : ℝ)..(min u (S ω) : ℝ≥0), (d ω).d10Rate r)) / Real.sqrt κ +
    (B u ω - B (min u (S ω)) ω)

/-- The exact remaining seeded (D10) integral calculation, in own time.
Here `B` is the Brownian coordinate under the actual seeded measure. -/
def SeedOwnD10Integral {n : ℕ} (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : Prop :=
  ∀ u, seedOwnMappedNoise κ d S B u =ᵐ[Q]
    stochIntegral Q 𝓕 B (seedCapacityCoeff d S) u

/-- The spliced mapped noise starts at zero pathwise. -/
theorem seedOwnMappedNoise_zero {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : seedOwnMappedNoise κ d S B 0 ω = 0 := by
  simp only [seedOwnMappedNoise, zero_min, NNReal.coe_zero, min_eq_left (S ω).coe_nonneg,
    intervalIntegral.integral_same,
    sub_self, zero_div, add_zero]

/-- The own-time stochastic integral and a nondegenerate bounded clock
coefficient construct a full Brownian motion in capacity time. -/
theorem exists_seed_capacity_brownian_of_integral
    (hB : IsFilteredBrownianReal 𝓕 B Q) (hw : IsStronglyProgressive 𝓕 w)
    {C c : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hc : 0 < c)
    (hlb : ∀ u ω, c ≤ w u ω ^ 2) (hr : IsRiemannRegular Q w)
    (hYc : ∀ ω, Continuous (Y · ω)) (hYm : ∀ u, Measurable[𝓕 u] (Y u))
    (hY0 : ∀ ω, Y 0 ω = 0) (hYI : ∀ u, Y u =ᵐ[Q] stochIntegral Q 𝓕 B w u) :
    ∃ 𝓗 : Filtration ℝ≥0 mΩ,
      IsFilteredBrownianReal 𝓗 (fun u ω => Y (invClockT (seedQuadClock w) u ω) ω) Q ∧
      ∀ ω, Continuous (fun u => Y (invClockT (seedQuadClock w) u ω) ω) := by
  have : IsProbabilityMeasure Q := hB.isProbabilityMeasure'
  have hCc := continuous_seedQuadClock hw hb
  have hCs := strictMono_seedQuadClock hw hb hc hlb
  have hC0 := seedQuadClock_zero w
  have hClb := seedQuadClock_ge hw hb hlb
  have hCm := measurable_seedQuadClock hw
  have hZ := seed_martingale_wald_of_integral
    (isFilteredPreBrownian_of_isFilteredBrownianReal hB) hw hb hr hYm hYI
  refine ⟨_, isFilteredBrownianReal_timeChange hYc hYm hY0 hCc hCs hC0 hc hClb hCm hZ, ?_⟩
  exact fun ω => (hYc ω).comp (continuous_invClockT hCc hCs hC0 hc hClb ω)

/-- Deterministic capacity substitution gives the required agreement with
the image coordinates. No Brownian agreement hypothesis is imposed. -/
theorem exists_SeedCapacityBrownian_of_own_integral
    {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {S T : Ω → ℝ≥0}
    (hB : IsFilteredBrownianReal 𝓕 B Q) (hw : IsStronglyProgressive 𝓕 w)
    {C c : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hc : 0 < c)
    (hlb : ∀ u ω, c ≤ w u ω ^ 2) (hr : IsRiemannRegular Q w)
    (hYc : ∀ ω, Continuous (Y · ω)) (hYm : ∀ u, Measurable[𝓕 u] (Y u))
    (hY0 : ∀ ω, Y 0 ω = 0) (hYI : ∀ u, Y u =ᵐ[Q] stochIntegral Q 𝓕 B w u)
    (hT : ∀ ω, (T ω : ℝ) = seedQuadClock w ω (S ω))
    (himage : ∀ ω r, r ≤ S ω →
      seedCapacityNoise κ ρL ρR (W · ω) (fun i u => VL i u ω) (fun j u => VR j u ω)
        (seedQuadClock w ω r).toNNReal = Y r ω) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (Bh : ℝ≥0 → Ω → ℝ),
      SeedCapacityBrownian κ ρL ρR Q 𝓗 W VL VR T Bh ∧ ∀ ω, Continuous (Bh · ω) := by
  obtain ⟨𝓗, hBh, hBhc⟩ := exists_seed_capacity_brownian_of_integral
    hB hw hb hc hlb hr hYc hYm hY0 hYI
  refine ⟨𝓗, _, ⟨hBh, ?_⟩, hBhc⟩
  intro ω u hu
  have hCc := continuous_seedQuadClock hw hb
  have hCs := strictMono_seedQuadClock hw hb hc hlb
  have hval := invClock_eq_coe hCc (seedQuadClock_zero w) hc (seedQuadClock_ge hw hb hlb) u ω
  have hτ : invClockT (seedQuadClock w) u ω ≤ S ω := by
    apply (hCs ω).le_iff_le.1
    rw [hval.2.1, ← hT ω]
    exact hu
  have he := himage ω _ hτ
  rw [hval.2.1, Real.toNNReal_coe] at he
  exact he.symm

/-- Capacity Brownian construction for the actual seeded mapped driver.
The coefficient, its predictability, regularity and nondegeneracy, and the
identity of its clock with the own-map capacity are all supplied here. -/
theorem exists_SeedCapacityBrownian_seeded_D10
    {n nL nR : ℕ} {κ : ℝ} {d : Ω → SeedData n} {S T : Ω → ℝ≥0}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {A : Ω → Set ℂ}
    (hB : IsFilteredBrownianReal 𝓕 B Q)
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u - 1))
    (hcA : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω)))
    {C a₀ : ℝ} (ha : 0 < a₀)
    (hb : ∀ ω u, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C)
    (hlb : ∀ ω u, 0 < u → u ≤ S ω → a₀ ≤ (d ω).A 1 u)
    (hYc : ∀ ω, Continuous (seedOwnMappedNoise κ d S B · ω))
    (hYm : ∀ u, Measurable[𝓕 u] (seedOwnMappedNoise κ d S B u))
    (hD10 : SeedOwnD10Integral Q 𝓕 B κ d S)
    (hT : ∀ ω, (T ω : ℝ) = (d ω).a (S ω))
    (himage : ∀ ω r, r ≤ S ω →
      seedCapacityNoise κ ρL ρR (W · ω) (fun i u => VL i u ω) (fun j u => VR j u ω)
        ((d ω).a r).toNNReal = seedOwnMappedNoise κ d S B r ω) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (Bh : ℝ≥0 → Ω → ℝ),
      SeedCapacityBrownian κ ρL ρR Q 𝓗 W VL VR T Bh ∧ ∀ ω, Continuous (Bh · ω) := by
  apply exists_SeedCapacityBrownian_of_own_integral hB
    (seedCapacityCoeff_predictable 𝓕 hm hcA).isStronglyProgressive
    (abs_seedCapacityCoeff_le hb) (c := min (a₀ ^ 2) 1)
    (lt_min (sq_pos_of_pos ha) zero_lt_one) (seedCapacityCoeff_sq_ge ha hlb)
    (seedCapacityCoeff_riemannRegular Q hcA) hYc hYm
    (seedOwnMappedNoise_zero κ d S B) hD10
  · intro ω
    rw [seedCapacityCoeff_clock_eq hown ω le_rfl]
    exact hT ω
  · intro ω r hr
    rw [seedCapacityCoeff_clock_eq hown ω hr]
    exact himage ω r hr

end InteractingSLE.ZhanGT4
