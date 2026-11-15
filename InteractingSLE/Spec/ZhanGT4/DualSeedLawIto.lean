/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawRemainder

/-!
# Random-field Itô identification from deterministic Taylor errors

Packet PROVE-ZHAN-GT4-A22. Unlike a martingale-form Itô theorem, the
conclusion identifies the actual general-filtration stochastic integral.
The Taylor input is a finite-partition estimate, not a stochastic identity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B X c₁ c₂ : ℝ≥0 → Ω → ℝ}

/-- The signed Taylor defects summed over the clamped dyadic grid. -/
def seedDyadicDefect (X c₁ c₂ B : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (cells n),
    Ito.itoDefect X c₁ c₂ B (min (grid n k) t) (min (grid n (k + 1)) t) ω

/-- Clamping the sampled coefficient does not change a Brownian Riemann
sum: every cell whose left endpoint exceeds `t` has zero increment. -/
theorem seed_riemannSum_clamped (B c : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    riemannSum B c n t ω = ∑ k ∈ Finset.range (cells n), c (min (grid n k) t) ω *
      (B (min (grid n (k + 1)) t) ω - B (min (grid n k) t) ω) := by
  unfold riemannSum
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : grid n k ≤ t
  · rw [min_eq_left hk]
  · have hk' : t ≤ grid n k := le_of_not_ge hk
    rw [min_eq_right hk', min_eq_right (hk'.trans (grid_mono n (Nat.le_succ k)))]
    simp only [sub_self, mul_zero]

/-- Exact telescoping on a finite partition, before taking any limit. -/
theorem seedDyadicDefect_eq (X c₁ c₂ B : ℝ≥0 → Ω → ℝ) (n : ℕ) {t : ℝ≥0}
    (ht : t ≤ n) (ω : Ω) :
    seedDyadicDefect X c₁ c₂ B n t ω = X t ω - X 0 ω - riemannSum B c₁ n t ω -
      seedQuadraticError B c₂ n t ω / 2 := by
  have htel : (∑ k ∈ Finset.range (cells n), X (min (grid n (k + 1)) t) ω) -
      (∑ k ∈ Finset.range (cells n), X (min (grid n k) t) ω) = X t ω - X 0 ω := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun k => X (min (grid n k) t) ω) (cells n),
      grid_cells, min_eq_right ht, grid_zero, zero_min]
  rw [seed_riemannSum_clamped]
  simp only [seedDyadicDefect, Ito.itoDefect, seedQuadraticError, Finset.sum_sub_distrib, htel,
    mul_assoc, ← Finset.mul_sum, NNReal.coe_min]
  ring

/-- **The integral form of the random-field Itô engine.** Vanishing signed
Taylor errors and bounded adapted coefficients identify the stochastic
integral, in the original filtration. -/
theorem seed_stochIntegral_eq_of_dyadicDefect (hB : IsFilteredPreBrownian B 𝓕 P)
    (h₁ : StronglyAdapted 𝓕 c₁) {C₁ : ℝ} (hb₁ : ∀ u ω, |c₁ u ω| ≤ C₁)
    (hr₁ : IsRiemannRegular P c₁) (h₂ : StronglyAdapted 𝓕 c₂)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ u ω, |c₂ u ω| ≤ C₂) (t : ℝ≥0)
    (hd : TendstoInMeasure P (fun n => seedDyadicDefect X c₁ c₂ B n t) atTop (fun _ => (0 : ℝ))) :
    (fun ω => X t ω - X 0 ω) =ᵐ[P] stochIntegral P 𝓕 B c₁ t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨ns, hns, hI⟩ := (tendstoInMeasure_riemannSum hB h₁ hb₁ hr₁ t).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hQ⟩ :=
    ((tendstoInMeasure_seedQuadraticError hB h₂ hC₂ hb₂ t).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ls, hls, hD⟩ :=
    ((hd.comp hns.tendsto_atTop).comp hms.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hI, hQ, hD] with ω hIω hQω hDω
  have hI' := (hIω.comp hms.tendsto_atTop).comp hls.tendsto_atTop
  have hQ' := hQω.comp hls.tendsto_atTop
  have hl := (hI'.add (hQ'.div_const 2)).add hDω
  simp only [zero_div, add_zero] at hl
  have he : ∀ᶠ k in atTop, riemannSum B c₁ (ns (ms (ls k))) t ω +
      seedQuadraticError B c₂ (ns (ms (ls k))) t ω / 2 +
      seedDyadicDefect X c₁ c₂ B (ns (ms (ls k))) t ω = X t ω - X 0 ω := by
    have hnat : Tendsto (fun k => (ns (ms (ls k)) : ℝ≥0)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (hns.tendsto_atTop.comp (hms.tendsto_atTop.comp hls.tendsto_atTop))
    filter_upwards [hnat.eventually (eventually_ge_atTop t)] with k hk
    rw [seedDyadicDefect_eq _ _ _ _ _ hk]
    ring
  have hc : Tendsto (fun _ : ℕ => X t ω - X 0 ω) atTop
      (𝓝 (stochIntegral P 𝓕 B c₁ t ω)) := (tendsto_congr' he).1 hl
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-- The deterministic cubic-plus-modulus estimate is sufficient for the
integral identity; the quadratic and cubic stochastic limits are proved. -/
theorem seed_stochIntegral_eq_of_taylor_bound (hB : IsFilteredBrownianReal 𝓕 B P)
    (h₁ : StronglyAdapted 𝓕 c₁) {C₁ : ℝ} (hb₁ : ∀ u ω, |c₁ u ω| ≤ C₁)
    (hr₁ : IsRiemannRegular P c₁) (h₂ : StronglyAdapted 𝓕 c₂)
    {C₂ C K : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ u ω, |c₂ u ω| ≤ C₂)
    (hC : 0 ≤ C) (t : ℝ≥0)
    (hm : ∀ n, Measurable (seedDyadicDefect X c₁ c₂ B n t))
    {R : ℕ → Ω → ℝ} (hR : ∀ n, Measurable (R n))
    (hR0 : ∀ n ω, 0 ≤ R n ω) (hRb : ∀ n ω, R n ω ≤ K)
    (hRl : ∀ ω, Tendsto (fun n => R n ω) atTop (𝓝 0))
    (he : ∀ n ω, |seedDyadicDefect X c₁ c₂ B n t ω| ≤ C * seedCubicError B n t ω + R n ω) :
    (fun ω => X t ω - X 0 ω) =ᵐ[P] stochIntegral P 𝓕 B c₁ t :=
  seed_stochIntegral_eq_of_dyadicDefect (Girsanov.isFilteredPreBrownian_of_isFilteredBrownianReal hB)
    h₁ hb₁ hr₁ h₂ hC₂ hb₂ t (tendstoInMeasure_seedTaylorError hB hm hR hC t hR0 hRb hRl he)

end InteractingSLE.ZhanGT4
