/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.ItoExpectation

/-!
# The zero set of the path is Lebesgue-null (localized occupation statement)

Packet PROVE-TANAKA. Under the hypotheses of `integral_sub_eq_of_isTanakaPath` with `a ≠ 0`, almost
surely the zero set `{r ∈ [s, ρ] : X_r = 0}` has Lebesgue measure zero
(`ae_volume_zeroSet_eq_zero`). This is the instance `∫_s^ρ 1{X_r = 0} d⟨X⟩_r = a² |{X = 0}| = 0`
of the occupation-times formula ([RY] Ch. VI, Cor. (1.6), p. 224) used by the specification
(p. 39: "The occupation-density formula first implies that `{X = 0}` has zero Lebesgue measure").

Proof: apply the expectation identity to `zeroFn δ`, whose second derivative is a unit-mass bump on
`[-δ/2, δ/2]` that is at least `1 / (4 m δ)` on `[-δ/4, δ/4]` and whose derivative is bounded by `1`
and vanishes at `0`. This gives `E ∫_s^ρ zeroFn'' δ (X) ≤ 6N / a²` uniformly in `δ`, while
`|{X = 0}| ≤ 4 m δ ∫_s^ρ zeroFn'' δ (X)` pathwise; Markov's inequality and `δ → 0` conclude.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology ENNReal

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ}
  {B X J b : ℝ≥0 → Ω → ℝ}

/-- The zero set of a path on `[s, ρ]`, in real time. -/
def zeroSet (x : ℝ≥0 → ℝ) (s ρ : ℝ≥0) : Set ℝ := {r | r ∈ Icc (s : ℝ) ρ ∧ x r.toNNReal = 0}

lemma zeroSet_subset (x : ℝ≥0 → ℝ) (s ρ : ℝ≥0) : zeroSet x s ρ ⊆ Icc (s : ℝ) ρ :=
  fun _ hr => hr.1

lemma isClosed_zeroSet {x : ℝ≥0 → ℝ} {s ρ : ℝ≥0} (hx : ContinuousOn x (Icc s ρ)) :
    IsClosed (zeroSet x s ρ) := by
  have := (continuousOn_comp_toNNReal hx).preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_singleton (x := (0 : ℝ)))
  convert this using 1
  ext r
  simp [zeroSet]

lemma volume_zeroSet_lt_top (x : ℝ≥0 → ℝ) (s ρ : ℝ≥0) : volume (zeroSet x s ρ) < ∞ :=
  (measure_mono (zeroSet_subset x s ρ)).trans_lt measure_Icc_lt_top

/-- Pathwise: `|{X = 0} ∩ [s, ρ]| ≤ 4 m δ ∫_s^ρ zeroFn'' δ (X)`. -/
lemma volume_real_zeroSet_le {x : ℝ≥0 → ℝ} {s ρ : ℝ≥0} (hsρ : s ≤ ρ)
    (hx : ContinuousOn x (Icc s ρ)) {δ : ℝ} (hδ : 0 < δ) :
    volume.real (zeroSet x s ρ) ≤
      4 * tentMass * δ * ∫ r in (s : ℝ)..ρ, zeroFn'' δ (x r.toNNReal) := by
  have hsρ' : (s : ℝ) ≤ ρ := by exact_mod_cast hsρ
  have hZ : MeasurableSet (zeroSet x s ρ) := (isClosed_zeroSet hx).measurableSet
  have hg : ContinuousOn (fun r : ℝ => zeroFn'' δ (x r.toNNReal)) (Icc (s : ℝ) ρ) :=
    (continuous_zeroFn'' δ).comp_continuousOn (continuousOn_comp_toNNReal hx)
  have hm := tentMass_pos
  have h1 : volume.real (zeroSet x s ρ) =
      ∫ r in Icc (s : ℝ) ρ, (zeroSet x s ρ).indicator 1 r := by
    rw [integral_indicator_one hZ, measureReal_restrict_apply hZ,
      inter_eq_left.2 (zeroSet_subset x s ρ)]
  rw [h1, intervalIntegral.integral_of_le hsρ', ← integral_Icc_eq_integral_Ioc,
    ← integral_const_mul]
  refine setIntegral_mono_on ?_ ((hg.integrableOn_Icc).const_mul _) measurableSet_Icc
    fun r hr => ?_
  · exact (integrableOn_const (measure_Icc_lt_top.ne)).indicator hZ |>.mono_set subset_rfl
  · by_cases hrZ : r ∈ zeroSet x s ρ
    · rw [indicator_of_mem hrZ, Pi.one_apply]
      have hle := le_zeroFn'' hδ (x := x r.toNNReal) (by rw [hrZ.2, abs_zero]; positivity)
      calc (1 : ℝ) = 4 * tentMass * δ * (1 / 4 / tentMass / δ) := by field_simp
        _ ≤ _ := by gcongr
    · rw [indicator_of_notMem hrZ]
      exact mul_nonneg (by positivity) (zeroFn''_nonneg hδ _)

lemma abs_termT_le' {g : ℝ → ℝ} {K : ℝ} {ω : Ω} (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |g x| ≤ K) (hK0 : 0 ≤ K) (n : ℕ) :
    |termT 𝒢 s t X g n ω| ≤ K * ((t : ℝ) - s) := by
  refine (abs_termT_le hst hP hK hK0 n).trans (mul_le_mul_of_nonneg_left ?_ hK0)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hst
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn)]

/-- `ω ↦ ∫_s^ρ g(X)` is integrable for continuous `g`. -/
lemma integrable_limitT (hst : s ≤ t) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (h𝒢a : Antitone 𝒢) {g : ℝ → ℝ} (hg : Continuous g)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω)) :
    Integrable (fun ω => ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), g (X r.toNNReal ω)) μ := by
  have hXm : ∀ u, Measurable (X u) := fun u => (hX u).mono (𝓕.le u) le_rfl
  have h𝒢m : ∀ u, MeasurableSet (𝒢 u) := fun u => 𝓕.le u _ (h𝒢 u)
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hg N
  exact integrable_of_ae_tendsto (measurable_termT h𝒢m hXm hg)
    (fun n => by filter_upwards [hpath] with ω hP using abs_termT_le' hst hP hK hK0 n)
    (ae_tendsto_termT h𝒢a hst hpath hg)

/-- The uniform bound `(a² / 2) E ∫_s^ρ zeroFn'' δ (X) ≤ 3 N`. -/
lemma integral_zeroFn''_le (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (h𝒢a : Antitone 𝒢)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {δ : ℝ} (hδ : 0 < δ) :
    a ^ 2 / 2 * ∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), zeroFn'' δ (X r.toNNReal ω)) ∂μ ≤
      3 * N := by
  have hid := integral_sub_eq_of_isTanakaPath hB hst hX h𝒢 h𝒢a (hasDerivAt_zeroFn δ)
    (hasDerivAt_zeroFn' δ) (continuous_zeroFn'' δ) hpath
  have hS : |∫ ω, (zeroFn δ (X (lifetime 𝒢 s t ω) ω) - zeroFn δ (X s ω)) ∂μ| ≤ 2 * N := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const (2 * N)) ?_).trans (by simp)
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs]
    refine (abs_zeroFn_sub_le hδ _ _).trans ((abs_sub _ _).trans ?_)
    have h1 : |X (lifetime 𝒢 s t ω) ω| ≤ N := hP.abs_le ⟨le_lifetimeOf _ _ _, le_rfl⟩
    have h2 : |X s ω| ≤ N := hP.abs_le ⟨le_rfl, le_lifetimeOf (fun u => ω ∈ 𝒢 u) s t⟩
    linarith
  have hA : |∫ ω, ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
      zeroFn' δ (X r.toNNReal ω) * b r.toNNReal ω) +
      c * zeroFn' δ 0 * (J (lifetime 𝒢 s t ω) ω - J s ω)) ∂μ| ≤ N := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_const N) ?_).trans (by simp)
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs, zeroFn'_zero, mul_zero, zero_mul, add_zero]
    have hsρ : (s : ℝ) ≤ lifetime 𝒢 s t ω := by exact_mod_cast le_lifetimeOf _ _ _
    have hb := hP.2.2.2.1
    refine (intervalIntegral.abs_integral_le_integral_abs hsρ).trans
      ((intervalIntegral.integral_mono_on hsρ ?_ hb.abs fun r _ => ?_).trans hP.2.2.2.2.2.2.2.2.1)
    · exact (hb.continuousOn_mul ((continuous_zeroFn' δ).comp_continuousOn
        (continuousOn_comp_toNNReal hP.1) |>.mono (by rw [uIcc_of_le hsρ]))).abs
    · rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_zeroFn'_le hδ _)
  have := le_abs_self (∫ ω, (zeroFn δ (X (lifetime 𝒢 s t ω) ω) - zeroFn δ (X s ω)) ∂μ)
  have := neg_abs_le (∫ ω, ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω),
      zeroFn' δ (X r.toNNReal ω) * b r.toNNReal ω) +
      c * zeroFn' δ 0 * (J (lifetime 𝒢 s t ω) ω - J s ω)) ∂μ)
  linarith

/-- **The zero set is Lebesgue-null** (localized): almost surely `|{r ∈ [s, ρ] : X_r = 0}| = 0`. -/
theorem ae_volume_zeroSet_eq_zero (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (h𝒢a : Antitone 𝒢) (ha : a ≠ 0)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω)) :
    ∀ᵐ ω ∂μ, volume (zeroSet (X · ω) s (lifetime 𝒢 s t ω)) = 0 := by
  set Z : Ω → ℝ := fun ω => volume.real (zeroSet (X · ω) s (lifetime 𝒢 s t ω))
  have hN : 0 ≤ N := by
    rcases hpath.exists with ⟨ω, hP⟩; exact hP.N_nonneg (le_lifetimeOf _ _ _)
  have hm := tentMass_pos
  have ha2 : 0 < a ^ 2 := by positivity
  have key : ∀ η > 0, μ {ω | η < Z ω} = 0 := by
    intro η hη
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    rw [zero_add]
    set δ := (ε : ℝ) * η * a ^ 2 / (24 * tentMass * (N + 1))
    have hδ : 0 < δ := by have : (0 : ℝ) < ε := hε; positivity
    set Λ : Ω → ℝ := fun ω => ∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), zeroFn'' δ (X r.toNNReal ω)
    have hΛi : Integrable Λ μ :=
      integrable_limitT hst hX h𝒢 h𝒢a (continuous_zeroFn'' δ) hpath
    have hΛ0 : 0 ≤ᵐ[μ] fun ω => 4 * tentMass * δ * Λ ω := by
      filter_upwards [hpath] with ω _
      have hsρ : (s : ℝ) ≤ lifetime 𝒢 s t ω := by exact_mod_cast le_lifetimeOf _ _ _
      exact mul_nonneg (by positivity)
        (intervalIntegral.integral_nonneg hsρ fun r _ => zeroFn''_nonneg hδ _)
    have hE : ∫ ω, Λ ω ∂μ ≤ 6 * N / a ^ 2 := by
      have := integral_zeroFn''_le hB hst hX h𝒢 h𝒢a hpath hδ
      rw [le_div_iff₀ ha2]; linarith
    have hsub : {ω | η < Z ω} ≤ᵐ[μ] {ω | η ≤ 4 * tentMass * δ * Λ ω} := by
      filter_upwards [hpath] with ω hP hω
      exact le_trans (le_of_lt hω)
        (volume_real_zeroSet_le (le_lifetimeOf _ _ _) hP.1 hδ)
    have hMarkov := mul_meas_ge_le_integral_of_nonneg hΛ0 (hΛi.const_mul _) η
    rw [integral_const_mul] at hMarkov
    have hreal : μ.real {ω | η ≤ 4 * tentMass * δ * Λ ω} ≤ ε := by
      have h1 : η * μ.real {ω | η ≤ 4 * tentMass * δ * Λ ω} ≤
          4 * tentMass * δ * (6 * N / a ^ 2) :=
        hMarkov.trans (mul_le_mul_of_nonneg_left hE (by positivity))
      have h2 : 4 * tentMass * δ * (6 * N / a ^ 2) ≤ η * ε := by
        simp only [δ]
        rw [show 4 * tentMass * ((ε : ℝ) * η * a ^ 2 / (24 * tentMass * (N + 1))) *
            (6 * N / a ^ 2) = η * ε * (N / (N + 1)) by field_simp; ring]
        exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
      exact le_of_mul_le_mul_left (h1.trans h2) hη
    calc μ {ω | η < Z ω} ≤ μ {ω | η ≤ 4 * tentMass * δ * Λ ω} := measure_mono_ae hsub
      _ = ENNReal.ofReal (μ.real {ω | η ≤ 4 * tentMass * δ * Λ ω}) :=
          (ofReal_measureReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal
      _ = ε := ENNReal.ofReal_coe_nnreal
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ω ∉ {ω | 1 / ((k : ℝ) + 1) < Z ω} :=
    ae_all_iff.2 fun k => measure_eq_zero_iff_ae_notMem.1 (key _ (by positivity))
  filter_upwards [hall] with ω hω
  have hZ0 : Z ω = 0 := by
    refine le_antisymm ?_ measureReal_nonneg
    by_contra hpos
    push Not at hpos
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact hω k hk
  rcases (ENNReal.toReal_eq_zero_iff _).1 hZ0 with h | h
  · exact h
  · exact absurd h (volume_zeroSet_lt_top _ _ _).ne

end InteractingSLE.LocalTime
