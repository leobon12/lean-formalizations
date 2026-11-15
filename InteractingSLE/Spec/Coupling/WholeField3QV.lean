/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceMain2Brownian
import MathFin.Probability.Martingales.LevyQuadraticSums

/-!
# The bracket passes to a larger filtration (quadratic-variation step of Aux. lemma 47)

Packet PROVE-WHOLEFIELD3 (follow-up note C.2, `ig1_followup_proofs.txt` L1528–1531: "The quadratic variation is the
pathwise quantity `t ∧ S`. Lévy's characterization … proves that `B` is Brownian in the enlarged germ filtration";
additional note §7.4, Aux. 47: "The quadratic variation is `t`, and the usual Brownian characterization applies").

Let `Y` be a bounded continuous martingale of a filtration `𝓔` whose bracket `A` is a slow clock (`Y² − A` an
`𝓔`-martingale, `0 ≤ ΔA ≤ Δt`). If `Y` is also a martingale of a second filtration `𝒢` (not comparable with `𝓔`) and `A`
is `𝒢`-adapted, then `Y² − A` is a `𝒢`-martingale (`martingale_sq_sub_of_bracket`): over `A ∈ 𝒢_s`,
`∫ (Y_t² − Y_s²) = ∫ ∑ (ΔY_k)²` by orthogonality of `𝒢`-increments (`Sec7.setIntegral_sq_sub_sq_eq_of_martingale`), and
`∑ (ΔY_k)² → A_t − A_s` in `L²` is a statement about `𝓔` (`MathFin.LevyQuadraticSums.tendsto_integral_sq_sum_sub`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The quadratic-variation step in a second filtration.** -/
theorem setIntegral_sq_sub_sq_eq_of_bracket [IsProbabilityMeasure P] {𝓔 𝒢 : Filtration ℝ≥0 mΩ}
    {Y A : ℝ≥0 → Ω → ℝ} (hA : MathFin.LevyQuadraticSums.IsSlowClock A) (hY𝓔 : Martingale Y 𝓔 P)
    {K : ℝ} (hK : ∀ t ω, |Y t ω| ≤ K) (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYA : Martingale (fun t ω => Y t ω ^ 2 - A t ω) 𝓔 P) (hYG : Martingale Y 𝒢 P)
    (hAm : ∀ t, Measurable (A t)) {s t : ℝ≥0} (hst : s ≤ t) {E : Set Ω} (hE : MeasurableSet[𝒢 s] E) :
    ∫ ω in E, (Y t ω ^ 2 - Y s ω ^ 2) ∂P = ∫ ω in E, (A t ω - A s ω) ∂P := by
  have hmeas : ∀ r, Measurable (Y r) := fun r => ((hYG.stronglyAdapted r).mono (𝒢.le r)).measurable
  have hL2 : ∀ r, MemLp (Y r) 2 P := fun r =>
    MemLp.of_bound (hmeas r).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hK r ω)
  have hsq : ∀ a b : ℝ≥0, Integrable (fun ω => (Y a ω - Y b ω) ^ 2) P := fun a b =>
    ((hL2 a).sub (hL2 b)).integrable_sq
  have hsq' : ∀ a b : ℝ≥0, Integrable (fun ω => Y a ω ^ 2 - Y b ω ^ 2) P := fun a b =>
    (hL2 a).integrable_sq.sub (hL2 b).integrable_sq
  have hSint : ∀ n, Integrable (fun ω => ∑ k ∈ Finset.range n,
      (Y (MathFin.unifPartIcc s t n (k + 1)) ω - Y (MathFin.unifPartIcc s t n k) ω) ^ 2) P :=
    fun n => integrable_finsetSum _ fun k _ => hsq _ _
  -- the set integral equals that of the sum of squared increments
  have hrepr : ∀ n, n ≠ 0 → ∫ ω in E, (Y t ω ^ 2 - Y s ω ^ 2) ∂P = ∫ ω in E, ∑ k ∈ Finset.range n,
      (Y (MathFin.unifPartIcc s t n (k + 1)) ω - Y (MathFin.unifPartIcc s t n k) ω) ^ 2 ∂P := by
    intro n hn
    have htel : ∀ ω, Y t ω ^ 2 - Y s ω ^ 2 = ∑ k ∈ Finset.range n,
        (Y (MathFin.unifPartIcc s t n (k + 1)) ω ^ 2 - Y (MathFin.unifPartIcc s t n k) ω ^ 2) :=
      fun ω => by
        rw [Finset.sum_range_sub (fun k => Y (MathFin.unifPartIcc s t n k) ω ^ 2),
          MathFin.unifPartIcc_zero, MathFin.unifPartIcc_self hst hn]
    simp_rw [htel]
    rw [integral_finsetSum (Finset.range n) fun k _ => (hsq' _ _).integrableOn,
      integral_finsetSum (Finset.range n) fun k _ => (hsq _ _).integrableOn]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsk : s ≤ MathFin.unifPartIcc s t n k := le_self_add
    exact Sec7.setIntegral_sq_sub_sq_eq_of_martingale hYG hL2
      (MathFin.unifPartIcc_mono s t n (Nat.le_succ k)) (𝒢.mono hsk E hE)
  -- the sums converge to `A_t − A_s` in `L²` (a statement in `𝓔`)
  have hqv := MathFin.LevyQuadraticSums.tendsto_integral_sq_sum_sub hA hY𝓔 hK hYc hst hYA
  have hAint : Integrable (fun ω => A t ω - A s ω) P := by
    refine Integrable.of_bound ((hAm t).sub (hAm s)).aestronglyMeasurable ((t : ℝ) - s)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hA.sub_nonneg hst ω)]
    exact hA.sub_le hst ω
  have hmem : ∀ n, MemLp (fun ω => (∑ k ∈ Finset.range n,
      (Y (MathFin.unifPartIcc s t n (k + 1)) ω - Y (MathFin.unifPartIcc s t n k) ω) ^ 2)
        - (A t ω - A s ω)) 2 P := fun n => by
    have hm : Measurable fun ω => (∑ k ∈ Finset.range n,
        (Y (MathFin.unifPartIcc s t n (k + 1)) ω - Y (MathFin.unifPartIcc s t n k) ω) ^ 2)
          - (A t ω - A s ω) :=
      (Finset.measurable_fun_sum _ fun k _ => ((hmeas _).sub (hmeas _)).pow_const 2).sub
        ((hAm t).sub (hAm s))
    refine MemLp.of_bound hm.aestronglyMeasurable (n * (2 * K) ^ 2 + ((t : ℝ) - s))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |∑ k ∈ Finset.range n,
        (Y (MathFin.unifPartIcc s t n (k + 1)) ω - Y (MathFin.unifPartIcc s t n k) ω) ^ 2|
          ≤ n * (2 * K) ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Finset.range n,
            |(Y (MathFin.unifPartIcc s t n (k + 1)) ω - Y (MathFin.unifPartIcc s t n k) ω) ^ 2|
          ≤ ∑ _k ∈ Finset.range n, (2 * K) ^ 2 := Finset.sum_le_sum fun k _ => by
            rw [abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _)
              (MathFin.LevyQuadraticSums.abs_sub_le_two_mul hK _ _ ω) 2
        _ = n * (2 * K) ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : |A t ω - A s ω| ≤ (t : ℝ) - s := by
      rw [abs_of_nonneg (hA.sub_nonneg hst ω)]; exact hA.sub_le hst ω
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hlim := LocalSets.tendsto_setIntegral_of_tendsto_integral_sq hAint hSint hmem hqv E
  refine tendsto_nhds_unique (f := fun _ : ℕ => ∫ ω in E, (Y t ω ^ 2 - Y s ω ^ 2) ∂P)
    tendsto_const_nhds (hlim.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (hrepr n hn).symm

/-- **The bracket in a second filtration.** A bounded continuous martingale `Y` of `𝓔` with slow-clock bracket `A`
that is a martingale of `𝒢`, with `A` adapted to `𝒢`, has `Y² − A` a `𝒢`-martingale. -/
theorem martingale_sq_sub_of_bracket [IsProbabilityMeasure P] {𝓔 𝒢 : Filtration ℝ≥0 mΩ}
    {Y A : ℝ≥0 → Ω → ℝ} (hA : MathFin.LevyQuadraticSums.IsSlowClock A) (hY𝓔 : Martingale Y 𝓔 P)
    {K : ℝ} (hK : ∀ t ω, |Y t ω| ≤ K) (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYA : Martingale (fun t ω => Y t ω ^ 2 - A t ω) 𝓔 P) (hYG : Martingale Y 𝒢 P)
    (hAa : StronglyAdapted 𝒢 A) : Martingale (fun t ω => Y t ω ^ 2 - A t ω) 𝒢 P := by
  have hAm : ∀ t, Measurable (A t) := fun t => ((hAa t).mono (𝒢.le t)).measurable
  have hmeas : ∀ r, Measurable (Y r) := fun r => ((hYG.stronglyAdapted r).mono (𝒢.le r)).measurable
  have hadp : StronglyAdapted 𝒢 (fun t ω => Y t ω ^ 2 - A t ω) := fun r =>
    ((hYG.stronglyAdapted r).pow 2).sub (hAa r)
  have hint : ∀ r, Integrable (fun ω => Y r ω ^ 2 - A r ω) P := fun r => by
    refine Integrable.of_bound ((hmeas r).pow_const 2 |>.sub (hAm r)).aestronglyMeasurable
      (K ^ 2 + r) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |Y r ω ^ 2| ≤ K ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hK r ω) 2
    have h2 : |A r ω| ≤ r := by rw [abs_of_nonneg (hA.apply_nonneg r ω)]; exact hA.apply_le r ω
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hint t)
    (fun E _ _ => (hint s).integrableOn) (fun E hE _ => ?_) (hadp s).aestronglyMeasurable).symm
  have hE' : MeasurableSet E := 𝒢.le s E hE
  have key := setIntegral_sq_sub_sq_eq_of_bracket hA hY𝓔 hK hYc hYA hYG hAm hst hE
  have hYsq : ∀ r, Integrable (fun ω => Y r ω ^ 2) P := fun r =>
    (hint r).add ((hAa r).mono (𝒢.le r) |>.measurable.aestronglyMeasurable |> fun h =>
      Integrable.of_bound h r (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA.apply_nonneg r ω)]; exact hA.apply_le r ω))
      |>.congr (Eventually.of_forall fun ω => by simp)
  have hAi : ∀ r, Integrable (A r) P := fun r =>
    Integrable.of_bound (hAm r).aestronglyMeasurable r (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hA.apply_nonneg r ω)]; exact hA.apply_le r ω)
  rw [integral_sub (hYsq t).integrableOn (hYsq s).integrableOn,
    integral_sub (hAi t).integrableOn (hAi s).integrableOn] at key
  rw [integral_sub (hYsq t).integrableOn (hAi t).integrableOn,
    integral_sub (hYsq s).integrableOn (hAi s).integrableOn]
  linarith

end WholeField

end InteractingSLE
