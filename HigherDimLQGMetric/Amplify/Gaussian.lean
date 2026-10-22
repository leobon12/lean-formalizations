import HigherDimLQGMetric.Sharp.W2Gaussian

/-! Uniform Gaussian control of the sphere-average ratio at finitely many trial centers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Filter Topology
open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- The variance at a trial center has a scale-independent upper bound. -/
theorem amplify_variance_sphereAvg_trial_le (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 < r)
    (w : Rd d) (hw : ‖w‖ ≤ 3) :
    Var[fun ω => sphereAvg (h ω) (ρ * r) (r • w) - sphereAvg (h ω) r 0; P] ≤
      Real.log (1 / ρ) + 2 * sphEnergy d + 2 * Real.log 5 := by
  have hs : 0 < ρ * r := mul_pos hρ hr
  have hvar := hh.variance_sphereAvg_sub_le_log hd hs hr (r • w) 0
  have hdiv : r / (ρ * r) = 1 / ρ := by field_simp
  have hrho : ρ * r / r = ρ := by field_simp
  have hnorm : ‖r • w - (0 : Rd d)‖ / r = ‖w‖ := by
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    field_simp
  rw [hdiv, hrho, hnorm] at hvar
  have hlog : Real.log (‖w‖ + ρ + 1) ≤ Real.log 5 :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- A finite union bound, uniform in the macroscopic radius and in the LGF law. -/
theorem amplify_gaussian_trial_union_bound [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 < r)
    {n : ℕ} (w : Fin n → Rd d) (hw : ∀ i, ‖w i‖ ≤ 3) (K : ℝ) :
    P {ω | ∃ i : Fin n,
      K < |sphereAvg (h ω) (ρ * r) (r • w i) - sphereAvg (h ω) r 0|} ≤
      ENNReal.ofReal ((n : ℝ) *
        (2 * Real.exp (-K + (Real.log (1 / ρ) + 2 * sphEnergy d +
          2 * Real.log 5) / 2))) := by
  let X : Fin n → Ω → ℝ := fun i ω =>
    sphereAvg (h ω) (ρ * r) (r • w i) - sphereAvg (h ω) r 0
  have hG (i : Fin n) : HasGaussianLaw (X i) P ∧ ∫ ω, X i ω ∂P = 0 :=
    hh.hasGaussianLaw_sphereAvg_sub hd (mul_pos hρ hr) hr (r • w i) 0
  have hV (i : Fin n) : Var[X i; P] ≤
      Real.log (1 / ρ) + 2 * sphEnergy d + 2 * Real.log 5 :=
    amplify_variance_sphereAvg_trial_le hd hh hρ hρ1 hr (w i) (hw i)
  simpa only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ, true_and,
    one_mul, one_pow, neg_mul, X] using
    (w2_gaussian_finset_union Finset.univ X
      (fun i _ => (hG i).1) (fun i _ => (hG i).2)
      (fun i _ => hV i) (show 0 ≤ (1 : ℝ) by norm_num) :
      P {ω | ∃ i ∈ Finset.univ, K < |X i ω|} ≤ _)

/-- A single deterministic cutoff controls all trial normalizer ratios, for
every whole-space LGF and every outer radius. -/
theorem amplify_exists_gaussian_trial_bound (hd : 2 ≤ d)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {n : ℕ} (w : Fin n → Rd d) (hw : ∀ i, ‖w i‖ ≤ 3)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ {Ω' : Type*} [MeasurableSpace Ω']
      {P' : Measure Ω'} [IsProbabilityMeasure P'] {h' : Ω' → DistRd d},
      IsWholeSpaceLGF h' P' → ∀ {r : ℝ}, 0 < r →
      P' {ω | ∃ i : Fin n,
        K < |sphereAvg (h' ω) (ρ * r) (r • w i) - sphereAvg (h' ω) r 0|} ≤
        ENNReal.ofReal η := by
  let V := Real.log (1 / ρ) + 2 * sphEnergy d + 2 * Real.log 5
  have ht : Tendsto (fun K : ℝ => (n : ℝ) * (2 * Real.exp (-K + V / 2)))
      Filter.atTop (nhds 0) := by
    have h1 : Tendsto (fun K : ℝ => -K + V / 2) Filter.atTop Filter.atBot :=
      tendsto_atBot_add_const_right _ _ tendsto_neg_atTop_atBot
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul ((n : ℝ) * 2)
    simpa only [Function.comp_def, mul_zero, mul_assoc] using h2
  obtain ⟨K, hK⟩ := (ht.eventually (eventually_lt_nhds hη)).exists
  refine ⟨K, fun {Ω'} _ {P'} _ {h'} hh' {r} hr => ?_⟩
  have hbound := amplify_gaussian_trial_union_bound hd hh' hρ hρ1 hr w hw K
  exact hbound.trans (ENNReal.ofReal_le_ofReal (by simpa only [V] using hK.le))

/-- The uniform Gaussian cutoff may always be chosen nonnegative. -/
theorem amplify_exists_nonneg_gaussian_trial_bound (hd : 2 ≤ d)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {n : ℕ} (w : Fin n → Rd d) (hw : ∀ i, ‖w i‖ ≤ 3)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω' : Type*} [MeasurableSpace Ω']
      {P' : Measure Ω'} [IsProbabilityMeasure P'] {h' : Ω' → DistRd d},
      IsWholeSpaceLGF h' P' → ∀ {r : ℝ}, 0 < r →
      P' {ω | ∃ i : Fin n,
        K < |sphereAvg (h' ω) (ρ * r) (r • w i) - sphereAvg (h' ω) r 0|} ≤
        ENNReal.ofReal η := by
  obtain ⟨K, hK⟩ := amplify_exists_gaussian_trial_bound hd hρ hρ1 w hw hη
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro Ω' _ P' _ h' hh' r hr
  exact (measure_mono (fun ω hω => by
    obtain ⟨i, hi⟩ := hω
    exact ⟨i, (lt_of_le_of_lt (le_max_left _ _) hi)⟩)).trans (hK hh' hr)

end HigherDimLQGMetric
