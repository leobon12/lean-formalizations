/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.ItoLimits

/-!
# Itô's formula in expectation for a process with a singular push on its zero set

Packet PROVE-TANAKA. Let `B` be a Brownian motion for a filtration `𝓕` (MathFin's
`IsFilteredPreBrownian`: adapted, increments independent of the past), `X` an `𝓕`-adapted
process, `𝒢` an antitone family of events with `𝒢 u ∈ 𝓕 u` and lifetime `ρ = lifetime 𝒢 s t`.
If almost surely, on `[s, ρ]`,

  `X_u = X_s + a (B_u - B_s) + ∫_s^u b + c (J_u - J_s)`

with `J` continuous, nondecreasing and moving only on `{X = 0}`, and `|X| ≤ N`, `∫_s^ρ |b| ≤ N`,
`J_ρ - J_s ≤ N` (`IsTanakaPath`), then for every `C²` function `f`

  `E[f(X_ρ) - f(X_s)] = E[∫_s^ρ f'(X) b + c f'(0) (J_ρ - J_s)] + a²/2 · E[∫_s^ρ f''(X)]`

(`integral_sub_eq_of_isTanakaPath`). This is Itô's formula for `f(X)` ([RY] Ch. IV, Thm (3.3),
p. 147; [KS] Thm 3.3.6, p. 153) after taking expectations, with `∫ f'(X) dJ = f'(0) (J_ρ - J_s)`
because `dJ` is carried by `{X = 0}`. No stochastic integral is constructed: the proof expands
`f(X)` along the uniform partition of `[s, t]` stopped at the alive cells (`termS_eq`), uses the
independence of the Brownian increments for the martingale terms (`integral_termM`,
`integral_termQ`), and passes to the limit in every other term (`ItoLimits.lean`). The method is the
smoothing proof of [RY] Ch. VI, Thm (1.1), p. 221, carried out at the level of expectations.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ}
  {B X J b : ℝ≥0 → Ω → ℝ} {f f' f'' : ℝ → ℝ}

omit [IsProbabilityMeasure μ] in
lemma integrable_of_ae_abs_le {Y g : Ω → ℝ} (hY : Measurable Y) (hg : Integrable g μ)
    (h : ∀ᵐ ω ∂μ, |Y ω| ≤ g ω) : Integrable Y μ :=
  hg.mono' hY.aestronglyMeasurable (by simpa [Real.norm_eq_abs] using h)

/-- The expectation of the discrete expansion, for every `n ≠ 0`. -/
lemma integral_termS_eq (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (h𝒢a : Antitone 𝒢) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, termS 𝒢 s t X f n ω ∂μ =
      -(a * ∫ ω, termE1 𝒢 s t B X f' n ω ∂μ) + ∫ ω, termA 𝒢 s t a B X f' n ω ∂μ +
      a ^ 2 / 2 * ∫ ω, termT 𝒢 s t X f'' n ω ∂μ -
      a ^ 2 / 2 * ∫ ω, termE2 𝒢 s t B X f'' n ω ∂μ + ∫ ω, termC1 𝒢 s t a B X f'' n ω ∂μ +
      ∫ ω, termC2 𝒢 s t a B X f'' n ω ∂μ + ∫ ω, termR 𝒢 s t X f f' f'' n ω ∂μ := by
  have hXm : ∀ u, Measurable (X u) := fun u => (hX u).mono (𝓕.le u) le_rfl
  have hBm : ∀ u, Measurable (B u) := hB.measurable_eval
  have h𝒢m : ∀ u, MeasurableSet (𝒢 u) := fun u => 𝓕.le u _ (h𝒢 u)
  have hBp := hB.toIsPreBrownianReal
  have hfc' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  obtain ⟨K1, hK10, hK1⟩ := exists_bound_Icc hfc' N
  obtain ⟨K2, hK20, hK2⟩ := exists_bound_Icc hf'' N
  -- integrability of every term
  have iM : Integrable (termM 𝒢 s t B X f' n) μ :=
    integrable_of_ae_abs_le (measurable_termM h𝒢m hBm hXm hfc' n)
      ((integrable_sumIncrAbs hBp n).const_mul K1)
      (by filter_upwards [hpath] with ω hP using abs_termM_le hst hP hK1 hK10 n)
  have iE1 : Integrable (termE1 𝒢 s t B X f' n) μ :=
    integrable_of_ae_abs_le (measurable_termE1 h𝒢m hBm hXm hfc' n)
      (((integrable_const 1).add ((integrable_sumIncrPow4 hBp n).div_const (1 ^ 3))).const_mul K1)
      (by filter_upwards [hpath] with ω hP using abs_termE1_le h𝒢a hst hP hK1 hK10 one_pos n)
  have iA : Integrable (termA 𝒢 s t a B X f' n) μ :=
    integrable_of_ae_abs_le (measurable_termA h𝒢m hBm hXm hfc' n) (integrable_const _)
      (by filter_upwards [hpath] with ω hP using abs_termA_le h𝒢a hst hP hK1 hK10 n)
  have iQ : Integrable (termQ 𝒢 s t B X f'' n) μ :=
    integrable_of_ae_abs_le (measurable_termQ h𝒢m hBm hXm hf'' n)
      ((integrable_sumIncrSq hBp n).const_mul K2)
      (by filter_upwards [hpath] with ω hP using abs_termQ_le hst hP hK2 hK20 n)
  have iE2 : Integrable (termE2 𝒢 s t B X f'' n) μ :=
    integrable_of_ae_abs_le (measurable_termE2 h𝒢m hBm hXm hf'' n)
      (((integrable_const _).add ((integrable_sumIncrPow4 hBp n).div_const (1 ^ 2))).const_mul K2)
      (by filter_upwards [hpath] with ω hP using abs_termE2_le h𝒢a hst hP hK2 hK20 one_pos n)
  have iC1 : Integrable (termC1 𝒢 s t a B X f'' n) μ :=
    integrable_of_ae_abs_le (measurable_termC1 h𝒢m hBm hXm hf'' n)
      (((integrable_const 1).add ((integrable_sumIncrPow4 hBp n).div_const (1 ^ 3))).const_mul _)
      (by filter_upwards [hpath] with ω hP using abs_termC1_le h𝒢a hst hP hK2 hK20 one_pos hn)
  have iC2 : Integrable (termC2 𝒢 s t a B X f'' n) μ :=
    integrable_of_ae_abs_le (measurable_termC2 h𝒢m hBm hXm hf'' n) (integrable_const _)
      (by filter_upwards [hpath] with ω hP using abs_termC2_le h𝒢a hst hP hK2 hK20 n)
  have iR : Integrable (termR 𝒢 s t X f f' f'' n) μ := by
    refine integrable_of_ae_abs_le (g := fun ω => (2 * K2 + 2 * K2 * 1) *
      (2 * a ^ 2 * sumIncrSq B s t n ω + 2 * ((1 + |c|) * N) ^ 2))
      (measurable_termR h𝒢m hXm (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt)
        hfc' hf'' n)
      ((((integrable_sumIncrSq hBp n).const_mul _).add (integrable_const _)).const_mul _) ?_
    filter_upwards [hpath] with ω hP
    have hδ : ∀ x ∈ Icc (-N) N, ∀ y ∈ Icc (-N) N, |x - y| ≤ 1 → |f'' x - f'' y| ≤ 2 * K2 :=
      fun x hx y hy _ => (abs_sub _ _).trans (by linarith [hK2 x hx, hK2 y hy])
    refine (abs_termR_le hf hf' h𝒢a hst hP hK2 hK20 (by positivity) hδ hn).trans ?_
    have hb := badInd_le_one (𝒢 := 𝒢) (s := s) (t := t) (X := X) 1 n ω
    have hb0 := badInd_nonneg (𝒢 := 𝒢) (s := s) (t := t) (X := X) 1 n ω
    have hQ := sumIncrSq_nonneg B s t n ω
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    nlinarith
  -- the martingale identities
  have hbd1 : ∀ k < n, ∀ᵐ ω ∂μ, |alive 𝒢 s t n k ω * f' (X (unifPartIcc s t n k) ω)| ≤ K1 :=
    fun k hk => by filter_upwards [hpath] with ω hP using abs_alive_mul_le hst hP hK1 hK10 hk.le
  have hbd2 : ∀ k < n, ∀ᵐ ω ∂μ, |alive 𝒢 s t n k ω * f'' (X (unifPartIcc s t n k) ω)| ≤ K2 :=
    fun k hk => by filter_upwards [hpath] with ω hP using abs_alive_mul_le hst hP hK2 hK20 hk.le
  have hM := integral_termM (μ := μ) hB hX h𝒢 hfc' n hbd1
  have hQT := integral_termQ (μ := μ) hB hX h𝒢 hst hf'' n hbd2
  -- integrate the expansion
  have hexp := termS_eq 𝒢 s t a B X f f' f'' n
  rw [show (fun ω => termS 𝒢 s t X f n ω) = fun ω =>
      a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω + termA 𝒢 s t a B X f' n ω +
      a ^ 2 / 2 * termQ 𝒢 s t B X f'' n ω - a ^ 2 / 2 * termE2 𝒢 s t B X f'' n ω +
      termC1 𝒢 s t a B X f'' n ω + termC2 𝒢 s t a B X f'' n ω +
      termR 𝒢 s t X f f' f'' n ω from funext hexp]
  have j1 : Integrable (fun ω => a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω) μ :=
    (iM.const_mul a).sub (iE1.const_mul a)
  have j2 : Integrable (fun ω => a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω +
      termA 𝒢 s t a B X f' n ω) μ := j1.add iA
  have j3 : Integrable (fun ω => a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω +
      termA 𝒢 s t a B X f' n ω + a ^ 2 / 2 * termQ 𝒢 s t B X f'' n ω) μ :=
    j2.add (iQ.const_mul _)
  have j4 : Integrable (fun ω => a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω +
      termA 𝒢 s t a B X f' n ω + a ^ 2 / 2 * termQ 𝒢 s t B X f'' n ω -
      a ^ 2 / 2 * termE2 𝒢 s t B X f'' n ω) μ := j3.sub (iE2.const_mul _)
  have j5 : Integrable (fun ω => a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω +
      termA 𝒢 s t a B X f' n ω + a ^ 2 / 2 * termQ 𝒢 s t B X f'' n ω -
      a ^ 2 / 2 * termE2 𝒢 s t B X f'' n ω + termC1 𝒢 s t a B X f'' n ω) μ := j4.add iC1
  have j6 : Integrable (fun ω => a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω +
      termA 𝒢 s t a B X f' n ω + a ^ 2 / 2 * termQ 𝒢 s t B X f'' n ω -
      a ^ 2 / 2 * termE2 𝒢 s t B X f'' n ω + termC1 𝒢 s t a B X f'' n ω +
      termC2 𝒢 s t a B X f'' n ω) μ := j5.add iC2
  rw [integral_add j6 iR, integral_add j5 iC2, integral_add j4 iC1, integral_sub j3
    (iE2.const_mul _), integral_add j2 (iQ.const_mul _), integral_add j1 iA,
    integral_sub (iM.const_mul a) (iE1.const_mul a), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hM, hQT]
  ring

/-- **Itô's formula in expectation** for a process with a singular push on its zero set. -/
theorem integral_sub_eq_of_isTanakaPath (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (h𝒢a : Antitone 𝒢) (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'')
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω)) :
    ∫ ω, (f (X (lifetime 𝒢 s t ω) ω) - f (X s ω)) ∂μ =
      ∫ ω, ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f' (X r.toNNReal ω) * b r.toNNReal ω) +
        c * f' 0 * (J (lifetime 𝒢 s t ω) ω - J s ω)) ∂μ +
      a ^ 2 / 2 * ∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f'' (X r.toNNReal ω)) ∂μ := by
  have hXm : ∀ u, Measurable (X u) := fun u => (hX u).mono (𝓕.le u) le_rfl
  have hBm : ∀ u, Measurable (B u) := hB.measurable_eval
  have h𝒢m : ∀ u, MeasurableSet (𝒢 u) := fun u => 𝓕.le u _ (h𝒢 u)
  have hBp := hB.toIsPreBrownianReal
  have hfc' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hS := tendsto_integral_termS (μ := μ) h𝒢m hXm h𝒢a hst hpath hfc
  have hR := ((((((tendsto_integral_termE1 hBp h𝒢a hst hpath hfc').const_mul a).neg.add
    (tendsto_integral_termA h𝒢m hBm hXm h𝒢a hst hpath hfc')).add
    ((tendsto_integral_termT h𝒢m hXm h𝒢a hst hpath hf'').const_mul (a ^ 2 / 2))).sub
    ((tendsto_integral_termE2 hBp h𝒢a hst hpath hf'').const_mul (a ^ 2 / 2))).add
    (tendsto_integral_termC1 hBp h𝒢a hst hpath hf'')).add
    (tendsto_integral_termC2 h𝒢m hBm hXm h𝒢a hst hpath hf'') |>.add
    (tendsto_integral_termR hBp h𝒢m hXm h𝒢a hst hpath hf hf' hf'')
  have hEq : (fun n => ∫ ω, termS 𝒢 s t X f n ω ∂μ) =ᶠ[atTop] fun n =>
      -(a * ∫ ω, termE1 𝒢 s t B X f' n ω ∂μ) + ∫ ω, termA 𝒢 s t a B X f' n ω ∂μ +
      a ^ 2 / 2 * ∫ ω, termT 𝒢 s t X f'' n ω ∂μ -
      a ^ 2 / 2 * ∫ ω, termE2 𝒢 s t B X f'' n ω ∂μ + ∫ ω, termC1 𝒢 s t a B X f'' n ω ∂μ +
      ∫ ω, termC2 𝒢 s t a B X f'' n ω ∂μ + ∫ ω, termR 𝒢 s t X f f' f'' n ω ∂μ := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact integral_termS_eq hB hst hX h𝒢 h𝒢a hf hf' hf'' hpath hn
  have := tendsto_nhds_unique (hS.congr' hEq) hR
  rw [this]
  ring

/-! ### The limit integrands are integrable -/

lemma integrable_of_ae_tendsto {F : ℕ → Ω → ℝ} {L : Ω → ℝ} (hF : ∀ n, Measurable (F n))
    {C : ℝ} (hC : ∀ n, ∀ᵐ ω ∂μ, |F n ω| ≤ C)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (L ω))) : Integrable L μ := by
  refine (integrable_const C).mono'
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hF n).aestronglyMeasurable) hlim) ?_
  have hC' : ∀ᵐ ω ∂μ, ∀ n, |F n ω| ≤ C := ae_all_iff.2 hC
  filter_upwards [hlim, hC'] with ω h1 h2
  rw [Real.norm_eq_abs]
  exact le_of_tendsto h1.abs (Eventually.of_forall h2)

omit [IsProbabilityMeasure μ] in
lemma ae_tendsto_termS (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf : Continuous f) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => termS 𝒢 s t X f n ω) atTop
      (𝓝 (f (X (lifetime 𝒢 s t ω) ω) - f (X s ω))) := by
  filter_upwards [hpath] with ω hP
  refine (hP.tendsto_telescope (gridApprox_aliveCells h𝒢a hst ω) hf).congr fun n => ?_
  rw [termS_eq_sub h𝒢a n ω, sum_sub_grid (fun n => aliveCells 𝒢 s t n ω) (fun u => f (X u ω)) n]

omit [IsProbabilityMeasure μ] in
lemma ae_tendsto_termA (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf' : Continuous f') :
    ∀ᵐ ω ∂μ, Tendsto (fun n => termA 𝒢 s t a B X f' n ω) atTop
      (𝓝 ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f' (X r.toNNReal ω) * b r.toNNReal ω) +
        c * f' 0 * (J (lifetime 𝒢 s t ω) ω - J s ω))) := by
  filter_upwards [hpath] with ω hP
  refine (hP.tendsto_drift_singular (gridApprox_aliveCells h𝒢a hst ω) hst hf').congr
    fun n => ?_
  unfold termA
  simp only [mul_assoc]
  rw [sum_alive_succ_mul h𝒢a n ω]
  rfl

/-- `ω ↦ ∫_s^ρ f'(X) b + c f'(0) (J_ρ - J_s)` is integrable. -/
lemma integrable_limitA (hB : IsFilteredPreBrownian B 𝓕 μ) (hst : s ≤ t)
    (hX : ∀ u, Measurable[𝓕 u] (X u)) (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (h𝒢a : Antitone 𝒢) (hf' : Continuous f')
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω)) :
    Integrable (fun ω => (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f' (X r.toNNReal ω) *
      b r.toNNReal ω) + c * f' 0 * (J (lifetime 𝒢 s t ω) ω - J s ω)) μ := by
  have hXm : ∀ u, Measurable (X u) := fun u => (hX u).mono (𝓕.le u) le_rfl
  have h𝒢m : ∀ u, MeasurableSet (𝒢 u) := fun u => 𝓕.le u _ (h𝒢 u)
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf' N
  exact integrable_of_ae_tendsto (measurable_termA h𝒢m hB.measurable_eval hXm hf')
    (fun n => by filter_upwards [hpath] with ω hP using abs_termA_le h𝒢a hst hP hK hK0 n)
    (ae_tendsto_termA h𝒢a hst hpath hf')

/-- `ω ↦ f(X_ρ) - f(X_s)` is integrable. -/
lemma integrable_limitS (hst : s ≤ t) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (h𝒢a : Antitone 𝒢) (hf : Continuous f)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω)) :
    Integrable (fun ω => f (X (lifetime 𝒢 s t ω) ω) - f (X s ω)) μ := by
  have hXm : ∀ u, Measurable (X u) := fun u => (hX u).mono (𝓕.le u) le_rfl
  have h𝒢m : ∀ u, MeasurableSet (𝒢 u) := fun u => 𝓕.le u _ (h𝒢 u)
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf N
  refine integrable_of_ae_tendsto (C := 2 * K) (measurable_termS h𝒢m hXm hf) (fun n => ?_)
    (ae_tendsto_termS h𝒢a hst hpath hf)
  filter_upwards [hpath] with ω hP
  rw [termS_eq_sub h𝒢a n ω]
  have hm : unifPartIcc s t n (aliveCells 𝒢 s t n ω) ∈ Icc s (lifetime 𝒢 s t ω) := by
    rcases eq_or_ne n 0 with rfl | hn
    · have : aliveCells 𝒢 s t 0 ω = 0 := Nat.le_zero.1 (firstFail_le _ 0)
      rw [this, unifPartIcc_zero]; exact ⟨le_rfl, le_lifetimeOf _ _ _⟩
    · exact (gridApprox_aliveCells h𝒢a hst ω).mem_Icc hn le_rfl
  have h1 := hK _ (abs_le.1 (hP.abs_le hm))
  have h2 := hK _ (abs_le.1 (hP.abs_le ⟨le_rfl, le_lifetimeOf _ _ _⟩))
  calc _ ≤ _ := abs_sub _ _
    _ ≤ K + K := add_le_add h1 h2
    _ = 2 * K := by ring

end InteractingSLE.LocalTime
