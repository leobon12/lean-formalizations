/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.Taylor
import InteractingSLE.Stochastic.LocalTime.Path
import InteractingSLE.Stochastic.LocalTime.Increments

/-!
# The terms of the discrete Itô expansion along a stopped uniform grid

Packet PROVE-TANAKA. Let `𝒢 : ℝ≥0 → Set Ω` be an antitone family of events with `𝒢 u ∈ 𝓕 u`
("still alive at time `u`"), and `alive n k = 1_{𝒢 t_k}` on the uniform partition `t_k` of
`[s, t]`. The telescoping sum `termS = ∑ alive_{k+1} (f(X_{k+1}) - f(X_k))` splits exactly
(`termS_eq`) into

* martingale terms `termM = ∑ alive_k f'(X_k) ΔB_k` and `termQ = ∑ alive_k f''(X_k) ΔB_k²`, whose
  expectations are computed from the independence of the increments of the filtered Brownian
  motion (`integral_termM`, `integral_termQ`);
* the drift-plus-singular term `termA = ∑ alive_{k+1} f'(X_k) (ΔX_k - a ΔB_k)`;
* exit terms `termE1`, `termE2` (weights `alive_k - alive_{k+1}`), cross terms `termC1`, `termC2`,
  and the Taylor remainder `termR`, whose expectations tend to `0`.

This file defines the terms, proves their measurability, the identity, and the expectation
identities for `termM` and `termQ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Grid data -/

/-- The lifetime of an antitone family of events: the supremum of the alive times in `[s, t]`
(or `s`). -/
def lifetime (𝒢 : ℝ≥0 → Set Ω) (s t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  lifetimeOf (fun u => ω ∈ 𝒢 u) s t

/-- The alive indicator at the `k`-th node of the `n`-th uniform partition of `[s, t]`. -/
def alive (𝒢 : ℝ≥0 → Set Ω) (s t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  (𝒢 (unifPartIcc s t n k)).indicator (fun _ => (1 : ℝ)) ω

/-- The number of alive cells (cells whose right node is alive). -/
def aliveCells (𝒢 : ℝ≥0 → Set Ω) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℕ :=
  firstFail (fun k => ω ∈ 𝒢 (unifPartIcc s t n (k + 1))) n

/-- The increment of a process over the `k`-th cell. -/
def gridIncr (Y : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  Y (unifPartIcc s t n (k + 1)) ω - Y (unifPartIcc s t n k) ω

section Alive

open Classical

variable {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0}

lemma alive_nonneg (n k : ℕ) (ω : Ω) : 0 ≤ alive 𝒢 s t n k ω := by
  unfold alive; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma alive_le_one (n k : ℕ) (ω : Ω) : alive 𝒢 s t n k ω ≤ 1 := by
  unfold alive; exact Set.indicator_le_self' (fun _ _ => zero_le_one) _

lemma alive_eq_ite (n k : ℕ) (ω : Ω) :
    alive 𝒢 s t n k ω = if ω ∈ 𝒢 (unifPartIcc s t n k) then 1 else 0 := by
  unfold alive; rw [Set.indicator_apply]

lemma alive_succ_le (h𝒢a : Antitone 𝒢) (n k : ℕ) (ω : Ω) :
    alive 𝒢 s t n (k + 1) ω ≤ alive 𝒢 s t n k ω := by
  rw [alive_eq_ite, alive_eq_ite]
  by_cases h : ω ∈ 𝒢 (unifPartIcc s t n (k + 1))
  · simp [h, h𝒢a (unifPartIcc_mono s t n (Nat.le_succ k)) h]
  · simp only [h, ite_false]; split_ifs <;> norm_num

lemma exitWeight_nonneg (h𝒢a : Antitone 𝒢) (n k : ℕ) (ω : Ω) :
    0 ≤ alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω :=
  sub_nonneg.2 (alive_succ_le h𝒢a n k ω)

lemma sum_exitWeight_le_one (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n, (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) ≤ 1 := by
  rw [Finset.sum_range_sub']
  linarith [alive_le_one (𝒢 := 𝒢) (s := s) (t := t) n 0 ω,
    alive_nonneg (𝒢 := 𝒢) (s := s) (t := t) n n ω]

/-- Sums weighted by the alive indicator of the right node are sums over the alive cells. -/
lemma sum_alive_succ_mul (h𝒢a : Antitone 𝒢) (n : ℕ) (ω : Ω) (y : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω * y k =
      ∑ k ∈ Finset.range (aliveCells 𝒢 s t n ω), y k := by
  rw [aliveCells, ← sum_ite_eq_sum_firstFail
    (fun k l hkl h => h𝒢a (unifPartIcc_mono s t n (Nat.succ_le_succ hkl)) h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [alive_eq_ite]
  split_ifs <;> simp

lemma gridApprox_aliveCells (h𝒢a : Antitone 𝒢) (hst : s ≤ t) (ω : Ω) :
    GridApprox s t (lifetime 𝒢 s t ω) fun n => aliveCells 𝒢 s t n ω :=
  gridApprox_firstFail (A := fun u => ω ∈ 𝒢 u) (fun _ _ huv h => h𝒢a huv h) hst

/-- An alive node lies in `[s, lifetime]`. -/
lemma mem_Icc_of_alive (hst : s ≤ t) {n k : ℕ} (hk : k ≤ n) {ω : Ω}
    (h : alive 𝒢 s t n k ω ≠ 0) : unifPartIcc s t n k ∈ Icc s (lifetime 𝒢 s t ω) := by
  rw [alive_eq_ite] at h
  have hω : ω ∈ 𝒢 (unifPartIcc s t n k) := by by_contra h'; simp [h'] at h
  exact ⟨le_unifPartIcc s t n k, le_lifetimeOf_of (unifPartIcc_le hst hk) hω⟩

lemma lt_aliveCells_of_alive (h𝒢a : Antitone 𝒢) {n k : ℕ} (hk : k < n) {ω : Ω}
    (h : alive 𝒢 s t n (k + 1) ω ≠ 0) : k < aliveCells 𝒢 s t n ω := by
  rw [alive_eq_ite] at h
  have hω : ω ∈ 𝒢 (unifPartIcc s t n (k + 1)) := by by_contra h'; simp [h'] at h
  by_contra hle
  push Not at hle
  have hlt : aliveCells 𝒢 s t n ω < n := lt_of_le_of_lt hle hk
  exact not_of_firstFail_lt hlt
    (h𝒢a (unifPartIcc_mono s t n (Nat.succ_le_succ hle)) hω)

lemma alive_eq_zero_or_one (n k : ℕ) (ω : Ω) :
    alive 𝒢 s t n k ω = 0 ∨ alive 𝒢 s t n k ω = 1 := by
  rw [alive_eq_ite]; split_ifs <;> simp

lemma measurable_alive {𝓕 : Filtration ℝ≥0 mΩ} (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u))
    (n k : ℕ) : Measurable[𝓕 (unifPartIcc s t n k)] (alive 𝒢 s t n k) :=
  measurable_const.indicator (h𝒢 _)

end Alive

/-! ### The terms -/

section Terms

variable (𝒢 : ℝ≥0 → Set Ω) (s t : ℝ≥0) (a : ℝ) (B X : ℝ≥0 → Ω → ℝ) (f f' f'' : ℝ → ℝ)

/-- The telescoping sum over the alive cells. -/
def termS (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
    (f (X (unifPartIcc s t n (k + 1)) ω) - f (X (unifPartIcc s t n k) ω))

/-- The discrete stochastic integral `∑ alive_k f'(X_k) ΔB_k`. -/
def termM (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n k ω * f' (X (unifPartIcc s t n k) ω) * gridIncr B s t n k ω

/-- The exit correction to `termM`. -/
def termE1 (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
    f' (X (unifPartIcc s t n k) ω) * gridIncr B s t n k ω

/-- The drift-plus-singular term `∑ alive_{k+1} f'(X_k) (ΔX_k - a ΔB_k)`. -/
def termA (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω * f' (X (unifPartIcc s t n k) ω) *
    (gridIncr X s t n k ω - a * gridIncr B s t n k ω)

/-- The discrete quadratic term `∑ alive_k f''(X_k) ΔB_k²`. -/
def termQ (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n k ω * f'' (X (unifPartIcc s t n k) ω) *
    gridIncr B s t n k ω ^ 2

/-- The Riemann sum `∑ alive_k f''(X_k) (t - s)/n`, the conditional mean of `termQ`. -/
def termT (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n k ω * f'' (X (unifPartIcc s t n k) ω) *
    (((t : ℝ) - s) / n)

/-- The exit correction to `termQ`. -/
def termE2 (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
    f'' (X (unifPartIcc s t n k) ω) * gridIncr B s t n k ω ^ 2

/-- The cross term `∑ alive_{k+1} f''(X_k) a ΔB_k (ΔX_k - a ΔB_k)`. -/
def termC1 (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω * f'' (X (unifPartIcc s t n k) ω) *
    (a * gridIncr B s t n k ω * (gridIncr X s t n k ω - a * gridIncr B s t n k ω))

/-- The finite-variation square term `∑ alive_{k+1} f''(X_k) (ΔX_k - a ΔB_k)² / 2`. -/
def termC2 (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω * f'' (X (unifPartIcc s t n k) ω) *
    ((gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2 / 2)

/-- The Taylor remainder. -/
def termR (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
    (f (X (unifPartIcc s t n (k + 1)) ω) - f (X (unifPartIcc s t n k) ω) -
      f' (X (unifPartIcc s t n k) ω) * gridIncr X s t n k ω -
      f'' (X (unifPartIcc s t n k) ω) * gridIncr X s t n k ω ^ 2 / 2)

/-- **The discrete Itô expansion** (an exact identity). -/
lemma termS_eq (n : ℕ) (ω : Ω) :
    termS 𝒢 s t X f n ω = a * termM 𝒢 s t B X f' n ω - a * termE1 𝒢 s t B X f' n ω +
      termA 𝒢 s t a B X f' n ω + a ^ 2 / 2 * termQ 𝒢 s t B X f'' n ω -
      a ^ 2 / 2 * termE2 𝒢 s t B X f'' n ω + termC1 𝒢 s t a B X f'' n ω +
      termC2 𝒢 s t a B X f'' n ω + termR 𝒢 s t X f f' f'' n ω := by
  simp only [termS, termM, termE1, termA, termQ, termE2, termC1, termC2, termR, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gridIncr]
  ring

end Terms

/-! ### Measurability -/

section Measurability

variable {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a : ℝ} {B X : ℝ≥0 → Ω → ℝ} {f f' f'' : ℝ → ℝ}

lemma measurable_alive_amb (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (n k : ℕ) :
    Measurable (alive 𝒢 s t n k) :=
  measurable_const.indicator (h𝒢m _)

lemma measurable_gridIncr {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ u, Measurable (Y u)) (n k : ℕ) :
    Measurable (gridIncr Y s t n k) :=
  (hY _).sub (hY _)

variable (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hBm : ∀ u, Measurable (B u))
  (hXm : ∀ u, Measurable (X u))
include h𝒢m hXm

lemma measurable_termS (hf : Continuous f) (n : ℕ) : Measurable (termS 𝒢 s t X f n) :=
  Finset.measurable_sum _ fun _ _ => (measurable_alive_amb h𝒢m n _).mul
    ((hf.measurable.comp (hXm _)).sub (hf.measurable.comp (hXm _)))

include hBm

lemma measurable_termM (hf' : Continuous f') (n : ℕ) : Measurable (termM 𝒢 s t B X f' n) :=
  Finset.measurable_sum _ fun k _ => ((measurable_alive_amb h𝒢m n _).mul
    (hf'.measurable.comp (hXm _))).mul (measurable_gridIncr hBm n k)

lemma measurable_termE1 (hf' : Continuous f') (n : ℕ) : Measurable (termE1 𝒢 s t B X f' n) :=
  Finset.measurable_sum _ fun k _ => (((measurable_alive_amb h𝒢m n _).sub
    (measurable_alive_amb h𝒢m n _)).mul (hf'.measurable.comp (hXm _))).mul
      (measurable_gridIncr hBm n k)

lemma measurable_termA (hf' : Continuous f') (n : ℕ) : Measurable (termA 𝒢 s t a B X f' n) :=
  Finset.measurable_sum _ fun k _ => ((measurable_alive_amb h𝒢m n _).mul
    (hf'.measurable.comp (hXm _))).mul
      ((measurable_gridIncr hXm n k).sub ((measurable_gridIncr hBm n k).const_mul a))

lemma measurable_termQ (hf'' : Continuous f'') (n : ℕ) : Measurable (termQ 𝒢 s t B X f'' n) :=
  Finset.measurable_sum _ fun k _ => ((measurable_alive_amb h𝒢m n _).mul
    (hf''.measurable.comp (hXm _))).mul ((measurable_gridIncr hBm n k).pow_const 2)

omit hBm in
lemma measurable_termT (hf'' : Continuous f'') (n : ℕ) : Measurable (termT 𝒢 s t X f'' n) :=
  Finset.measurable_sum _ fun _ _ => ((measurable_alive_amb h𝒢m n _).mul
    (hf''.measurable.comp (hXm _))).mul measurable_const

lemma measurable_termE2 (hf'' : Continuous f'') (n : ℕ) :
    Measurable (termE2 𝒢 s t B X f'' n) :=
  Finset.measurable_sum _ fun k _ => (((measurable_alive_amb h𝒢m n _).sub
    (measurable_alive_amb h𝒢m n _)).mul (hf''.measurable.comp (hXm _))).mul
      ((measurable_gridIncr hBm n k).pow_const 2)

lemma measurable_termC1 (hf'' : Continuous f'') (n : ℕ) :
    Measurable (termC1 𝒢 s t a B X f'' n) :=
  Finset.measurable_sum _ fun k _ => ((measurable_alive_amb h𝒢m n _).mul
    (hf''.measurable.comp (hXm _))).mul (((measurable_gridIncr hBm n k).const_mul a).mul
      ((measurable_gridIncr hXm n k).sub ((measurable_gridIncr hBm n k).const_mul a)))

lemma measurable_termC2 (hf'' : Continuous f'') (n : ℕ) :
    Measurable (termC2 𝒢 s t a B X f'' n) :=
  Finset.measurable_sum _ fun k _ => ((measurable_alive_amb h𝒢m n _).mul
    (hf''.measurable.comp (hXm _))).mul
      ((((measurable_gridIncr hXm n k).sub
        ((measurable_gridIncr hBm n k).const_mul a)).pow_const 2).div_const 2)

omit hBm in
lemma measurable_termR (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (n : ℕ) : Measurable (termR 𝒢 s t X f f' f'' n) :=
  Finset.measurable_sum _ fun k _ => (measurable_alive_amb h𝒢m n _).mul
    ((((hf.measurable.comp (hXm _)).sub (hf.measurable.comp (hXm _))).sub
      ((hf'.measurable.comp (hXm _)).mul (measurable_gridIncr hXm n k))).sub
      (((hf''.measurable.comp (hXm _)).mul ((measurable_gridIncr hXm n k).pow_const 2)).div_const
        2))

end Measurability

/-! ### The martingale terms -/

section Martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
  {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {B X : ℝ≥0 → Ω → ℝ} {g : ℝ → ℝ} {K : ℝ}

lemma measurable_alive_mul_comp (hX : ∀ u, Measurable[𝓕 u] (X u))
    (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (hg : Continuous g) (n k : ℕ) :
    Measurable[𝓕 (unifPartIcc s t n k)]
      fun ω => alive 𝒢 s t n k ω * g (X (unifPartIcc s t n k) ω) :=
  (measurable_alive h𝒢 n k).mul (hg.measurable.comp (hX _))

omit [IsProbabilityMeasure μ] in
/-- `E[∑ alive_k g(X_k) ΔB_k] = 0` (independent Brownian increments). -/
lemma integral_termM (hB : IsFilteredPreBrownian B 𝓕 μ) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (hg : Continuous g) (n : ℕ)
    (hbd : ∀ k < n, ∀ᵐ ω ∂μ, |alive 𝒢 s t n k ω * g (X (unifPartIcc s t n k) ω)| ≤ K) :
    ∫ ω, termM 𝒢 s t B X g n ω ∂μ = 0 := by
  unfold termM
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun k _ => ?_
    exact ItoIsometryAdapted.integral_adapted_mul_increment hB
      (unifPartIcc_mono s t n (Nat.le_succ k)) (measurable_alive_mul_comp hX h𝒢 hg n k)
  · intro k hk
    refine (integrable_increment hB.toIsPreBrownianReal _ _).bdd_mul (c := K)
      ((measurable_alive_mul_comp hX h𝒢 hg n k).mono (𝓕.le _) le_rfl).aestronglyMeasurable ?_
    filter_upwards [hbd k (Finset.mem_range.1 hk)] with ω hω
    rwa [Real.norm_eq_abs]

/-- `E[∑ alive_k g(X_k) ΔB_k²] = E[∑ alive_k g(X_k) (t - s)/n]`. -/
lemma integral_termQ (hB : IsFilteredPreBrownian B 𝓕 μ) (hX : ∀ u, Measurable[𝓕 u] (X u))
    (h𝒢 : ∀ u, MeasurableSet[𝓕 u] (𝒢 u)) (hst : s ≤ t) (hg : Continuous g) (n : ℕ)
    (hbd : ∀ k < n, ∀ᵐ ω ∂μ, |alive 𝒢 s t n k ω * g (X (unifPartIcc s t n k) ω)| ≤ K) :
    ∫ ω, termQ 𝒢 s t B X g n ω ∂μ = ∫ ω, termT 𝒢 s t X g n ω ∂μ := by
  have hint : ∀ k < n,
      Integrable (fun ω => alive 𝒢 s t n k ω * g (X (unifPartIcc s t n k) ω)) μ :=
    fun k hk => (integrable_const K).mono'
      ((measurable_alive_mul_comp hX h𝒢 hg n k).mono (𝓕.le _) le_rfl).aestronglyMeasurable
      (by filter_upwards [hbd k hk] with ω hω; rwa [Real.norm_eq_abs])
  unfold termQ termT gridIncr
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ItoIsometryAdapted.integral_adapted_mul_increment_sq hB
      (unifPartIcc_mono s t n (Nat.le_succ k)) (measurable_alive_mul_comp hX h𝒢 hg n k),
      unifPartIcc_succ_sub hst, integral_mul_const]
  · exact fun k hk => (hint k (Finset.mem_range.1 hk)).mul_const _
  · intro k hk
    refine (integrable_increment_pow hB.toIsPreBrownianReal _ _ two_ne_zero).bdd_mul (c := K)
      ((measurable_alive_mul_comp hX h𝒢 hg n k).mono (𝓕.le _) le_rfl).aestronglyMeasurable ?_
    filter_upwards [hbd k (Finset.mem_range.1 hk)] with ω hω
    rwa [Real.norm_eq_abs]

end Martingale

end InteractingSLE.LocalTime
