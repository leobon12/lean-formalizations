/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.LocalTime.ItoTerms

/-!
# Limits of the expectations of the terms of the discrete Itô expansion

Packet PROVE-TANAKA. Under the pathwise hypotheses `IsTanakaPath` on `[s, lifetime 𝒢 s t ω]`
(almost surely), this file proves that, as the mesh of the uniform partition tends to zero,

* `E termS → E[f(X_ρ) - f(X_s)]`, `E termA → E[∫_s^ρ f'(X) b + c f'(0)(J_ρ - J_s)]`,
  `E termT → E[∫_s^ρ f''(X)]` (dominated convergence and the pathwise limits of `Path.lean`);
* `E termE1, E termE2, E termC1, E termC2, E termR → 0` (fourth moments of the Brownian
  increments, `Increments.lean`, and the uniform continuity of `f''` on `[-N, N]`);

and that every term is integrable.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Elementary helpers -/

lemma exists_bound_Icc {g : ℝ → ℝ} (hg : Continuous g) (N : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Icc (-N) N, |g x| ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-N) N)
    hg.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x hx => ?_⟩
  have := hK x hx
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- If `|u n| ≤ ε + D q n` for every `ε > 0` (with `D` depending on `ε`) and `q → 0`, then
`u → 0`. -/
lemma tendsto_zero_of_forall_le {u q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (h : ∀ ε > 0, ∃ D, ∀ n, |u n| ≤ ε + D * q n) : Tendsto u atTop (𝓝 0) := by
  refine tendsto_of_forall_eventually_abs_le fun ε hε => ?_
  obtain ⟨D, hD⟩ := h (ε / 2) (half_pos hε)
  have := (hq.const_mul D)
  rw [mul_zero] at this
  filter_upwards [(Metric.tendsto_nhds.1 this) (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero] at hn
  rw [sub_zero]
  linarith [hD n, le_abs_self (D * q n)]

/-- The sum of the fourth powers of the Brownian increments. -/
def sumIncrPow4 (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, gridIncr B s t n k ω ^ 4

/-- The sum of the squares of the Brownian increments. -/
def sumIncrSq (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, gridIncr B s t n k ω ^ 2

/-- The sum of the absolute Brownian increments. -/
def sumIncrAbs (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, |gridIncr B s t n k ω|

lemma sumIncrPow4_nonneg (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ sumIncrPow4 B s t n ω :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma sumIncrSq_nonneg (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ sumIncrSq B s t n ω :=
  Finset.sum_nonneg fun _ _ => by positivity

section Moments

variable {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0}

lemma integrable_sumIncrPow4 (hB : IsPreBrownianReal B μ) (n : ℕ) :
    Integrable (sumIncrPow4 B s t n) μ :=
  integrable_finsetSum _ fun _ _ => integrable_increment_pow hB _ _ (by norm_num)

lemma integrable_sumIncrSq (hB : IsPreBrownianReal B μ) (n : ℕ) :
    Integrable (sumIncrSq B s t n) μ :=
  integrable_finsetSum _ fun _ _ => integrable_increment_pow hB _ _ two_ne_zero

lemma integrable_sumIncrAbs (hB : IsPreBrownianReal B μ) (n : ℕ) :
    Integrable (sumIncrAbs B s t n) μ :=
  integrable_finsetSum _ fun _ _ => (integrable_increment hB _ _).abs

lemma tendsto_integral_sumIncrPow4 (hB : IsPreBrownianReal B μ) (hst : s ≤ t) :
    Tendsto (fun n => ∫ ω, sumIncrPow4 B s t n ω ∂μ) atTop (𝓝 0) :=
  tendsto_integral_sum_increment_pow4 hB hst

lemma integral_sumIncrPow4 (hB : IsPreBrownianReal B μ) (hst : s ≤ t) (n : ℕ) :
    ∫ ω, sumIncrPow4 B s t n ω ∂μ = n * (3 * (((t : ℝ) - s) / n) ^ 2) :=
  integral_sum_increment_pow4 hB hst n

lemma integral_sumIncrSq (hB : IsPreBrownianReal B μ) (hst : s ≤ t) (n : ℕ) :
    ∫ ω, sumIncrSq B s t n ω ∂μ = n * (((t : ℝ) - s) / n) :=
  integral_sum_increment_sq hB hst n

end Moments

/-! ### Pathwise bounds on the alive cells -/

section PathBounds

variable {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ} {B X J b : ℝ≥0 → Ω → ℝ} {ω : Ω}

/-- On an alive node, `X ∈ [-N, N]`. -/
lemma mem_Icc_N_of_alive (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {n k : ℕ} (hk : k ≤ n) (h : alive 𝒢 s t n k ω ≠ 0) :
    X (unifPartIcc s t n k) ω ∈ Icc (-N) N :=
  abs_le.1 (hP.abs_le (mem_Icc_of_alive hst hk h))

/-- The left node of an alive cell is alive-in-`[s, ρ]` too: `X ∈ [-N, N]` at both ends. -/
lemma mem_Icc_N_of_alive_succ (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {n k : ℕ} (hk : k < n) (h : alive 𝒢 s t n (k + 1) ω ≠ 0) :
    X (unifPartIcc s t n k) ω ∈ Icc (-N) N ∧ X (unifPartIcc s t n (k + 1)) ω ∈ Icc (-N) N := by
  have h1 := mem_Icc_of_alive hst hk h
  have h0 : unifPartIcc s t n k ∈ Icc s (lifetime 𝒢 s t ω) :=
    ⟨le_unifPartIcc s t n k, (unifPartIcc_mono s t n (Nat.le_succ k)).trans h1.2⟩
  exact ⟨abs_le.1 (hP.abs_le h0), abs_le.1 (hP.abs_le h1)⟩

/-- `|w · g(X_k)| ≤ K w` for a weight `0 ≤ w ≤ alive_k`. -/
lemma abs_weight_mul_le (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {g : ℝ → ℝ} {K : ℝ} (hgK : ∀ x ∈ Icc (-N) N, |g x| ≤ K) {n k : ℕ} (hk : k ≤ n)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ alive 𝒢 s t n k ω) :
    |w * g (X (unifPartIcc s t n k) ω)| ≤ K * w := by
  rcases alive_eq_zero_or_one (𝒢 := 𝒢) (s := s) (t := t) n k ω with h0 | h1
  · have : w = 0 := le_antisymm (h0 ▸ hw) hw0
    simp [this]
  · rw [abs_mul, abs_of_nonneg hw0, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (hgK _ (mem_Icc_N_of_alive hst hP hk (by rw [h1]; exact one_ne_zero))) hw0

lemma abs_alive_mul_le (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {g : ℝ → ℝ} {K : ℝ} (hgK : ∀ x ∈ Icc (-N) N, |g x| ≤ K) (hK0 : 0 ≤ K) {n k : ℕ}
    (hk : k ≤ n) : |alive 𝒢 s t n k ω * g (X (unifPartIcc s t n k) ω)| ≤ K :=
  (abs_weight_mul_le hst hP hgK hk (alive_nonneg n k ω) le_rfl).trans
    (mul_le_of_le_one_right hK0 (alive_le_one n k ω))

/-- The finite-variation increments over the alive cells: `∑ alive_{k+1} |ΔX - a ΔB| ≤ V`. -/
lemma sum_alive_abs_fv_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
      |gridIncr X s t n k ω - a * gridIncr B s t n k ω| ≤ (1 + |c|) * N := by
  rw [sum_alive_succ_mul h𝒢a n ω]
  exact hP.sum_abs_fv_le (gridApprox_aliveCells h𝒢a hst ω) hn

lemma sum_alive_sq_fv_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {n : ℕ} (hn : n ≠ 0) :
    ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
      (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2 ≤ ((1 + |c|) * N) ^ 2 := by
  have hV := sum_alive_abs_fv_le h𝒢a hst hP hn
  set D : ℕ → ℝ := fun k => alive 𝒢 s t n (k + 1) ω *
    |gridIncr X s t n k ω - a * gridIncr B s t n k ω|
  have hD0 : ∀ k, 0 ≤ D k := fun k => mul_nonneg (alive_nonneg _ _ _) (abs_nonneg _)
  have hterm : ∀ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
      (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2 ≤ D k ^ 2 := by
    intro k _
    simp only [D]
    rw [mul_pow, sq_abs]
    have h1 := alive_nonneg (𝒢 := 𝒢) (s := s) (t := t) n (k + 1) ω
    have h2 := alive_le_one (𝒢 := 𝒢) (s := s) (t := t) n (k + 1) ω
    have h3 : alive 𝒢 s t n (k + 1) ω ≤ alive 𝒢 s t n (k + 1) ω ^ 2 := by
      rcases alive_eq_zero_or_one (𝒢 := 𝒢) (s := s) (t := t) n (k + 1) ω with h | h <;>
        rw [h] <;> norm_num
    exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  calc _ ≤ ∑ k ∈ Finset.range n, D k ^ 2 := Finset.sum_le_sum hterm
    _ ≤ (∑ k ∈ Finset.range n, D k) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => hD0 k
    _ ≤ ((1 + |c|) * N) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hD0 k) hV 2

end PathBounds

/-! ### Pathwise bounds on the terms -/

section TermBounds

variable {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ} {B X J b : ℝ≥0 → Ω → ℝ} {ω : Ω}
  {f f' f'' : ℝ → ℝ} {K : ℝ}

lemma abs_termE1_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f' x| ≤ K) (hK0 : 0 ≤ K) {η : ℝ} (hη : 0 < η) (n : ℕ) :
    |termE1 𝒢 s t B X f' n ω| ≤ K * (η + sumIncrPow4 B s t n ω / η ^ 3) := by
  unfold termE1 sumIncrPow4
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range n, K * ((alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
        |gridIncr B s t n k ω|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul]
        have := abs_weight_mul_le hst hP hK (Finset.mem_range.1 hk).le
          (exitWeight_nonneg h𝒢a n k ω) (sub_le_self _ (alive_nonneg n (k + 1) ω)) (g := f')
        calc _ ≤ K * (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
              |gridIncr B s t n k ω| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
          _ = _ := by ring
    _ = K * ∑ k ∈ Finset.range n, (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
        |gridIncr B s t n k ω| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_weight_abs_le hη (exitWeight_nonneg h𝒢a n · ω)
        (sum_exitWeight_le_one n ω)) hK0

lemma abs_termE2_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K) (hK0 : 0 ≤ K) {η : ℝ} (hη : 0 < η) (n : ℕ) :
    |termE2 𝒢 s t B X f'' n ω| ≤ K * (η ^ 2 + sumIncrPow4 B s t n ω / η ^ 2) := by
  unfold termE2 sumIncrPow4
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range n, K * ((alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
        gridIncr B s t n k ω ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul, abs_pow, sq_abs]
        have := abs_weight_mul_le hst hP hK (Finset.mem_range.1 hk).le
          (exitWeight_nonneg h𝒢a n k ω) (sub_le_self _ (alive_nonneg n (k + 1) ω)) (g := f'')
        calc _ ≤ K * (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
              gridIncr B s t n k ω ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
          _ = _ := by ring
    _ = K * ∑ k ∈ Finset.range n, (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
        gridIncr B s t n k ω ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_weight_sq_le hη (exitWeight_nonneg h𝒢a n · ω)
        (sum_exitWeight_le_one n ω)) hK0

lemma abs_termC1_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K) (hK0 : 0 ≤ K) {η : ℝ} (hη : 0 < η) {n : ℕ}
    (hn : n ≠ 0) :
    |termC1 𝒢 s t a B X f'' n ω| ≤
      K * |a| * ((1 + |c|) * N + 1) * (η + sumIncrPow4 B s t n ω / η ^ 3) := by
  set V := (1 + |c|) * N
  have hV0 : 0 ≤ V := mul_nonneg (by positivity) (hP.N_nonneg (le_lifetimeOf _ _ _))
  set w : ℕ → ℝ := fun k => alive 𝒢 s t n (k + 1) ω *
    |gridIncr X s t n k ω - a * gridIncr B s t n k ω| / (V + 1)
  have hw0 : ∀ k, 0 ≤ w k := fun k =>
    div_nonneg (mul_nonneg (alive_nonneg _ _ _) (abs_nonneg _)) (by positivity)
  have hw1 : ∑ k ∈ Finset.range n, w k ≤ 1 := by
    rw [← Finset.sum_div, div_le_one (by positivity)]
    linarith [sum_alive_abs_fv_le h𝒢a hst hP hn]
  unfold termC1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range n, K * |a| * (V + 1) * (w k * |gridIncr B s t n k ω|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        have h1 := abs_weight_mul_le hst hP hK hk'.le (alive_nonneg n (k + 1) ω)
          (alive_succ_le h𝒢a n k ω) (g := f'')
        have hV1 : (V + 1) * w k = alive 𝒢 s t n (k + 1) ω *
            |gridIncr X s t n k ω - a * gridIncr B s t n k ω| := by
          simp only [w]; field_simp
        have he : |alive 𝒢 s t n (k + 1) ω * f'' (X (unifPartIcc s t n k) ω) *
            (a * gridIncr B s t n k ω * (gridIncr X s t n k ω - a * gridIncr B s t n k ω))| =
            |alive 𝒢 s t n (k + 1) ω * f'' (X (unifPartIcc s t n k) ω)| *
            (|a| * |gridIncr B s t n k ω| *
              |gridIncr X s t n k ω - a * gridIncr B s t n k ω|) := by
          rw [abs_mul _ (a * _ * _), abs_mul (a * _), abs_mul a]
        rw [he]
        calc _ ≤ K * alive 𝒢 s t n (k + 1) ω * (|a| * |gridIncr B s t n k ω| *
              |gridIncr X s t n k ω - a * gridIncr B s t n k ω|) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = K * |a| * ((V + 1) * w k) * |gridIncr B s t n k ω| := by rw [hV1]; ring
          _ = K * |a| * (V + 1) * (w k * |gridIncr B s t n k ω|) := by ring
    _ = K * |a| * (V + 1) * ∑ k ∈ Finset.range n, w k * |gridIncr B s t n k ω| := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_weight_abs_le hη hw0 hw1) (by positivity)

lemma abs_termM_le (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f' x| ≤ K) (hK0 : 0 ≤ K) (n : ℕ) :
    |termM 𝒢 s t B X f' n ω| ≤ K * sumIncrAbs B s t n ω := by
  unfold termM sumIncrAbs
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (abs_alive_mul_le hst hP hK hK0 (Finset.mem_range.1 hk).le) (abs_nonneg _)

lemma abs_termQ_le (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K) (hK0 : 0 ≤ K) (n : ℕ) :
    |termQ 𝒢 s t B X f'' n ω| ≤ K * sumIncrSq B s t n ω := by
  unfold termQ sumIncrSq
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_alive_mul_le hst hP hK hK0 (Finset.mem_range.1 hk).le) (sq_nonneg _)

lemma abs_termT_le (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K) (hK0 : 0 ≤ K) (n : ℕ) :
    |termT 𝒢 s t X f'' n ω| ≤ K * (n * (((t : ℝ) - s) / n)) := by
  unfold termT
  have hh : 0 ≤ ((t : ℝ) - s) / n := mesh_nonneg hst n
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range n, K * (((t : ℝ) - s) / n) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_right
          (abs_alive_mul_le hst hP hK hK0 (Finset.mem_range.1 hk).le) hh
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

lemma abs_termA_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f' x| ≤ K) (hK0 : 0 ≤ K) (n : ℕ) :
    |termA 𝒢 s t a B X f' n ω| ≤ K * ((1 + |c|) * N) := by
  have hV0 : 0 ≤ (1 + |c|) * N :=
    mul_nonneg (by positivity) (hP.N_nonneg (le_lifetimeOf _ _ _))
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [termA, Finset.range_zero, Finset.sum_empty, abs_zero]; positivity
  unfold termA
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range n, K * (alive 𝒢 s t n (k + 1) ω *
        |gridIncr X s t n k ω - a * gridIncr B s t n k ω|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul]
        have := abs_weight_mul_le hst hP hK (Finset.mem_range.1 hk).le
          (alive_nonneg n (k + 1) ω) (alive_succ_le h𝒢a n k ω) (g := f')
        calc _ ≤ K * alive 𝒢 s t n (k + 1) ω *
              |gridIncr X s t n k ω - a * gridIncr B s t n k ω| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
          _ = _ := by ring
    _ = K * ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
        |gridIncr X s t n k ω - a * gridIncr B s t n k ω| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_alive_abs_fv_le h𝒢a hst hP hn) hK0

lemma abs_termC2_le (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K) (hK0 : 0 ≤ K) (n : ℕ) :
    |termC2 𝒢 s t a B X f'' n ω| ≤ K * ((1 + |c|) * N) ^ 2 / 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [termC2, Finset.range_zero, Finset.sum_empty, abs_zero]; positivity
  unfold termC2
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ Finset.range n, K / 2 * (alive 𝒢 s t n (k + 1) ω *
        (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul, abs_div, abs_pow, sq_abs, abs_two]
        have := abs_weight_mul_le hst hP hK (Finset.mem_range.1 hk).le
          (alive_nonneg n (k + 1) ω) (alive_succ_le h𝒢a n k ω) (g := f'')
        calc _ ≤ K * alive 𝒢 s t n (k + 1) ω *
              ((gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := by ring
    _ = K / 2 * ∑ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω *
        (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ K / 2 * ((1 + |c|) * N) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_alive_sq_fv_le h𝒢a hst hP hn) (by positivity)
    _ = _ := by ring

end TermBounds

/-! ### Limits of the expectations -/

section Limits

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ}
  {B X J b : ℝ≥0 → Ω → ℝ} {f f' f'' : ℝ → ℝ}

/-- `∫ K (η + Q₄/η³) = K η + K/η³ ∫ Q₄`. -/
lemma integral_bound_pow4 (hB : IsPreBrownianReal B μ) (K η ζ : ℝ) (n : ℕ) :
    ∫ ω, K * (η + sumIncrPow4 B s t n ω / ζ) ∂μ =
      K * η + K / ζ * ∫ ω, sumIncrPow4 B s t n ω ∂μ := by
  rw [integral_const_mul, integral_add (integrable_const _)
    ((integrable_sumIncrPow4 hB n).div_const _), integral_const, integral_div]
  simp only [probReal_univ, one_smul]
  ring

lemma tendsto_integral_termE1 (hB : IsPreBrownianReal B μ) (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf' : Continuous f') :
    Tendsto (fun n => ∫ ω, termE1 𝒢 s t B X f' n ω ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf' N
  refine tendsto_zero_of_forall_le (tendsto_integral_sumIncrPow4 hB hst) fun ε hε => ?_
  set η := ε / (K + 1)
  have hη : 0 < η := by positivity
  refine ⟨K / η ^ 3, fun n => ?_⟩
  have h := norm_integral_le_of_norm_le (μ := μ)
    (g := fun ω => K * (η + sumIncrPow4 B s t n ω / η ^ 3))
    (((integrable_const η).add
      ((integrable_sumIncrPow4 hB n).div_const (η ^ 3))).const_mul K)
    (by filter_upwards [hpath] with ω hP
        rw [Real.norm_eq_abs]; exact abs_termE1_le h𝒢a hst hP hK hK0 hη n)
  rw [Real.norm_eq_abs, integral_bound_pow4 hB] at h
  have : K * η ≤ ε := by
    simp only [η]; rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma tendsto_integral_termE2 (hB : IsPreBrownianReal B μ) (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf'' : Continuous f'') :
    Tendsto (fun n => ∫ ω, termE2 𝒢 s t B X f'' n ω ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf'' N
  refine tendsto_zero_of_forall_le (tendsto_integral_sumIncrPow4 hB hst) fun ε hε => ?_
  set η := min 1 (ε / (K + 1))
  have hη : 0 < η := lt_min one_pos (by positivity)
  refine ⟨K / η ^ 2, fun n => ?_⟩
  have h := norm_integral_le_of_norm_le (μ := μ)
    (g := fun ω => K * (η ^ 2 + sumIncrPow4 B s t n ω / η ^ 2))
    (((integrable_const (η ^ 2)).add
      ((integrable_sumIncrPow4 hB n).div_const (η ^ 2))).const_mul K)
    (by filter_upwards [hpath] with ω hP
        rw [Real.norm_eq_abs]; exact abs_termE2_le h𝒢a hst hP hK hK0 hη n)
  rw [Real.norm_eq_abs, integral_bound_pow4 hB] at h
  have h1 : η ^ 2 ≤ η := by
    rw [sq]; exact mul_le_of_le_one_left hη.le (min_le_left _ _)
  have h2 : η ≤ ε / (K + 1) := min_le_right _ _
  have : K * η ^ 2 ≤ ε := by
    calc K * η ^ 2 ≤ K * (ε / (K + 1)) := by gcongr; exact h1.trans h2
      _ ≤ ε := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma tendsto_integral_termC1 (hB : IsPreBrownianReal B μ) (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf'' : Continuous f'') :
    Tendsto (fun n => ∫ ω, termC1 𝒢 s t a B X f'' n ω ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf'' N
  set C := K * |a| * ((1 + |c|) * N + 1)
  have hC0 : 0 ≤ C := by
    have : 0 ≤ (1 + |c|) * N + 1 := by
      rcases hpath.exists with ⟨ω, hP⟩
      have := hP.N_nonneg (le_lifetimeOf _ _ _)
      positivity
    positivity
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_zero_of_forall_le
    ((tendsto_add_atTop_iff_nat 1).2 (tendsto_integral_sumIncrPow4 hB hst)) fun ε hε => ?_
  set η := ε / (C + 1)
  have hη : 0 < η := by positivity
  refine ⟨C / η ^ 3, fun n => ?_⟩
  have h := norm_integral_le_of_norm_le (μ := μ)
    (g := fun ω => C * (η + sumIncrPow4 B s t (n + 1) ω / η ^ 3))
    (((integrable_const η).add
      ((integrable_sumIncrPow4 hB (n + 1)).div_const (η ^ 3))).const_mul C)
    (by filter_upwards [hpath] with ω hP
        rw [Real.norm_eq_abs]; exact abs_termC1_le h𝒢a hst hP hK hK0 hη n.succ_ne_zero)
  rw [Real.norm_eq_abs, integral_bound_pow4 hB] at h
  have : C * η ≤ ε := by
    simp only [η]; rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma termS_eq_sub (h𝒢a : Antitone 𝒢) (n : ℕ) (ω : Ω) :
    termS 𝒢 s t X f n ω =
      f (X (unifPartIcc s t n (aliveCells 𝒢 s t n ω)) ω) - f (X s ω) := by
  unfold termS
  rw [sum_alive_succ_mul h𝒢a n ω
    (fun k => f (X (unifPartIcc s t n (k + 1)) ω) - f (X (unifPartIcc s t n k) ω)),
    sum_sub_grid (fun n => aliveCells 𝒢 s t n ω) (fun u => f (X u ω)) n]

lemma tendsto_integral_termS (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hXm : ∀ u, Measurable (X u))
    (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf : Continuous f) :
    Tendsto (fun n => ∫ ω, termS 𝒢 s t X f n ω ∂μ) atTop
      (𝓝 (∫ ω, (f (X (lifetime 𝒢 s t ω) ω) - f (X s ω)) ∂μ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf N
  refine tendsto_integral_of_dominated_convergence (fun _ => 2 * K)
    (fun n => (measurable_termS h𝒢m hXm hf n).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs, termS_eq_sub h𝒢a n ω]
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
  · filter_upwards [hpath] with ω hP
    refine (hP.tendsto_telescope (gridApprox_aliveCells h𝒢a hst ω) hf).congr fun n => ?_
    rw [termS_eq_sub h𝒢a n ω, sum_sub_grid (fun n => aliveCells 𝒢 s t n ω) (fun u => f (X u ω)) n]

lemma tendsto_integral_termA (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hBm : ∀ u, Measurable (B u))
    (hXm : ∀ u, Measurable (X u)) (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf' : Continuous f') :
    Tendsto (fun n => ∫ ω, termA 𝒢 s t a B X f' n ω ∂μ) atTop
      (𝓝 (∫ ω, ((∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f' (X r.toNNReal ω) * b r.toNNReal ω) +
        c * f' 0 * (J (lifetime 𝒢 s t ω) ω - J s ω)) ∂μ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf' N
  refine tendsto_integral_of_dominated_convergence (fun _ => K * ((1 + |c|) * N))
    (fun n => (measurable_termA h𝒢m hBm hXm hf' n).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs]
    exact abs_termA_le h𝒢a hst hP hK hK0 n
  · filter_upwards [hpath] with ω hP
    refine (hP.tendsto_drift_singular (gridApprox_aliveCells h𝒢a hst ω) hst hf').congr
      fun n => ?_
    unfold termA
    simp only [mul_assoc]
    rw [sum_alive_succ_mul h𝒢a n ω]
    rfl

omit [IsProbabilityMeasure μ] in
lemma ae_tendsto_termT (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf'' : Continuous f'') :
    ∀ᵐ ω ∂μ, Tendsto (fun n => termT 𝒢 s t X f'' n ω) atTop
      (𝓝 (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f'' (X r.toNNReal ω))) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf'' N
  filter_upwards [hpath] with ω hP
  have h1 := hP.tendsto_riemann_f'' (gridApprox_aliveCells h𝒢a hst ω) hst hf''
  -- the exit part
  have h2 : Tendsto (fun n => ∑ k ∈ Finset.range n,
      (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) * f'' (X (unifPartIcc s t n k) ω) *
        (((t : ℝ) - s) / n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => K * (((t : ℝ) - s) / n))
    · intro n
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hh : 0 ≤ ((t : ℝ) - s) / n := mesh_nonneg hst n
      calc _ ≤ ∑ k ∈ Finset.range n, K * (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) *
            (((t : ℝ) - s) / n) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul, abs_of_nonneg hh]
            exact mul_le_mul_of_nonneg_right (abs_weight_mul_le hst hP hK
              (Finset.mem_range.1 hk).le (exitWeight_nonneg h𝒢a n k ω)
              (sub_le_self _ (alive_nonneg n (k + 1) ω))) hh
        _ = K * (((t : ℝ) - s) / n) * ∑ k ∈ Finset.range n,
            (alive 𝒢 s t n k ω - alive 𝒢 s t n (k + 1) ω) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ K * (((t : ℝ) - s) / n) * 1 :=
            mul_le_mul_of_nonneg_left (sum_exitWeight_le_one n ω) (by positivity)
        _ = _ := mul_one _
    · simpa using (tendsto_mesh s t).const_mul K
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr fun n => ?_
  unfold termT
  rw [← sum_alive_succ_mul h𝒢a n ω (fun k => f'' (X (unifPartIcc s t n k) ω) *
    (((t : ℝ) - s) / n)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma tendsto_integral_termT (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hXm : ∀ u, Measurable (X u))
    (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf'' : Continuous f'') :
    Tendsto (fun n => ∫ ω, termT 𝒢 s t X f'' n ω ∂μ) atTop
      (𝓝 (∫ ω, (∫ r in (s : ℝ)..(lifetime 𝒢 s t ω), f'' (X r.toNNReal ω)) ∂μ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf'' N
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (by exact_mod_cast hst)
  refine tendsto_integral_of_dominated_convergence (fun _ => K * ((t : ℝ) - s))
    (fun n => (measurable_termT h𝒢m hXm hf'' n).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs]
    refine (abs_termT_le hst hP hK hK0 n).trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using hts
    · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn)]
  · exact ae_tendsto_termT h𝒢a hst hpath hf''

lemma tendsto_integral_termC2 (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hBm : ∀ u, Measurable (B u))
    (hXm : ∀ u, Measurable (X u)) (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf'' : Continuous f'') :
    Tendsto (fun n => ∫ ω, termC2 𝒢 s t a B X f'' n ω ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf'' N
  have h0 : (0 : ℝ) = ∫ _ : Ω, (0 : ℝ) ∂μ := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun _ => K * ((1 + |c|) * N) ^ 2 / 2)
    (fun n => (measurable_termC2 h𝒢m hBm hXm hf'' n).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs]
    exact abs_termC2_le h𝒢a hst hP hK hK0 n
  · filter_upwards [hpath] with ω hP
    have := (hP.tendsto_sq_fv (gridApprox_aliveCells h𝒢a hst ω) hst hf'').div_const 2
    rw [zero_div] at this
    refine this.congr fun n => ?_
    unfold termC2
    simp only [mul_assoc]
    rw [sum_alive_succ_mul h𝒢a n ω, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by simp only [gridIncr]; ring

end Limits

/-! ### The Taylor remainder -/

section Remainder

/-- The remainder of one Taylor step, with the modulus of continuity of `f''` on `[-N, N]`. -/
lemma abs_rem_le {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) {K δ η N : ℝ} (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K)
    (hδ : ∀ x ∈ Icc (-N) N, ∀ y ∈ Icc (-N) N, |x - y| ≤ δ → |f'' x - f'' y| ≤ η)
    {x y : ℝ} (hx : x ∈ Icc (-N) N) (hy : y ∈ Icc (-N) N) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤
      (if δ < |y - x| then 2 * K else η) * (y - x) ^ 2 := by
  refine abs_taylor_two_le hf hf' fun z hz => ?_
  have hz' : z ∈ Icc (-N) N := uIcc_subset_Icc hx hy hz
  split_ifs with h
  · calc _ ≤ |f'' z| + |f'' x| := abs_sub _ _
      _ ≤ K + K := add_le_add (hK z hz') (hK x hx)
      _ = 2 * K := by ring
  · exact hδ z hz' x hx ((abs_sub_left_of_mem_uIcc hz).trans (not_lt.1 h))

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : ℝ≥0 → Set Ω} {s t : ℝ≥0} {a c N : ℝ}
  {B X J b : ℝ≥0 → Ω → ℝ} {f f' f'' : ℝ → ℝ}

open Classical in
/-- The indicator of a "bad" partition: some alive cell has an increment of `X` above `δ`. -/
def badInd (𝒢 : ℝ≥0 → Set Ω) (s t : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (δ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if ∃ k < n, alive 𝒢 s t n (k + 1) ω ≠ 0 ∧ δ < |gridIncr X s t n k ω| then 1 else 0

lemma badInd_nonneg (δ : ℝ) (n : ℕ) (ω : Ω) : 0 ≤ badInd 𝒢 s t X δ n ω := by
  unfold badInd; split_ifs <;> norm_num

lemma badInd_le_one (δ : ℝ) (n : ℕ) (ω : Ω) : badInd 𝒢 s t X δ n ω ≤ 1 := by
  unfold badInd; split_ifs <;> norm_num

lemma measurable_badInd (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hXm : ∀ u, Measurable (X u))
    (δ : ℝ) (n : ℕ) : Measurable (badInd 𝒢 s t X δ n) := by
  classical
  have hset : {ω | ∃ k < n, alive 𝒢 s t n (k + 1) ω ≠ 0 ∧ δ < |gridIncr X s t n k ω|} =
      ⋃ k ∈ Finset.range n, ({ω | alive 𝒢 s t n (k + 1) ω ≠ 0} ∩
        {ω | δ < |gridIncr X s t n k ω|}) := by
    ext ω; simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Finset.mem_range, exists_prop]
  have hm : MeasurableSet
      {ω | ∃ k < n, alive 𝒢 s t n (k + 1) ω ≠ 0 ∧ δ < |gridIncr X s t n k ω|} := by
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun k _ =>
      ((measurable_alive_amb h𝒢m n (k + 1)) (measurableSet_singleton 0).compl).inter
        (measurableSet_lt measurable_const
          (continuous_abs.measurable.comp (measurable_gridIncr (s := s) (t := t) hXm n k)))
  unfold badInd
  exact Measurable.ite hm measurable_const measurable_const

/-- Pathwise remainder bound. -/
lemma abs_termR_le (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {ω : Ω} (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hP : IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    {K δ η : ℝ} (hK : ∀ x ∈ Icc (-N) N, |f'' x| ≤ K) (hK0 : 0 ≤ K) (hη : 0 ≤ η)
    (hδ : ∀ x ∈ Icc (-N) N, ∀ y ∈ Icc (-N) N, |x - y| ≤ δ → |f'' x - f'' y| ≤ η)
    {n : ℕ} (hn : n ≠ 0) :
    |termR 𝒢 s t X f f' f'' n ω| ≤ (η + 2 * K * badInd 𝒢 s t X δ n ω) *
      (2 * a ^ 2 * sumIncrSq B s t n ω + 2 * ((1 + |c|) * N) ^ 2) := by
  set β := badInd 𝒢 s t X δ n ω
  have hβ0 : 0 ≤ β := badInd_nonneg δ n ω
  have hterm : ∀ k ∈ Finset.range n, |alive 𝒢 s t n (k + 1) ω *
      (f (X (unifPartIcc s t n (k + 1)) ω) - f (X (unifPartIcc s t n k) ω) -
        f' (X (unifPartIcc s t n k) ω) * gridIncr X s t n k ω -
        f'' (X (unifPartIcc s t n k) ω) * gridIncr X s t n k ω ^ 2 / 2)| ≤
      (η + 2 * K * β) * (alive 𝒢 s t n (k + 1) ω * gridIncr X s t n k ω ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rcases alive_eq_zero_or_one (𝒢 := 𝒢) (s := s) (t := t) n (k + 1) ω with h0 | h1
    · rw [h0]; simp
    · rw [h1, one_mul, one_mul]
      obtain ⟨hx0, hx1⟩ := mem_Icc_N_of_alive_succ hst hP hk' (by rw [h1]; exact one_ne_zero)
      have := abs_rem_le hf hf' hK hδ hx0 hx1
      simp only [gridIncr]
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      split_ifs with hbig
      · have hex : ∃ k' < n, alive 𝒢 s t n (k' + 1) ω ≠ 0 ∧ δ < |gridIncr X s t n k' ω| :=
          ⟨k, hk', by rw [h1]; exact one_ne_zero, hbig⟩
        have : β = 1 := by simp only [β, badInd, hex, ite_true]
        rw [this]; linarith
      · nlinarith
  have hsq : ∀ k ∈ Finset.range n, alive 𝒢 s t n (k + 1) ω * gridIncr X s t n k ω ^ 2 ≤
      2 * a ^ 2 * gridIncr B s t n k ω ^ 2 + 2 * (alive 𝒢 s t n (k + 1) ω *
        (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2) := by
    intro k _
    have h1 := alive_nonneg (𝒢 := 𝒢) (s := s) (t := t) n (k + 1) ω
    have h2 := alive_le_one (𝒢 := 𝒢) (s := s) (t := t) n (k + 1) ω
    have key : gridIncr X s t n k ω ^ 2 ≤ 2 * (a * gridIncr B s t n k ω) ^ 2 +
        2 * (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2 := by
      nlinarith [sq_nonneg (a * gridIncr B s t n k ω -
        (gridIncr X s t n k ω - a * gridIncr B s t n k ω))]
    have hB2 : alive 𝒢 s t n (k + 1) ω * (2 * (a * gridIncr B s t n k ω) ^ 2) ≤
        2 * a ^ 2 * gridIncr B s t n k ω ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg (a * gridIncr B s t n k ω), sq_nonneg a,
        sq_nonneg (gridIncr B s t n k ω), mul_nonneg (sq_nonneg a) (sq_nonneg (gridIncr B s t n k ω))]
    calc _ ≤ alive 𝒢 s t n (k + 1) ω * (2 * (a * gridIncr B s t n k ω) ^ 2 +
          2 * (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2) :=
          mul_le_mul_of_nonneg_left key h1
      _ = alive 𝒢 s t n (k + 1) ω * (2 * (a * gridIncr B s t n k ω) ^ 2) +
          2 * (alive 𝒢 s t n (k + 1) ω *
            (gridIncr X s t n k ω - a * gridIncr B s t n k ω) ^ 2) := by ring
      _ ≤ _ := by linarith
  unfold termR
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.sum_le_sum hsq).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sumIncrSq]
  have := sum_alive_sq_fv_le h𝒢a hst hP hn
  linarith

lemma integrable_badInd (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hXm : ∀ u, Measurable (X u))
    (δ : ℝ) (n : ℕ) : Integrable (badInd 𝒢 s t X δ n) μ :=
  (integrable_const (1 : ℝ)).mono' (measurable_badInd h𝒢m hXm δ n).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (badInd_nonneg δ n ω)]; exact badInd_le_one δ n ω)

/-- `β Q₂ ≤ (n / L) Q₄ + L β` for `0 ≤ β ≤ 1`. -/
lemma mul_sumIncrSq_le {L β : ℝ} (hL : 0 < L) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {n : ℕ} (hn : n ≠ 0)
    (ω : Ω) :
    β * sumIncrSq B s t n ω ≤ n / L * sumIncrPow4 B s t n ω + L * β := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hc : 0 < L / n := div_pos hL hn'
  unfold sumIncrSq sumIncrPow4
  rw [Finset.mul_sum, Finset.mul_sum]
  calc ∑ k ∈ Finset.range n, β * gridIncr B s t n k ω ^ 2
      ≤ ∑ k ∈ Finset.range n, (gridIncr B s t n k ω ^ 4 / (L / n) + L / n * β) :=
        Finset.sum_le_sum fun k _ => mul_sq_le_pow4_add hc hβ0 hβ1 _
    _ = ∑ k ∈ Finset.range n, n / L * gridIncr B s t n k ω ^ 4 + L * β := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by field_simp
        · field_simp

lemma integral_remBound (hB : IsPreBrownianReal B μ) (hst : s ≤ t)
    (h𝒢m : ∀ u, MeasurableSet (𝒢 u)) (hXm : ∀ u, Measurable (X u)) (η V K L C δ : ℝ) {n : ℕ}
    (hn : n ≠ 0) (hL : L ≠ 0) :
    ∫ ω, (η * (2 * a ^ 2 * sumIncrSq B s t n ω + 2 * V ^ 2) +
      4 * K * a ^ 2 * (n / L) * sumIncrPow4 B s t n ω + C * badInd 𝒢 s t X δ n ω) ∂μ =
      η * (2 * a ^ 2 * ((t : ℝ) - s) + 2 * V ^ 2) + 12 * K * a ^ 2 * ((t : ℝ) - s) ^ 2 / L +
        C * ∫ ω, badInd 𝒢 s t X δ n ω ∂μ := by
  have i0 : Integrable (fun ω => 2 * a ^ 2 * sumIncrSq B s t n ω) μ :=
    (integrable_sumIncrSq hB n).const_mul _
  have i1 : Integrable (fun ω => η * (2 * a ^ 2 * sumIncrSq B s t n ω + 2 * V ^ 2)) μ :=
    (i0.add (integrable_const _)).const_mul _
  have i2 : Integrable (fun ω => 4 * K * a ^ 2 * (n / L) * sumIncrPow4 B s t n ω) μ :=
    (integrable_sumIncrPow4 hB n).const_mul _
  have i3 : Integrable (fun ω => C * badInd 𝒢 s t X δ n ω) μ :=
    (integrable_badInd h𝒢m hXm δ n).const_mul _
  have i12 : Integrable (fun ω => η * (2 * a ^ 2 * sumIncrSq B s t n ω + 2 * V ^ 2) +
      4 * K * a ^ 2 * (n / L) * sumIncrPow4 B s t n ω) μ := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_add i0 (integrable_const _), integral_const_mul,
    integral_sumIncrSq hB hst, integral_const, integral_sumIncrPow4 hB hst]
  simp only [probReal_univ, one_smul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp
  ring

lemma tendsto_integral_termR (hB : IsPreBrownianReal B μ) (h𝒢m : ∀ u, MeasurableSet (𝒢 u))
    (hXm : ∀ u, Measurable (X u)) (h𝒢a : Antitone 𝒢) (hst : s ≤ t)
    (hpath : ∀ᵐ ω ∂μ, IsTanakaPath a c N s (lifetime 𝒢 s t ω) (X · ω) (B · ω) (J · ω) (b · ω))
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') :
    Tendsto (fun n => ∫ ω, termR 𝒢 s t X f f' f'' n ω ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_Icc hf'' N
  have hN : 0 ≤ N := by
    rcases hpath.exists with ⟨ω, hP⟩; exact hP.N_nonneg (le_lifetimeOf _ _ _)
  set V := (1 + |c|) * N
  set T : ℝ := (t : ℝ) - s
  have hT : 0 ≤ T := sub_nonneg.2 (by exact_mod_cast hst)
  refine tendsto_of_forall_eventually_abs_le fun ε hε => ?_
  set η := ε / (3 * (2 * a ^ 2 * T + 2 * V ^ 2 + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc (-N) N) hf''.continuousOn) η hη
  have hδ' : ∀ x ∈ Icc (-N) N, ∀ y ∈ Icc (-N) N, |x - y| ≤ δ → |f'' x - f'' y| ≤ η :=
    fun x hx y hy hxy => by
      have := hδ x hx y hy (by rwa [Real.dist_eq]); rwa [Real.dist_eq] at this
  set L := 36 * K * a ^ 2 * T ^ 2 / ε + 1
  have hL : 0 < L := by positivity
  -- the bad event has vanishing probability
  have hbad : Tendsto (fun n => ∫ ω, badInd 𝒢 s t X δ n ω ∂μ) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : Ω, (0 : ℝ) ∂μ := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (measurable_badInd h𝒢m hXm δ n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (badInd_nonneg δ n ω)]; exact badInd_le_one δ n ω) ?_
    filter_upwards [hpath] with ω hP
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hP.eventually_incr_le (gridApprox_aliveCells h𝒢a hst ω) hst hδ0]
      with n ⟨_, hinc⟩
    symm
    unfold badInd
    rw [ite_eq_right_iff]
    rintro ⟨k, hk, hal, hbig⟩
    exfalso
    have := (hinc k (lt_aliveCells_of_alive h𝒢a hk hal)).1
    simp only [gridIncr] at hbig
    linarith
  set C := 4 * K * a ^ 2 * L + 4 * K * V ^ 2
  have hC : 0 ≤ C := by positivity
  filter_upwards [eventually_ne_atTop 0,
    (Metric.tendsto_nhds.1 hbad) (ε / (3 * (C + 1))) (by positivity)] with n hn hbn
  rw [Real.dist_eq, sub_zero] at hbn
  rw [sub_zero]
  set G : Ω → ℝ := fun ω => η * (2 * a ^ 2 * sumIncrSq B s t n ω + 2 * V ^ 2) +
    4 * K * a ^ 2 * (n / L) * sumIncrPow4 B s t n ω + C * badInd 𝒢 s t X δ n ω
  have hGi : Integrable G μ :=
    ((((integrable_sumIncrSq hB n).const_mul _).add (integrable_const _)).const_mul _).add
      ((integrable_sumIncrPow4 hB n).const_mul _) |>.add
      ((integrable_badInd h𝒢m hXm δ n).const_mul _)
  have hbound : ∀ᵐ ω ∂μ, ‖termR 𝒢 s t X f f' f'' n ω‖ ≤ G ω := by
    filter_upwards [hpath] with ω hP
    rw [Real.norm_eq_abs]
    refine (abs_termR_le hf hf' h𝒢a hst hP hK hK0 hη.le hδ' hn).trans ?_
    have hb0 := badInd_nonneg (𝒢 := 𝒢) (s := s) (t := t) (X := X) δ n ω
    have hb1 := badInd_le_one (𝒢 := 𝒢) (s := s) (t := t) (X := X) δ n ω
    have hQ := mul_sumIncrSq_le (B := B) (s := s) (t := t) hL hb0 hb1 hn ω
    have hQ0 := sumIncrSq_nonneg B s t n ω
    simp only [G, C]
    nlinarith [mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 4 * K * a ^ 2)]
  have hint : ∫ ω, G ω ∂μ = η * (2 * a ^ 2 * T + 2 * V ^ 2) + 12 * K * a ^ 2 * T ^ 2 / L +
      C * ∫ ω, badInd 𝒢 s t X δ n ω ∂μ :=
    integral_remBound hB hst h𝒢m hXm η V K L C δ hn hL.ne'
  have h1 : η * (2 * a ^ 2 * T + 2 * V ^ 2) ≤ ε / 3 := by
    simp only [η]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg a, sq_nonneg V]
  have h2 : 12 * K * a ^ 2 * T ^ 2 / L ≤ ε / 3 := by
    rw [div_le_div_iff₀ hL (by norm_num)]
    have hεL : ε * L = 36 * K * a ^ 2 * T ^ 2 + ε := by simp only [L]; field_simp
    linarith
  have h3 : C * ∫ ω, badInd 𝒢 s t X δ n ω ∂μ ≤ ε / 3 := by
    have hpos : 0 ≤ ∫ ω, badInd 𝒢 s t X δ n ω ∂μ :=
      integral_nonneg fun ω => badInd_nonneg δ n ω
    rw [abs_of_nonneg hpos] at hbn
    calc C * _ ≤ (C + 1) * (ε / (3 * (C + 1))) := by gcongr; linarith
      _ = ε / 3 := by field_simp
  calc |∫ ω, termR 𝒢 s t X f f' f'' n ω ∂μ| ≤ ∫ ω, G ω ∂μ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_of_norm_le hGi hbound
    _ ≤ ε := by rw [hint]; linarith

end Remainder

end InteractingSLE.LocalTime
