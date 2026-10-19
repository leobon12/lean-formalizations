import GaussianLQG.Metric.Geodesic

/-!
# The tube lemma (blueprint Lemma `lem:tube`)

Deterministic form of blueprint Lemma `lem:tube`. Let `D` be a continuous metric on `ℂ`, `b ∈ ℝ`,
`R₁ ≥ 1`, and `K ⊆ B̄_{R₁-1}(0)` (in the blueprint `R₁ = 1 + sup_{z ∈ K} |z|`). Let `E` bound the
Euclidean error on `B̄_R(0)`, `R = 4R₁`:
`|e^{-b} D(x, y) - |x - y|| ≤ E` for `x, y ∈ B̄_R(0)` (for instance `E = 𝖤_γ(R)`, the supremum),
and assume `E ≤ ε₀ = min(R₁/4, 1/(16R₁))`. Then every constant-speed `D`-geodesic `η` between
`z, w ∈ K` satisfies `η([0,1]) ⊆ B_{3R₁}(0)` and
`sup_t |η(t) - ((1-t) z + t w)| ≤ (8 R₁ E)^{1/2} < 1` (`tube_of_isGeod01`).

Proof (blueprint). Write `D̃ = e^{-b} D` and `a = |z - w| ≤ 2R₁ - 2`. If `η` reached
`∂B_{3R₁}(0)` at `v` (intermediate value theorem), then `|z - v| ≥ 2R₁ + 1`, so
`D̃(z, v) ≥ 2R₁ + 1 - E > 2R₁ - 2 + E ≥ D̃(z, w)`, contradicting `D̃(z, v) ≤ D̃(z, w)`. For
`v = η(t)`: `|v - z| ≤ t D̃(z, w) + E ≤ t a + 2E` and `|v - w| ≤ (1-t) a + 2E`, and the identity
`|v - ((1-t) z + t w)|² = (1-t)|v - z|² + t|v - w|² - t(1-t) a²` (`norm_sub_segment_sq`) gives
`|v - ((1-t) z + t w)|² ≤ 8 t(1-t) a E + 4E² ≤ 8 R₁ E`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-- The identity `|v - ((1-t) z + t w)|² = (1-t)|v - z|² + t|v - w|² - t(1-t)|z - w|²`. -/
theorem norm_sub_segment_sq (v z w : ℂ) (t : ℝ) :
    ‖v - (((1 - t : ℝ) : ℂ) * z + (t : ℂ) * w)‖ ^ 2 =
      (1 - t) * ‖v - z‖ ^ 2 + t * ‖v - w‖ ^ 2 - t * (1 - t) * ‖z - w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The algebraic core of the tube estimate: if `0 ≤ A ≤ t a + 2E`, `0 ≤ B ≤ (1-t) a + 2E`,
`t ∈ [0,1]`, `0 ≤ a ≤ 2R₁ - 2` and `0 ≤ E ≤ R₁/4`, then
`(1-t) A² + t B² - t(1-t) a² ≤ 8 R₁ E`. -/
theorem tube_quadratic_le {t a A B E R₁ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha0 : 0 ≤ a)
    (ha : a ≤ 2 * R₁ - 2) (hE0 : 0 ≤ E) (hE1 : E ≤ R₁ / 4) (hA0 : 0 ≤ A)
    (hA : A ≤ t * a + 2 * E) (hB0 : 0 ≤ B) (hB : B ≤ (1 - t) * a + 2 * E) :
    (1 - t) * A ^ 2 + t * B ^ 2 - t * (1 - t) * a ^ 2 ≤ 8 * R₁ * E := by
  have hA2 : A ^ 2 ≤ (t * a + 2 * E) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have hB2 : B ^ 2 ≤ ((1 - t) * a + 2 * E) ^ 2 := pow_le_pow_left₀ hB0 hB 2
  have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
  have hsum : (1 - t) * A ^ 2 + t * B ^ 2 - t * (1 - t) * a ^ 2 ≤
      8 * (t * (1 - t)) * (a * E) + 4 * E ^ 2 := by
    have e : (1 - t) * (t * a + 2 * E) ^ 2 + t * ((1 - t) * a + 2 * E) ^ 2 -
        t * (1 - t) * a ^ 2 = 8 * (t * (1 - t)) * (a * E) + 4 * E ^ 2 := by ring
    have h1 := mul_le_mul_of_nonneg_left hA2 h1t
    have h2 := mul_le_mul_of_nonneg_left hB2 ht0
    linarith
  have htt : t * (1 - t) ≤ 1 / 4 := by
    have h := sq_nonneg (2 * t - 1)
    linarith
  have haE : 0 ≤ a * E := mul_nonneg ha0 hE0
  have h3 : t * (1 - t) * (a * E) ≤ 1 / 4 * (a * E) := mul_le_mul_of_nonneg_right htt haE
  have h4 : a * E ≤ (2 * R₁ - 2) * E := mul_le_mul_of_nonneg_right ha hE0
  have h5 : E ^ 2 ≤ R₁ / 4 * E := by rw [sq]; exact mul_le_mul_of_nonneg_right hE1 hE0
  have hRE : 0 ≤ R₁ * E := mul_nonneg (by linarith) hE0
  linarith

/-- **Blueprint Lemma `lem:tube`** (deterministic form). Let `D` be a continuous metric, `b ∈ ℝ`,
`R₁ ≥ 1` and `K ⊆ B̄_{R₁-1}(0)`. Suppose `|e^{-b} D(x, y) - |x - y|| ≤ E` for all
`x, y ∈ B̄_{4R₁}(0)` and `E ≤ min(R₁/4, 1/(16R₁))`. Then every constant-speed `D`-geodesic `η`
between points `z, w ∈ K` satisfies `η([0,1]) ⊆ B_{3R₁}(0)` and
`|η(t) - ((1-t) z + t w)| ≤ (8 R₁ E)^{1/2}` for all `t ∈ [0,1]`, and `(8 R₁ E)^{1/2} < 1`. -/
theorem tube_of_isGeod01 {D : ContMetric} {b R₁ E : ℝ} {K : Set ℂ} (hR₁ : 1 ≤ R₁)
    (hK : K ⊆ Metric.closedBall 0 (R₁ - 1))
    (hE : ∀ x ∈ Metric.closedBall (0 : ℂ) (4 * R₁), ∀ y ∈ Metric.closedBall (0 : ℂ) (4 * R₁),
      |Real.exp (-b) * D.1 (x, y) - ‖x - y‖| ≤ E)
    (hE₀ : E ≤ min (R₁ / 4) (1 / (16 * R₁)))
    {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) {η : C(unitInterval, ℂ)} (hη : IsGeod01 D z w η) :
    range η ⊆ Metric.ball 0 (3 * R₁) ∧
      (∀ t : unitInterval,
        ‖η t - (((1 - t : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w)‖ ≤ Real.sqrt (8 * R₁ * E)) ∧
      Real.sqrt (8 * R₁ * E) < 1 := by
  have hz' : ‖z‖ ≤ R₁ - 1 := mem_closedBall_zero_iff.1 (hK hz)
  have hw' : ‖w‖ ≤ R₁ - 1 := mem_closedBall_zero_iff.1 (hK hw)
  have hR₁0 : 0 < R₁ := by linarith
  have hE1 : E ≤ R₁ / 4 := hE₀.trans (min_le_left _ _)
  have hE2 : 16 * R₁ * E ≤ 1 := by
    have h := hE₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hzR : z ∈ Metric.closedBall (0 : ℂ) (4 * R₁) := mem_closedBall_zero_iff.2 (by linarith)
  have hwR : w ∈ Metric.closedBall (0 : ℂ) (4 * R₁) := mem_closedBall_zero_iff.2 (by linarith)
  have hE0 : 0 ≤ E := by
    have h := hE z hzR z hzR
    rwa [D.2.self_eq_zero, mul_zero, sub_self, norm_zero, sub_zero, abs_zero] at h
  have hE16 : E ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_right hR₁ hE0
    linarith
  -- the scaled distance `L = e^{-b} D(z, w)` and its values along the geodesic
  set L := Real.exp (-b) * D.1 (z, w) with hL
  have hLnn : 0 ≤ L := mul_nonneg (Real.exp_pos _).le (ContMetric.nonneg D z w)
  have hLle : L ≤ ‖z - w‖ + E := by
    have h := (abs_le.1 (hE z hzR w hwR)).2
    linarith
  have hzw : ‖z - w‖ ≤ 2 * R₁ - 2 := by
    calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
      _ ≤ 2 * R₁ - 2 := by linarith
  have hdz : ∀ t : unitInterval, Real.exp (-b) * D.1 (z, η t) = (t : ℝ) * L := by
    intro t
    have h := hη.2.2 0 t
    rw [hη.1] at h
    rw [h, Set.Icc.coe_zero, sub_zero, abs_of_nonneg t.2.1, hL]
    ring
  have hdw : ∀ t : unitInterval, Real.exp (-b) * D.1 (η t, w) = (1 - (t : ℝ)) * L := by
    intro t
    have h := hη.2.2 t 1
    rw [hη.2.1] at h
    rw [h, Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.2 t.2.2), hL]
    ring
  -- (1) the geodesic stays in `B_{3R₁}(0)`
  have hrange : range η ⊆ Metric.ball 0 (3 * R₁) := by
    rintro _ ⟨t, rfl⟩
    rw [mem_ball_zero_iff]
    by_contra hcon
    push Not at hcon
    have hg : Continuous fun s : unitInterval => ‖η s‖ := continuous_norm.comp η.continuous
    have h0 : ‖η 0‖ ≤ 3 * R₁ := by rw [hη.1]; linarith
    obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hg ⟨h0, hcon⟩
    have hs' : ‖η s‖ = 3 * R₁ := hs
    have hsR : η s ∈ Metric.closedBall (0 : ℂ) (4 * R₁) :=
      mem_closedBall_zero_iff.2 (by linarith)
    have h1 := (abs_le.1 (hE z hzR (η s) hsR)).1
    rw [hdz s] at h1
    have h2 : 2 * R₁ + 1 ≤ ‖z - η s‖ := by
      have := norm_sub_norm_le (η s) z
      rw [norm_sub_rev] at this
      linarith
    have h3 : (s : ℝ) * L ≤ L := mul_le_of_le_one_left hLnn s.2.2
    linarith
  -- (2) the tube estimate
  have htube : ∀ t : unitInterval,
      ‖η t - (((1 - t : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w)‖ ≤ Real.sqrt (8 * R₁ * E) := by
    intro t
    have hvR : η t ∈ Metric.closedBall (0 : ℂ) (4 * R₁) := by
      have h := mem_ball_zero_iff.1 (hrange ⟨t, rfl⟩)
      exact mem_closedBall_zero_iff.2 (by linarith)
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hA : ‖η t - z‖ ≤ (t : ℝ) * ‖z - w‖ + 2 * E := by
      have h := (abs_le.1 (hE z hzR (η t) hvR)).1
      rw [hdz t, norm_sub_rev z] at h
      have : (t : ℝ) * L ≤ (t : ℝ) * (‖z - w‖ + E) := mul_le_mul_of_nonneg_left hLle ht0
      have : (t : ℝ) * E ≤ E := mul_le_of_le_one_left hE0 ht1
      linarith
    have hB : ‖η t - w‖ ≤ (1 - (t : ℝ)) * ‖z - w‖ + 2 * E := by
      have h := (abs_le.1 (hE (η t) hvR w hwR)).1
      rw [hdw t] at h
      have : (1 - (t : ℝ)) * L ≤ (1 - (t : ℝ)) * (‖z - w‖ + E) :=
        mul_le_mul_of_nonneg_left hLle (sub_nonneg.2 ht1)
      have : (1 - (t : ℝ)) * E ≤ E := mul_le_of_le_one_left hE0 (by linarith)
      linarith
    have hq := tube_quadratic_le ht0 ht1 (norm_nonneg _) hzw hE0 hE1 (norm_nonneg _) hA
      (norm_nonneg _) hB
    rw [← norm_sub_segment_sq] at hq
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 hq
  -- (3) `(8 R₁ E)^{1/2} < 1`
  have hlt : Real.sqrt (8 * R₁ * E) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  exact ⟨hrange, htube, hlt⟩

end GaussianLQG
