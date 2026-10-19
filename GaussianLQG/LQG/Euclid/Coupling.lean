import GaussianLQG.LQG.Tube
import GaussianLQG.Energy.All
import GaussianLQG.Field.Pairing

/-!
# Pathwise energy bounds for Lemma `lem:energy-approx`

Let `Q(ν, λ) = ℰ(ν,ν) - 2ℰ(ν,λ) + ℰ(λ,λ) = ‖ν - λ‖_*²` for regular `ν, λ`.

* `energy_quad_le_two_mul`: `Q(ν, λ) ≤ 2ℰ(ν,ν) + 2ℰ(λ,λ)` (from the frame identity:
  `Q = ∑_j (a_j - b_j)²` with `a_j = ∫ e_j dν`, `b_j = ∫ e_j dλ`); this is the bound "off the good
  event" `‖ν_P - λ‖_* ≤ Θ + Λ_{K,δ}` of the blueprint, with constant `√2`.
* `energy_segMeasure_le_of_mem`: `ℰ(λ_{z,w}, λ_{z,w}) ≤ 2 log max(1, 2/δ) + 2 + 2 log R₁` for
  `z, w ∈ B̄_{R₁-1}(0)` with `|z - w| ≥ δ` (Lemma `lem:energy-bound`); so `Λ_{K,δ} < ∞`.
* `energy_quad_le_of_tube` (blueprint Lemma `lem:energy-approx`, on the good event): if the
  Euclidean error on `B̄_{4R₁}(0)` is at most `E ≤ ε₀`, then for a constant-speed geodesic `η`
  between `z, w ∈ K` with `|z - w| ≥ δ`, whose length measure is regular with
  `ν_η(B_r(u)) ≤ B_ν r^{1/2}`, `Q(ν_η, λ_{z,w}) ≤ 2 (1 + B_ν + 2/δ) (8 R₁ E)^{1/6}`. Proof: the tube
  lemma bounds the displacement of the coupling `t ↦ (η(t), (1-t) z + t w)` by
  `η₀ = (8 R₁ E)^{1/2} < 1`; Lemma `lem:coupling` with `α = 1/2` and `ρ = η₀^{2/3}` gives
  `Q ≤ 2η₀^{1/3} + 2(B_ν + 2/δ) η₀^{1/3}`. If `η₀ = 0` then `ν_η = λ_{z,w}` and `Q = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-- `‖μ - ν‖_*² ≤ 2‖μ‖_*² + 2‖ν‖_*²`, from the frame identity. -/
theorem energy_quad_le_two_mul {e : ℕ → ℂ → ℝ} (he : IsGFFFrame e) {μ ν : Measure ℂ}
    (hμ : IsRegular μ) (hν : IsRegular ν) :
    energy μ μ - 2 * energy μ ν + energy ν ν ≤ 2 * energy μ μ + 2 * energy ν ν := by
  have h1 := he.2.2 μ μ hμ hμ
  have h2 := he.2.2 μ ν hμ hν
  have h3 := he.2.2 ν ν hν hν
  have hL := (h1.sub (h2.mul_left 2)).add h3
  have hR := (h1.mul_left 2).add (h3.mul_left 2)
  refine hasSum_le (fun j => ?_) hL hR
  have := sq_nonneg ((∫ z, e j z ∂μ) + ∫ z, e j z ∂ν)
  nlinarith

/-- `λ_{z,w}(B_r(u)) ≤ (2/δ) r^{1/2}` for `|z - w| ≥ δ > 0` and `0 < r ≤ 1`. -/
theorem segMeasure_ball_toReal_le_rpow {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hzw : δ ≤ ‖z - w‖)
    (u : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (segMeasure z w (Metric.ball u r)).toReal ≤ 2 / δ * r ^ (1 / 2 : ℝ) := by
  have hzw' : z ≠ w := fun h => by
    rw [h, sub_self, norm_zero] at hzw
    linarith
  have hn : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw')
  have h1 := segMeasure_ball_toReal_le hzw' u hr.le
  have h2 : 2 / ‖z - w‖ ≤ 2 / δ := div_le_div_of_nonneg_left zero_le_two hδ hzw
  have h3 : r ≤ r ^ (1 / 2 : ℝ) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  calc (segMeasure z w (Metric.ball u r)).toReal ≤ 2 / ‖z - w‖ * r := h1
    _ ≤ 2 / δ * r := mul_le_mul_of_nonneg_right h2 hr.le
    _ ≤ 2 / δ * r ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **`Λ_{K,δ} < ∞`** (Lemma `lem:energy-bound`): for `z, w ∈ B̄_{R₁-1}(0)` with `|z - w| ≥ δ > 0`,
`λ_{z,w}` is regular and `ℰ(λ_{z,w}, λ_{z,w}) ≤ 2 log max(1, 2/δ) + 2 + 2 log R₁`. -/
theorem energy_segMeasure_le_of_mem {R₁ δ : ℝ} (hR₁ : 1 ≤ R₁) (hδ : 0 < δ) {z w : ℂ}
    (hz : ‖z‖ ≤ R₁ - 1) (hw : ‖w‖ ≤ R₁ - 1) (hzw : δ ≤ ‖z - w‖) :
    IsRegular (segMeasure z w) ∧
      energy (segMeasure z w) (segMeasure z w) ≤
        2 * Real.log (max 1 (2 / δ)) + 2 + 2 * Real.log R₁ := by
  refine isRegular_and_energy_le hR₁ ?_ (le_max_left _ _) fun u r hr hr1 => ?_
  · refine measure_mono_null (compl_subset_compl.2 (Metric.closedBall_subset_closedBall ?_))
      (segMeasure_compl_closedBall z w)
    exact max_le (by linarith) (by linarith)
  · refine (segMeasure_ball_toReal_le_rpow hδ hzw u hr hr1).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- If `η t = (1-t) z + t w` for all `t`, the length measure of `η` is `λ_{z,w}`. -/
theorem lengthMeasure_eq_segMeasure {η : C(unitInterval, ℂ)} {z w : ℂ}
    (h : ∀ t : unitInterval, η t = ((1 - t : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w) :
    lengthMeasure η = segMeasure z w := by
  unfold lengthMeasure segMeasure
  refine Measure.map_congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => ?_)
  dsimp only
  rw [Set.projIcc_of_mem zero_le_one ht]
  exact h ⟨t, ht⟩

/-- **Blueprint Lemma `lem:energy-approx`, the good event** (deterministic form). Let `D` be a
continuous metric, `R₁ ≥ 1`, `K ⊆ B̄_{R₁-1}(0)`, and suppose `|e^{-b} D(x,y) - |x - y|| ≤ E` on
`B̄_{4R₁}(0)` with `E ≤ min(R₁/4, 1/(16R₁))`. Let `z, w ∈ K` with `|z - w| ≥ δ > 0` and `η` a
constant-speed geodesic from `z` to `w` whose length measure is regular with
`ν_η(B_r(u)) ≤ B_ν r^{1/2}` (`0 < r ≤ 1`). Then
`‖ν_η - λ_{z,w}‖_*² ≤ 2 (1 + B_ν + 2/δ) (8 R₁ E)^{1/6}`. -/
theorem energy_quad_le_of_tube {D : ContMetric} {b R₁ E δ Bν : ℝ} {K : Set ℂ} (hR₁ : 1 ≤ R₁)
    (hK : K ⊆ Metric.closedBall 0 (R₁ - 1))
    (hE : ∀ x ∈ Metric.closedBall (0 : ℂ) (4 * R₁), ∀ y ∈ Metric.closedBall (0 : ℂ) (4 * R₁),
      |Real.exp (-b) * D.1 (x, y) - ‖x - y‖| ≤ E)
    (hE₀ : E ≤ min (R₁ / 4) (1 / (16 * R₁))) (hδ : 0 < δ) (hBν : 0 ≤ Bν)
    {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) (hzw : δ ≤ ‖z - w‖) {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 D z w η) (hreg : IsRegular (lengthMeasure η))
    (hball : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (lengthMeasure η (Metric.ball u r)).toReal ≤ Bν * r ^ (1 / 2 : ℝ)) :
    energy (lengthMeasure η) (lengthMeasure η) - 2 * energy (lengthMeasure η) (segMeasure z w) +
        energy (segMeasure z w) (segMeasure z w) ≤
      2 * (1 + Bν + 2 / δ) * (8 * R₁ * E) ^ (1 / 6 : ℝ) := by
  obtain ⟨-, htube, hlt⟩ := tube_of_isGeod01 hR₁ hK hE hE₀ hz hw hη
  have hzw' : z ≠ w := fun h => by
    rw [h, sub_self, norm_zero] at hzw
    linarith
  have hzR : z ∈ Metric.closedBall (0 : ℂ) (4 * R₁) := by
    have := mem_closedBall_zero_iff.1 (hK hz)
    exact mem_closedBall_zero_iff.2 (by linarith)
  have hE0 : 0 ≤ E := by
    have h := hE z hzR z hzR
    rwa [D.2.self_eq_zero, mul_zero, sub_self, norm_zero, sub_zero, abs_zero] at h
  set η0 := Real.sqrt (8 * R₁ * E) with hη0_def
  have hη0 : 0 ≤ η0 := Real.sqrt_nonneg _
  have hpow : η0 ^ (1 / 3 : ℝ) = (8 * R₁ * E) ^ (1 / 6 : ℝ) := by
    rw [hη0_def, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  have hRHS : 0 ≤ 2 * (1 + Bν + 2 / δ) * (8 * R₁ * E) ^ (1 / 6 : ℝ) := by positivity
  rcases hη0.eq_or_lt with h0 | hpos
  · -- `η₀ = 0`: the geodesic is the segment
    have hseg : ∀ t : unitInterval, η t = ((1 - t : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w := by
      intro t
      have h := htube t
      rw [← h0] at h
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
    rw [lengthMeasure_eq_segMeasure hseg]
    linarith
  · -- the coupling `t ↦ (η(t), (1-t) z + t w)` has displacement at most `η₀`
    have hsreg := isRegular_segMeasure hzw'
    set F : ℝ → ℂ × ℂ := fun t =>
      (η (projIcc 0 1 zero_le_one t), ((1 - t : ℝ) : ℂ) * z + (t : ℂ) * w) with hF_def
    have hFc : Continuous F :=
      (continuous_comp_projIcc η).prodMk (by fun_prop)
    set P : Measure (ℂ × ℂ) := (volume.restrict (Icc (0 : ℝ) 1)).map F with hP_def
    have hP1 : P.map Prod.fst = lengthMeasure η := by
      rw [hP_def, Measure.map_map measurable_fst hFc.measurable]
      rfl
    have hP2 : P.map Prod.snd = segMeasure z w := by
      rw [hP_def, Measure.map_map measurable_snd hFc.measurable]
      rfl
    have hmeas : MeasurableSet {p : ℂ × ℂ | η0 < ‖p.1 - p.2‖} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hPη : P {p : ℂ × ℂ | η0 < ‖p.1 - p.2‖} = 0 := by
      rw [hP_def, Measure.map_apply hFc.measurable hmeas,
        Measure.restrict_apply' measurableSet_Icc]
      refine measure_mono_null (fun t ht => ?_) measure_empty
      obtain ⟨h1, h2⟩ := ht
      simp only [mem_preimage, mem_ofPred_eq, hF_def] at h1
      rw [Set.projIcc_of_mem zero_le_one h2] at h1
      exact absurd (htube ⟨t, h2⟩) (not_le.2 h1)
    have hρ : 0 < η0 ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hpos _
    have hρ1 : η0 ^ (2 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hη0 hlt.le (by norm_num)
    have hc := energy_sub_le_of_coupling hreg hsreg (α := 1 / 2) (by norm_num) hBν
      (by positivity : (0 : ℝ) ≤ 2 / δ) hball
      (fun u r hr hr1 => segMeasure_ball_toReal_le_rpow hδ hzw u hr hr1) hP1 hP2 hPη hρ hρ1
    have e1 : η0 / η0 ^ (2 / 3 : ℝ) = η0 ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_sub hpos (1 : ℝ) (2 / 3)
      rw [Real.rpow_one] at h
      rw [← h]
      norm_num
    have e2 : (η0 ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) = η0 ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_mul hη0]
      norm_num
    calc energy (lengthMeasure η) (lengthMeasure η) -
          2 * energy (lengthMeasure η) (segMeasure z w) + energy (segMeasure z w) (segMeasure z w)
        ≤ 2 * η0 / η0 ^ (2 / 3 : ℝ) + (Bν + 2 / δ) * (η0 ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2) :=
          hc
      _ = 2 * (1 + Bν + 2 / δ) * η0 ^ (1 / 3 : ℝ) := by
          rw [mul_div_assoc, e1, e2]
          ring
      _ = 2 * (1 + Bν + 2 / δ) * (8 * R₁ * E) ^ (1 / 6 : ℝ) := by rw [hpow]

end GaussianLQG
