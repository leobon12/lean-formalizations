import HigherDimLQGMetric.Proper.Geometry

/-!
# High-probability barriers on distant Euclidean spheres

The sharp drift dominates sphere-average fluctuations. Thus a distant sphere has uniformly
large distance from the origin, relative to the metric scale at the base radius.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem proper_sNorm_pos (ξ Q : ℝ) (h : DistRd d) {r : ℝ} (hr : 0 < r) :
    0 < sNorm ξ Q h r 0 := by
  unfold sNorm
  exact mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)

/-- On the good field event, the sharp normalizer grows by at least half its deterministic
logarithmic drift. -/
theorem proper_sNorm_growth {ξ Q : ℝ} (hξ : 0 < ξ)
    (h : DistRd d) {R : ℝ} (hR : 0 < R) (n : ℕ)
    (hgood : sphereAvg h R 0 - sphereAvg h (Real.exp n * R) 0 < Q / 2 * n) :
    sNorm ξ Q h R 0 * Real.exp (ξ * Q / 2 * n) <
      sNorm ξ Q h (Real.exp n * R) 0 := by
  rw [proper_sNorm_exp_mul ξ Q h hR n]
  have harg : ξ * Q / 2 * (n : ℝ) <
      ξ * Q * n + ξ * (sphereAvg h (Real.exp n * R) 0 - sphereAvg h R 0) := by
    have hh := mul_lt_mul_of_pos_left hgood hξ
    nlinarith
  exact mul_lt_mul_of_pos_left (Real.exp_strictMono harg)
    (proper_sNorm_pos ξ Q h hR)

/-- A good normalized distance and a good sphere-average increment imply a large original
distance, pointwise on the unit sphere. -/
theorem proper_dist_big_of_good {ξ Q a B : ℝ} (hξ : 0 < ξ)
    (ha : 0 < a) (h : DistRd d) (D : DistRd d → ContMetric d)
    {R : ℝ} (hR : 0 < R) (n : ℕ)
    (hB : B < a * Real.exp (ξ * Q / 2 * n))
    (hfield : sphereAvg h R 0 - sphereAvg h (Real.exp n * R) 0 < Q / 2 * n)
    (u : Rd d)
    (hmetric : a < normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) h
      (Real.exp n * R) (0, u)) :
    B * sNorm ξ Q h R 0 < (D h).1 (0, (Real.exp n * R) • u) := by
  have hRbig : 0 < Real.exp (n : ℝ) * R :=
    mul_pos (Real.exp_pos _) hR
  have hpR := proper_sNorm_pos ξ Q h hR
  have hpBig := proper_sNorm_pos ξ Q h hRbig
  have hnorm := proper_sNorm_growth hξ h hR n hfield
  have heq := proper_normalized_mul ξ Q D h hRbig 0 u
  rw [smul_zero] at heq
  calc
    B * sNorm ξ Q h R 0
        < (a * Real.exp (ξ * Q / 2 * n)) * sNorm ξ Q h R 0 :=
          mul_lt_mul_of_pos_right hB hpR
    _ = a * (sNorm ξ Q h R 0 * Real.exp (ξ * Q / 2 * n)) := by ring
    _ < a * sNorm ξ Q h (Real.exp n * R) 0 :=
      mul_lt_mul_of_pos_left hnorm ha
    _ = sNorm ξ Q h (Real.exp n * R) 0 * a := by ring
    _ < (D h).1 (0, (Real.exp n * R) • u) := by
      rw [← heq]
      exact mul_lt_mul_of_pos_left hmetric hpBig

/-- Rescale a point on a Euclidean sphere to the unit sphere. -/
theorem proper_exists_unit_sphere {r : ℝ} (hr : 0 < r) {v : Rd d} (hv : ‖v‖ = r) :
    ∃ u : Rd d, ‖u‖ = 1 ∧ r • u = v := by
  refine ⟨r⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), hv]
    exact inv_mul_cancel₀ hr.ne'
  · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- At a suitably distant sphere, all metric distances from the origin beat any fixed multiple
of the base normalizer, except with an arbitrarily small probability uniform in the base radius. -/
theorem proper_exists_high_sphere (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (B δ : ℝ) (hδ : 0 < δ) (tMin : ℝ) :
    ∃ t : ℝ, tMin < t ∧ 0 < t ∧ ∀ R : ℝ, 0 < R →
      P {ω | ¬ ∀ v : Rd d, ‖v‖ = t * R →
        B * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (0, v)} < ENNReal.ofReal δ := by
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨a, ha, hlow⟩ := proper_exists_sphere_lower P h hD hh
    ((ENNReal.ofReal_pos.mpr hhalf))
  obtain ⟨n, hn, hnt, hB, hfield⟩ := proper_exists_large_step P h hd hh hξ hQ ha hhalf
    tMin (B := B)
  refine ⟨Real.exp n, hnt, Real.exp_pos _, fun R hR => ?_⟩
  let E₁ : Set Ω := {ω | ∃ u ∈ Metric.sphere (0 : Rd d) 1,
    normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω)
      (Real.exp n * R) (0, u) ≤ a}
  let E₂ : Set Ω := {ω | Q / 2 * n ≤ sphereAvg (h ω) R 0 -
    sphereAvg (h ω) (Real.exp n * R) 0}
  have hsubset : {ω | ¬ ∀ v : Rd d, ‖v‖ = Real.exp n * R →
      B * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (0, v)} ⊆ E₁ ∪ E₂ := by
    intro ω hω
    by_contra hnot
    have hnot₁ : ω ∉ E₁ := fun he => hnot (Or.inl he)
    have hnot₂ : ω ∉ E₂ := fun he => hnot (Or.inr he)
    push Not at hω
    obtain ⟨v, hv, hvD⟩ := hω
    obtain ⟨u, hu, huv⟩ := proper_exists_unit_sphere
      (mul_pos (Real.exp_pos _) hR) hv
    have hu' : u ∈ Metric.sphere (0 : Rd d) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hu
    have hmetric : a < normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω)
        (Real.exp n * R) (0, u) := lt_of_not_ge (fun hle => hnot₁ ⟨u, hu', hle⟩)
    have hfield' : sphereAvg (h ω) R 0 - sphereAvg (h ω) (Real.exp n * R) 0 <
        Q / 2 * n := lt_of_not_ge hnot₂
    have hdist := proper_dist_big_of_good hξ ha (h ω) D hR n hB hfield' u hmetric
    rw [huv] at hdist
    exact (not_lt_of_ge hvD) hdist
  have hRbig : 0 < Real.exp (n : ℝ) * R := mul_pos (Real.exp_pos _) hR
  have hE₁ : P E₁ < ENNReal.ofReal (δ / 2) := hlow _ hRbig
  have hE₂ : P E₂ < ENNReal.ofReal (δ / 2) := hfield R hR
  calc
    P {ω | ¬ ∀ v : Rd d, ‖v‖ = Real.exp n * R →
        B * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (0, v)}
        ≤ P (E₁ ∪ E₂) := measure_mono hsubset
    _ ≤ P E₁ + P E₂ := measure_union_le _ _
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add hE₁ hE₂
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

end HigherDimLQGMetric
