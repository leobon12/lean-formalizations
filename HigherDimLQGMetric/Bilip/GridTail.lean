import HigherDimLQGMetric.Bilip.ScaleBlock

/-! Polynomial failure bound for the finite shell grid, from `l7c_metricShell`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- Every grid point has a good radius between `ε²` and `ε`, except with
probability at most `K ε²`. The coefficient and threshold depend only on `d`. -/
theorem bilip_gridTail {d : ℕ} (hd : 2 ≤ d) :
    ∃ p K : ℝ, 0 < p ∧ p < 1 ∧ 0 ≤ K ∧
      ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (D₁ D₂ : Ω → ContMetric d), IsNormalizedLGF h P →
        IsXiAdditiveRd ξ P h D₁ D₂ →
      ∀ E : Rd d → ℝ → Set Ω,
        (∀ z r, 0 < r → MeasurableSet[
          fieldSigmaRd (fun ω => l7b_recenter (h ω) r z)
            (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
          famSigmaRd (rescFam ξ h D₁ z r)
            (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
          famSigmaRd (rescFam ξ h D₂ z r)
            (shellOpen z ((1 / 4) * r) (4 * r))] (E z r)) →
        (∀ z r, 0 < r → ENNReal.ofReal p ≤ P (E z r)) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 64 →
        P {ω | ∃ w ∈ gridPts (ε ^ 2 / (10 * d)) ∩
          ball (0 : Rd d) (1 / ε),
          ∀ k : ℕ, ε ^ 2 ≤ 1 / 2 ^ k → 1 / 2 ^ k ≤ ε →
            ω ∉ E w (1 / 2 ^ k)} ≤ ENNReal.ofReal (K * ε ^ 2) := by
  classical
  let m : ℕ := 3 * d + 2
  let A : ℝ := ((5 * m : ℕ) : ℝ) * Real.log 2
  have hA : 0 < A := by dsimp [A, m]; positivity
  obtain ⟨p₀, hp₀, htail⟩ := l7c_metricShell d hd
    (1 / 4) 4 (1 / 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) A (1 / 2) hA (by norm_num) (by norm_num)
  let p : ℝ := max p₀ (1 / 2)
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hp1 : p < 1 := max_lt hp₀ (by norm_num)
  let K : ℝ := (25 * d : ℝ) ^ d * (2 : ℝ) ^ (5 * m)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨p, K, hp, hp1, hK, ?_⟩
  intro ξ Ω mΩ P hProb h D₁ D₂ hh hxi E hE hpE ε hε hε64
  obtain ⟨k, N, hN, hkbound, hkε, hblock⟩ := bilip_exists_sparse_block hε hε64
  let s : ℝ := ε ^ 2 / (10 * d)
  let B : ℝ := 1 / ε
  let F : Finset (Rd d) := shellGridBox d (⌈B / s⌉₊ + 1) s
  let r : ℕ → ℝ := fun i => (1 / 2 : ℝ) ^ (k + 5 * i)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < s := by dsimp [s]; positivity
  have hF : gridPts s ∩ ball (0 : Rd d) B ⊆ (F : Set (Rd d)) :=
    grid_ball_subset_shellGridBox hs (by dsimp [B]; positivity)
  have hr : ∀ i, 0 < r i := fun i => by dsimp [r]; positivity
  have hratio : ∀ i, r (i + 1) ≤ (1 / 32 : ℝ) * r i := by
    intro i
    dsimp [r]
    have he : k + 5 * (i + 1) = (k + 5 * i) + 5 := by omega
    rw [he, pow_add]
    norm_num
    apply le_of_eq
    ring
  have hprob (w : Rd d) : ∀ i, ENNReal.ofReal p₀ ≤ P (E w (r i)) := by
    intro i
    exact (ENNReal.ofReal_le_ofReal (le_max_left _ _)).trans
      (hpE w (r i) (hr i))
  have hone (w : Rd d) :
      P {ω | ∀ i ∈ Finset.range N, ω ∉ E w (r i)} ≤
        ENNReal.ofReal (Real.exp (-A * N)) := by
    have hlocal (i : ℕ) : MeasurableSet[
        fieldSigmaRd (fun ω => l7b_recenter (h ω) (r i) w)
          (shellOpen w ((1 / 4) * r i) (4 * r i)) ⊔
        famSigmaRd (rescFam ξ h D₁ w (r i))
          (shellOpen w ((1 / 4) * r i) (4 * r i)) ⊔
        famSigmaRd (rescFam ξ h D₂ w (r i))
          (shellOpen w ((1 / 4) * r i) (4 * r i))] (E w (r i)) :=
      hE w (r i) (hr i)
    have H := htail ξ P h D₁ D₂ hh hxi w r hr hratio
      (fun i => E w (r i)) hlocal (hprob w) N
    refine (measure_mono ?_).trans H
    intro ω hω
    change (((Finset.range N).filter (fun i => ω ∈ E w (r i))).card : ℝ) <
      (1 / 2 : ℝ) * N
    have hempty : (Finset.range N).filter (fun i => ω ∈ E w (r i)) = ∅ := by
      exact Finset.filter_eq_empty_iff.mpr (fun i hi => hω i hi)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hfinite :
      P {ω | ∃ w ∈ F, ∀ i ∈ Finset.range N, ω ∉ E w (r i)} ≤
        (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * N)) := by
    have hset : {ω | ∃ w ∈ F, ∀ i ∈ Finset.range N, ω ∉ E w (r i)} =
        ⋃ w ∈ F, {ω | ∀ i ∈ Finset.range N, ω ∉ E w (r i)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨w, hw, h⟩
        exact ⟨w, hw, h⟩
      · rintro ⟨w, hw, h⟩
        exact ⟨w, hw, h⟩
    rw [hset]
    calc
      P _ ≤ ∑ w ∈ F, P {ω | ∀ i ∈ Finset.range N, ω ∉ E w (r i)} :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ F, ENNReal.ofReal (Real.exp (-A * N)) :=
        Finset.sum_le_sum fun w _ => hone w
      _ = (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * N)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hsubset : {ω | ∃ w ∈ gridPts s ∩ ball (0 : Rd d) B,
        ∀ j : ℕ, ε ^ 2 ≤ 1 / 2 ^ j → 1 / 2 ^ j ≤ ε → ω ∉ E w (1 / 2 ^ j)} ⊆
      {ω | ∃ w ∈ F, ∀ i ∈ Finset.range N, ω ∉ E w (r i)} := by
    intro ω hω
    obtain ⟨w, hw, hbad⟩ := hω
    refine ⟨w, hF hw, ?_⟩
    intro i hi
    have hbi := hblock i (Finset.mem_range.mp hi)
    have hre : r i = 1 / 2 ^ (k + 5 * i) := by
      dsimp [r]
      rw [one_div_pow]
    rw [hre]
    exact hbad (k + 5 * i)
      (by simpa only [one_div_pow] using hbi.1)
      (by simpa only [one_div_pow] using hbi.2)
  have hcount : (F.card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d := by
    simpa only [F, B, s, mul_one] using bilip_card_shellGridBox_scaled hd
      (𝕣 := 1) (by norm_num) hε (by linarith : ε < 1)
  have hexp : Real.exp (-A * N) ≤ (2 : ℝ) ^ (5 * m) * ε ^ m :=
    by simpa only [A, neg_mul] using (bilip_exp_sparse_bound (m := m) hε hkbound hkε)
  have hreal : (F.card : ℝ) * Real.exp (-A * N) ≤ K * ε ^ 2 := by
    calc
      (F.card : ℝ) * Real.exp (-A * N) ≤
          (F.card : ℝ) * ((2 : ℝ) ^ (5 * m) * ε ^ m) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((F.card : ℝ) * ε ^ (3 * d)) * (2 : ℝ) ^ (5 * m) * ε ^ 2 := by
        dsimp [m]
        rw [pow_add]
        ring
      _ ≤ ((25 * d : ℝ) ^ d * (2 : ℝ) ^ (5 * m)) * ε ^ 2 := by
        gcongr
      _ = K * ε ^ 2 := rfl
  have hcast : (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * N)) =
      ENNReal.ofReal ((F.card : ℝ) * Real.exp (-A * N)) := by
    rw [ENNReal.ofReal_mul (p := (F.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
  change P {ω | ∃ w ∈ gridPts s ∩ ball (0 : Rd d) B,
        ∀ j : ℕ, ε ^ 2 ≤ 1 / 2 ^ j → 1 / 2 ^ j ≤ ε →
          ω ∉ E w (1 / 2 ^ j)} ≤ ENNReal.ofReal (K * ε ^ 2)
  calc
    P _ ≤ P {ω | ∃ w ∈ F, ∀ i ∈ Finset.range N, ω ∉ E w (r i)} :=
      measure_mono hsubset
    _ ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * N)) := hfinite
    _ = ENNReal.ofReal ((F.card : ℝ) * Real.exp (-A * N)) := hcast
    _ ≤ ENNReal.ofReal (K * ε ^ 2) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGMetric
