import HigherDimLQGMetric.Sharp.GoodScalesFinite
import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.Sharp.ScaleIndices

/-!
# Good scales at every translated grid point

MA6 P4, with `ShellInputA1` exactly in the form supplied by the source's
Appendix A. The event measurability uses `fieldSigma0` modulo constants.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

private theorem w2_exp_dyadic_block_bound {m n k : ℕ} {ε : ℝ}
    (_hε0 : 0 < ε) (hnk : n + 1 = k) (hk : (1 / 2 : ℝ) ^ k < ε) :
    Real.exp (-((m : ℝ) * Real.log 2) * n) ≤ (2 : ℝ) ^ m * ε ^ m := by
  have hlog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have heq : Real.exp (-((m : ℝ) * Real.log 2) * n) =
      ((1 / 2 : ℝ) ^ n) ^ m := by
    calc
      Real.exp (-((m : ℝ) * Real.log 2) * n) =
          Real.exp (((m * n : ℕ) : ℝ) * (-Real.log 2)) := by
            congr 1
            push_cast
            ring_nf
      _ = (Real.exp (-Real.log 2)) ^ (m * n) := Real.exp_nat_mul _ _
      _ = (1 / 2 : ℝ) ^ (m * n) := by rw [hlog]
      _ = ((1 / 2 : ℝ) ^ n) ^ m := by rw [← pow_mul, mul_comm]
  have hqn : (1 / 2 : ℝ) ^ n ≤ 2 * ε := by
    have hpow : (1 / 2 : ℝ) ^ k = ((1 / 2 : ℝ) ^ n) / 2 := by
      rw [← hnk, pow_succ]
      ring_nf
    linarith
  rw [heq]
  calc
    ((1 / 2 : ℝ) ^ n) ^ m ≤ (2 * ε) ^ m :=
      pow_le_pow_left₀ (by positivity) hqn m
    _ = (2 : ℝ) ^ m * ε ^ m := mul_pow 2 ε m

private theorem w2_radius_eq (𝕣 : ℝ) (j : ℕ) :
    𝕣 * (1 / 2 : ℝ) ^ j = 𝕣 / 2 ^ j := by
  rw [one_div_pow]
  ring_nf

/-- MA6 P4: every point of the shell grid has a good dyadic radius with polynomially high
probability. The probability threshold depends only on `d` and `M`. -/
theorem w2_goodScales_shifted {d : ℕ} (hA1 : ShellInputA1 d) (hd : 3 ≤ d)
    {M : ℝ} (hM : 0 < M) :
    ∃ p : ℝ, p < 1 ∧ ∃ K : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ E : Rd d → ℝ → Set Ω,
        (∀ z r, 0 < r → AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) (E z r)) →
        (∀ z r, 0 < r → ENNReal.ofReal p ≤ P (E z r)) →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ z : Rd d, ∀ ε ∈ Ioo (0 : ℝ) 1,
        P {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
          Metric.ball (0 : Rd d) (𝕣 / ε),
          ∀ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k → 𝕣 / 2 ^ k ≤ ε * 𝕣 →
            ω ∉ E (z + w) (𝕣 / 2 ^ k)} ≤ ENNReal.ofReal (K * ε ^ M) := by
  classical
  let t : ℕ := ⌈M⌉₊ + 1
  let m : ℕ := t + 3 * d
  let A : ℝ := m * Real.log 2
  have hm0 : 0 < m := by dsimp [m, t]; omega
  have hA : 0 < A := mul_pos (by exact_mod_cast hm0) (Real.log_pos (by norm_num))
  obtain ⟨p, hp, Hp⟩ := goodScales_finite hA1 hA
  let K : ℝ := (25 * d : ℝ) ^ d * 2 ^ m + (8 : ℝ) ^ M
  refine ⟨p, hp, K, ?_⟩
  intro Ω _ P _ h hh E hE hpE 𝕣 h𝕣 z ε hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have hεM : 0 < ε ^ M := Real.rpow_pos_of_pos hε0 _
  have hKsmall : 0 ≤ (25 * d : ℝ) ^ d * 2 ^ m := by positivity
  by_cases hε8 : ε < 1 / 8
  · obtain ⟨k, n, hnk, hn, hk, -, hblock⟩ := exists_dyadic_block hε0 hε8
    let s : ℝ := ε ^ 2 * 𝕣 / (10 * d)
    let B : ℝ := 𝕣 / ε
    let N : ℕ := ⌈B / s⌉₊ + 1
    let S : Finset (Rd d) := shellGridBox d N s
    let F : Finset (Rd d) := S.image (fun w => z + w)
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hs : 0 < s := by dsimp [s]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hS : gridPts s ∩ Metric.ball (0 : Rd d) B ⊆ (S : Set (Rd d)) :=
      grid_ball_subset_shellGridBox hs hB
    have hF : ∀ w ∈ gridPts s ∩ Metric.ball (0 : Rd d) B, z + w ∈ F := by
      intro w hw
      exact Finset.mem_image.mpr ⟨w, hS hw, rfl⟩
    let r : ℕ → ℝ := fun i => 𝕣 * (1 / 2 : ℝ) ^ (k + i)
    have hr : ∀ i, 0 < r i := fun i => by dsimp [r]; positivity
    have hratio : ∀ i, r (i + 1) ≤ (1 / 2 : ℝ) * r i := by
      intro i
      dsimp [r]
      have he : k + (i + 1) = (k + i) + 1 := by omega
      rw [he, pow_succ]
      apply le_of_eq
      ring_nf
    have hE' : ∀ w ∈ F, ∀ i,
        AEEventIn P (fieldSigma0 h (ann w ((1 / 4) * r i) (4 * r i))) (E w (r i)) := by
      intro w _ i
      convert hE w (r i) (hr i) using 1
      ring_nf
    have hpE' : ∀ w ∈ F, ∀ i, ENNReal.ofReal p ≤ P (E w (r i)) := by
      intro w _ i
      exact hpE w (r i) (hr i)
    have hfinite := Hp P h hh F r hr hratio E hE' hpE' n hn
    have hsub : {ω | ∃ w ∈ gridPts s ∩ Metric.ball (0 : Rd d) B,
        ∀ j : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ j → 𝕣 / 2 ^ j ≤ ε * 𝕣 →
          ω ∉ E (z + w) (𝕣 / 2 ^ j)} ⊆
        {ω | ∃ w ∈ F, ∀ i ∈ Finset.range n, ω ∉ E w (r i)} := by
      intro ω hω
      obtain ⟨w, hw, hbad⟩ := hω
      refine ⟨z + w, hF w hw, ?_⟩
      intro i hi
      have hii : i < n := Finset.mem_range.mp hi
      have hbi := hblock i hii
      have hre : r i = 𝕣 / 2 ^ (k + i) := w2_radius_eq 𝕣 (k + i)
      have hlow : ε ^ 2 * 𝕣 ≤ r i := by
        simpa only [r, mul_comm] using mul_le_mul_of_nonneg_right hbi.1 h𝕣.le
      have hupp : r i ≤ ε * 𝕣 := by
        simpa only [r, mul_comm] using mul_le_mul_of_nonneg_right hbi.2 h𝕣.le
      rw [hre] at hlow hupp ⊢
      exact hbad (k + i) hlow hupp
    have hcount : (F.card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d := by
      have hcard : F.card ≤ S.card := Finset.card_image_le
      calc
        (F.card : ℝ) * ε ^ (3 * d) ≤ (S.card : ℝ) * ε ^ (3 * d) := by
          gcongr
        _ ≤ (25 * d : ℝ) ^ d := card_shellGridBox_scaled hd h𝕣 hε0 hε1
    have htM : M ≤ (t : ℝ) := by
      have hceil : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
      dsimp [t]
      push_cast
      linarith
    have hpow : ε ^ t ≤ ε ^ M := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le htM
    have hexp : Real.exp (-A * n) ≤ (2 : ℝ) ^ m * ε ^ m := by
      exact w2_exp_dyadic_block_bound hε0 hnk hk
    have hreal : (F.card : ℝ) * Real.exp (-A * n) ≤
        ((25 * d : ℝ) ^ d * 2 ^ m) * ε ^ M := by
      calc
        (F.card : ℝ) * Real.exp (-A * n) ≤
            (F.card : ℝ) * ((2 : ℝ) ^ m * ε ^ m) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = ((F.card : ℝ) * ε ^ (3 * d)) * 2 ^ m * ε ^ t := by
          dsimp [m]
          rw [pow_add]
          ring_nf
        _ ≤ ((25 * d : ℝ) ^ d * 2 ^ m) * ε ^ t := by
          gcongr
        _ ≤ ((25 * d : ℝ) ^ d * 2 ^ m) * ε ^ M :=
          mul_le_mul_of_nonneg_left hpow hKsmall
    have hK : ((25 * d : ℝ) ^ d * 2 ^ m) * ε ^ M ≤ K * ε ^ M := by
      dsimp [K]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hεM.le
    have hcast : (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * n)) =
        ENNReal.ofReal ((F.card : ℝ) * Real.exp (-A * n)) := by
      rw [ENNReal.ofReal_mul (p := (F.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    change P {ω | ∃ w ∈ gridPts s ∩ Metric.ball (0 : Rd d) B,
        ∀ j : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ j → 𝕣 / 2 ^ j ≤ ε * 𝕣 →
          ω ∉ E (z + w) (𝕣 / 2 ^ j)} ≤ ENNReal.ofReal (K * ε ^ M)
    calc
      P _ ≤ P {ω | ∃ w ∈ F, ∀ i ∈ Finset.range n, ω ∉ E w (r i)} := measure_mono hsub
      _ ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-A * n)) := hfinite
      _ = ENNReal.ofReal ((F.card : ℝ) * Real.exp (-A * n)) := hcast
      _ ≤ ENNReal.ofReal (((25 * d : ℝ) ^ d * 2 ^ m) * ε ^ M) :=
        ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal (K * ε ^ M) := ENNReal.ofReal_le_ofReal hK
  · have hε8' : 1 / 8 ≤ ε := le_of_not_gt hε8
    have h8 : 1 ≤ (8 * ε) ^ M :=
      Real.one_le_rpow (by nlinarith) hM.le
    have hlarge : 1 ≤ K * ε ^ M := by
      have heq : (8 * ε) ^ M = (8 : ℝ) ^ M * ε ^ M :=
        Real.mul_rpow (by norm_num) hε0.le
      rw [heq] at h8
      dsimp [K]
      nlinarith [mul_nonneg hKsmall hεM.le]
    calc
      P _ ≤ 1 := by
        exact (measure_mono (Set.subset_univ _)).trans (by simp)
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal (K * ε ^ M) := ENNReal.ofReal_le_ofReal hlarge

end HigherDimLQGMetric
