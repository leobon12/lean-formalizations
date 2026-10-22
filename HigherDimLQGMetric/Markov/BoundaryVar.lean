import HigherDimLQGMetric.Markov.BoundaryEnergy

/-! Vanishing (L^2) variance of a mean-zero boundary pairing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The (L^2) random pairing of the recentered boundary error converges to zero. The
quadratic logarithmic energy estimate turns the (L^1) cutoff error into a variance bound. -/
theorem markov_boundaryPair_L2_tendsto_zero (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (φ ρ : TestRd d) (hρ : ∫ x, ρ x = 1)
    (hnull : volume (frontier (V : Set (Rd d))) = 0) :
    Tendsto (fun n : ℕ =>
      (markov_memLp_pair hh (subMean hρ (markovBoundaryError V φ n))).toLp
        (markovPair h (subMean hρ (markovBoundaryError V φ n))))
      atTop (𝓝 0) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨M, D, hφ⟩ := exists_isBddSupp_testOn φ
  obtain ⟨Mρ, Dρ, hρb⟩ := exists_isBddSupp_testOn ρ
  let MM : ℝ := M + (∫ x, |φ x|) * Mρ
  let DD : ℝ := max D Dρ
  let f (n : ℕ) : TestRd0 d := subMean hρ (markovBoundaryError V φ n)
  let X (n : ℕ) : Lp ℝ 2 P :=
    (markov_memLp_pair hh (f n)).toLp (markovPair h (f n))
  let N (n : ℕ) : ℝ := ∫ x, |(f n).1 x|
  have hN : Tendsto N atTop (𝓝 0) :=
    markovBoundaryError_subMean_L1_tendsto_zero V φ ρ hρ hnull
  have hf (n : ℕ) : IsBddSupp (fun x => (f n).1 x) MM DD :=
    markovBoundaryError_subMean_bddSupp V φ ρ hρ hφ hρb n
  have hXsq (n : ℕ) : ‖X n‖ ^ 2 ≤
      N n * (MM * volBall d + N n * (1 + max 0 (Real.log (2 * DD)))) := by
    have hvar : ‖X n‖ ^ 2 = logCovF (f n).1 (f n).1 := by
      rw [← real_inner_self_eq_norm_sq (X n), markov_inner_pair_eq_logCovRd hh,
        logCovRd_eq_logCovF (hf n) (hf n)]
    rw [hvar]
    exact (le_abs_self _).trans (abs_logCovF_self_le (hf n))
  have hRight : Tendsto
      (fun n => N n * (MM * volBall d + N n * (1 + max 0 (Real.log (2 * DD)))))
      atTop (𝓝 0) := by
    simpa only [zero_mul, add_zero] using hN.mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => MM * volBall d)
      atTop (𝓝 (MM * volBall d))).add
        (hN.mul_const (1 + max 0 (Real.log (2 * DD)))))
  have hSq : Tendsto (fun n => ‖X n‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hXsq hRight
  have hNorm : Tendsto (fun n => ‖X n‖) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hSq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] using hs
  simpa only [X, f] using (tendsto_zero_iff_norm_tendsto_zero.mpr hNorm)

end HigherDimLQGMetric
