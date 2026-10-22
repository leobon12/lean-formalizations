import HigherDimLQGMetric.Markov.BoundaryApprox

/-! Logarithmic energy of the boundary approximation error. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The boundary error inherits a uniform pointwise and support bound from the original test. -/
theorem markovBoundaryError_bddSupp (V : Opens (Rd d)) (φ : TestRd d)
    {M D : ℝ} (hφ : IsBddSupp (fun x => φ x) M D) (n : ℕ) :
    IsBddSupp (fun x => markovBoundaryError V φ n x) M D := by
  refine ⟨(markovBoundaryError V φ n).continuous.measurable, ?_, ?_⟩
  · intro x
    exact (markovBoundaryError_abs_le V φ n x).trans (hφ.abs_le x)
  · intro x hx
    simp [markovBoundaryError_apply, hφ.eq_zero x hx]

/-- The coefficient used in smooth-test recentering is controlled by the boundary-error
`L¹` norm. -/
theorem markovBoundaryError_integral_abs_le (V : Opens (Rd d))
    (φ : TestRd d) (n : ℕ) :
    |∫ x, markovBoundaryError V φ n x| ≤
      ∫ x, |markovBoundaryError V φ n x| := by
  exact abs_integral_le_integral_abs

theorem markovBoundaryError_L1_le_test (V : Opens (Rd d))
    (φ : TestRd d) (n : ℕ) :
    (∫ x, |markovBoundaryError V φ n x|) ≤ ∫ x, |φ x| := by
  exact integral_mono ((integrable_testOn (markovBoundaryError V φ n)).abs)
    (integrable_testOn φ).abs (markovBoundaryError_abs_le V φ n)

/-- The mean-zero test obtained from a boundary error has uniformly bounded support and
supremum norm. -/
theorem markovBoundaryError_subMean_bddSupp (V : Opens (Rd d))
    (φ ρ : TestRd d) (hρ : ∫ x, ρ x = 1)
    {M D Mρ Dρ : ℝ}
    (hφ : IsBddSupp (fun x => φ x) M D)
    (hρb : IsBddSupp (fun x => ρ x) Mρ Dρ) (n : ℕ) :
    IsBddSupp (fun x => (subMean hρ (markovBoundaryError V φ n)).1 x)
      (M + (∫ x, |φ x|) * Mρ) (max D Dρ) := by
  let f := markovBoundaryError V φ n
  let c : ℝ := ∫ x, f x
  have hf : IsBddSupp (fun x => f x) M D :=
    markovBoundaryError_bddSupp V φ hφ n
  have hc : |c| ≤ ∫ x, |φ x| :=
    (markovBoundaryError_integral_abs_le V φ n).trans
      (markovBoundaryError_L1_le_test V φ n)
  have hρM : 0 ≤ Mρ := hρb.nonneg
  have hfc : IsBddSupp (fun x => f x) M (max D Dρ) :=
    hf.mono le_rfl (le_max_left _ _)
  have hρc : IsBddSupp (fun x => c * ρ x)
      ((∫ x, |φ x|) * Mρ) (max D Dρ) :=
    (hρb.const_mul c).mono (mul_le_mul_of_nonneg_right hc hρM)
      (le_max_right _ _)
  have hsub := hfc.sub hρc
  convert hsub using 1
  funext x
  simp only [subMean, sub_apply, smul_apply, smul_eq_mul]
  rfl

/-- The recentered boundary error has vanishing `L¹` norm. -/
theorem markovBoundaryError_subMean_L1_tendsto_zero (V : Opens (Rd d))
    (φ ρ : TestRd d) (hρ : ∫ x, ρ x = 1)
    (hnull : volume (frontier (V : Set (Rd d))) = 0) :
    Tendsto (fun n => ∫ x, |(subMean hρ (markovBoundaryError V φ n)).1 x|)
      atTop (𝓝 0) := by
  let A : ℕ → ℝ := fun n => ∫ x, |markovBoundaryError V φ n x|
  let B : ℕ → ℝ := fun n =>
    ∫ x, |(subMean hρ (markovBoundaryError V φ n)).1 x|
  let Nρ : ℝ := ∫ x, |ρ x|
  have hA : Tendsto A atTop (𝓝 0) :=
    markovBoundaryError_L1_tendsto_zero V φ hnull
  have hNρ : 0 ≤ Nρ := integral_nonneg fun _ => abs_nonneg _
  have hB0 (n : ℕ) : 0 ≤ B n := integral_nonneg fun _ => abs_nonneg _
  have hBbound (n : ℕ) : B n ≤ A n * (1 + Nρ) := by
    let f := markovBoundaryError V φ n
    let c : ℝ := ∫ x, f x
    have hf : Integrable (fun x => |f x|) := (integrable_testOn f).abs
    have hρi : Integrable (fun x => |ρ x|) := (integrable_testOn ρ).abs
    have hc : |c| ≤ A n := markovBoundaryError_integral_abs_le V φ n
    have hpoint (x : Rd d) :
        |(subMean hρ f).1 x| ≤ |f x| + |c| * |ρ x| := by
      simp only [subMean, sub_apply, smul_apply, smul_eq_mul]
      calc |f x - c * ρ x| ≤ |f x| + |c * ρ x| := abs_sub _ _
        _ = _ := by rw [abs_mul]
    have hI : B n ≤ A n + |c| * Nρ := by
      calc
        B n ≤ ∫ x, (|f x| + |c| * |ρ x|) := by
          exact integral_mono
            ((integrable_testOn (subMean hρ f).1).abs)
            (hf.add (hρi.const_mul _)) hpoint
        _ = A n + |c| * Nρ := by rw [integral_add hf (hρi.const_mul _), integral_const_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hNρ]
  have hRight : Tendsto (fun n => A n * (1 + Nρ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hA.mul_const (1 + Nρ)
  exact squeeze_zero hB0 hBbound hRight

end HigherDimLQGMetric
