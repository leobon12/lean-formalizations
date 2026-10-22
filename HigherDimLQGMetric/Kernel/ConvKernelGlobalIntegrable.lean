import HigherDimLQGMetric.Kernel.ConvKernelInfinity
import HigherDimLQGMetric.Kernel.ConvKernelNearIntegrable
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Global integrability of symbol derivatives

The near-zero estimate, continuity on compact annuli, and rapid decay at infinity imply
integrability of the derivatives and their moments for orders less than `2d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

private theorem integrableOn_inv_norm_pow_outside (N : ℕ) (hN : d < N) :
    IntegrableOn (fun ζ : Rd d => ‖ζ‖ ^ (-(N : ℝ)))
      {ζ : Rd d | 1 ≤ ‖ζ‖} := by
  have hint : Integrable (fun ζ : Rd d => (1 + ‖ζ‖) ^ (-(N : ℝ))) := by
    apply integrable_one_add_norm (μ := volume)
    simpa only [finrank_euclideanSpace_fin] using (by exact_mod_cast hN : (d : ℝ) < N)
  apply ((hint.const_mul (2 ^ N : ℝ)).integrableOn).mono'
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm :
      MeasurableSet {ζ : Rd d | 1 ≤ ‖ζ‖})]
      with ζ hζ
    have hr : 0 < ‖ζ‖ := lt_of_lt_of_le (by norm_num) hζ
    have hs : 0 < 1 + ‖ζ‖ := by positivity
    have hpow : (1 + ‖ζ‖) ^ N ≤ (2 : ℝ) ^ N * ‖ζ‖ ^ N := by
      calc
        _ ≤ (2 * ‖ζ‖) ^ N := by gcongr; linarith
        _ = _ := by rw [mul_pow]
    have hbound : ‖ζ‖ ^ (-(N : ℝ)) ≤
        (2 : ℝ) ^ N * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg hr.le, Real.rpow_natCast,
        Real.rpow_neg hs.le, Real.rpow_natCast]
      have hfrac : (1 : ℝ) / ‖ζ‖ ^ N ≤
          (2 : ℝ) ^ N / (1 + ‖ζ‖) ^ N :=
        (div_le_div_iff₀ (pow_pos hr N) (pow_pos hs N)).mpr
          (by simpa only [one_mul] using hpow)
      simpa only [one_div, div_eq_mul_inv, one_mul] using hfrac
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.le _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ N *
        (1 + ‖ζ‖) ^ (-(N : ℝ)))] using hbound

private theorem kernelSymbol_deriv_aestronglyMeasurable (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    AEStronglyMeasurable (iteratedFDeriv ℝ n (kernelSymbol κ)) volume := by
  let : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
    ContinuousOn.continuousOn_iteratedFDeriv
      (kernelSymbol_contDiffOn hd hκ) (isClosed_singleton.isOpen_compl) (by simp)
  have hh := hcont.aestronglyMeasurable (μ := volume)
    (isClosed_singleton.isOpen_compl.measurableSet)
  have hfull : volume.restrict ({0}ᶜ : Set (Rd d)) = volume :=
    Measure.restrict_eq_self_of_ae_mem (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (Measure.ae_ne volume (0 : Rd d)))
  rwa [hfull] at hh

private theorem kernelSymbol_deriv_continuousOn (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n (kernelSymbol κ))
      ({0}ᶜ : Set (Rd d)) :=
  ContinuousOn.continuousOn_iteratedFDeriv
    (kernelSymbol_contDiffOn hd hκ) (isClosed_singleton.isOpen_compl) (by simp)

private theorem integrableOn_symbol_deriv_moment_near (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n k : ℕ) (hn : 0 < n)
    (hnd : n < 2 * d) :
    ∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.ball (0 : Rd d) ρ) := by
  obtain ⟨ρ, hρ, hnear⟩ :=
    integrableOn_kernelSymbol_iteratedFDeriv_near_zero hd hκ n hn hnd
  refine ⟨ρ, hρ, ?_⟩
  apply ((hnear.norm).const_mul (ρ ^ k)).mono'
  · exact ((measurable_norm.pow_const k).aestronglyMeasurable).mul
      (kernelSymbol_deriv_aestronglyMeasurable hd hκ n).norm |>.restrict
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with ζ hζ
    have hr : ‖ζ‖ ≤ ρ := by
      have hh : ‖ζ‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hζ
      exact hh.le
    have hpow := pow_le_pow_left₀ (norm_nonneg ζ) hr k
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)] using
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

private theorem integrableOn_symbol_deriv_moment_outside (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n k : ℕ) :
    IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      {ζ : Rd d | 1 ≤ ‖ζ‖} := by
  let N := d + 1
  obtain ⟨C, hC⟩ := kernelSymbol_iteratedFDeriv_decay hd hκ n (k + N)
  have hsource : IntegrableOn (fun ζ : Rd d => C * ‖ζ‖ ^ (-(N : ℝ)))
      {ζ : Rd d | 1 ≤ ‖ζ‖} :=
    (integrableOn_inv_norm_pow_outside N (by dsimp [N]; omega)).const_mul C
  apply hsource.mono'
  · exact (((measurable_norm.pow_const k).aestronglyMeasurable).mul
      (kernelSymbol_deriv_aestronglyMeasurable hd hκ n).norm).restrict
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm :
        MeasurableSet {ζ : Rd d | 1 ≤ ‖ζ‖})] with ζ hζ
    have hr : 0 < ‖ζ‖ := lt_of_lt_of_le (by norm_num) hζ
    have hpow : ‖ζ‖ ^ N *
        (‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) ≤ C := by
      simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using hC ζ hζ
    have hbound : ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤
        C * ‖ζ‖ ^ (-(N : ℝ)) := by
      have hh : ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤
          C / ‖ζ‖ ^ N := (le_div_iff₀ (pow_pos hr N)).mpr (by
            simpa only [mul_comm] using hpow)
      simpa only [Real.rpow_neg hr.le, Real.rpow_natCast, div_eq_mul_inv] using hh
    have hs : 0 ≤ C * ‖ζ‖ ^ (-(N : ℝ)) := le_trans (by positivity) hbound
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ‖ζ‖ ^ k *
        ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖), abs_of_nonneg hs] using hbound

private theorem integrableOn_symbol_deriv_moment_annulus (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n k : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ) := by
  have hsubset : Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ ⊆
      ({0}ᶜ : Set (Rd d)) := by
    intro ζ hζ
    change ζ ≠ 0
    intro he
    subst ζ
    exact hζ.2 (Metric.mem_ball_self hρ)
  have hcont : ContinuousOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ) :=
    ((continuous_norm.pow k).continuousOn.mul
      (kernelSymbol_deriv_continuousOn hd hκ n).norm).mono hsubset
  exact hcont.integrableOn_compact ((isCompact_closedBall _ _).diff Metric.isOpen_ball)

/-- The `k`-th moment of the norm of each symbol derivative of order `n < 2d` is integrable. -/
theorem integrable_kernelSymbol_iteratedFDeriv_moment (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n k : ℕ) (hnd : n < 2 * d) :
    Integrable (fun ζ : Rd d =>
      ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖) := by
  by_cases hn : n = 0
  · subst n
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      integrable_kernelSymbol_moment hd hκ k
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨ρ, hρ, hnear⟩ :=
    integrableOn_symbol_deriv_moment_near hd hκ n k hn hnd
  have hann := integrableOn_symbol_deriv_moment_annulus hd hκ n k hρ
  have hout : IntegrableOn
      (fun ζ : Rd d => ‖ζ‖ ^ k * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖)
      (Metric.closedBall (0 : Rd d) 1)ᶜ :=
    (integrableOn_symbol_deriv_moment_outside hd hκ n k).mono_set (by
      intro ζ hζ
      have hnot : ¬ ‖ζ‖ ≤ 1 := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] using hζ
      exact le_of_lt (lt_of_not_ge hnot))
  have hunion := (hnear.union hann).union hout
  have hcover : Set.univ ⊆
      (Metric.ball (0 : Rd d) ρ ∪
        (Metric.closedBall (0 : Rd d) 1 \ Metric.ball 0 ρ)) ∪
        (Metric.closedBall (0 : Rd d) 1)ᶜ := by
    intro ζ _
    by_cases hb : ζ ∈ Metric.ball (0 : Rd d) ρ
    · exact Or.inl (Or.inl hb)
    by_cases hc : ζ ∈ Metric.closedBall (0 : Rd d) 1
    · exact Or.inl (Or.inr ⟨hc, hb⟩)
    · exact Or.inr hc
  simpa only [integrableOn_univ] using hunion.mono_set hcover

end HigherDimLQGMetric
