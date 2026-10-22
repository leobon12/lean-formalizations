import HigherDimLQGMetric.Kernel.ConvKernelDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set MeasureTheory
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

private theorem radial_deriv_uniform_decay (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n M : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ n, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedFDeriv ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r‖ ≤
        B * r ^ (-(M : ℝ)) := by
  have hh (i : ℕ) : ∃ C : ℝ, ∀ r ∈ Ici (1 : ℝ),
      ‖iteratedFDeriv ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r‖ ≤
        C * r ^ (-(M : ℝ)) := by
    obtain ⟨C, hC⟩ := sqrt_symbolSq_decay hd hκ i M
    refine ⟨C, fun r hr => ?_⟩
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
    have h : |iteratedDeriv i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r| ≤
        C / r ^ M := by
      apply (le_div_iff₀ (pow_pos hr0 M)).mpr
      simpa only [mul_comm] using hC r hr
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      Real.rpow_neg hr0.le, Real.rpow_natCast, div_eq_mul_inv] using h
  obtain ⟨B, hB, hBi⟩ := finite_uniform_weighted_bound
    (fun i r => ‖iteratedFDeriv ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t)) r‖)
    (fun r : ℝ => r ^ (-(M : ℝ))) (Ici (1 : ℝ))
    (fun r hr => Real.rpow_nonneg (by linarith [show 1 ≤ r from hr]) _)
    hh n
  exact ⟨B, hB, fun i hi r hr => hBi i hi r hr⟩

private theorem norm_deriv_uniform_outside (d n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ x : Rd d,
      1 ≤ ‖x‖ → ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ ≤ A := by
  have hh (i : ℕ) : ∃ C : ℝ, ∀ x ∈ {x : Rd d | 1 ≤ ‖x‖},
      (if i = 0 then 0 else ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖) ≤ C := by
    by_cases hi : i = 0
    · exact ⟨0, fun x hx => by simp [hi]⟩
    · obtain ⟨C, hC⟩ := norm_pow_deriv_weighted (dim := d) 1 i
      refine ⟨C, fun x hx => ?_⟩
      have hr : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx
      have hx0 : x ≠ 0 := norm_pos_iff.mp hr
      have hw := hC x hx0
      simp only [pow_one] at hw
      have hrpow : ‖x‖ ≤ ‖x‖ ^ i := le_self_pow₀ hx hi
      have hle : ‖x‖ * ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ ≤
          ‖x‖ * C := by
        calc
          ‖x‖ * ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ ≤
              ‖x‖ ^ i * ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖ :=
            mul_le_mul_of_nonneg_right hrpow (norm_nonneg _)
          _ ≤ C * ‖x‖ := hw
          _ = ‖x‖ * C := mul_comm _ _
      simpa [hi] using le_of_mul_le_mul_left hle hr
  obtain ⟨A, hA, hAi⟩ := finite_uniform_bound
    (fun i (x : Rd d) => if i = 0 then 0 else
      ‖iteratedFDeriv ℝ i (fun z : Rd d => ‖z‖) x‖)
    {x : Rd d | 1 ≤ ‖x‖} hh n
  refine ⟨A, hA, fun i hi hin x hx => ?_⟩
  simpa [Nat.ne_of_gt hi] using hAi i hin x hx

theorem kernelSymbol_iteratedFDeriv_decay (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n M : ℕ) :
    ∃ C : ℝ, ∀ ζ : Rd d, 1 ≤ ‖ζ‖ →
      ‖ζ‖ ^ M * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤ C := by
  obtain ⟨A, hA, hAi⟩ := norm_deriv_uniform_outside d n
  obtain ⟨B, hB, hBi⟩ := radial_deriv_uniform_decay hd hκ n M
  let C : ℝ := (n.factorial : ℝ) * B * A ^ n
  refine ⟨C, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := by
    intro he
    have : (1 : ℝ) ≤ 0 := by simpa [he] using hζ
    linarith
  have hnorm0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hs : IsOpen ({0}ᶜ : Set (Rd d)) := isClosed_singleton.isOpen_compl
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Rd d => ‖z‖) ({0}ᶜ : Set (Rd d)) := by
    intro z hz
    exact (contDiffAt_norm ℝ (show z ≠ 0 from hz)).contDiffWithinAt
  have hmap : MapsTo (fun z : Rd d => ‖z‖) ({0}ᶜ : Set (Rd d)) (Ioi 0) := by
    intro z hz
    exact norm_pos_iff.mpr hz
  have houter : ∀ i ≤ n,
      ‖iteratedFDerivWithin ℝ i (fun t : ℝ => Real.sqrt (symbolSq κ t))
        (Ioi 0) ‖ζ‖‖ ≤ B * ‖ζ‖ ^ (-(M : ℝ)) := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hnorm0]
    exact hBi i hi ‖ζ‖ hζ
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun z : Rd d => ‖z‖)
        ({0}ᶜ : Set (Rd d)) ζ‖ ≤ A ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hs hζ0]
    exact (hAi i hi hin ζ hζ).trans (le_self_pow₀ hA (Nat.ne_of_gt hi))
  have hc := norm_iteratedFDerivWithin_comp_le (sqrt_symbolSq_contDiffOn hd hκ)
    hf (by simp : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)) isOpen_Ioi.uniqueDiffOn
    hs.uniqueDiffOn hmap hζ0 houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hs hζ0] at hc
  have heq : ((fun t : ℝ => Real.sqrt (symbolSq κ t)) ∘
      (fun z : Rd d => ‖z‖)) = kernelSymbol κ := by
    funext z
    exact (kernelSymbol_eq_sqrt_symbolSq (κ := κ) z).symm
  rw [heq] at hc
  have hpow : ‖ζ‖ ^ M * ‖ζ‖ ^ (-(M : ℝ)) = 1 := by
    rw [Real.rpow_neg hnorm0.le, Real.rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero M hnorm0.ne')
  have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg hnorm0.le M)
  calc
    ‖ζ‖ ^ M * ‖iteratedFDeriv ℝ n (kernelSymbol κ) ζ‖ ≤
        ‖ζ‖ ^ M * ((n.factorial : ℝ) * (B * ‖ζ‖ ^ (-(M : ℝ))) * A ^ n) := hh
    _ = C := by
      calc
        _ = ((n.factorial : ℝ) * B * A ^ n) *
            (‖ζ‖ ^ M * ‖ζ‖ ^ (-(M : ℝ))) := by ring
        _ = C := by rw [hpow, mul_one]

end HigherDimLQGMetric
