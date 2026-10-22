import HigherDimLQGMetric.Kernel.ConvKernelNormPow
import HigherDimLQGMetric.Kernel.ConvKernelZero
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Near-zero derivatives of the kernel symbol

The A2.4 perturbation `‖ζ‖^d * symbolAux κ ζ` inherits the homogeneous
weighted derivative bound from `‖ζ‖^d` because all derivatives of the
smooth auxiliary are bounded on the unit ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Weighted `n`th derivative estimate for the A2.4 perturbation. -/
theorem symbolPerturb_iteratedFDeriv_weighted
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    ∃ C : ℝ, ∀ ζ : Rd d, ζ ≠ 0 → ‖ζ‖ ≤ 1 →
      ‖ζ‖ ^ n * ‖iteratedFDeriv ℝ n
        (fun z : Rd d => ‖z‖ ^ d * symbolAux κ z) ζ‖ ≤ C * ‖ζ‖ ^ d := by
  let f : Rd d → ℝ := fun z => ‖z‖ ^ d
  let g : Rd d → ℝ := symbolAux κ
  let Cp : ℕ → ℝ := fun i => max (Classical.choose (norm_pow_deriv_weighted (dim := d) d i)) 0
  let Cg : ℕ → ℝ := fun j => max (Classical.choose (symbolAux_iteratedFDeriv_bounded hκ j)) 0
  have hCp (i : ℕ) (x : Rd d) (hx : x ≠ 0) :
      ‖x‖ ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ Cp i * ‖x‖ ^ d := by
    exact (Classical.choose_spec (norm_pow_deriv_weighted (dim := d) d i) x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg _) _))
  have hCg (j : ℕ) (x : Rd d) (hx : ‖x‖ ≤ 1) :
      ‖iteratedFDeriv ℝ j g x‖ ≤ Cg j :=
    (Classical.choose_spec (symbolAux_iteratedFDeriv_bounded hκ j) x hx).trans
      (le_max_left _ _)
  have hCp0 (i : ℕ) : 0 ≤ Cp i := le_max_right _ _
  have hCg0 (i : ℕ) : 0 ≤ Cg i := le_max_right _ _
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cp i * Cg (n - i)
  refine ⟨C, fun ζ hζ hζ1 => ?_⟩
  let r : ℝ := ‖ζ‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ 1 := hζ1
  have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ({0}ᶜ : Set (Rd d)) := by
    intro x hx
    exact ((contDiffAt_norm ℝ (show x ≠ 0 from hx)).pow d).contDiffWithinAt
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ({0}ᶜ : Set (Rd d)) :=
    (symbolAux_contDiff hκ).contDiffOn
  have hs : IsOpen ({0}ᶜ : Set (Rd d)) := isClosed_singleton.isOpen_compl
  have hbound := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn
    (show ζ ∈ ({0}ᶜ : Set (Rd d)) from hζ) (by simp : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  simp only [iteratedFDerivWithin_of_isOpen (s := ({0}ᶜ : Set (Rd d)))
    (f := f) _ hs hζ,
    iteratedFDerivWithin_of_isOpen (s := ({0}ᶜ : Set (Rd d)))
    (f := g) _ hs hζ,
    iteratedFDerivWithin_of_isOpen (s := ({0}ᶜ : Set (Rd d)))
    (f := fun z : Rd d => f z * g z) _ hs hζ] at hbound
  calc
    r ^ n * ‖iteratedFDeriv ℝ n (fun z : Rd d => f z * g z) ζ‖ ≤
        r ^ n * (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ζ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ζ‖) :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg hr0 _)
    _ = ∑ i ∈ Finset.range (n + 1),
          r ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ζ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ζ‖) := Finset.mul_sum ..
    _ ≤ C * r ^ d := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow : r ^ n = r ^ i * r ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_of_le hin]
      have hp : r ^ i * ‖iteratedFDeriv ℝ i f ζ‖ ≤ Cp i * r ^ d := hCp i ζ hζ
      have hg' : r ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g ζ‖ ≤ Cg (n - i) := by
        calc
          r ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g ζ‖ ≤
            1 * ‖iteratedFDeriv ℝ (n - i) g ζ‖ := by
            gcongr
            exact pow_le_one₀ hr0 hr1
          _ ≤ Cg (n - i) := by simpa using hCg (n - i) ζ hζ1
      calc
        r ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ζ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ζ‖) =
          (n.choose i : ℝ) * (r ^ i * ‖iteratedFDeriv ℝ i f ζ‖) *
            (r ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) g ζ‖) := by
          rw [hpow]
          ring
        _ ≤ (n.choose i : ℝ) * (Cp i * r ^ d) * Cg (n - i) := by
          gcongr
        _ = ((n.choose i : ℝ) * Cp i * Cg (n - i)) * r ^ d := by ring
