import QuantumZipper.Proofs.Zipper.UnifUCE2Basic
import QuantumZipper.Proofs.Zipper.JointModKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-E2 (decision D33), step 3: the `r₀`-scaling of the JointMod time constant

The E2 time modulus uses the JointMod moduli at a radius threshold `r₀ = δ^{a/96}` that tends to
`0` with the time separation `δ = dist p p'`, so their constants must be controlled as
`r₀ → 0`. `UnifUC1RadBasic.spaceK_mul_sq_le` gives `spaceK M T r₀ R · r₀² ≤ spaceKs M T R`; this
file proves the companion bound for the time constant,

`timeK M T r₀ R CH · r₀² ≤ timeKs M T R CH` for `r₀ ∈ (0,1]`,

by the same elementary computation (`frostC T r₀ R · r₀ ≤ 18 + 12√(R²+4T)`, `frostC_mul_le`, fed
into the explicit forms of `potMax`, `holderK`, `timeConst`).

Own elementary argument (bookkeeping of explicit constants); the moduli themselves come from
`JointModKolm.abs_kernelCov2_νT_time_unif`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint

/-- The `r₀`-free majorant of `timeK M T r₀ R CH · r₀²`. -/
def timeKs (M T R CH : ℝ) : ℝ :=
  (2 * (2 + 24 * (18 + 12 * Real.sqrt (R ^ 2 + 4 * T)) +
      2 * (6 * (18 + 12 * Real.sqrt (R ^ 2 + 4 * T)) +
        2 * Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1))) *
      (2 * Real.sqrt (R ^ 2 + 8 * T)) ^ ((1 / 3 : ℝ) / 2) +
    80 * (6 * (18 + 12 * Real.sqrt (R ^ 2 + 4 * T)) +
      2 * Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1))) *
    (CH + 1) ^ (1 / 12 : ℝ)

theorem timeK_mul_sq_le {M T r₀ R CH : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀)
    (hr₁ : r₀ ≤ 1) (hCH : 0 ≤ CH) : timeK M T r₀ R CH * r₀ ^ 2 ≤ timeKs M T R CH := by
  have hBf0 : 0 ≤ revBound (2 * M) T R := revBound_nonneg (by linarith) hT
  have hLg : 0 ≤ Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1) :=
    Real.log_nonneg (by linarith)
  have hCF0 : 0 ≤ frostC T r₀ R := by unfold frostC; positivity
  have hCFr := frostC_mul_le (T := T) (R := R) hr₀ hr₁
  have hs : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have hs1 : Real.sqrt r₀ ≤ 1 := by
    have := Real.sqrt_le_sqrt hr₁; rwa [Real.sqrt_one] at this
  have hss : Real.sqrt r₀ * Real.sqrt r₀ = r₀ := Real.mul_self_sqrt hr₀.le
  have hS6 : 0 ≤ (2 * Real.sqrt (R ^ 2 + 8 * T)) ^ ((1 / 3 : ℝ) / 2) := by positivity
  have hE0 : 0 ≤ (CH + 1) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by linarith) _
  unfold timeK timeConst potC timeKs
  rw [potMax_eq, holderK_eq]
  generalize (CH + 1) ^ (1 / 12 : ℝ) = E at hE0 ⊢
  generalize (2 * Real.sqrt (R ^ 2 + 8 * T)) ^ ((1 / 3 : ℝ) / 2) = S6 at hS6 ⊢
  generalize Real.log (revBound (2 * M) T R + revBound (2 * M) T R + 1) = Lg at hLg ⊢
  generalize frostC T r₀ R = CF at hCF0 hCFr ⊢
  generalize Real.sqrt (R ^ 2 + 4 * T) = Q at hCFr ⊢
  generalize Real.sqrt r₀ = s at hs hs1 hss ⊢
  subst hss
  have eK : (2 * (2 + 24 * CF + 2 * (6 * CF + 2 * Lg)) * S6 + 72 * (6 * CF + 2 * Lg) / s +
      8 * (6 * CF + 2 * Lg)) * E * (s * s) ^ 2 =
      (2 * ((2 + 24 * CF + 2 * (6 * CF + 2 * Lg)) * (s * s) ^ 2) * S6 +
        72 * ((6 * CF + 2 * Lg) * (s * s) * s) + 8 * ((6 * CF + 2 * Lg) * (s * s) ^ 2)) * E := by
    field_simp
  rw [eK]
  refine mul_le_mul_of_nonneg_right ?_ hE0
  set F := 18 + 12 * Q with hF
  have hr2 : (s * s) ^ 2 ≤ s * s := by nlinarith [mul_pos hs hs]
  have hP : (6 * CF + 2 * Lg) * (s * s) ≤ 6 * F + 2 * Lg := by nlinarith [mul_pos hs hs]
  have hP2 : (6 * CF + 2 * Lg) * (s * s) ^ 2 ≤ (6 * CF + 2 * Lg) * (s * s) :=
    mul_le_mul_of_nonneg_left hr2 (by positivity)
  have hH : (2 + 24 * CF + 2 * (6 * CF + 2 * Lg)) * (s * s) ^ 2 ≤
      2 + 24 * F + 2 * (6 * F + 2 * Lg) := by
    have h1 : (s * s) ^ 2 ≤ 1 := by nlinarith [mul_pos hs hs]
    have h2 : CF * (s * s) ^ 2 ≤ F := by nlinarith [mul_pos hs hs]
    nlinarith
  have hPs : (6 * CF + 2 * Lg) * (s * s) * s ≤ 6 * F + 2 * Lg := by
    have h0 : 0 ≤ (6 * CF + 2 * Lg) * (s * s) := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_right hH hS6
  nlinarith

end RegUnif
end QuantumZipper
