import HigherDimLQGMetric.Amplify.Normalizer
import HigherDimLQGMetric.Metric.WeylMetric
import HigherDimLQGMetric.Events.EventLocal

/-! Local normalized metric comparison under a continuous coarse field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Symmetric form of two-sided exponential bounds. -/
theorem amplify_reverse_exp_bounds (β : ℝ) {A B : ℝ≥0∞}
    (hlo : ENNReal.ofReal (Real.exp (-β)) * A ≤ B)
    (hhi : B ≤ ENNReal.ofReal (Real.exp β) * A) :
    ENNReal.ofReal (Real.exp (-β)) * B ≤ A ∧
      A ≤ ENNReal.ofReal (Real.exp β) * B := by
  have hc : ENNReal.ofReal (Real.exp (-β)) * ENNReal.ofReal (Real.exp β) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  constructor
  · calc
      ENNReal.ofReal (Real.exp (-β)) * B ≤
          ENNReal.ofReal (Real.exp (-β)) * (ENNReal.ofReal (Real.exp β) * A) := by gcongr
      _ = A := by rw [← mul_assoc, hc, one_mul]
  · calc
      A = ENNReal.ofReal (Real.exp β) *
          (ENNReal.ofReal (Real.exp (-β)) * A) := by
            rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.exp β))
              (ENNReal.ofReal (Real.exp (-β))), hc, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp β) * B := by gcongr

/-- The normalized internal metrics of a field and its continuous
perturbation differ by at most the exponential of its local oscillation. -/
theorem amplify_normInt_weyl_mem_Icc (hd : 1 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) (Q : ℝ) {s δ : ℝ} (hs : 0 < s)
    (w : Rd d) (X : DistRd d) (g : C(Rd d, ℝ))
    {a : ℝ} (hlim : Tendsto (sphereAvgSeq X s w) atTop (𝓝 a))
    (hosc : ∀ x ∈ Metric.ball w (5 * s), ∀ y ∈ Metric.ball w (5 * s),
      |g x - g y| ≤ δ)
    (D : DistRd d → ContMetric d)
    (hweyl : ∀ x y : Rd d,
      ENNReal.ofReal ((D (addFun X g)).1 (x, y)) = weylScale ξ g (D X) x y)
    {U : Set (Rd d)} (hU : IsOpen U) (hUball : U ⊆ Metric.ball w (5 * s))
    (x y : Rd d) :
    ENNReal.ofReal (Real.exp (-ξ * δ)) * normInt ξ Q D X s w U x y ≤
      normInt ξ Q D (addFun X g) s w U x y ∧
    normInt ξ Q D (addFun X g) s w U x y ≤
      ENNReal.ofReal (Real.exp (ξ * δ)) * normInt ξ Q D X s w U x y := by
  let μ := sphereAvg (ofCont g) s w
  let sf := sNorm ξ Q X s w
  let sh := sNorm ξ Q (addFun X g) s w
  have hsf : 0 < sf := sNorm_pos ξ Q X hs w
  have hsh : 0 < sh := sNorm_pos ξ Q (addFun X g) hs w
  have hshEq : sh = Real.exp (ξ * μ) * sf :=
    amplify_sNorm_addFun hlim g ξ Q
  have hgb (z : Rd d) (hz : z ∈ U) : |g z - μ| ≤ δ :=
    amplify_abs_coarse_sub_sphereMean_le hd hs w g hosc (hUball hz)
  have hlow (z : Rd d) (hz : z ∈ U) : ξ * μ - ξ * δ ≤ ξ * g z := by
    have h := (abs_le.mp (hgb z hz)).1
    have hm := mul_le_mul_of_nonneg_left h hξ.le
    nlinarith
  have hhigh (z : Rd d) (hz : z ∈ U) : ξ * g z ≤ ξ * μ + ξ * δ := by
    have h := (abs_le.mp (hgb z hz)).2
    have hm := mul_le_mul_of_nonneg_left h hξ.le
    nlinarith
  obtain ⟨hrawLow, hrawHigh⟩ :=
    internal_mem_Icc_of_le (D (addFun X g)) hweyl hU hlow hhigh x y
  have hrealLow : sh⁻¹ * Real.exp (ξ * μ - ξ * δ) =
      Real.exp (-ξ * δ) * sf⁻¹ := by
    rw [hshEq, Real.exp_sub]
    field_simp [Real.exp_ne_zero, ne_of_gt hsf]
    rw [← Real.exp_add]
    simp
  have hrealHigh : sh⁻¹ * Real.exp (ξ * μ + ξ * δ) =
      Real.exp (ξ * δ) * sf⁻¹ := by
    rw [hshEq, Real.exp_add]
    field_simp [Real.exp_ne_zero, ne_of_gt hsf]
  have hcoefLow : ENNReal.ofReal sh⁻¹ * ENNReal.ofReal (Real.exp (ξ * μ - ξ * δ)) =
      ENNReal.ofReal (Real.exp (-ξ * δ)) * ENNReal.ofReal sf⁻¹ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hsh.le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, hrealLow]
  have hcoefHigh : ENNReal.ofReal sh⁻¹ * ENNReal.ofReal (Real.exp (ξ * μ + ξ * δ)) =
      ENNReal.ofReal (Real.exp (ξ * δ)) * ENNReal.ofReal sf⁻¹ := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hsh.le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, hrealHigh]
  constructor
  · calc
      ENNReal.ofReal (Real.exp (-ξ * δ)) * normInt ξ Q D X s w U x y =
          (ENNReal.ofReal sh⁻¹ * ENNReal.ofReal (Real.exp (ξ * μ - ξ * δ))) *
            (D X).internal U x y := by
              change ENNReal.ofReal (Real.exp (-ξ * δ)) *
                (ENNReal.ofReal sf⁻¹ * (D X).internal U x y) = _
              rw [← mul_assoc, ← hcoefLow]
      _ ≤ ENNReal.ofReal sh⁻¹ * (D (addFun X g)).internal U x y := by
        rw [mul_assoc]
        gcongr
      _ = normInt ξ Q D (addFun X g) s w U x y := rfl
  · calc
      normInt ξ Q D (addFun X g) s w U x y =
          ENNReal.ofReal sh⁻¹ * (D (addFun X g)).internal U x y := rfl
      _ ≤ ENNReal.ofReal sh⁻¹ *
          (ENNReal.ofReal (Real.exp (ξ * μ + ξ * δ)) * (D X).internal U x y) := by
            gcongr
      _ = ENNReal.ofReal (Real.exp (ξ * δ)) * normInt ξ Q D X s w U x y := by
        change ENNReal.ofReal sh⁻¹ *
          (ENNReal.ofReal (Real.exp (ξ * μ + ξ * δ)) * (D X).internal U x y) =
          ENNReal.ofReal (Real.exp (ξ * δ)) *
            (ENNReal.ofReal sf⁻¹ * (D X).internal U x y)
        rw [← mul_assoc, hcoefHigh, mul_assoc]

end HigherDimLQGMetric
