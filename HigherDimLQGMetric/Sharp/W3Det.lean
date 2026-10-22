import HigherDimLQGMetric.Sharp.W3Multiscale
import HigherDimLQGMetric.Sharp.W3Grid
import HigherDimLQGMetric.Core.Interfaces

/-! Deterministic normalization on good dyadic events. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem w3_beta_formula {A C c r ξ Q q ζ h₀ : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hc : 0 < c) (hr : 0 < r)
    (n : ℕ) :
    A * (2 : ℝ) ^ (ζ * n) * (c * r / 2 ^ n) ^ (ξ * Q) *
      Real.exp (ξ * (h₀ + Real.log C + q * n * Real.log 2)) =
    (A * c ^ (ξ * Q) * r ^ (ξ * Q) * Real.exp (ξ * h₀) * C ^ ξ) *
      ((2 : ℝ) ^ (ζ + ξ * q - ξ * Q)) ^ n := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos h2 _
  have hcr : 0 < c * r / 2 ^ n := by positivity
  have hL : 0 < A * (2 : ℝ) ^ (ζ * n) * (c * r / 2 ^ n) ^ (ξ * Q) *
      Real.exp (ξ * (h₀ + Real.log C + q * n * Real.log 2)) := by positivity
  have hR : 0 < (A * c ^ (ξ * Q) * r ^ (ξ * Q) * Real.exp (ξ * h₀) * C ^ ξ) *
      ((2 : ℝ) ^ (ζ + ξ * q - ξ * Q)) ^ n := by positivity
  have hρlog : Real.log (c * r / 2 ^ n) =
      Real.log c + Real.log r - n * Real.log 2 := by
    rw [Real.log_div (mul_ne_zero hc.ne' hr.ne') (pow_ne_zero _ h2.ne'),
      Real.log_mul hc.ne' hr.ne', Real.log_pow]
  apply Real.log_injOn_pos hL hR
  repeat' rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_rpow h2, Real.log_rpow hcr, Real.log_rpow hc,
    Real.log_rpow hr, Real.log_rpow hC, Real.log_exp, Real.log_pow, hρlog]
  ring

/-- On the good shell and field events, the normalized internal diameter is
bounded by a fixed multiple of `A C^ξ`. -/
theorem w3_normDiam_good (hd : 2 ≤ d) {ξ Q q ζ c r A C : ℝ}
    (hξ : 0 < ξ) (_hQ : 0 ≤ Q) (_hq : q < Q)
    (_hζ : 0 < ζ) (hζsmall : ζ < ξ * (Q - q))
    (hc : 0 < c) (hr : 0 < r) (hA : 0 < A) (hC : 0 < C)
    (D : ContMetric d) (hD : D.IsLength) (g : DistRd d)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K)
    (z : Rd d) (G : ℕ → Finset (Rd d)) (N₀ : ℕ)
    (hN₀ : (G 0).card ≤ N₀)
    (hGK : ∀ n, ∀ y ∈ affineSet r z K,
      ∃ w ∈ G n, ‖y - w‖ ≤ (c * r / 2 ^ n) / 64)
    (hGU : ∀ n, ∀ w ∈ G n,
      Metric.closedBall w (2 * (c * r / 2 ^ n)) ⊆ affineSet r z U)
    (hfield : ∀ n, ∀ w ∈ G n,
      sphereAvg g (c * r / 2 ^ n) w - sphereAvg g r z ≤
        Real.log C + q * n * Real.log 2)
    (hacross : ∀ n, ∀ w ∈ G n,
      setDistIn D (ann w ((c * r / 2 ^ n) / 16) (2 * (c * r / 2 ^ n)))
        (Metric.sphere w ((c * r / 2 ^ n) / 8))
        (Metric.sphere w (c * r / 2 ^ n)) ≤
        ENNReal.ofReal (A * (2 : ℝ) ^ (ζ * n) *
          (c * r / 2 ^ n) ^ (ξ * Q) *
          Real.exp (ξ * sphereAvg g (c * r / 2 ^ n) w)))
    (haround : ∀ n, ∀ w ∈ G n,
      aroundDist D w (3 * (c * r / 2 ^ n) / 16)
        (3 * (c * r / 2 ^ n) / 8) ≤
        ENNReal.ofReal (A * (2 : ℝ) ^ (ζ * n) *
          (c * r / 2 ^ n) ^ (ξ * Q) *
          Real.exp (ξ * sphereAvg g (c * r / 2 ^ n) w))) :
    normDiam ξ Q (fun _ => D) g U K r z ≤
      ENNReal.ofReal (((5 + 2 * N₀) * A * c ^ (ξ * Q) * C ^ ξ) /
        (1 - (2 : ℝ) ^ (ζ + ξ * q - ξ * Q))) := by
  let ratio : ℝ := (2 : ℝ) ^ (ζ + ξ * q - ξ * Q)
  have hratio0 : 0 ≤ ratio := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hratio1 : ratio < 1 := by
    apply (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
    right; left
    constructor
    · norm_num
    · nlinarith only [hζsmall]
  let h₀ : ℝ := sphereAvg g r z
  let B₀ : ℝ := A * c ^ (ξ * Q) * r ^ (ξ * Q) * Real.exp (ξ * h₀) * C ^ ξ
  let β : ℕ → ℝ := fun n => B₀ * ratio ^ n
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hβ0 : ∀ n, 0 ≤ β n := fun n => mul_nonneg hB₀ (pow_nonneg hratio0 _)
  have hβ : Summable β := (summable_geometric_of_lt_one hratio0 hratio1).mul_left B₀
  have hβsum : (∑' n, β n) = B₀ / (1 - ratio) := by
    dsimp [β]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio1]
    ring
  have hcost (n : ℕ) (w : Rd d) (hw : w ∈ G n) :
      A * (2 : ℝ) ^ (ζ * n) * (c * r / 2 ^ n) ^ (ξ * Q) *
        Real.exp (ξ * sphereAvg g (c * r / 2 ^ n) w) ≤ β n := by
    have hfld := hfield n w hw
    have hle : sphereAvg g (c * r / 2 ^ n) w ≤
        h₀ + Real.log C + q * n * Real.log 2 := by
      dsimp [h₀]
      linarith only [hfld]
    have hexp : Real.exp (ξ * sphereAvg g (c * r / 2 ^ n) w) ≤
        Real.exp (ξ * (h₀ + Real.log C + q * n * Real.log 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hξ.le)
    have hfac : 0 ≤ A * (2 : ℝ) ^ (ζ * n) * (c * r / 2 ^ n) ^ (ξ * Q) := by
      positivity
    have hprod := mul_le_mul_of_nonneg_left hexp hfac
    calc
      _ ≤ A * (2 : ℝ) ^ (ζ * n) * (c * r / 2 ^ n) ^ (ξ * Q) *
          Real.exp (ξ * (h₀ + Real.log C + q * n * Real.log 2)) := hprod
      _ = β n := by
        simpa only [β, B₀, ratio] using
          (w3_beta_formula hA hC hc hr n (ξ := ξ) (Q := Q) (q := q)
            (ζ := ζ) (h₀ := h₀))
  have hA3 (n : ℕ) (w : Rd d) (hw : w ∈ G n) :
      setDistIn D (ann w ((c * r / 2 ^ n) / 16) (2 * (c * r / 2 ^ n)))
        (Metric.sphere w ((c * r / 2 ^ n) / 8))
        (Metric.sphere w (c * r / 2 ^ n)) ≤ ENNReal.ofReal (β n) :=
    (hacross n w hw).trans (ENNReal.ofReal_le_ofReal (hcost n w hw))
  have hA4 (n : ℕ) (w : Rd d) (hw : w ∈ G n) :
      aroundDist D w (3 * (c * r / 2 ^ n) / 16)
        (3 * (c * r / 2 ^ n) / 8) ≤ ENNReal.ofReal (β n) :=
    (haround n w hw).trans (ENNReal.ofReal_le_ofReal (hcost n w hw))
  have hopen : IsOpen (affineSet r z U) := by
    have hm : IsOpenMap (fun x : Rd d => z + r • x) := by
      simpa only [Function.comp_def] using
        (isOpenMap_add_left z).comp (isOpenMap_smul₀ hr.ne')
    exact hm U hU
  have hconn : IsConnected (affineSet r z K) := by
    exact hKc.image _ (by fun_prop)
  have hcompact : IsCompact (affineSet r z K) :=
    hK.image (by fun_prop : Continuous fun x : Rd d => z + r • x)
  have hMC := internalDiam_le_of_multiscale hd D hD hopen
    hcompact hconn (fun n => c * r / 2 ^ n)
    (by simpa using mul_pos hc hr)
    (by intro n; simp) G hGK hGU β hβ0 hβ hA3 hA4
  let a : ℝ := (r ^ (ξ * Q))⁻¹ * Real.exp (-(ξ * h₀))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum0 : 0 ≤ ∑' n, β n := tsum_nonneg hβ0
  have hcoef : ((5 + 2 * (G 0).card : ℝ) * ∑' n, β n) ≤
      (5 + 2 * N₀ : ℝ) * B₀ / (1 - ratio) := by
    rw [hβsum]
    have hden : 0 < 1 - ratio := by linarith
    have hBdiv : 0 ≤ B₀ / (1 - ratio) := div_nonneg hB₀ hden.le
    have hn : (G 0).card ≤ N₀ := hN₀
    have hnR : ((G 0).card : ℝ) ≤ N₀ := by exact_mod_cast hn
    calc
      (5 + 2 * (G 0).card : ℝ) * (B₀ / (1 - ratio)) ≤
          (5 + 2 * N₀ : ℝ) * (B₀ / (1 - ratio)) := by
            exact mul_le_mul_of_nonneg_right (by linarith only [hnR]) hBdiv
      _ = (5 + 2 * N₀ : ℝ) * B₀ / (1 - ratio) := by ring
  have hnormbound : normDiam ξ Q (fun _ => D) g U K r z ≤
      ENNReal.ofReal (a * ((5 + 2 * N₀ : ℝ) * B₀ / (1 - ratio))) := by
    unfold normDiam
    change ENNReal.ofReal a * _ ≤ _
    calc
      ENNReal.ofReal a *
          (⨆ (x ∈ affineSet r z K) (y ∈ affineSet r z K),
            D.internal (affineSet r z U) x y) ≤
        ENNReal.ofReal a *
          ENNReal.ofReal ((5 + 2 * (G 0).card : ℝ) * ∑' n, β n) :=
            mul_le_mul_of_nonneg_left hMC (by simp)
      _ = ENNReal.ofReal (a * ((5 + 2 * (G 0).card : ℝ) * ∑' n, β n)) := by
        rw [ENNReal.ofReal_mul ha]
      _ ≤ ENNReal.ofReal (a * ((5 + 2 * N₀ : ℝ) * B₀ / (1 - ratio))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcoef ha)
  refine hnormbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hrpow : 0 < r ^ (ξ * Q) := Real.rpow_pos_of_pos hr _
  have heh : 0 < Real.exp (ξ * h₀) := Real.exp_pos _
  have hden : 0 < 1 - ratio := by linarith
  apply le_of_eq
  dsimp [a, B₀, ratio]
  rw [Real.exp_neg]
  field_simp

end HigherDimLQGMetric
