import HigherDimLQGContinuity.MomentsW1.Scale

/-! Exponent bookkeeping for the normalized white-noise chain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLQGMetric HigherDimLQGMetric.DGZ

theorem wnSlope_lower {d : ℕ} {b μ σ ξ : ℝ} (hb : 0 < b) (hσμ : σ < μ)
    (hξb : ξ ≤ b) (hgap : μ ≤ ξ * (distExp d ξ - Real.sqrt (2 * d))) :
    (3*μ+5*σ)/8 ≤
      ξ * (distExp d ξ - (Real.sqrt (2 * d) + (μ-σ)/(2*b))) - (μ-σ)/8 := by
  have hT : 0 ≤ (μ-σ)/(2*b) := by positivity
  have hbound := mul_le_mul_of_nonneg_right hξb hT
  have hbT : b * ((μ-σ)/(2*b)) = (μ-σ)/2 := by field_simp
  rw [hbT] at hbound
  nlinarith

theorem wnSlope_between {μ σ : ℝ} (hμ : μ ≤ 1) (hσμ : σ < μ) :
    σ < (3*μ+5*σ)/8 ∧ (3*μ+5*σ)/8 < 1 := by
  constructor <;> linarith

theorem wnNorm_scale_id (ξ Q φ ε : ℝ) (k : ℕ) :
    (2 : ℝ)⁻¹ ^ k * Real.exp (ξ * (Q * k * Real.log 2)) *
      (2 : ℝ) ^ ((1-ξ*φ+ε)*k) =
      (2 : ℝ) ^ (-((ξ*(φ-Q)-ε)*k)) := by
  have hpow : (2 : ℝ)⁻¹ ^ k = Real.exp (-(k:ℝ)*Real.log 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow,
      Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  rw [hpow, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem wnNorm_terminal_id (ξ Q φ ε : ℝ) (n : ℕ) :
    (2 : ℝ)⁻¹ ^ n * Real.exp (ξ * (Q * n * Real.log 2)) *
      (2 : ℝ) ^ ((1-ξ*φ+ε)*n) =
      (2 : ℝ) ^ (-((ξ*(φ-Q)-ε)*n)) :=
  wnNorm_scale_id ξ Q φ ε n

theorem wnNorm_edge_bound {ξ Q φ ε s₀ C₁ C₂ u v w : ℝ} (k : ℕ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hu : u ≤ C₁ * (2 : ℝ)^((1-ξ*φ+ε)*k) * v)
    (hv : v ≤ C₂*w) (hw : 0 ≤ w) (hslope : s₀ ≤ ξ*(φ-Q)-ε) :
    (2 : ℝ)⁻¹ ^ k * Real.exp (ξ*(Q*k*Real.log 2)) * u ≤
      (C₁*C₂) * (2 : ℝ)^(-(s₀*k)) * w := by
  let L : ℝ := (2 : ℝ)⁻¹ ^ k * Real.exp (ξ*(Q*k*Real.log 2))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hpow : 0 ≤ (2 : ℝ)^((1-ξ*φ+ε)*k) := by positivity
  have hscale : (2 : ℝ)^(-((ξ*(φ-Q)-ε)*k)) ≤
      (2 : ℝ)^(-(s₀*k)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  calc
    L*u ≤ L*(C₁*(2 : ℝ)^((1-ξ*φ+ε)*k)*v) := mul_le_mul_of_nonneg_left hu hL
    _ ≤ L*(C₁*(2 : ℝ)^((1-ξ*φ+ε)*k)*(C₂*w)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv (mul_nonneg hC₁ hpow)) hL
    _ = (C₁*C₂) * (L*(2 : ℝ)^((1-ξ*φ+ε)*k)) * w := by ring
    _ = (C₁*C₂) * (2 : ℝ)^(-((ξ*(φ-Q)-ε)*k)) * w := by
      rw [show L*(2 : ℝ)^((1-ξ*φ+ε)*k) =
        (2 : ℝ)^(-((ξ*(φ-Q)-ε)*k)) from wnNorm_scale_id ξ Q φ ε k]
    _ ≤ (C₁*C₂) * (2 : ℝ)^(-(s₀*k)) * w := by
      have hcw : 0 ≤ C₁*C₂*w := by positivity
      nlinarith [mul_nonneg hcw (sub_nonneg.mpr hscale)]

theorem wnNorm_terminal_bound {ξ Q φ ε s₀ C w : ℝ} (n : ℕ)
    (hC : 0 < C)
    (hlow : C⁻¹ * (2 : ℝ)^(-((1-ξ*φ+ε)*n)) ≤ w)
    (hslope : s₀ ≤ ξ*(φ-Q)-ε) :
    (2 : ℝ)⁻¹ ^ n * Real.exp (ξ*(Q*n*Real.log 2)) ≤
      C * (2 : ℝ)^(-(s₀*n)) * w := by
  let t : ℝ := (2 : ℝ)^((1-ξ*φ+ε)*n)
  have ht : 0 < t := by dsimp [t]; positivity
  have hti : (2 : ℝ)^(-((1-ξ*φ+ε)*n)) = t⁻¹ := by
    dsimp [t]
    exact Real.rpow_neg (by norm_num : (0:ℝ)≤2) _
  have hunit : 1 ≤ C*t*w := by
    have hm := mul_le_mul_of_nonneg_left hlow (mul_nonneg hC.le ht.le)
    rw [hti] at hm
    have heq : (C*t)*(C⁻¹*t⁻¹) = 1 := by
      field_simp
    simpa only [heq] using hm
  let L : ℝ := (2 : ℝ)⁻¹ ^ n * Real.exp (ξ*(Q*n*Real.log 2))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hscale : (2 : ℝ)^(-((ξ*(φ-Q)-ε)*n)) ≤ (2 : ℝ)^(-(s₀*n)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  calc
    L = L*1 := by ring
    _ ≤ L*(C*t*w) := mul_le_mul_of_nonneg_left hunit hL
    _ = C*(L*t)*w := by ring
    _ = C*(2 : ℝ)^(-((ξ*(φ-Q)-ε)*n))*w := by
      rw [show L*t = (2 : ℝ)^(-((ξ*(φ-Q)-ε)*n)) from wnNorm_scale_id ξ Q φ ε n]
    _ ≤ C*(2 : ℝ)^(-(s₀*n))*w := by
      have hw : 0 ≤ w := le_trans (by positivity : 0 ≤ C⁻¹ * (2 : ℝ)^(-((1-ξ*φ+ε)*n))) hlow
      have hcw : 0 ≤ C*w := by positivity
      nlinarith [mul_nonneg hcw (sub_nonneg.mpr hscale)]

theorem wnNorm_terminal_cancel {a e G : ℝ} (n : ℕ)
    (h : (2 : ℝ)⁻¹ ^ n * e ≤ G*(2 : ℝ)^(-(a*(n:ℝ)))) :
    e ≤ G*(2 : ℝ)^((1-a)*(n:ℝ)) := by
  have hpow : (2 : ℝ)⁻¹ ^ n * (2 : ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  have hscale : (2 : ℝ)^(-(a*(n:ℝ))) * (2 : ℝ)^n =
      (2 : ℝ)^((1-a)*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (2 : ℝ)^n)
  calc
    e = ((2 : ℝ)⁻¹ ^ n * e)*(2 : ℝ)^n := by rw [mul_comm ((2 : ℝ)⁻¹ ^ n) e, mul_assoc, hpow, mul_one]
    _ ≤ (G*(2 : ℝ)^(-(a*(n:ℝ))))*(2 : ℝ)^n := hm
    _ = G*(2 : ℝ)^((1-a)*(n:ℝ)) := by rw [mul_assoc, hscale]

end HigherDimLQGContinuity
