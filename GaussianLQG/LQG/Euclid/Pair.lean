import GaussianLQG.LQG.ConcentrationU
import GaussianLQG.LQG.Exponents
import GaussianLQG.LQG.Euclid.Basic

/-!
# Fixed endpoints (blueprint Lemma `lem:euclidean`, Steps 1 and 2)

For `z, w ∈ B̄_{ρ₀}(0)` and `P₀ ≥ 1`, `‖e^{-b_γ} D^γ(z,w) - |z - w|‖_{P₀} ≤ K ξ_γ` for small `γ`,
with `K` depending only on `ρ₀`, `P₀` (`Setup.exists_eLpNorm_pair_le`).

Proof. Let `r = |z - w| ∈ (0, 2ρ₀]`, `h = h_r(z)` the circle average (a centered Gaussian of
variance `v = ℰ(σ_{z,r}, σ_{z,r}) ≤ log⁺(1/r) + 2 log⁺(3ρ₀)`), and
`Y = log D(z,w) - ξQ log r - ξ h`, which has the law of `log D(0,1)` (Lemma `lem:scaling`(b)).
Put `X = log D(z,w) - b - log r`, so that `X = ξ h + (Y - b) + (ξQ - 1) log r` and
`e^{-b} D(z,w) = r e^X`. Then
`|e^{-b} D(z,w) - r| = r |e^X - 1| ≤ |X| (r + e^{-b} D(z,w))` (`abs_exp_sub_one_le_mul`), and by
Hölder's inequality `‖e^{-b} D(z,w) - r‖_{P₀} ≤ ‖X‖_{2P₀} ‖r + e^{-b} D(z,w)‖_{2P₀}`. Here
`‖X‖_{2P₀} ≤ ξ √v ‖N‖_{2P₀} + ‖log D(0,1) - b‖_{2P₀} + |ξQ - 1| |log r|
  ≤ ξ (√v ‖N‖_{2P₀} + C_c + C₁ |log r|)` by Corollary `cor:logD-concentration` and
Lemma `lem:exponents`, and `D(z,w) ≤ A_γ(B̄_{ρ₀}) r^{1/2}` together with (S6) give
`‖r + e^{-b} D(z,w)‖_{2P₀} ≤ r + e^{|b|} C_A r^{1/2}`. The deterministic bounds `√r √v ≤ C`,
`√r |log r| ≤ C` on `(0, 2ρ₀]` conclude.

This combines Steps 1 and 2 of the blueprint: writing `e^{-b} D(z,w) = r e^X` with
`X = log D(z,w) - b - log r` absorbs the deterministic error `|r^{ξQ} - r|` of Step 2 into the
term `(ξQ - 1) log r` of `X`, and the bound `e^{-b} D(z,w) ≤ e^{|b|} A_γ(B̄_{ρ₀}) r^{1/2}` replaces
the exponential-moment estimate of `‖e^X‖_{2P₀}`. The inputs are Lemma `lem:scaling`(a),(b),
Corollary `cor:logD-concentration`, Lemma `lem:exponents`, the Gaussian moments of Lemma `lem:gauss`
and (S6); the exponential moments of `h_r(z)` are not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

/-- `|e^{-b} d - r| ≤ |log d - b - log r| (r + e^{-b} d)` for `d, r > 0`. -/
theorem abs_exp_neg_mul_sub_le (b : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r) :
    |Real.exp (-b) * d - r| ≤ |Real.log d - b - Real.log r| * (r + Real.exp (-b) * d) := by
  set x := Real.log d - b - Real.log r with hx_def
  have hx : Real.exp (-b) * d = r * Real.exp x := by
    rw [hx_def, Real.exp_sub, Real.exp_sub, Real.exp_log hd, Real.exp_log hr, Real.exp_neg]
    field_simp
  rw [hx]
  have h := abs_exp_sub_one_le_mul x
  calc |r * Real.exp x - r| = r * |Real.exp x - 1| := by
        rw [← mul_sub_one, abs_mul, abs_of_pos hr]
    _ ≤ r * (|x| * (1 + Real.exp x)) := mul_le_mul_of_nonneg_left h hr.le
    _ = |x| * (r + r * Real.exp x) := by ring

/-- The deterministic part of the fixed-endpoint bound: for `0 < r ≤ 2ρ` and
`v ≤ log⁺(1/r) + c₀`, `(√v m + C_c + C₁ |log r|)(r + E √r C_A)` is bounded by a constant. -/
theorem pair_bound_le {r v m Cc C1 E CA ρ c0 : ℝ} (hr : 0 < r) (hrρ : r ≤ 2 * ρ)
    (hc0 : 0 ≤ c0) (hv : v ≤ Real.posLog r⁻¹ + c0) (hm : 0 ≤ m) (hCc : 0 ≤ Cc) (hC1 : 0 ≤ C1)
    (hE : 0 ≤ E) (hCA : 0 ≤ CA) :
    (Real.sqrt v * m + Cc + C1 * |Real.log r|) * (r + E * Real.sqrt r * CA) ≤
      (m * Real.sqrt (1 + 2 * ρ * c0) + Cc * Real.sqrt (2 * ρ) + C1 * (2 + 4 * ρ ^ 2)) *
        (Real.sqrt (2 * ρ) + E * CA) := by
  have hsr : Real.sqrt r ≤ Real.sqrt (2 * ρ) := Real.sqrt_le_sqrt hrρ
  have hsr0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have h1 : Real.sqrt r * Real.sqrt v ≤ Real.sqrt (1 + 2 * ρ * c0) :=
    sqrt_mul_sqrt_le_of_le_posLog hr hrρ hc0 hv
  have h2 : Real.sqrt r * |Real.log r| ≤ 2 + 4 * ρ ^ 2 := sqrt_mul_abs_log_le hr hrρ
  have hrr : r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr.le).symm
  have key : Real.sqrt r * (Real.sqrt v * m + Cc + C1 * |Real.log r|) ≤
      m * Real.sqrt (1 + 2 * ρ * c0) + Cc * Real.sqrt (2 * ρ) + C1 * (2 + 4 * ρ ^ 2) := by
    have e : Real.sqrt r * (Real.sqrt v * m + Cc + C1 * |Real.log r|) =
        m * (Real.sqrt r * Real.sqrt v) + Cc * Real.sqrt r +
          C1 * (Real.sqrt r * |Real.log r|) := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 hm
    have := mul_le_mul_of_nonneg_left hsr hCc
    have := mul_le_mul_of_nonneg_left h2 hC1
    linarith
  have hfac : r + E * Real.sqrt r * CA = Real.sqrt r * (Real.sqrt r + E * CA) := by
    rw [mul_add, ← hrr]
    ring
  have hfac2 : Real.sqrt r + E * CA ≤ Real.sqrt (2 * ρ) + E * CA := by linarith
  have hfac20 : 0 ≤ Real.sqrt r + E * CA := add_nonneg hsr0 (mul_nonneg hE hCA)
  have hR0 : 0 ≤ m * Real.sqrt (1 + 2 * ρ * c0) + Cc * Real.sqrt (2 * ρ) +
      C1 * (2 + 4 * ρ ^ 2) := by
    positivity
  rw [hfac, show (Real.sqrt v * m + Cc + C1 * |Real.log r|) *
      (Real.sqrt r * (Real.sqrt r + E * CA)) =
      (Real.sqrt r * (Real.sqrt v * m + Cc + C1 * |Real.log r|)) * (Real.sqrt r + E * CA) by ring]
  calc (Real.sqrt r * (Real.sqrt v * m + Cc + C1 * |Real.log r|)) * (Real.sqrt r + E * CA)
      ≤ (m * Real.sqrt (1 + 2 * ρ * c0) + Cc * Real.sqrt (2 * ρ) + C1 * (2 + 4 * ρ ^ 2)) *
          (Real.sqrt r + E * CA) := mul_le_mul_of_nonneg_right key hfac20
    _ ≤ (m * Real.sqrt (1 + 2 * ρ * c0) + Cc * Real.sqrt (2 * ρ) + C1 * (2 + 4 * ρ ^ 2)) *
          (Real.sqrt (2 * ρ) + E * CA) := mul_le_mul_of_nonneg_left hfac2 hR0

namespace Setup

variable (S : Setup)

/-- The constant of the fixed-endpoint bound (`Setup.eLpNorm_pair_le`). -/
def pairConst (ρ0 P0 Cc C1 Cb : ℝ) (C6 : ℝ≥0∞) : ℝ :=
  ((eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * P0)) (gaussianReal 0 1)).toReal *
      Real.sqrt (1 + 2 * ρ0 * (2 * Real.posLog (3 * ρ0))) + max Cc 0 * Real.sqrt (2 * ρ0) +
      max C1 0 * (2 + 4 * ρ0 ^ 2)) *
    (Real.sqrt (2 * ρ0) + Real.exp Cb * (C6 ^ (1 / (2 * P0))).toReal)

/-- **Blueprint Lemma `lem:euclidean`, Steps 1–2 (fixed endpoints), for one `γ`.** Let `0 < γ < 2`,
`P₀ ≥ 1`, `z, w ∈ B̄_{ρ₀}(0)`, and assume the inputs at this `γ`: concentration
`‖log D(0,1) - b‖_{2P₀} ≤ C_c ξ`, the exponent bound `|ξQ - 1| ≤ C₁ ξ`, `|b| ≤ C_b`, and the
moment `E[A_γ(B̄_{ρ₀})^{2P₀}] ≤ C₆ < ∞`. Then `‖e^{-b} D(z,w) - |z - w|‖_{P₀} ≤ K ξ` with
`K = pairConst`. -/
theorem eLpNorm_pair_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {P0 : ℝ} (hP0 : 1 ≤ P0)
    {ρ0 : ℝ} {z w : ℂ} (hz : ‖z‖ ≤ ρ0) (hw : ‖w‖ ≤ ρ0)
    {Cc C1 Cb : ℝ} {C6 : ℝ≥0∞} (hC6 : C6 ≠ ⊤)
    (hconc : eLpNorm (fun ω => Real.log ((S.D γ ω).1 (0, 1)) - S.b γ)
      (ENNReal.ofReal (2 * P0)) stdP ≤ ENNReal.ofReal (Cc * S.ξ γ))
    (hexp : |S.ξ γ * LQGMetric.Q γ - 1| ≤ C1 * S.ξ γ) (hb : |S.b γ| ≤ Cb)
    (h6 : ∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedBall 0 ρ0) ^ (2 * P0) ∂stdP ≤ C6) :
    eLpNorm (fun ω => Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖)
      (ENNReal.ofReal P0) stdP ≤ ENNReal.ofReal (S.ξ γ * pairConst ρ0 P0 Cc C1 Cb C6) := by
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ hγ2
  have hP0' : 0 < P0 := by linarith
  rcases eq_or_ne z w with rfl | hzw
  · have h0 : (fun ω => Real.exp (-S.b γ) * (S.D γ ω).1 (z, z) - ‖z - z‖) =
        fun _ => (0 : ℝ) := by
      funext ω
      rw [(S.D γ ω).2.self_eq_zero, sub_self, norm_zero, mul_zero, sub_zero]
    rw [h0, eLpNorm_zero']
    exact zero_le
  set r : ℝ := ‖z - w‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hrwz : ‖w - z‖ = r := norm_sub_rev w z
  have hrρ : r ≤ 2 * ρ0 := (norm_sub_le z w).trans (by linarith)
  have hρ0 : 0 ≤ ρ0 := (norm_nonneg z).trans hz
  set q : ℝ≥0∞ := ENNReal.ofReal (2 * P0) with hq_def
  have hq1 : 1 ≤ q := by
    rw [hq_def, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hq0 : q ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  set σ := circleMeasure z ‖w - z‖ with hσ_def
  set h : Coord → ℝ := pairing S.e σ with hh_def
  set L : Coord → ℝ := fun ω => Real.log ((S.D γ ω).1 (z, w)) with hL_def
  set Y : Coord → ℝ := fun ω => Real.log ((S.D γ ω).1 (z, w)) -
    S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ - S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω
    with hY_def
  set X : Coord → ℝ := fun ω => L ω - S.b γ - Real.log r with hX_def
  set Dzw : Coord → ℝ := fun ω => (S.D γ ω).1 (z, w) with hDzw_def
  set G : Coord → ℝ := fun ω => r + Real.exp (-S.b γ) * Dzw ω with hG_def
  have hm_h : Measurable h := measurable_pairing _ _
  have hm_L : Measurable L := S.measurable_log_D γ z w
  have hm_D : Measurable Dzw := S.measurable_D_apply γ (z, w)
  have hm_Y : Measurable Y :=
    (hm_L.sub_const _).sub ((measurable_pairing _ _).const_mul _)
  have hm_X : Measurable X := (hm_L.sub_const _).sub_const _
  have hm_G : Measurable G := measurable_const.add (hm_D.const_mul _)
  -- Step 1a: the pointwise bound and Hölder's inequality
  have hpt : ∀ ω, ‖Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖‖ ≤
      ((1 : ℝ≥0) : ℝ) * ‖X ω‖ * ‖G ω‖ := by
    intro ω
    have hd : 0 < (S.D γ ω).1 (z, w) := contMetric_pos (S.D γ ω) hzw
    have hG0 : 0 ≤ G ω := add_nonneg hr.le (mul_nonneg (Real.exp_pos _).le hd.le)
    rw [NNReal.coe_one, one_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hG0]
    exact abs_exp_neg_mul_sub_le (S.b γ) hd hr
  have hH := holderTriple_two_mul hP0'
  have step1 : eLpNorm (fun ω => Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖)
      (ENNReal.ofReal P0) stdP ≤ eLpNorm X q stdP * eLpNorm G q stdP := by
    calc eLpNorm (fun ω => Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖)
          (ENNReal.ofReal P0) stdP
        ≤ eLpNorm (fun ω => X ω * G ω) (ENNReal.ofReal P0) stdP := by
          refine eLpNorm_mono fun ω => ?_
          have := hpt ω
          rw [NNReal.coe_one, one_mul] at this
          rwa [norm_mul]
      _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm X q stdP * eLpNorm G q stdP :=
          eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hm_X.aestronglyMeasurable
            hm_G.aestronglyMeasurable (fun x y : ℝ => x * y) 1
            (ae_of_all _ fun ω => by rw [norm_mul, NNReal.coe_one, one_mul])
      _ = eLpNorm X q stdP * eLpNorm G q stdP := by rw [ENNReal.coe_one, one_mul]
  -- Step 1b: `X = ξ h + (Y - b) + (ξQ - 1) log r` and Minkowski
  set a : ℝ := S.ξ γ * LQGMetric.Q γ with ha_def
  have hXeq : X = (fun ω => S.ξ γ * h ω) + (fun ω => Y ω - S.b γ) +
      (fun _ => (a - 1) * Real.log r) := by
    funext ω
    simp only [hX_def, hY_def, hL_def, hh_def, hσ_def, Pi.add_apply, hrwz]
    ring
  -- the Gaussian term
  have hlawh : HasLaw h (gaussianReal 0 (energy σ σ).toNNReal) stdP :=
    hasLaw_pairing_circleMeasure S.frame z (r := ‖w - z‖) (by rw [hrwz]; exact hr)
  set v : ℝ := ((energy σ σ).toNNReal : ℝ) with hv_def
  set mN : ℝ≥0∞ := eLpNorm (id : ℝ → ℝ) q (gaussianReal 0 1) with hmN_def
  have hmN : mN ≠ ⊤ := (memLp_id_gaussianReal' q ENNReal.ofReal_ne_top).eLpNorm_ne_top
  have hT1 : eLpNorm (fun ω => S.ξ γ * h ω) q stdP =
      ENNReal.ofReal (S.ξ γ * (Real.sqrt v * mN.toReal)) := by
    have e : (fun ω => S.ξ γ * h ω) = S.ξ γ • h := rfl
    rw [e, eLpNorm_const_smul, eLpNorm_of_hasLaw_gaussianReal hlawh,
      Real.enorm_eq_ofReal hξ.le, ENNReal.ofReal_mul hξ.le,
      ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hmN]
  -- the concentration term, transferred along the law of `Y`
  have hT2 : eLpNorm (fun ω => Y ω - S.b γ) q stdP ≤ ENNReal.ofReal (Cc * S.ξ γ) := by
    have hlaw := S.map_log_D_sub hγ hγ2 hzw
    have hg : Measurable fun x : ℝ => x - S.b γ := measurable_id.sub_const _
    have e1 : (fun ω => Y ω - S.b γ) = (fun x : ℝ => x - S.b γ) ∘ Y := rfl
    have e2 : (fun ω => Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) =
        (fun x : ℝ => x - S.b γ) ∘ fun ω => Real.log ((S.D γ ω).1 (0, 1)) := rfl
    rw [e1, ← eLpNorm_map_measure hg.aestronglyMeasurable hm_Y.aemeasurable]
    have e3 : stdP.map Y = stdP.map fun ω => Real.log ((S.D γ ω).1 (0, 1)) := hlaw
    rw [e3, eLpNorm_map_measure hg.aestronglyMeasurable
      (S.measurable_log_D γ 0 1).aemeasurable, ← e2]
    exact hconc
  -- the deterministic term
  have hT3 : eLpNorm (fun _ : Coord => (a - 1) * Real.log r) q stdP ≤
      ENNReal.ofReal (max C1 0 * S.ξ γ * |Real.log r|) := by
    rw [eLpNorm_const_prob _ hq0, Real.enorm_eq_ofReal_abs, abs_mul]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact hexp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hξ.le)
  have hX : eLpNorm X q stdP ≤ ENNReal.ofReal (S.ξ γ *
      (Real.sqrt v * mN.toReal + max Cc 0 + max C1 0 * |Real.log r|)) := by
    have hm1 : AEStronglyMeasurable (fun ω => S.ξ γ * h ω) stdP :=
      (hm_h.const_mul _).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun ω => Y ω - S.b γ) stdP :=
      (hm_Y.sub_const _).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (fun _ : Coord => (a - 1) * Real.log r) stdP :=
      aestronglyMeasurable_const
    have hCc : ENNReal.ofReal (Cc * S.ξ γ) ≤ ENNReal.ofReal (max Cc 0 * S.ξ γ) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hξ.le)
    rw [hXeq]
    calc eLpNorm ((fun ω => S.ξ γ * h ω) + (fun ω => Y ω - S.b γ) +
          (fun _ => (a - 1) * Real.log r)) q stdP
        ≤ eLpNorm ((fun ω => S.ξ γ * h ω) + (fun ω => Y ω - S.b γ)) q stdP +
            eLpNorm (fun _ : Coord => (a - 1) * Real.log r) q stdP :=
          eLpNorm_add_le (hm1.add hm2) hm3 hq1
      _ ≤ eLpNorm (fun ω => S.ξ γ * h ω) q stdP + eLpNorm (fun ω => Y ω - S.b γ) q stdP +
            eLpNorm (fun _ : Coord => (a - 1) * Real.log r) q stdP := by
          gcongr
          exact eLpNorm_add_le hm1 hm2 hq1
      _ ≤ ENNReal.ofReal (S.ξ γ * (Real.sqrt v * mN.toReal)) +
            ENNReal.ofReal (max Cc 0 * S.ξ γ) +
            ENNReal.ofReal (max C1 0 * S.ξ γ * |Real.log r|) := by
          rw [hT1]
          gcongr
          exact hT2.trans hCc
      _ = ENNReal.ofReal (S.ξ γ *
            (Real.sqrt v * mN.toReal + max Cc 0 + max C1 0 * |Real.log r|)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  -- Step 1c: `‖r + e^{-b} D(z,w)‖_{2P₀} ≤ r + e^{C_b} √r C_A`
  set CA : ℝ := (C6 ^ (1 / (2 * P0))).toReal with hCA_def
  have hCA6 : C6 ^ (1 / (2 * P0)) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hC6
  have hzK : z ∈ Metric.closedBall (0 : ℂ) ρ0 := mem_closedBall_zero_iff.2 hz
  have hwK : w ∈ Metric.closedBall (0 : ℂ) ρ0 := mem_closedBall_zero_iff.2 hw
  have hDq : eLpNorm Dzw q stdP ≤ ENNReal.ofReal (Real.sqrt r) * C6 ^ (1 / (2 * P0)) := by
    refine eLpNorm_le_of_enorm_le_mul (by linarith) ENNReal.ofReal_ne_top (fun ω => ?_) h6
    rw [Real.enorm_eq_ofReal (contMetric_nonneg (S.D γ ω) z w), mul_comm, Real.sqrt_eq_rpow]
    exact ofReal_le_holderConst_mul (S.D γ ω) hzK hwK
  have hexpb : Real.exp (-S.b γ) ≤ Real.exp Cb :=
    Real.exp_le_exp.2 ((neg_le_abs _).trans hb)
  have hG : eLpNorm G q stdP ≤ ENNReal.ofReal (r + Real.exp Cb * Real.sqrt r * CA) := by
    have hGeq : G = (fun _ => r) + fun ω => Real.exp (-S.b γ) * Dzw ω := rfl
    have hm2 : AEStronglyMeasurable (fun ω => Real.exp (-S.b γ) * Dzw ω) stdP :=
      (hm_D.const_mul _).aestronglyMeasurable
    rw [hGeq]
    calc eLpNorm ((fun _ => r) + fun ω => Real.exp (-S.b γ) * Dzw ω) q stdP
        ≤ eLpNorm (fun _ : Coord => r) q stdP +
            eLpNorm (fun ω => Real.exp (-S.b γ) * Dzw ω) q stdP :=
          eLpNorm_add_le aestronglyMeasurable_const hm2 hq1
      _ = ENNReal.ofReal r + ENNReal.ofReal (Real.exp (-S.b γ)) * eLpNorm Dzw q stdP := by
          rw [eLpNorm_const_prob _ hq0, Real.enorm_eq_ofReal hr.le,
            show (fun ω => Real.exp (-S.b γ) * Dzw ω) = Real.exp (-S.b γ) • Dzw from rfl,
            eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal (Real.exp Cb) *
            (ENNReal.ofReal (Real.sqrt r) * C6 ^ (1 / (2 * P0))) := by
          gcongr
      _ = ENNReal.ofReal (r + Real.exp Cb * Real.sqrt r * CA) := by
          rw [hCA_def, ← ENNReal.ofReal_toReal hCA6, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
            ← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_add hr.le (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
          ring_nf
  -- Step 1d: the variance bound and the deterministic estimate
  have hv : v ≤ Real.posLog r⁻¹ + 2 * Real.posLog (3 * ρ0) := by
    have hE : energy σ σ ≤ Real.posLog r⁻¹ + 2 * Real.posLog (‖z‖ + r) := by
      have h := energy_circleMeasure_le z (r := ‖w - z‖) (by rw [hrwz]; exact hr)
      refine h.trans (le_of_eq ?_)
      rw [hrwz]
    have h3 : Real.posLog (‖z‖ + r) ≤ Real.posLog (3 * ρ0) :=
      Real.posLog_le_posLog (by linarith [norm_nonneg z, hr.le]) (by linarith)
    have hvmax : v = max (energy σ σ) 0 := Real.coe_toNNReal' _
    rw [hvmax]
    refine max_le (hE.trans (by linarith)) ?_
    have := Real.posLog_nonneg (x := r⁻¹)
    have := Real.posLog_nonneg (x := 3 * ρ0)
    linarith
  have hdet := pair_bound_le (v := v) (m := mN.toReal) (Cc := max Cc 0) (C1 := max C1 0)
    (E := Real.exp Cb) (CA := CA) hr hrρ (by have := Real.posLog_nonneg (x := 3 * ρ0); linarith)
    hv ENNReal.toReal_nonneg (le_max_right _ _) (le_max_right _ _) (Real.exp_pos _).le
    ENNReal.toReal_nonneg
  calc eLpNorm (fun ω => Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖)
        (ENNReal.ofReal P0) stdP
      ≤ eLpNorm X q stdP * eLpNorm G q stdP := step1
    _ ≤ ENNReal.ofReal (S.ξ γ *
          (Real.sqrt v * mN.toReal + max Cc 0 + max C1 0 * |Real.log r|)) *
        ENNReal.ofReal (r + Real.exp Cb * Real.sqrt r * CA) := by gcongr
    _ = ENNReal.ofReal (S.ξ γ *
          ((Real.sqrt v * mN.toReal + max Cc 0 + max C1 0 * |Real.log r|) *
            (r + Real.exp Cb * Real.sqrt r * CA))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal (S.ξ γ * pairConst ρ0 P0 Cc C1 Cb C6) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hξ.le)
        exact hdet

/-- **Blueprint Lemma `lem:euclidean`, Steps 1–2 (fixed endpoints).** For `ρ₀ ∈ ℝ` and `P₀ ≥ 1`
there are `γ_* > 0` and `K` such that for `γ ∈ (0, γ_*]` and all `z, w ∈ B̄_{ρ₀}(0)`,
`‖e^{-b_γ} D^γ(z,w) - |z - w|‖_{P₀} ≤ K ξ_γ`. -/
theorem exists_eLpNorm_pair_le (ρ0 : ℝ) {P0 : ℝ} (hP0 : 1 ≤ P0) :
    ∃ γs K : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ z w : ℂ, ‖z‖ ≤ ρ0 → ‖w‖ ≤ ρ0 →
      eLpNorm (fun ω => Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖)
        (ENNReal.ofReal P0) stdP ≤ ENNReal.ofReal (K * S.ξ γ) := by
  obtain ⟨γc, Cc, hγc, hconc⟩ := S.concentration (2 * P0) (by linarith)
  obtain ⟨γe, C1, hγe, hγe2, hexp⟩ := S.exists_exponents
  obtain ⟨γb, Cb, hγb, hb⟩ := S.abs_b_le
  obtain ⟨γ6, hγ6, h6⟩ := S.S6 (2 * P0) (by linarith)
  obtain ⟨C6, hC6, hC6b⟩ := h6 (Metric.closedBall 0 ρ0) (isCompact_closedBall _ _) 1 one_pos
  refine ⟨min (min γc γe) (min γb γ6), pairConst ρ0 P0 Cc C1 Cb C6,
    lt_min (lt_min hγc hγe) (lt_min hγb hγ6), fun γ hγ z w hz hw => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγc' : γ ≤ γc := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγe' : γ ≤ γe := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγb' : γ ≤ γb := hγle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ6' : γ ≤ γ6 := hγle.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [mul_comm]
  exact S.eLpNorm_pair_le hγ0 (lt_of_le_of_lt hγe' hγe2) hP0 hz hw hC6 (hconc γ ⟨hγ0, hγc'⟩)
    (hexp γ ⟨hγ0, hγe'⟩).2.2.2 (hb γ ⟨hγ0, hγb'⟩) (hC6b γ ⟨hγ0, hγ6'⟩).1

end Setup

end GaussianLQG
