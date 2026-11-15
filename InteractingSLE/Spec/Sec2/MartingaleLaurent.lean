import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Spec.Ito.Loewner
import InteractingSLE.Spec.Sec2.MartingaleQV
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Laurent coefficients of the coupling mean at `∞` (deterministic layer of Theorem 2.4)

Packet PROVE-SEC2-MART. Specification, proof of Theorem 2.4 (`source/spec/p001-048.md`, anchor
`thm-2.4-proof`, L828–L866): `𝔥_t(z) = Im H_t(z)` with `H_t` of (2.5). Instead of Itô's formula for
a general semimartingale driver (not available), the proof of the converse implication here reads
off the two lowest Laurent coefficients of `𝔥_t(z)` at `z = ∞`, uniformly in time: with
`N = 2W + ∑ⱼ ρⱼ Vʲ` and `Q = W² + ½ ∑ⱼ ρⱼ (Vʲ)² − (2 ∑ⱼ ρⱼ + κ) t` (`driftValue`, `quadValue`),

* `Y (φ_t(iY) − φ₀) = −N_t/√κ + O(Y⁻²)`,
* `2Y² √κ (φ_t(Y(1+i)) − φ₁) = −Y N_t − Q_t + O(Y⁻¹)`,

where `φ_t(z) = −(1/√κ) (2 arg f_t(z) + ∑ⱼ ρⱼ arg (g_t(z) − Vʲ)) − χ Im log f_t′(z)` is the
non-constant part of the coupling mean (`harmPart`) and `φ₀, φ₁` are constants. The `O`-terms are
uniform over drivers bounded by `K` on `[0, t]`, `t ≤ T`, and force points bounded by `K`.

## Main results

* `norm_log_expansion_le`: `log (z + a + b/z + e) = log z + a/z + (b − a²/2)/z² + O(|z|⁻³)` in the
  sector `0 ≤ arg z ≤ π/2` (with the principal branch);
* `norm_logDerivFwd_add_le`: `log f_t′(z) = −2t/z² + O(|z|⁻³)`;
* `abs_harmPart_sub_harmMain_le`: the expansion of `φ_t(z)` to order `|z|⁻³`;
* `abs_laurent_one_le`, `abs_laurent_two_le`: the two coefficient estimates above.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE

namespace MartChar

/-! ### The logarithm near `∞` -/

lemma norm_log_one_add_sub_le {δ : ℂ} (hδ : ‖δ‖ ≤ 1 / 2) :
    ‖Complex.log (1 + δ) - (δ - δ ^ 2 / 2)‖ ≤ ‖δ‖ ^ 3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2 (lt_of_le_of_lt hδ (by norm_num))
  have hT : Complex.logTaylor (2 + 1) δ = δ - δ ^ 2 / 2 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  rw [hT] at h
  refine h.trans ?_
  have h1 : (1 - ‖δ‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h3 : 0 ≤ ‖δ‖ ^ 3 := by positivity
  calc ‖δ‖ ^ (2 + 1) * (1 - ‖δ‖)⁻¹ / (2 + 1) ≤ ‖δ‖ ^ 3 * 2 / 3 := by
        rw [show (2 + 1 : ℕ) = 3 from rfl]
        gcongr
        norm_num
    _ ≤ ‖δ‖ ^ 3 := by linarith

/-- The constant of `norm_log_expansion_le`. -/
def logConst (A B E : ℝ) : ℝ := E + A * (B + E) + (B + E) ^ 2 + (A + B + E) ^ 3

/-- **Expansion of the logarithm at `∞`.** In the sector `0 ≤ arg z ≤ π/2`, for
`‖a‖ ≤ A`, `‖b‖ ≤ B`, `‖e‖ ≤ E/‖z‖²` and `‖z‖ ≥ max 1 (2 (A + B + E))`,
`‖log (z + a + b/z + e) − log z − a/z − (b − a²/2)/z²‖ ≤ logConst A B E / ‖z‖³`. -/
theorem norm_log_expansion_le {z a b e : ℂ} {A B E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (harg0 : 0 ≤ arg z) (harg1 : arg z ≤ Real.pi / 2) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (he : ‖e‖ ≤ E / ‖z‖ ^ 2) (hz1 : 1 ≤ ‖z‖) (hz2 : 2 * (A + B + E) ≤ ‖z‖) :
    ‖Complex.log (z + a + b / z + e) - Complex.log z - a / z - (b - a ^ 2 / 2) / z ^ 2‖
      ≤ logConst A B E / ‖z‖ ^ 3 := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set u : ℂ := z⁻¹ with hu
  have hun : ‖u‖ = ‖z‖⁻¹ := by rw [hu, norm_inv]
  have hu1 : ‖u‖ ≤ 1 := by rw [hun]; exact inv_le_one_of_one_le₀ hz1
  set δ : ℂ := (a + b * u + e) * u with hδ
  set β : ℂ := b * u ^ 2 + e * u with hβ
  have hp : z + a + b / z + e = z * (1 + δ) := by
    rw [hδ, hu]; field_simp; ring
  -- size of `δ`
  have he' : ‖e‖ ≤ E * ‖u‖ ^ 2 := by rw [hun, inv_pow, ← div_eq_mul_inv]; exact he
  have hδn : ‖δ‖ ≤ (A + B + E) * ‖u‖ := by
    rw [hδ, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖a + b * u + e‖ ≤ ‖a‖ + ‖b‖ * ‖u‖ + ‖e‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [← norm_mul]; exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ A + B * 1 + E * 1 := by
          have hu2 : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
          gcongr
          exact he'.trans (mul_le_mul_of_nonneg_left hu2 hE)
      _ = A + B + E := by ring
  have hABE : (A + B + E) * ‖u‖ ≤ 1 / 2 := by
    rw [hun, ← div_eq_mul_inv, div_le_iff₀ hnz]; linarith
  have hδ12 : ‖δ‖ ≤ 1 / 2 := hδn.trans hABE
  -- the branch of the logarithm
  have h1δ : 0 < (1 + δ).re := by
    have := Complex.abs_re_le_norm δ
    have : -‖δ‖ ≤ δ.re := (abs_le.1 this).1
    simp only [add_re, one_re]; linarith
  have h1δ0 : (1 + δ) ≠ 0 := fun h => by rw [h, zero_re] at h1δ; exact lt_irrefl _ h1δ
  have harg : |arg (1 + δ)| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h1δ)
  have hlog : Complex.log (z * (1 + δ)) = Complex.log z + Complex.log (1 + δ) := by
    refine Complex.log_mul hz0 h1δ0 ⟨?_, ?_⟩
    · linarith [(abs_lt.1 harg).1, Real.pi_pos]
    · linarith [(abs_lt.1 harg).2, Real.pi_pos]
  -- the algebraic identity
  have hid : Complex.log (z + a + b / z + e) - Complex.log z - a / z - (b - a ^ 2 / 2) / z ^ 2
      = (Complex.log (1 + δ) - (δ - δ ^ 2 / 2)) + (e * u - (a * u) * β - β ^ 2 / 2) := by
    rw [hp, hlog]
    have h1 : a / z = a * u := by rw [hu, div_eq_mul_inv]
    have h2 : (b - a ^ 2 / 2) / z ^ 2 = (b - a ^ 2 / 2) * u ^ 2 := by
      rw [hu, div_eq_mul_inv, inv_pow]
    rw [h1, h2, hδ, hβ]
    ring
  rw [hid]
  -- the bounds
  have hβn : ‖β‖ ≤ (B + E) * ‖u‖ ^ 2 := by
    rw [hβ]
    calc ‖b * u ^ 2 + e * u‖ ≤ ‖b‖ * ‖u‖ ^ 2 + ‖e‖ * ‖u‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ B * ‖u‖ ^ 2 + E * ‖u‖ ^ 2 * 1 := by
          have h1 : ‖e‖ * ‖u‖ ≤ E * ‖u‖ ^ 2 * 1 :=
            mul_le_mul he' hu1 (norm_nonneg _) (by positivity)
          have h2 : ‖b‖ * ‖u‖ ^ 2 ≤ B * ‖u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hb (by positivity)
          linarith
      _ = (B + E) * ‖u‖ ^ 2 := by ring
  have hu3 : ‖u‖ ^ 3 = 1 / ‖z‖ ^ 3 := by rw [hun, inv_pow, one_div]
  have hu4 : ‖u‖ ^ 4 ≤ ‖u‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hu1 (by norm_num)
  have t1 : ‖Complex.log (1 + δ) - (δ - δ ^ 2 / 2)‖ ≤ (A + B + E) ^ 3 * ‖u‖ ^ 3 := by
    refine (norm_log_one_add_sub_le hδ12).trans ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hδn 3
  have t2 : ‖e * u‖ ≤ E * ‖u‖ ^ 3 := by
    rw [norm_mul]
    calc ‖e‖ * ‖u‖ ≤ E * ‖u‖ ^ 2 * ‖u‖ := mul_le_mul_of_nonneg_right he' (norm_nonneg _)
      _ = E * ‖u‖ ^ 3 := by ring
  have t3 : ‖(a * u) * β‖ ≤ A * (B + E) * ‖u‖ ^ 3 := by
    rw [norm_mul, norm_mul]
    calc ‖a‖ * ‖u‖ * ‖β‖ ≤ A * ‖u‖ * ((B + E) * ‖u‖ ^ 2) := by gcongr
      _ = A * (B + E) * ‖u‖ ^ 3 := by ring
  have t4 : ‖β ^ 2 / 2‖ ≤ (B + E) ^ 2 * ‖u‖ ^ 3 := by
    rw [norm_div, norm_pow, Complex.norm_ofNat]
    calc ‖β‖ ^ 2 / 2 ≤ ((B + E) * ‖u‖ ^ 2) ^ 2 / 1 := by
          have := pow_le_pow_left₀ (norm_nonneg _) hβn 2
          have h0 : 0 ≤ ‖β‖ ^ 2 := by positivity
          linarith
      _ = (B + E) ^ 2 * ‖u‖ ^ 4 := by ring
      _ ≤ (B + E) ^ 2 * ‖u‖ ^ 3 := mul_le_mul_of_nonneg_left hu4 (by positivity)
  calc ‖(Complex.log (1 + δ) - (δ - δ ^ 2 / 2)) + (e * u - (a * u) * β - β ^ 2 / 2)‖
      ≤ ‖Complex.log (1 + δ) - (δ - δ ^ 2 / 2)‖ + (‖e * u‖ + ‖(a * u) * β‖ + ‖β ^ 2 / 2‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ ≤ (A + B + E) ^ 3 * ‖u‖ ^ 3 + (E * ‖u‖ ^ 3 + A * (B + E) * ‖u‖ ^ 3
        + (B + E) ^ 2 * ‖u‖ ^ 3) := by gcongr
    _ = logConst A B E / ‖z‖ ^ 3 := by
        rw [hu3, logConst]; ring

/-! ### The Loewner flow near `∞` -/

section Flow

variable {w : ℝ → ℝ}

/-- Points of `ℍ` far from the origin are not swallowed (QuantumZipper's
`CaraR.fwdHull_subset_closedBall`, `K_t ⊆ B̄(0, K + 3√t)`). -/
lemma mem_diff_fwdHull_of_norm (hw : Continuous w) {t K : ℝ} (ht : 0 ≤ t)
    (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) {z : ℂ} (hzH : z ∈ H) (hz : K + 3 * Real.sqrt t < ‖z‖) :
    z ∈ H \ QuantumZipper.fwdHull w t := by
  refine ⟨hzH, fun hzK => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have hle : QuantumZipper.swallowTime w z ≤ ENNReal.ofReal 0 := hzK.2
    rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hle
    exact (QuantumZipper.swallowTime_pos hw hzH).ne' hle
  · have h := QuantumZipper.CaraR.fwdHull_subset_closedBall hw hpos hK hzK
    rw [Metric.mem_closedBall, dist_zero_right] at h
    linarith

/-- **`log f_t′(z) = −2t/z² + O(|z|⁻³)`**, with `D = 24K + 8√t` the displacement bound. -/
theorem norm_logDerivFwd_add_le (hw : Continuous w) (hw0 : w 0 = 0) {t K : ℝ} (ht : 0 ≤ t)
    (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull w t)
    (hzD : 2 * (24 * K + 8 * Real.sqrt t) ≤ ‖z‖) :
    ‖QuantumZipper.logDerivFwd w t z + 2 * t / z ^ 2‖
      ≤ 24 * (24 * K + 8 * Real.sqrt t) * t / ‖z‖ ^ 3 := by
  set D := 24 * K + 8 * Real.sqrt t with hD
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hD0 : 0 ≤ D := by positivity
  have hz0 : z ≠ 0 := fun h => by
    have h1 : 0 < z.im := hz.1
    rw [h, Complex.zero_im] at h1
    exact lt_irrefl _ h1
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hzD' : D ≤ ‖z‖ := by linarith
  -- pointwise bound
  have hpt : ∀ s ∈ Icc (0 : ℝ) t, ‖2 / (QuantumZipper.fwdMap w s z) ^ 2 - 2 / z ^ 2‖
      ≤ 24 * D / ‖z‖ ^ 3 := by
    intro s hs
    set f := QuantumZipper.fwdMap w s z
    have hf : ‖z‖ / 2 ≤ ‖f‖ := norm_fwdMap_ge_half hw hw0 ht hK hz hzD hs
    have hf0 : 0 < ‖f‖ := lt_of_lt_of_le (by positivity) hf
    have hfz : ‖f - z‖ ≤ D := norm_fwdMap_sub_self_le hw hw0 ht hK hz hs
    have hf0' : f ≠ 0 := norm_pos_iff.1 hf0
    have hid : 2 / f ^ 2 - 2 / z ^ 2 = 2 * ((z - f) * (z + f)) / (f ^ 2 * z ^ 2) := by
      field_simp; ring
    rw [hid, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
    have hzf : ‖z + f‖ ≤ 3 * ‖z‖ := by
      calc ‖z + f‖ = ‖2 * z + (f - z)‖ := by ring_nf
        _ ≤ ‖2 * z‖ + ‖f - z‖ := norm_add_le _ _
        _ ≤ 3 * ‖z‖ := by rw [norm_mul, Complex.norm_ofNat]; linarith
    have hzf' : ‖z - f‖ ≤ D := by rw [norm_sub_rev]; exact hfz
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 * (‖z - f‖ * ‖z + f‖) * ‖z‖ ^ 3 ≤ 2 * (D * (3 * ‖z‖)) * ‖z‖ ^ 3 := by gcongr
      _ = 24 * D * ((‖z‖ / 2) ^ 2 * ‖z‖ ^ 2) := by ring
      _ ≤ 24 * D * (‖f‖ ^ 2 * ‖z‖ ^ 2) := by gcongr
  -- the integral
  have hcont : ContinuousOn (fun s => 2 / (QuantumZipper.fwdMap w s z) ^ 2) (Icc 0 t) :=
    continuousOn_const.div ((Ito.continuousOn_fwdMap_time' hw ht hz).pow 2) fun s hs =>
      pow_ne_zero 2 (Ito.fwdMap_ne_zero hw ht hz hs)
  have hint : IntervalIntegrable (fun s => 2 / (QuantumZipper.fwdMap w s z) ^ 2) MeasureTheory.volume
      0 t := (hcont.mono (by rw [uIcc_of_le ht])).intervalIntegrable
  have heq : QuantumZipper.logDerivFwd w t z + 2 * t / z ^ 2
      = -∫ s in (0 : ℝ)..t, (2 / (QuantumZipper.fwdMap w s z) ^ 2 - 2 / z ^ 2) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      QuantumZipper.logDerivFwd, sub_zero, Complex.real_smul]
    ring
  rw [heq, norm_neg]
  calc ‖∫ s in (0 : ℝ)..t, (2 / (QuantumZipper.fwdMap w s z) ^ 2 - 2 / z ^ 2)‖
      ≤ 24 * D / ‖z‖ ^ 3 * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
          rw [uIoc_of_le ht] at hs
          exact hpt s ⟨hs.1.le, hs.2⟩
    _ = 24 * D * t / ‖z‖ ^ 3 := by rw [sub_zero, abs_of_nonneg ht]; ring

end Flow

/-! ### The non-constant part of the coupling mean -/

section Harm

variable {ι : Type*} [Fintype ι] {w : ℝ → ℝ}

/-- The non-constant part of the coupling mean (2.5),
`φ_t(z) = −(1/√κ) (2 arg f_t(z) + ∑ⱼ ρⱼ arg (g_t(z) − vʲ)) − χ Im log f_t′(z)`, for uncentred
force-point positions `v` (`g_t(z) − vʲ = f_t(z) + w_t − vʲ`). -/
def harmPart (κ : ℝ) (ρ : ι → ℝ) (w : ℝ → ℝ) (t : ℝ) (v : ι → ℝ) (z : ℂ) : ℝ :=
  -(1 / Real.sqrt κ) * (2 * arg (QuantumZipper.fwdMap w t z)
      + ∑ j, ρ j * arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j : ℂ)))
    - QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t z).im

/-- The second-order expansion of `arg (g_t(z) − c)` at `∞`. -/
def argMain (c t : ℝ) (z : ℂ) : ℝ :=
  arg z + (-(c : ℂ) / z).im + ((2 * (t : ℂ) - (c : ℂ) ^ 2 / 2) / z ^ 2).im

/-- The second-order expansion of `harmPart` at `∞`. -/
def harmMain (κ : ℝ) (ρ : ι → ℝ) (c t : ℝ) (v : ι → ℝ) (z : ℂ) : ℝ :=
  -(1 / Real.sqrt κ) * (2 * argMain c t z + ∑ j, ρ j * argMain (v j) t z)
    - QuantumZipper.chiC κ * (-(2 * (t : ℂ)) / z ^ 2).im

/-- The displacement constant `D = 24K + 8√T`. -/
def dispConst (K T : ℝ) : ℝ := 24 * K + 8 * Real.sqrt T

/-- The radius beyond which the expansions hold. -/
def laurentRadius (K T : ℝ) : ℝ :=
  max 1 (max (2 * (K + 2 * T + 4 * dispConst K T * T))
    (max (2 * dispConst K T + 1) (K + 3 * Real.sqrt T + 1)))

lemma one_le_laurentRadius (K T : ℝ) : 1 ≤ laurentRadius K T := le_max_left _ _

/-- **Expansion of `arg (g_t(z) − c)`**: the error is at most
`logConst K (2T) (4 D T) / ‖z‖³`. -/
theorem abs_arg_sub_argMain_le (hw : Continuous w) (hw0 : w 0 = 0) {t T K c : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) (hc : |c| ≤ K) {z : ℂ}
    (hzH : z ∈ H) (harg0 : 0 ≤ arg z) (harg1 : arg z ≤ Real.pi / 2)
    (hzR : laurentRadius K T ≤ ‖z‖) :
    z ∈ H \ QuantumZipper.fwdHull w t ∧
      |arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (c : ℂ)) - argMain c t z|
        ≤ logConst K (2 * T) (4 * dispConst K T * T) / ‖z‖ ^ 3 := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hT0 : 0 ≤ T := ht.trans htT
  have hsq : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hDt : dispConst K t ≤ dispConst K T := by simp only [dispConst]; linarith
  have hD0 : 0 ≤ dispConst K t := by simp only [dispConst]; positivity
  have hR1 : 1 ≤ ‖z‖ := (one_le_laurentRadius K T).trans hzR
  have hR2 : 2 * (K + 2 * T + 4 * dispConst K T * T) ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hzR)
  have hR3 : 2 * dispConst K T + 1 ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hz : z ∈ H \ QuantumZipper.fwdHull w t :=
    mem_diff_fwdHull_of_norm hw ht hK hzH (by linarith)
  refine ⟨hz, ?_⟩
  have hnz : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hnz
  -- the error term of the hydrodynamic expansion
  set e : ℂ := QuantumZipper.fwdMap w t z + (w t : ℂ) - z - 2 * (t : ℂ) / z with he_def
  have hzD : 2 * (24 * K + 8 * Real.sqrt t) < ‖z‖ := by
    have : 2 * dispConst K t ≤ 2 * dispConst K T := by linarith
    simp only [dispConst] at this hR3
    linarith
  have hhyd := norm_mul_fwdMap_add_sub_sub_le hw hw0 ht hK hz hzD
  have he : ‖e‖ ≤ 4 * dispConst K T * T / ‖z‖ ^ 2 := by
    have hid : e = (z * (QuantumZipper.fwdMap w t z + (w t : ℂ) - z) - ((2 * t : ℝ) : ℂ)) / z := by
      rw [he_def]; push_cast; field_simp
    rw [hid, norm_div]
    rw [div_le_div_iff₀ hnz (by positivity)]
    calc ‖z * (QuantumZipper.fwdMap w t z + (w t : ℂ) - z) - ((2 * t : ℝ) : ℂ)‖ * ‖z‖ ^ 2
        ≤ 4 * (24 * K + 8 * Real.sqrt t) * t / ‖z‖ * ‖z‖ ^ 2 := by gcongr
      _ = 4 * dispConst K t * t * ‖z‖ := by simp only [dispConst]; field_simp
      _ ≤ 4 * dispConst K T * T * ‖z‖ := by
          have : 0 ≤ dispConst K T := hD0.trans hDt
          gcongr
  -- apply the logarithm expansion
  have hp : QuantumZipper.fwdMap w t z + (w t : ℂ) - (c : ℂ) = z + (-(c : ℂ)) + (2 * (t : ℂ)) / z + e := by
    rw [he_def]; ring
  have hlog := norm_log_expansion_le (a := -(c : ℂ)) (b := 2 * (t : ℂ)) (e := e) hK0
    (by positivity : (0 : ℝ) ≤ 2 * T) (by simp only [dispConst]; positivity) harg0 harg1
    (by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hc)
    (by rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]; linarith)
    he hR1 hR2
  rw [hp, ← Complex.log_im]
  have hneg : (-(c : ℂ)) ^ 2 = (c : ℂ) ^ 2 := by ring
  rw [hneg] at hlog
  refine le_trans ?_ hlog
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  simp only [argMain, ← Complex.log_im, sub_im]
  ring_nf

/-- The constant of `abs_harmPart_sub_harmMain_le`. -/
def harmConst (κ : ℝ) (ρ : ι → ℝ) (K T : ℝ) : ℝ :=
  1 / Real.sqrt κ * (2 + ∑ j, |ρ j|) * logConst K (2 * T) (4 * dispConst K T * T)
    + |QuantumZipper.chiC κ| * (24 * dispConst K T * T)

/-- **Expansion of the coupling mean at `∞`** to order `|z|⁻³`, uniformly over drivers and force
points bounded by `K` on `[0, t]`, `t ≤ T`. -/
theorem abs_harmPart_sub_harmMain_le (κ : ℝ) (ρ : ι → ℝ) (hw : Continuous w) (hw0 : w 0 = 0)
    {t T K : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) {v : ι → ℝ}
    (hv : ∀ j, |v j| ≤ K) {z : ℂ} (hzH : z ∈ H) (harg0 : 0 ≤ arg z) (harg1 : arg z ≤ Real.pi / 2)
    (hzR : laurentRadius K T ≤ ‖z‖) :
    |harmPart κ ρ w t v z - harmMain κ ρ (w t) t v z| ≤ harmConst κ ρ K T / ‖z‖ ^ 3 := by
  set Lc := logConst K (2 * T) (4 * dispConst K T * T) with hLc
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hR1 : 1 ≤ ‖z‖ := (one_le_laurentRadius K T).trans hzR
  have hnz : 0 < ‖z‖ := by linarith
  have hw_t : |w t| ≤ K := hK t ⟨ht, le_rfl⟩
  obtain ⟨hz, hf⟩ := abs_arg_sub_argMain_le hw hw0 ht htT hK hw_t hzH harg0 harg1 hzR
  rw [add_sub_cancel_right] at hf
  have hvj := fun j => (abs_arg_sub_argMain_le hw hw0 ht htT hK (hv j) hzH harg0 harg1 hzR).2
  -- the logarithmic derivative
  have hR3 : 2 * dispConst K T + 1 ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hDt : dispConst K t ≤ dispConst K T := by
    simp only [dispConst]; linarith [Real.sqrt_le_sqrt htT]
  have hD0 : 0 ≤ dispConst K t := by simp only [dispConst]; positivity
  have hL := norm_logDerivFwd_add_le hw hw0 ht hK hz (by simp only [dispConst] at hDt hR3; linarith)
  have hLim : |(QuantumZipper.logDerivFwd w t z).im - (-(2 * (t : ℂ)) / z ^ 2).im|
      ≤ 24 * dispConst K T * T / ‖z‖ ^ 3 := by
    have h1 : (QuantumZipper.logDerivFwd w t z).im - (-(2 * (t : ℂ)) / z ^ 2).im
        = (QuantumZipper.logDerivFwd w t z + 2 * t / z ^ 2).im := by
      simp only [add_im, neg_div, neg_im]; ring
    rw [h1]
    refine (Complex.abs_im_le_norm _).trans (hL.trans ?_)
    have hD0' : 0 ≤ 24 * K + 8 * Real.sqrt t := by positivity
    have hDT0 : 0 ≤ dispConst K T := by simp only [dispConst]; positivity
    have hnum : 24 * (24 * K + 8 * Real.sqrt t) * t ≤ 24 * dispConst K T * T := by
      have h2 : 24 * K + 8 * Real.sqrt t ≤ dispConst K T := hDt
      have := mul_le_mul h2 htT ht hDT0
      linarith
    exact div_le_div_of_nonneg_right hnum (by positivity)
  -- combine
  have hid : harmPart κ ρ w t v z - harmMain κ ρ (w t) t v z
      = -(1 / Real.sqrt κ) * (2 * (arg (QuantumZipper.fwdMap w t z) - argMain (w t) t z)
          + ∑ j, ρ j * (arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j : ℂ))
            - argMain (v j) t z))
        - QuantumZipper.chiC κ * ((QuantumZipper.logDerivFwd w t z).im
          - (-(2 * (t : ℂ)) / z ^ 2).im) := by
    simp only [harmPart, harmMain, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  have hsum : |∑ j, ρ j * (arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j : ℂ))
      - argMain (v j) t z)| ≤ (∑ j, |ρ j|) * (Lc / ‖z‖ ^ 3) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvj j) (abs_nonneg _)
  have hsk : 0 ≤ 1 / Real.sqrt κ := by positivity
  calc |-(1 / Real.sqrt κ) * (2 * (arg (QuantumZipper.fwdMap w t z) - argMain (w t) t z)
          + ∑ j, ρ j * (arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j : ℂ))
            - argMain (v j) t z))
        - QuantumZipper.chiC κ * ((QuantumZipper.logDerivFwd w t z).im
          - (-(2 * (t : ℂ)) / z ^ 2).im)|
      ≤ 1 / Real.sqrt κ * (2 * (Lc / ‖z‖ ^ 3) + (∑ j, |ρ j|) * (Lc / ‖z‖ ^ 3))
        + |QuantumZipper.chiC κ| * (24 * dispConst K T * T / ‖z‖ ^ 3) := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_neg, abs_of_nonneg hsk]
          refine mul_le_mul_of_nonneg_left ?_ hsk
          refine (abs_add_le _ _).trans (add_le_add ?_ hsum)
          rw [abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left hf (by norm_num)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hLim (abs_nonneg _)
    _ = harmConst κ ρ K T / ‖z‖ ^ 3 := by
        simp only [harmConst, ← hLc]; field_simp

/-! ### The two Laurent coefficients -/

lemma im_neg_div_mul_I (c Y : ℝ) : (-(c : ℂ) / ((Y : ℂ) * I)).im = c / Y := by
  simp [Complex.div_im, Complex.normSq_apply]
  field_simp

lemma im_div_mul_I_sq (d Y : ℝ) : ((d : ℂ) / ((Y : ℂ) * I) ^ 2).im = 0 := by
  simp [Complex.div_im, Complex.normSq_apply, pow_two]

lemma im_neg_div_mul_one_add_I (c Y : ℝ) (hY : 0 < Y) :
    (-(c : ℂ) / ((Y : ℂ) * (1 + I))).im = c / (2 * Y) := by
  simp [Complex.div_im, Complex.normSq_apply]
  field_simp
  ring

lemma im_div_mul_one_add_I_sq (d Y : ℝ) (hY : 0 < Y) :
    ((d : ℂ) / ((Y : ℂ) * (1 + I)) ^ 2).im = -d / (2 * Y ^ 2) := by
  simp [Complex.div_im, Complex.normSq_apply, pow_two]
  field_simp
  ring

lemma argMain_mul_I (c t Y : ℝ) (hY : 0 < Y) :
    argMain c t ((Y : ℂ) * I) = arg I + c / Y := by
  have h2 : (2 * (t : ℂ) - (c : ℂ) ^ 2 / 2) = ((2 * t - c ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [argMain, Complex.arg_real_mul _ hY, im_neg_div_mul_I, h2, im_div_mul_I_sq, add_zero]

lemma argMain_mul_one_add_I (c t Y : ℝ) (hY : 0 < Y) :
    argMain c t ((Y : ℂ) * (1 + I)) = arg (1 + I) + c / (2 * Y) - (2 * t - c ^ 2 / 2) / (2 * Y ^ 2) := by
  have h2 : (2 * (t : ℂ) - (c : ℂ) ^ 2 / 2) = ((2 * t - c ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [argMain, Complex.arg_real_mul _ hY, im_neg_div_mul_one_add_I c Y hY, h2,
    im_div_mul_one_add_I_sq _ Y hY]
  ring

/-- The constant `φ₀` of the first coefficient. -/
def phiI (κ : ℝ) (ρ : ι → ℝ) : ℝ := -(1 / Real.sqrt κ) * ((2 + ∑ j, ρ j) * arg I)

/-- The constant `φ₁` of the second coefficient. -/
def phiD (κ : ℝ) (ρ : ι → ℝ) : ℝ := -(1 / Real.sqrt κ) * ((2 + ∑ j, ρ j) * arg (1 + I))

omit [Fintype ι] in
lemma sum_mul_quad [Fintype ι] (ρ v : ι → ℝ) (α β γ : ℝ) :
    ∑ j, ρ j * (α + β * v j + γ * v j ^ 2)
      = α * (∑ j, ρ j) + β * (∑ j, ρ j * v j) + γ * (∑ j, ρ j * v j ^ 2) := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun j _ => by ring

theorem harmMain_mul_I (κ : ℝ) (ρ : ι → ℝ) (c t : ℝ) (v : ι → ℝ) {Y : ℝ} (hY : 0 < Y) :
    Y * (harmMain κ ρ c t v ((Y : ℂ) * I) - phiI κ ρ) = -(driftValue ρ c v / Real.sqrt κ) := by
  have hχ : (-(2 * (t : ℂ)) / ((Y : ℂ) * I) ^ 2).im = 0 := by
    rw [show -(2 * (t : ℂ)) = ((-(2 * t) : ℝ) : ℂ) by push_cast; ring]
    exact im_div_mul_I_sq _ _
  have hs : ∑ j, ρ j * argMain (v j) t ((Y : ℂ) * I)
      = arg I * (∑ j, ρ j) + (1 / Y) * (∑ j, ρ j * v j) + 0 * (∑ j, ρ j * v j ^ 2) := by
    rw [← sum_mul_quad]
    exact Finset.sum_congr rfl fun j _ => by rw [argMain_mul_I _ t Y hY]; ring
  rw [harmMain, hs, argMain_mul_I _ t Y hY, hχ, phiI, driftValue]
  have hY0 : Y ≠ 0 := hY.ne'
  field_simp
  ring

theorem harmMain_mul_one_add_I {κ : ℝ} (hκ : 0 < κ) (ρ : ι → ℝ) (c t : ℝ) (v : ι → ℝ) {Y : ℝ}
    (hY : 0 < Y) :
    2 * Y ^ 2 * Real.sqrt κ * (harmMain κ ρ c t v ((Y : ℂ) * (1 + I)) - phiD κ ρ)
      = -(Y * driftValue ρ c v) - quadValue κ ρ c v t := by
  have hχ : (-(2 * (t : ℂ)) / ((Y : ℂ) * (1 + I)) ^ 2).im = t / Y ^ 2 := by
    rw [show -(2 * (t : ℂ)) = ((-(2 * t) : ℝ) : ℂ) by push_cast; ring,
      im_div_mul_one_add_I_sq _ _ hY]
    ring
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hchi : QuantumZipper.chiC κ = (2 - κ / 2) / Real.sqrt κ := by
    simp only [QuantumZipper.chiC]
    field_simp
    rw [hsq]
  have hY0 : Y ≠ 0 := hY.ne'
  have hs : ∑ j, ρ j * argMain (v j) t ((Y : ℂ) * (1 + I))
      = (arg (1 + I) - 2 * t / (2 * Y ^ 2)) * (∑ j, ρ j) + (1 / (2 * Y)) * (∑ j, ρ j * v j)
        + (1 / (4 * Y ^ 2)) * (∑ j, ρ j * v j ^ 2) := by
    rw [← sum_mul_quad]
    exact Finset.sum_congr rfl fun j _ => by
      rw [argMain_mul_one_add_I _ t Y hY]; field_simp; ring
  rw [harmMain, hs, argMain_mul_one_add_I _ t Y hY, hχ, phiD, driftValue, quadValue, hchi]
  field_simp
  ring

lemma harmConst_nonneg (κ : ℝ) (ρ : ι → ℝ) {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) :
    0 ≤ harmConst κ ρ K T := by
  have hD : 0 ≤ dispConst K T := by simp only [dispConst]; positivity
  have hL : 0 ≤ logConst K (2 * T) (4 * dispConst K T * T) := by
    simp only [logConst]; positivity
  have hρ : 0 ≤ ∑ j, |ρ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  simp only [harmConst]
  positivity

/-- **The first Laurent coefficient**: `Y (φ_t(iY) − φ₀) = −N_t/√κ + O(Y⁻²)`. -/
theorem abs_laurent_one_le (κ : ℝ) (ρ : ι → ℝ) (hw : Continuous w) (hw0 : w 0 = 0) {t T K : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) {v : ι → ℝ}
    (hv : ∀ j, |v j| ≤ K) {Y : ℝ} (hYR : laurentRadius K T ≤ Y) :
    |Y * (harmPart κ ρ w t v ((Y : ℂ) * I) - phiI κ ρ) + driftValue ρ (w t) v / Real.sqrt κ|
      ≤ harmConst κ ρ K T / Y ^ 2 := by
  have hY : 0 < Y := lt_of_lt_of_le one_pos ((one_le_laurentRadius K T).trans hYR)
  have hnorm : ‖(Y : ℂ) * I‖ = Y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have hH : (Y : ℂ) * I ∈ H := by
    show 0 < ((Y : ℂ) * I).im
    simp [hY]
  have harg : arg ((Y : ℂ) * I) = Real.pi / 2 := by rw [Complex.arg_real_mul _ hY, Complex.arg_I]
  have h := abs_harmPart_sub_harmMain_le κ ρ hw hw0 ht htT hK hv hH (by rw [harg]; positivity)
    (by rw [harg]) (by rw [hnorm]; exact hYR)
  rw [hnorm] at h
  have hid : Y * (harmPart κ ρ w t v ((Y : ℂ) * I) - phiI κ ρ) + driftValue ρ (w t) v / Real.sqrt κ
      = Y * (harmPart κ ρ w t v ((Y : ℂ) * I) - harmMain κ ρ (w t) t v ((Y : ℂ) * I)) := by
    have := harmMain_mul_I κ ρ (w t) t v hY
    linarith
  rw [hid, abs_mul, abs_of_pos hY]
  calc Y * |harmPart κ ρ w t v ((Y : ℂ) * I) - harmMain κ ρ (w t) t v ((Y : ℂ) * I)|
      ≤ Y * (harmConst κ ρ K T / Y ^ 3) := mul_le_mul_of_nonneg_left h hY.le
    _ = harmConst κ ρ K T / Y ^ 2 := by field_simp

/-- **The second Laurent coefficient**:
`2Y² √κ (φ_t(Y(1+i)) − φ₁) = −Y N_t − Q_t + O(Y⁻¹)`. -/
theorem abs_laurent_two_le {κ : ℝ} (hκ : 0 < κ) (ρ : ι → ℝ) (hw : Continuous w) (hw0 : w 0 = 0)
    {t T K : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) {v : ι → ℝ}
    (hv : ∀ j, |v j| ≤ K) {Y : ℝ} (hYR : laurentRadius K T ≤ Y) :
    |2 * Y ^ 2 * Real.sqrt κ * (harmPart κ ρ w t v ((Y : ℂ) * (1 + I)) - phiD κ ρ)
        + Y * driftValue ρ (w t) v + quadValue κ ρ (w t) v t|
      ≤ 2 * Real.sqrt κ * harmConst κ ρ K T / Y := by
  have hY : 0 < Y := lt_of_lt_of_le one_pos ((one_le_laurentRadius K T).trans hYR)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hC := harmConst_nonneg κ ρ hK0 (ht.trans htT)
  have h1I : (1 : ℝ) ≤ ‖(1 : ℂ) + I‖ := by
    have h := Complex.abs_re_le_norm ((1 : ℂ) + I)
    simp only [add_re, one_re, I_re, add_zero, abs_one] at h
    exact h
  have hnorm : Y ≤ ‖(Y : ℂ) * (1 + I)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
    nlinarith
  have hH : (Y : ℂ) * (1 + I) ∈ H := by
    show 0 < ((Y : ℂ) * (1 + I)).im
    simp [hY]
  have harg0 : 0 ≤ arg ((Y : ℂ) * (1 + I)) := by
    rw [Complex.arg_real_mul _ hY, Complex.arg_nonneg_iff]; simp
  have harg1 : arg ((Y : ℂ) * (1 + I)) ≤ Real.pi / 2 := by
    rw [Complex.arg_real_mul _ hY, Complex.arg_le_pi_div_two_iff]; left; simp
  have h := abs_harmPart_sub_harmMain_le κ ρ hw hw0 ht htT hK hv hH harg0 harg1 (hYR.trans hnorm)
  have h' : |harmPart κ ρ w t v ((Y : ℂ) * (1 + I)) - harmMain κ ρ (w t) t v ((Y : ℂ) * (1 + I))|
      ≤ harmConst κ ρ K T / Y ^ 3 :=
    h.trans (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ hY.le hnorm 3))
  have hid : 2 * Y ^ 2 * Real.sqrt κ * (harmPart κ ρ w t v ((Y : ℂ) * (1 + I)) - phiD κ ρ)
        + Y * driftValue ρ (w t) v + quadValue κ ρ (w t) v t
      = 2 * Y ^ 2 * Real.sqrt κ * (harmPart κ ρ w t v ((Y : ℂ) * (1 + I))
          - harmMain κ ρ (w t) t v ((Y : ℂ) * (1 + I))) := by
    have := harmMain_mul_one_add_I hκ ρ (w t) t v hY
    linarith
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rw [hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Y ^ 2 * Real.sqrt κ)]
  calc 2 * Y ^ 2 * Real.sqrt κ * |harmPart κ ρ w t v ((Y : ℂ) * (1 + I))
        - harmMain κ ρ (w t) t v ((Y : ℂ) * (1 + I))|
      ≤ 2 * Y ^ 2 * Real.sqrt κ * (harmConst κ ρ K T / Y ^ 3) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = 2 * Real.sqrt κ * harmConst κ ρ K T / Y := by field_simp

end Harm

end MartChar

end InteractingSLE
