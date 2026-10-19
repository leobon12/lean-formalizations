import GaussianLQG.Uniform.FieldComparison.Shift
import GaussianLQG.Uniform.FieldComparison.Kernel

/-!
# `L²` bounds for the comparison kernel (Route U, U14; source (A.21))

Fix `0 < δ ≤ 1` (in U14, `δ = 2^{-n}`), and let `a = δ²` be the time shift. With the shifted
white noise `W' = shiftWN a W`, DDDF's field `φ_{0,n}` of `W'` is `√π W(shiftL2 a k_z)`, where
`k_z = phiKernelL2 δ 1 z` is the kernel `1_{[δ², 1]}(t) p_{t/2}(z, y)` and `shiftL2` is
`LQGMetric`'s `DDDF.P29WN.shiftL2`; after the shift it is
a.e. `shPhiKer a z (t, y) = 1_{(0, 1−a]}(t) p_{a/2+t/2}(z, y)` (`coeFn_shiftL2_phiKernelL2`). So
`h*_δ(z) − φ_{0,n}(z) = W(cmpL2 δ z − circKerL2)` with

  `cmpL2 δ z = molKerL2 δ z − √π shiftL2 a k_z`,  a.e. `cmpKer δ z = molKer δ z − √π shPhiKer a z`.

This file proves the two uniform bounds that make the difference a large-scale smooth field:

* `norm_cmpL2_sub_sq_le`: `‖cmpL2 δ v − cmpL2 δ u‖² ≤ |v − u|² / 2`. The kernels differ by
  `√π 1_{t > 1−a} (p_{a/2+t/2}(v, ·) − p_{a/2+t/2}(u, ·))` (the small scales cancel exactly; this is
  why the time shift is needed), and `∫ (p_r(v,·) − p_r(u,·))² ≤ |v−u|²/(8π r²)`,
  `∫_{1−a}^∞ (t + a)^{-2} dt = 1`;
* `norm_cmpL2_zero_sq_le`: `‖cmpL2 δ 0‖² ≤ 1`. The kernel is `√π p_{a/2+t/2}(0, ·)` for
  `1 − a < t ≤ 1` (time slice of length `a`, slice integral `≤ 1/2`) and
  `√π (p_{a/2+t/2}(0, ·) − p_{t/2}(0, ·))` for `t > 1` (slice integral
  `a² / (4 t (t + a/2)(t + a)) ≤ 1/(4t³)`, Chapman–Kolmogorov).

Both bounds hold for all `0 < δ ≤ 1`, including `n = 0` (audit A5-06). Own elementary
computations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace GaussianLQG
namespace FieldCmp

open LQGMetric LQGMetric.WhiteNoise LQGMetric.GFFExist

/-! ### The shifted DDDF kernel -/

/-- The time-shifted DDDF kernel `1_{(0, 1−a]}(t) p_{a/2+t/2}(z, y)`. -/
def shPhiKer (a : ℝ) (z : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Ioc (0 : ℝ) (1 - a)).indicator (fun t => heatKernel (a / 2 + t / 2) z q.2) q.1

lemma ae_fst_ne (c : ℝ) : ∀ᵐ q : ℝ × ℂ ∂(volume : Measure (ℝ × ℂ)), q.1 ≠ c := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have : {p : ℝ × ℂ | p.1 = c} = {c} ×ˢ univ := by ext p; simp
  rw [this, show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
  simp

/-- The shifted DDDF kernel is a.e. `shPhiKer`. -/
lemma coeFn_shiftL2_phiKernelL2 {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    (DDDF.P29WN.shiftL2 (δ ^ 2) (phiKernelL2 δ 1 z) : ℝ × ℂ → ℝ) =ᵐ[volume]
      shPhiKer (δ ^ 2) z := by
  filter_upwards [DDDF.P29WN.coeFn_shiftL2 (δ ^ 2) (phiKernelL2 δ 1 z),
    (DDDF.P29WN.measurePreserving_tShift (δ ^ 2)).quasiMeasurePreserving.ae_eq_comp
      (coeFn_phiKernelL2 δ 1 hδ z), ae_fst_ne 0] with q h1 h2 h3
  rw [h1]
  have h2' : (phiKernelL2 δ 1 z : ℝ × ℂ → ℝ) (DDDF.P29WN.tShift (δ ^ 2) q) =
      phiKernel δ 1 z (DDDF.P29WN.tShift (δ ^ 2) q) := h2
  rw [Function.comp_apply, h2']
  unfold phiKernel shPhiKer DDDF.P29WN.tShift
  simp only [indicator, mem_prod, mem_Icc, mem_univ, and_true, mem_Ioc, one_pow]
  split_ifs with hA hB hB
  · congr 1; ring
  · exact absurd ⟨lt_of_le_of_ne (by linarith [hA.1]) (Ne.symm h3), by linarith [hA.2]⟩ hB
  · exact absurd ⟨by linarith [hB.1], by linarith [hB.2]⟩ hA
  · rfl

/-! ### The comparison kernel -/

/-- The comparison kernel `molKer δ z − √π shPhiKer δ² z`. -/
def cmpKer (δ : ℝ) (z : ℂ) (q : ℝ × ℂ) : ℝ :=
  molKer δ z q - Real.sqrt Real.pi * shPhiKer (δ ^ 2) z q

/-- The comparison kernel in `L²`: `molKerL2 δ z − √π shiftL2 δ² (phiKernelL2 δ 1 z)`. -/
def cmpL2 (δ : ℝ) (z : ℂ) : WNSpace :=
  molKerL2 δ z - Real.sqrt Real.pi • DDDF.P29WN.shiftL2 (δ ^ 2) (phiKernelL2 δ 1 z)

lemma coeFn_cmpL2 {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    (cmpL2 δ z : ℝ × ℂ → ℝ) =ᵐ[volume] cmpKer δ z := by
  filter_upwards [Lp.coeFn_sub (molKerL2 δ z)
      (Real.sqrt Real.pi • DDDF.P29WN.shiftL2 (δ ^ 2) (phiKernelL2 δ 1 z)),
    coeFn_molKerL2 hδ.ne' z,
    Lp.coeFn_smul (Real.sqrt Real.pi) (DDDF.P29WN.shiftL2 (δ ^ 2) (phiKernelL2 δ 1 z)),
    coeFn_shiftL2_phiKernelL2 hδ z] with q h1 h2 h3 h4
  rw [cmpL2, h1, Pi.sub_apply, h2, h3, Pi.smul_apply, h4, smul_eq_mul]
  rfl

/-- `‖f‖² ≤ B` from a lintegral bound on an a.e. representative. -/
lemma norm_sq_le_of_lintegral {f : WNSpace} {F : ℝ × ℂ → ℝ} (hF : (f : ℝ × ℂ → ℝ) =ᵐ[volume] F)
    {B : ℝ} (hB : 0 ≤ B) (h : ∫⁻ q, ENNReal.ofReal (F q ^ 2) ≤ ENNReal.ofReal B) :
    ‖f‖ ^ 2 ≤ B := by
  rw [DG.norm_sq_eq_integral]
  have e : (fun q => ((f : ℝ × ℂ → ℝ) q) ^ 2) =ᵐ[volume] fun q => F q ^ 2 := by
    filter_upwards [hF] with q hq
    rw [hq]
  have hFm : AEStronglyMeasurable F volume := (Lp.aestronglyMeasurable f).congr hF
  rw [integral_congr_ae e, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun q => sq_nonneg (F q)) (hFm.pow 2)]
  exact ENNReal.toReal_le_of_le_ofReal hB h

/-! ### Increments -/

lemma cmpKer_sub_eq {δ : ℝ} (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ) (u v : ℂ) (q : ℝ × ℂ) :
    cmpKer δ v q - cmpKer δ u q = Real.sqrt Real.pi * (Ioi (1 - δ ^ 2)).indicator
      (fun t => heatKernel (δ ^ 2 / 2 + t / 2) v q.2 - heatKernel (δ ^ 2 / 2 + t / 2) u q.2) q.1 := by
  have ha : δ ^ 2 ≤ 1 := by nlinarith
  unfold cmpKer molKer shPhiKer
  rcases le_or_gt q.1 0 with h0 | h0
  · have n1 : q.1 ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, not_lt]; exact h0
    have n2 : q.1 ∉ Ioc (0 : ℝ) (1 - δ ^ 2) := fun h => absurd h.1 (not_lt.2 h0)
    have n3 : q.1 ∉ Ioi (1 - δ ^ 2) := by simp only [mem_Ioi, not_lt]; linarith
    simp only [indicator_of_notMem n1, indicator_of_notMem n2, indicator_of_notMem n3]
    ring
  rcases le_or_gt q.1 (1 - δ ^ 2) with h1 | h1
  · have m1 : q.1 ∈ Ioi (0 : ℝ) := h0
    have m2 : q.1 ∈ Ioc (0 : ℝ) (1 - δ ^ 2) := ⟨h0, h1⟩
    have n3 : q.1 ∉ Ioi (1 - δ ^ 2) := by simp only [mem_Ioi, not_lt]; exact h1
    simp only [indicator_of_mem m1, indicator_of_mem m2, indicator_of_notMem n3]
    ring
  · have m1 : q.1 ∈ Ioi (0 : ℝ) := h0
    have n2 : q.1 ∉ Ioc (0 : ℝ) (1 - δ ^ 2) := fun h => absurd h.2 (not_le.2 h1)
    have m3 : q.1 ∈ Ioi (1 - δ ^ 2) := h1
    simp only [indicator_of_mem m1, indicator_of_notMem n2, indicator_of_mem m3]
    ring

/-- Translation: `∫ (p_r(v,·) − p_r(u,·))² ≤ |v − u|² / (8π r²)`. -/
lemma lintegral_sq_heatKernel_sub_two_le {r : ℝ} (hr : 0 < r) (u v : ℂ) :
    ∫⁻ y, ENNReal.ofReal ((heatKernel r v y - heatKernel r u y) ^ 2) ≤
      ENNReal.ofReal (‖v - u‖ ^ 2 / (8 * Real.pi * r ^ 2)) := by
  have e : ∀ y, (heatKernel r v (y + u) - heatKernel r u (y + u)) ^ 2 =
      (heatKernel r (v - u) y - heatKernel r 0 y) ^ 2 := by
    intro y
    rw [DG.heatKernel_translate r v u y, DG.heatKernel_translate r u u y, sub_self]
  rw [← lintegral_add_right_eq_self (fun y => ENNReal.ofReal
    ((heatKernel r v y - heatKernel r u y) ^ 2)) u]
  simp_rw [e]
  exact lintegral_ofReal_sq_heatKernel_sub_le hr (v - u)

lemma lintegral_sq_cmpKer_sub_slice {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (u v : ℂ) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal ((cmpKer δ v (t, y) - cmpKer δ u (t, y)) ^ 2) ≤
      (Ioi (1 : ℝ)).indicator (fun τ => ENNReal.ofReal (‖v - u‖ ^ 2 / 2 * τ ^ (-2 : ℝ)))
        (t + δ ^ 2) := by
  simp_rw [cmpKer_sub_eq hδ1 hδ.le u v]
  by_cases ht : t ∈ Ioi (1 - δ ^ 2)
  · have ht' : t + δ ^ 2 ∈ Ioi (1 : ℝ) := by simp only [mem_Ioi] at ht ⊢; linarith
    rw [indicator_of_mem ht']
    simp only [indicator_of_mem ht]
    set r := δ ^ 2 / 2 + t / 2 with hr_def
    have hτ : 0 < t + δ ^ 2 := by simp only [mem_Ioi] at ht'; linarith
    have hr : 0 < r := by simp only [hr_def]; linarith
    have e : ∀ y, ENNReal.ofReal ((Real.sqrt Real.pi *
        (heatKernel r v y - heatKernel r u y)) ^ 2) =
        ENNReal.ofReal Real.pi * ENNReal.ofReal ((heatKernel r v y - heatKernel r u y) ^ 2) := by
      intro y
      rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ENNReal.ofReal_mul Real.pi_pos.le]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (lintegral_sq_heatKernel_sub_two_le hr u v)).trans
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul Real.pi_pos.le]
    congr 1
    rw [Real.rpow_neg hτ.le, Real.rpow_two]
    have hr2 : r = (t + δ ^ 2) / 2 := by simp only [hr_def]; ring
    rw [hr2]
    field_simp
    ring
  · simp only [indicator_of_notMem ht, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, ENNReal.ofReal_zero, lintegral_const, zero_mul]
    exact zero_le

lemma lintegral_sq_cmpKer_sub_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (u v : ℂ) :
    ∫⁻ q, ENNReal.ofReal ((cmpKer δ v q - cmpKer δ u q) ^ 2) ≤
      ENNReal.ofReal (‖v - u‖ ^ 2 / 2) := by
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl]
  refine (lintegral_prod_le _).trans ?_
  refine (lintegral_mono fun t => lintegral_sq_cmpKer_sub_slice hδ hδ1 u v t).trans
    (le_of_eq ?_)
  rw [lintegral_add_right_eq_self (fun τ => (Ioi (1 : ℝ)).indicator
    (fun τ => ENNReal.ofReal (‖v - u‖ ^ 2 / 2 * τ ^ (-2 : ℝ))) τ) (δ ^ 2),
    lintegral_indicator measurableSet_Ioi]
  have hi : IntegrableOn (fun τ : ℝ => ‖v - u‖ ^ 2 / 2 * τ ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => ?_
    have : 0 < τ := lt_trans one_pos hτ
    have := Real.rpow_nonneg this.le (-2 : ℝ)
    simp only [Pi.zero_apply]; positivity

/-- **Increment bound**: `‖cmpL2 δ v − cmpL2 δ u‖² ≤ |v − u|² / 2` for `0 < δ ≤ 1`. -/
theorem norm_cmpL2_sub_sq_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (u v : ℂ) :
    ‖cmpL2 δ v - cmpL2 δ u‖ ^ 2 ≤ ‖v - u‖ ^ 2 / 2 := by
  have hF : ((cmpL2 δ v - cmpL2 δ u : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun q => cmpKer δ v q - cmpKer δ u q := by
    filter_upwards [Lp.coeFn_sub (cmpL2 δ v) (cmpL2 δ u), coeFn_cmpL2 hδ v, coeFn_cmpL2 hδ u]
      with q h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  exact norm_sq_le_of_lintegral hF (by positivity) (lintegral_sq_cmpKer_sub_le hδ hδ1 u v)

/-! ### The kernel at `z = 0` -/

/-- `∫ (p_r(0,·) − p_s(0,·))² = p_{2r}(0,0) − 2 p_{r+s}(0,0) + p_{2s}(0,0)`. -/
lemma integral_sq_heatKernel_sub_time {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∫ y, (heatKernel r 0 y - heatKernel s 0 y) ^ 2 =
      heatKernel (r + r) 0 0 - 2 * heatKernel (r + s) 0 0 + heatKernel (s + s) 0 0 := by
  have e : ∀ y, (heatKernel r 0 y - heatKernel s 0 y) ^ 2 =
      heatKernel r 0 y * heatKernel r y 0 - 2 * (heatKernel r 0 y * heatKernel s y 0) +
        heatKernel s 0 y * heatKernel s y 0 := fun y => by
    rw [heatKernel_symm r y 0, heatKernel_symm s y 0]; ring
  simp_rw [e]
  have i1 := HeatSq.integrable_heatKernel_mul_heatKernel_ck r r hr hr 0 0
  have i2 := (HeatSq.integrable_heatKernel_mul_heatKernel_ck r s hr hs 0 0).const_mul 2
  have i3 := HeatSq.integrable_heatKernel_mul_heatKernel_ck s s hs hs 0 0
  have i12 : Integrable (fun y => heatKernel r 0 y * heatKernel r y 0 -
      2 * (heatKernel r 0 y * heatKernel s y 0)) := i1.sub i2
  rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
    HeatSq.integral_heatKernel_mul_heatKernel_ck r r hr hr 0 0,
    HeatSq.integral_heatKernel_mul_heatKernel_ck r s hr hs 0 0,
    HeatSq.integral_heatKernel_mul_heatKernel_ck s s hs hs 0 0]

lemma heatKernel_zero_zero (x : ℝ) : heatKernel x 0 0 = (2 * Real.pi * x)⁻¹ := by
  simp [heatKernel]

lemma integrable_sq_heatKernel_sub_time {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable fun y => (heatKernel r 0 y - heatKernel s 0 y) ^ 2 := by
  have e : (fun y => (heatKernel r 0 y - heatKernel s 0 y) ^ 2) = fun y =>
      heatKernel r 0 y * heatKernel r y 0 - 2 * (heatKernel r 0 y * heatKernel s y 0) +
        heatKernel s 0 y * heatKernel s y 0 := by
    funext y; rw [heatKernel_symm r y 0, heatKernel_symm s y 0]; ring
  rw [e]
  exact ((HeatSq.integrable_heatKernel_mul_heatKernel_ck r r hr hr 0 0).sub
    ((HeatSq.integrable_heatKernel_mul_heatKernel_ck r s hr hs 0 0).const_mul 2)).add
    (HeatSq.integrable_heatKernel_mul_heatKernel_ck s s hs hs 0 0)

/-- The arithmetic of the large-time slice: `π (p_{t+a} − 2p_{t+a/2} + p_t)(0) ≤ 1/(4t³)`. -/
lemma pi_mul_second_diff_le {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) :
    Real.pi * ((2 * Real.pi * (t + a))⁻¹ - 2 * (2 * Real.pi * (t + a / 2))⁻¹ +
      (2 * Real.pi * t)⁻¹) ≤ 1 / 4 * t ^ (-3 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hpi := Real.pi_pos
  have key : Real.pi * ((2 * Real.pi * (t + a))⁻¹ - 2 * (2 * Real.pi * (t + a / 2))⁻¹ +
      (2 * Real.pi * t)⁻¹) = a ^ 2 / (4 * (t * (t + a / 2) * (t + a))) := by
    field_simp
    ring
  rw [key, Real.rpow_neg ht0.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : a ^ 2 ≤ 1 := by nlinarith
  have h2 : t ^ 3 ≤ t * (t + a / 2) * (t + a) := by
    have e1 : t ^ 3 = t * t * t := by ring
    rw [e1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) ht0.le) (by linarith)
      ht0.le (by positivity)
  have h3 : 0 < t ^ 3 := by positivity
  rw [show 1 / 4 * (t ^ 3)⁻¹ = 1 / (4 * t ^ 3) by field_simp]
  exact div_le_div₀ zero_le_one h1 (by positivity) (by linarith)

lemma lintegral_sq_cmpKer_zero_slice {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (cmpKer δ 0 (t, y) ^ 2) ≤
      (Ioc (1 - δ ^ 2) 1).indicator (fun _ => ENNReal.ofReal (1 / 2)) t +
        (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (1 / 4 * t ^ (-3 : ℝ))) t := by
  have ha : δ ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 < δ ^ 2 := by positivity
  have hpi := Real.pi_pos
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  unfold cmpKer molKer shPhiKer
  rcases le_or_gt t (1 - δ ^ 2) with h1 | h1
  · -- the small scales cancel exactly
    have hz : ∀ y : ℂ, (Real.sqrt Real.pi * (Ioi (0 : ℝ)).indicator (fun t =>
        heatKernel (δ ^ 2 / 2 + t / 2) 0 y - (Ioi (1 : ℝ)).indicator
          (fun _ => heatKernel (t / 2) 0 y) t) t - Real.sqrt Real.pi * (Ioc (0 : ℝ)
          (1 - δ ^ 2)).indicator (fun t => heatKernel (δ ^ 2 / 2 + t / 2) 0 y) t) = 0 := by
      intro y
      rcases le_or_gt t 0 with h0 | h0
      · have n1 : t ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi, not_lt]; exact h0
        have n2 : t ∉ Ioc (0 : ℝ) (1 - δ ^ 2) := fun h => absurd h.1 (not_lt.2 h0)
        simp only [indicator_of_notMem n1, indicator_of_notMem n2]
        ring
      · have m1 : t ∈ Ioi (0 : ℝ) := h0
        have m2 : t ∈ Ioc (0 : ℝ) (1 - δ ^ 2) := ⟨h0, h1⟩
        have n3 : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; linarith
        simp only [indicator_of_mem m1, indicator_of_mem m2, indicator_of_notMem n3]
        ring
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero,
      lintegral_const, zero_mul]
    exact zero_le
  have h0 : 0 < t := by linarith
  have m1 : t ∈ Ioi (0 : ℝ) := h0
  have n2 : t ∉ Ioc (0 : ℝ) (1 - δ ^ 2) := fun h => absurd h.2 (not_le.2 h1)
  simp only [indicator_of_mem m1, indicator_of_notMem n2, mul_zero, sub_zero]
  set r := δ ^ 2 / 2 + t / 2 with hr_def
  have hr : 0 < r := by simp only [hr_def]; positivity
  rcases le_or_gt t 1 with h2 | h2
  · -- the slice `1 − δ² < t ≤ 1`
    have n3 : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; exact h2
    have m4 : t ∈ Ioc (1 - δ ^ 2) 1 := ⟨h1, h2⟩
    simp only [indicator_of_notMem n3, sub_zero, indicator_of_mem m4, add_zero]
    have e : ∀ y, ENNReal.ofReal ((Real.sqrt Real.pi * heatKernel r 0 y) ^ 2) =
        ENNReal.ofReal (Real.pi * (heatKernel r 0 y * heatKernel r y 0)) := fun y => by
      rw [mul_pow, hsq, heatKernel_symm r y 0, sq]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((HeatSq.integrable_heatKernel_mul_heatKernel_ck r r hr hr 0 0).const_mul _)
      (Eventually.of_forall fun y => mul_nonneg hpi.le (mul_nonneg
        (heatKernel_nonneg _ hr.le _ _) (heatKernel_nonneg _ hr.le _ _)))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, HeatSq.integral_heatKernel_mul_heatKernel_ck r r hr hr 0 0,
      heatKernel_zero_zero]
    have h4 : 1 ≤ r + r := by simp only [hr_def]; linarith
    rw [show Real.pi * (2 * Real.pi * (r + r))⁻¹ = 1 / (2 * (r + r)) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · -- the slice `t > 1`
    have m3 : t ∈ Ioi (1 : ℝ) := h2
    have n4 : t ∉ Ioc (1 - δ ^ 2) 1 := fun h => absurd h.2 (not_le.2 h2)
    simp only [indicator_of_mem m3, indicator_of_notMem n4, zero_add]
    set s := t / 2 with hs_def
    have hs : 0 < s := by simp only [hs_def]; linarith
    have e : ∀ y, ENNReal.ofReal ((Real.sqrt Real.pi * (heatKernel r 0 y - heatKernel s 0 y)) ^ 2)
        = ENNReal.ofReal (Real.pi * (heatKernel r 0 y - heatKernel s 0 y) ^ 2) := fun y => by
      rw [mul_pow, hsq]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((integrable_sq_heatKernel_sub_time hr hs).const_mul _)
      (Eventually.of_forall fun y => mul_nonneg hpi.le (sq_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, integral_sq_heatKernel_sub_time hr hs, heatKernel_zero_zero,
      heatKernel_zero_zero, heatKernel_zero_zero]
    have e1 : r + r = t + δ ^ 2 := by simp only [hr_def]; ring
    have e2 : r + s = t + δ ^ 2 / 2 := by simp only [hr_def, hs_def]; ring
    have e3 : s + s = t := by simp only [hs_def]; ring
    rw [e1, e2, e3]
    exact pi_mul_second_diff_le ha0 ha h2.le

lemma lintegral_sq_cmpKer_zero_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫⁻ q, ENNReal.ofReal (cmpKer δ 0 q ^ 2) ≤ ENNReal.ofReal 1 := by
  have ha : δ ^ 2 ≤ 1 := by nlinarith
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl]
  refine (lintegral_prod_le _).trans ?_
  refine (lintegral_mono fun t => lintegral_sq_cmpKer_zero_slice hδ hδ1 t).trans ?_
  rw [lintegral_add_left (Measurable.indicator measurable_const measurableSet_Ioc),
    lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioi,
    setLIntegral_const, Real.volume_Ioc]
  have hi : IntegrableOn (fun τ : ℝ => 1 / 4 * τ ^ (-3 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by nlinarith) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    norm_num
    nlinarith
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => ?_
    have : 0 < τ := lt_trans one_pos hτ
    have := Real.rpow_nonneg this.le (-3 : ℝ)
    simp only [Pi.zero_apply]; positivity

/-- **The kernel at the origin**: `‖cmpL2 δ 0‖² ≤ 1` for `0 < δ ≤ 1`. -/
theorem norm_cmpL2_zero_sq_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ‖cmpL2 δ 0‖ ^ 2 ≤ 1 :=
  norm_sq_le_of_lintegral (coeFn_cmpL2 hδ 0) zero_le_one (lintegral_sq_cmpKer_zero_le hδ hδ1)

/-- **Uniform variance bound** for the comparison kernel minus the normalization kernel. -/
theorem norm_cmpL2_sub_circKerL2_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (v : ℂ) :
    ‖cmpL2 δ v - circKerL2‖ ≤ ‖v‖ + 1 + ‖circKerL2‖ := by
  have h1 : ‖cmpL2 δ v - cmpL2 δ 0‖ ≤ ‖v‖ := by
    have := norm_cmpL2_sub_sq_le hδ hδ1 0 v
    rw [sub_zero] at this
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖v‖]
  have h2 : ‖cmpL2 δ 0‖ ≤ 1 := by
    have := norm_cmpL2_zero_sq_le hδ hδ1
    nlinarith [norm_nonneg (cmpL2 δ 0)]
  calc ‖cmpL2 δ v - circKerL2‖ = ‖(cmpL2 δ v - cmpL2 δ 0) + cmpL2 δ 0 - circKerL2‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖(cmpL2 δ v - cmpL2 δ 0) + cmpL2 δ 0‖ + ‖circKerL2‖ := norm_sub_le _ _
    _ ≤ ‖cmpL2 δ v - cmpL2 δ 0‖ + ‖cmpL2 δ 0‖ + ‖circKerL2‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖v‖ + 1 + ‖circKerL2‖ := by linarith

end FieldCmp
end GaussianLQG
