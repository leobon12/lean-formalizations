/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailPullback
import InteractingSLE.Spec.Zhan.StripTimeGap
import QuantumZipper.Proofs.Complex.KoebeCovering
import QuantumZipper.Proofs.Complex.BasicsReflection
import QuantumZipper.Proofs.RS.KoebeLoewnerTime

/-!
# Constant strip drift `|σ| < 1`: Koebe at an upper boundary point

Packet PROVE-ZHAN-A5. Astra, *Formalization proofs and dependency audit* (ruling R35), "Constant drift with
`|σ| < 1`", second paragraph (`source/external/AstraIG1/ig1_formalization_proofs.txt` L1441–L1458): "Differentiating
the upper-boundary ODE gives `A_t(x) = ψ_t'(x + iπ) = exp(½ ∫₀ᵗ sech²(X_s(x)/2) ds)` (3.23). […] Reflect the map and
domain across the upper boundary. The resulting map is conformal onto the doubled strip of height `2π`. […] Koebe
quarter gives distance from that point to the doubled-domain boundary at least `1/A_t(x)`. The uniform derivative
bound therefore keeps every upper point different from `J + iπ` a positive distance from every hull."

In the R36 form the upper point `x + iπ` is the chordal real point `y = −1 − e^x < −1`, left of the end mark `−1`
(whose centred flow is `v − W`). We work entirely in chordal coordinates, with QuantumZipper's centred real flows
`u = g − W` (`IsForwardSol`):

* `re_eq_of_isForwardSol_real`, `re_sub_re_eq_of_isForwardSol` (**the derivative identity, integrated**): two real
  flows satisfy `u₂ − u₁ = (x₂ − x₁) exp(−∫₀ᵗ 2/(u₁ u₂))` (a linear equation; `Zhan.eq_mul_exp_neg_integral`). In
  strip time this is (3.23) for difference quotients;
* `re_sub_re_le_left`, `re_sub_re_le_right`: the difference quotients at `y` are bounded by
  `(v − y)_t/(−1 − y) · exp(∫₀ᵗ j)` with `j = 2/((v − y)(W − v))` (left quotients) or `j = 2(v − y)/(W − v)³`
  (right quotients); in strip time these are `2e^{−X}` and `2e^{X}`, `X = Re ψ(x + iπ) − ξ` the upper gap;
* `disjoint_ball_fwdHull_of_slope` (**Koebe at a real point left of the end mark**): the inverse map `F_T`, continuous
  on `ℍ̄`, is reflected (Schwarz) to the disk `B(u_y, v − u_y)`, where it is injective; Koebe's covering theorem
  (QuantumZipper's constant `1/48`) gives `B(y, (v − u_y)|F'(u_y)|/48) ∩ K_T = ∅`, and `|F'(u_y)| ≥ 1/M` if the
  one-sided difference quotients of `x ↦ u_x(T)` at `y` are at most `M`;
* `disjoint_ball_fwdHull_left`, `disjoint_ball_fwdHull_right`: hence `dist(y, K_T) ≥ (−1 − y) e^{−∫ j}/48`
  (respectively `/96`);
* `disjoint_ball_fwdHull_sech` (**(3.23)**, used downstream): the right quotients are at most `exp(−∫ 2/u_y²)`
  (`= 1/F_T'(u_y)`), so `dist(y, K_T) ≥ (−1 − y) exp(−∫ (2/(u_y u_V) − 2/u_y²))/48`; in strip time the exponent is
  `½∫ sech²(X/2)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace Zhan

variable {W : ℝ → ℝ}

/-! ### Real flows and the linear equation for their difference -/

/-- A centred flow from a real point is `u = ↑(u.re)`. -/
theorem flow_eq_ofReal_re (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc 0 T) : u t = ((u t).re : ℂ) := by
  have him := im_eq_zero_of_isForwardSol_real hW hu ht
  apply Complex.ext <;> simp [him]

/-- The real centred flow solves the real integral equation `u_t = x − W_t + ∫₀ᵗ 2/u`. -/
theorem re_eq_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (u t).re = x - W t + ∫ s in (0 : ℝ)..t, 2 / (u s).re := by
  have heq := (hu.2 t ht).2
  have hint : IntervalIntegrable (fun s => 2 / u s) MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact continuousOn_const.div (hu.1.mono (Icc_subset_Icc le_rfl ht.2)) fun s hs =>
      (hu.2 s ⟨hs.1, hs.2.trans ht.2⟩).1
  have hre : (∫ s in (0 : ℝ)..t, 2 / u s).re = ∫ s in (0 : ℝ)..t, (2 / u s).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  have hcongr : ∫ s in (0 : ℝ)..t, (2 / u s).re = ∫ s in (0 : ℝ)..t, 2 / (u s).re := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    show (2 / u s).re = 2 / (u s).re
    rw [flow_eq_ofReal_re hW hu hs']
    simp only [ofReal_re]
    rw [← ofReal_ofNat, ← ofReal_div, ofReal_re]
  have := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
  rw [this, hre, hcongr]

theorem re_ne_zero_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc 0 T) : (u t).re ≠ 0 := by
  intro h0
  apply (hu.2 t ht).1
  rw [flow_eq_ofReal_re hW hu ht, h0, ofReal_zero]

theorem continuousOn_re_of_isForwardSol {x T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) :
    ContinuousOn (fun s => (u s).re) (Icc 0 T) :=
  continuous_re.comp_continuousOn hu.1

/-- **The difference of two real flows** solves a linear equation:
`u₂(t) − u₁(t) = (x₂ − x₁) exp(−∫₀ᵗ 2/(u₁ u₂))`. -/
theorem re_sub_re_eq_of_isForwardSol (hW : Continuous W) {x₁ x₂ T : ℝ} {u₁ u₂ : ℝ → ℂ}
    (hu₁ : IsForwardSol W (x₁ : ℂ) T u₁) (hu₂ : IsForwardSol W (x₂ : ℂ) T u₂) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (u₂ t).re - (u₁ t).re =
      (x₂ - x₁) * Real.exp (-∫ s in (0 : ℝ)..t, 2 / ((u₁ s).re * (u₂ s).re)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hc₁ := continuousOn_re_of_isForwardSol hu₁
  have hc₂ := continuousOn_re_of_isForwardSol hu₂
  have hn₁ := fun s (hs : s ∈ Icc 0 T) => re_ne_zero_of_isForwardSol_real hW hu₁ hs
  have hn₂ := fun s (hs : s ∈ Icc 0 T) => re_ne_zero_of_isForwardSol_real hW hu₂ hs
  have hf : ContinuousOn (fun s => 2 / (u₂ s).re - 2 / (u₁ s).re) (Icc 0 T) :=
    (continuousOn_const.div hc₂ hn₂).sub (continuousOn_const.div hc₁ hn₁)
  have hcc : ContinuousOn (fun s => 2 / ((u₁ s).re * (u₂ s).re)) (Icc 0 T) :=
    continuousOn_const.div (hc₁.mul hc₂) fun s hs => mul_ne_zero (hn₁ s hs) (hn₂ s hs)
  have hfi : IntervalIntegrable (fun s => 2 / (u₂ s).re - 2 / (u₁ s).re) MeasureTheory.volume 0 T :=
    hf.intervalIntegrable_of_Icc hT
  have hci : IntervalIntegrable (fun s => 2 / ((u₁ s).re * (u₂ s).re)) MeasureTheory.volume 0 T :=
    hcc.intervalIntegrable_of_Icc hT
  have hy : ∀ r ∈ Icc 0 T, (u₂ r).re - (u₁ r).re = ((u₂ 0).re - (u₁ 0).re) +
      ∫ s in (0 : ℝ)..r, (2 / (u₂ s).re - 2 / (u₁ s).re) := by
    intro r hr
    have hr0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    rw [re_eq_of_isForwardSol_real hW hu₂ hr, re_eq_of_isForwardSol_real hW hu₁ hr,
      re_eq_of_isForwardSol_real hW hu₂ hr0, re_eq_of_isForwardSol_real hW hu₁ hr0]
    have hi₁ : IntervalIntegrable (fun s => 2 / (u₁ s).re) MeasureTheory.volume 0 r :=
      ((continuousOn_const.div hc₁ hn₁).mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1
    have hi₂ : IntervalIntegrable (fun s => 2 / (u₂ s).re) MeasureTheory.volume 0 r :=
      ((continuousOn_const.div hc₂ hn₂).mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1
    rw [intervalIntegral.integral_sub hi₂ hi₁]
    simp only [intervalIntegral.integral_same, add_zero]
    ring
  have hfc : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Icc 0 T →
      2 / (u₂ s).re - 2 / (u₁ s).re = -(2 / ((u₁ s).re * (u₂ s).re) * ((u₂ s).re - (u₁ s).re)) := by
    refine Filter.Eventually.of_forall fun s hs => ?_
    have h1 := hn₁ s hs
    have h2 := hn₂ s hs
    field_simp
    ring
  have key := eq_mul_exp_neg_integral (y := fun r => (u₂ r).re - (u₁ r).re) hT hfi hci hy hfc t ht
  have h0 : (u₂ 0).re - (u₁ 0).re = x₂ - x₁ := by
    have hr0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have e₁ := (hu₁.2 0 hr0).2
    have e₂ := (hu₂.2 0 hr0).2
    simp only [intervalIntegral.integral_same, add_zero] at e₁ e₂
    rw [e₁, e₂]
    simp
  simpa only [h0] using key

/-- Real flows preserve the order of their starting points. -/
theorem flow_re_lt_flow_re (hW : Continuous W) {x₁ x₂ T : ℝ} {u₁ u₂ : ℝ → ℂ}
    (hu₁ : IsForwardSol W (x₁ : ℂ) T u₁) (hu₂ : IsForwardSol W (x₂ : ℂ) T u₂) (hx : x₁ < x₂) {t : ℝ}
    (ht : t ∈ Icc 0 T) : (u₁ t).re < (u₂ t).re := by
  have := re_sub_re_eq_of_isForwardSol hW hu₁ hu₂ ht
  have hpos : 0 < (x₂ - x₁) * Real.exp (-∫ s in (0 : ℝ)..t, 2 / ((u₁ s).re * (u₂ s).re)) :=
    mul_pos (sub_pos.2 hx) (Real.exp_pos _)
  linarith

/-! ### The difference quotients at a point left of the end mark -/

/-- `2/(QR) − 2/(PQ) ≤ 2/((Q − R) R)` for `P ≥ Q > R > 0`. -/
theorem two_div_sub_two_div_le_left {P Q R : ℝ} (hR : 0 < R) (hRQ : R < Q) (hQP : Q ≤ P) :
    2 / (Q * R) - 2 / (P * Q) ≤ 2 / ((Q - R) * R) := by
  have hQ : 0 < Q := hR.trans hRQ
  have hP : 0 < P := hQ.trans_le hQP
  have hQR : 0 < Q - R := sub_pos.2 hRQ
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hP hQ, mul_pos hQR hR, mul_pos (mul_pos hP hQ) hR, mul_pos hR hR,
    mul_pos (mul_pos hQ hR) hR]

/-- `2/(QR) − 2/(PQ) ≤ 2(P − R)/R³` for `P ≥ Q ≥ R > 0`. -/
theorem two_div_sub_two_div_le_right {P Q R : ℝ} (hR : 0 < R) (hRQ : R ≤ Q) (hQP : Q ≤ P) :
    2 / (Q * R) - 2 / (P * Q) ≤ 2 * (P - R) / R ^ 3 := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hP : 0 < P := hQ.trans_le hQP
  have e : 2 / (Q * R) - 2 / (P * Q) = 2 * (P - R) / (P * Q * R) := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_left (by nlinarith) (by positivity)
  have h1 : R * R ≤ P * Q := mul_le_mul (hRQ.trans hQP) hRQ hR.le hP.le
  nlinarith

/-- **Left difference quotients at `y`.** For real `a < y < −1` with flows on `[0, T]` (and the end mark `uV`
from `−1`): `u_y − u_a ≤ (y − a)/(−1 − y) · (u_V − u_y) · exp(∫₀ᵗ 2/((u_V − u_y)(−u_V)))`. -/
theorem re_sub_re_le_left (hW : Continuous W) (hW0 : W 0 = 0) {a y T : ℝ} (hay : a < y) (hy : y < -1)
    {ua uy uV : ℝ → ℂ} (hua : IsForwardSol W (a : ℂ) T ua) (huy : IsForwardSol W (y : ℂ) T uy)
    (huV : IsForwardSol W ((-1 : ℝ) : ℂ) T uV) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (uy t).re - (ua t).re ≤ (y - a) / (-1 - y) * ((uV t).re - (uy t).re) *
      Real.exp (∫ s in (0 : ℝ)..t, 2 / (((uV s).re - (uy s).re) * -(uV s).re)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hVn := re_neg_of_isForwardSol hW hW0 (show (-1 : ℝ) < 0 by norm_num) huV
  have hyV : ∀ s ∈ Icc 0 T, (uy s).re < (uV s).re := fun s hs => flow_re_lt_flow_re hW huy huV hy hs
  have hay' : ∀ s ∈ Icc 0 T, (ua s).re < (uy s).re := fun s hs => flow_re_lt_flow_re hW hua huy hay hs
  have e₁ := re_sub_re_eq_of_isForwardSol hW hua huy ht
  have e₂ := re_sub_re_eq_of_isForwardSol hW huy huV ht
  set I₁ := ∫ s in (0 : ℝ)..t, 2 / ((ua s).re * (uy s).re)
  set I₂ := ∫ s in (0 : ℝ)..t, 2 / ((uy s).re * (uV s).re)
  set I₃ := ∫ s in (0 : ℝ)..t, 2 / (((uV s).re - (uy s).re) * -(uV s).re)
  have hca := continuousOn_re_of_isForwardSol hua
  have hcy := continuousOn_re_of_isForwardSol huy
  have hcV := continuousOn_re_of_isForwardSol huV
  have hi₁ : IntervalIntegrable (fun s => 2 / ((ua s).re * (uy s).re)) MeasureTheory.volume 0 t :=
    ((continuousOn_const.div (hca.mul hcy) fun s hs => mul_ne_zero
      (re_ne_zero_of_isForwardSol_real hW hua hs) (re_ne_zero_of_isForwardSol_real hW huy hs)).mono
      hsub).intervalIntegrable_of_Icc ht.1
  have hi₂ : IntervalIntegrable (fun s => 2 / ((uy s).re * (uV s).re)) MeasureTheory.volume 0 t :=
    ((continuousOn_const.div (hcy.mul hcV) fun s hs => mul_ne_zero
      (re_ne_zero_of_isForwardSol_real hW huy hs) (re_ne_zero_of_isForwardSol_real hW huV hs)).mono
      hsub).intervalIntegrable_of_Icc ht.1
  have hi₃ : IntervalIntegrable (fun s => 2 / (((uV s).re - (uy s).re) * -(uV s).re))
      MeasureTheory.volume 0 t :=
    ((continuousOn_const.div ((hcV.sub hcy).mul hcV.neg) fun s hs => mul_ne_zero
      (sub_pos.2 (hyV s hs)).ne' (neg_pos.2 (hVn s hs)).ne').mono hsub).intervalIntegrable_of_Icc ht.1
  have hle : I₂ - I₁ ≤ I₃ := by
    rw [← intervalIntegral.integral_sub hi₂ hi₁]
    refine intervalIntegral.integral_mono_on ht.1 (hi₂.sub hi₁) hi₃ fun s hs => ?_
    have hs' := hsub hs
    have h := two_div_sub_two_div_le_left (P := -(ua s).re) (Q := -(uy s).re) (R := -(uV s).re)
      (by linarith [hVn s hs']) (by linarith [hyV s hs']) (by linarith [hay' s hs'])
    have e1 : -(uy s).re * -(uV s).re = (uy s).re * (uV s).re := by ring
    have e2 : -(ua s).re * -(uy s).re = (ua s).re * (uy s).re := by ring
    have e3 : (-(uy s).re - -(uV s).re) * -(uV s).re = ((uV s).re - (uy s).re) * -(uV s).re := by ring
    rw [e1, e2, e3] at h
    exact h
  have hy1 : 0 < -1 - y := by linarith
  rw [e₁, e₂]
  have hexp : Real.exp (-I₁) ≤ Real.exp (-I₂) * Real.exp I₃ := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hya : 0 ≤ y - a := by linarith
  calc (y - a) * Real.exp (-I₁) ≤ (y - a) * (Real.exp (-I₂) * Real.exp I₃) :=
        mul_le_mul_of_nonneg_left hexp hya
    _ = (y - a) / (-1 - y) * ((-1 - y) * Real.exp (-I₂)) * Real.exp I₃ := by
        field_simp
  
/-- **Right difference quotients at `y`.** For real `y < b < −1` with flows on `[0, T]`:
`u_b − u_y ≤ (b − y)/(−1 − b) · (u_V − u_y) · exp(∫₀ᵗ 2(u_V − u_y)/(−u_V)³)`. -/
theorem re_sub_re_le_right (hW : Continuous W) (hW0 : W 0 = 0) {b y T : ℝ} (hyb : y < b) (hb : b < -1)
    {ub uy uV : ℝ → ℂ} (hub : IsForwardSol W (b : ℂ) T ub) (huy : IsForwardSol W (y : ℂ) T uy)
    (huV : IsForwardSol W ((-1 : ℝ) : ℂ) T uV) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (ub t).re - (uy t).re ≤ (b - y) / (-1 - b) * ((uV t).re - (uy t).re) *
      Real.exp (∫ s in (0 : ℝ)..t, 2 * ((uV s).re - (uy s).re) / (-(uV s).re) ^ 3) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hVn := re_neg_of_isForwardSol hW hW0 (show (-1 : ℝ) < 0 by norm_num) huV
  have hbV : ∀ s ∈ Icc 0 T, (ub s).re < (uV s).re := fun s hs => flow_re_lt_flow_re hW hub huV hb hs
  have hyb' : ∀ s ∈ Icc 0 T, (uy s).re < (ub s).re := fun s hs => flow_re_lt_flow_re hW huy hub hyb hs
  have e₁ := re_sub_re_eq_of_isForwardSol hW huy hub ht
  have e₂ := re_sub_re_eq_of_isForwardSol hW hub huV ht
  set I₁ := ∫ s in (0 : ℝ)..t, 2 / ((uy s).re * (ub s).re)
  set I₂ := ∫ s in (0 : ℝ)..t, 2 / ((ub s).re * (uV s).re)
  set I₃ := ∫ s in (0 : ℝ)..t, 2 * ((uV s).re - (uy s).re) / (-(uV s).re) ^ 3
  have hcb := continuousOn_re_of_isForwardSol hub
  have hcy := continuousOn_re_of_isForwardSol huy
  have hcV := continuousOn_re_of_isForwardSol huV
  have hi₁ : IntervalIntegrable (fun s => 2 / ((uy s).re * (ub s).re)) MeasureTheory.volume 0 t :=
    ((continuousOn_const.div (hcy.mul hcb) fun s hs => mul_ne_zero
      (re_ne_zero_of_isForwardSol_real hW huy hs) (re_ne_zero_of_isForwardSol_real hW hub hs)).mono
      hsub).intervalIntegrable_of_Icc ht.1
  have hi₂ : IntervalIntegrable (fun s => 2 / ((ub s).re * (uV s).re)) MeasureTheory.volume 0 t :=
    ((continuousOn_const.div (hcb.mul hcV) fun s hs => mul_ne_zero
      (re_ne_zero_of_isForwardSol_real hW hub hs) (re_ne_zero_of_isForwardSol_real hW huV hs)).mono
      hsub).intervalIntegrable_of_Icc ht.1
  have hi₃ : IntervalIntegrable (fun s => 2 * ((uV s).re - (uy s).re) / (-(uV s).re) ^ 3)
      MeasureTheory.volume 0 t :=
    (((continuousOn_const.mul (hcV.sub hcy)).div (hcV.neg.pow 3) fun s hs =>
      pow_ne_zero 3 (neg_pos.2 (hVn s hs)).ne').mono hsub).intervalIntegrable_of_Icc ht.1
  have hle : I₂ - I₁ ≤ I₃ := by
    rw [← intervalIntegral.integral_sub hi₂ hi₁]
    refine intervalIntegral.integral_mono_on ht.1 (hi₂.sub hi₁) hi₃ fun s hs => ?_
    have hs' := hsub hs
    have h := two_div_sub_two_div_le_right (P := -(uy s).re) (Q := -(ub s).re) (R := -(uV s).re)
      (by linarith [hVn s hs']) (by linarith [hbV s hs']) (by linarith [hyb' s hs'])
    have e1 : -(ub s).re * -(uV s).re = (ub s).re * (uV s).re := by ring
    have e2 : -(uy s).re * -(ub s).re = (uy s).re * (ub s).re := by ring
    have e3 : -(uy s).re - -(uV s).re = (uV s).re - (uy s).re := by ring
    rw [e1, e2, e3] at h
    exact h
  have hb1 : 0 < -1 - b := by linarith
  have hVb : (uV t).re - (ub t).re ≤ (uV t).re - (uy t).re := by linarith [hyb' t ht]
  rw [e₁]
  have e₂' : (-1 - b) * Real.exp (-I₂) = (uV t).re - (ub t).re := by rw [e₂]
  have hexp : Real.exp (-I₁) ≤ Real.exp (-I₂) * Real.exp I₃ := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hby : 0 ≤ b - y := by linarith
  calc (b - y) * Real.exp (-I₁) ≤ (b - y) * (Real.exp (-I₂) * Real.exp I₃) :=
        mul_le_mul_of_nonneg_left hexp hby
    _ = (b - y) / (-1 - b) * ((-1 - b) * Real.exp (-I₂)) * Real.exp I₃ := by
        field_simp
    _ ≤ (b - y) / (-1 - b) * ((uV t).re - (uy t).re) * Real.exp I₃ := by
        rw [e₂']
        gcongr

/-! ### Koebe at a real point left of the end mark -/

/-- The ball about a real point is invariant under conjugation. -/
theorem conj_mem_ball_real {c r : ℝ} {z : ℂ} (hz : z ∈ ball (c : ℂ) r) : conj z ∈ ball (c : ℂ) r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rwa [← Complex.conj_ofReal, ← map_sub, Complex.norm_conj]

theorem re_lt_of_mem_ball_ofReal {c r : ℝ} {z : ℂ} (hz : z ∈ ball (c : ℂ) r) : z.re < c + r := by
  have h1 : |z.re - c| < r := by
    calc |z.re - c| = |(z - c).re| := by simp
      _ ≤ ‖z - c‖ := abs_re_le_norm _
      _ < r := by rw [← dist_eq_norm]; exact hz
  have := (abs_lt.1 h1).2
  linarith

/-- **Koebe at a real point left of the end mark.** Let `F` be the inverse map `F_T` of a continuous driver, extended
continuously to `ℍ̄`, let `−1` be alive on `[0, T]` (centred flow `uV`), and let `y < −1` (centred flow `uy`). If the
one-sided difference quotients of `x ↦ u_x(T)` at `y` (on one side, within `δ`) are at most `M`, then the ball about
`y` of radius `(u_V(T) − u_y(T))/(48 M)` does not meet the hull `K_T`. -/
theorem disjoint_ball_fwdHull_of_slope (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    {uV : ℝ → ℂ} (huV : IsForwardSol W ((-1 : ℝ) : ℂ) T uV) {y : ℝ} (hy : y < -1) {uy : ℝ → ℂ}
    (huy : IsForwardSol W (y : ℂ) T uy) {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hslope : (∀ x : ℝ, y - δ < x → x < y → ∀ ux : ℝ → ℂ, IsForwardSol W (x : ℂ) T ux →
        (uy T).re - (ux T).re ≤ M * (y - x)) ∨
      (∀ x : ℝ, y < x → x < y + δ → ∀ ux : ℝ → ℂ, IsForwardSol W (x : ℂ) T ux →
        (ux T).re - (uy T).re ≤ M * (x - y))) :
    Disjoint (ball (y : ℂ) (QuantumZipper.CA.Koebe.koebeCovConst * ((uV T).re - (uy T).re) / M))
      (fwdHull W T) := by
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  set c : ℝ := (uy T).re with hc
  set r : ℝ := (uV T).re - c with hr
  have hr0 : 0 < r := sub_pos.2 (flow_re_lt_flow_re hW huy huV hy hTT)
  have hcuy : uy T = (c : ℂ) := flow_eq_ofReal_re hW huy hTT
  have hpre : ∀ ξ : ℝ, ξ < (uV T).re →
      ∃ x : ℝ, x < -1 ∧ ∃ u' : ℝ → ℂ, IsForwardSol W (x : ℂ) T u' ∧ u' T = ξ :=
    fun ξ hξ => exists_isForwardSol_eq_of_lt hW hW0 hT huV hξ
  have hFx : ∀ {x : ℝ} {u' : ℝ → ℂ}, IsForwardSol W (x : ℂ) T u' → F (u' T) = x :=
    fun hu' => extendFrom_eq_of_isForwardSol hW hW0 hT hFeq hFc hu'
  have hreal : ∀ z ∈ ball (c : ℂ) r, z.im = 0 → (F z).im = 0 := fun z hz hz0 => by
    obtain ⟨x, -, u', hu', hu'T⟩ := hpre z.re (by have := re_lt_of_mem_ball_ofReal hz; linarith)
    have hz' : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    rw [hz', ← hu'T, hFx hu']
    simp
  have hd : DifferentiableOn ℂ F (H ∩ ball (c : ℂ) r) :=
    ((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hT).mono fun z hz => hz.1).congr
      fun z hz => hFeq hz.1
  obtain ⟨G, hGd, hGF, hGconj⟩ :=
    QuantumZipper.CA.exists_reflection_extension hd (hFc.mono inter_subset_left) hreal
  have himg := QuantumZipper.RS.image_fwdMapInv_H hW hW0 hT
  -- the three regions
  have hGpos : ∀ z ∈ ball (c : ℂ) r, 0 < z.im → G z ∈ H \ fwdHull W T ∧ G z = fwdMapInv W T z := by
    intro z hz hz0
    have h1 : G z = fwdMapInv W T z := by
      rw [hGF ⟨(show (0 : ℝ) ≤ z.im from hz0.le), hz⟩]; exact hFeq hz0
    refine ⟨?_, h1⟩
    rw [h1, ← himg]
    exact mem_image_of_mem _ hz0
  have hGneg : ∀ z ∈ ball (c : ℂ) r, z.im < 0 → G z = conj (G (conj z)) ∧ (G z).im < 0 := by
    intro z hz hz0
    have hcz := conj_mem_ball_real hz
    have h1 := hGconj (conj z) hcz
    rw [Complex.conj_conj] at h1
    refine ⟨h1, ?_⟩
    rw [h1, Complex.conj_im, neg_neg_iff_pos]
    exact (hGpos _ hcz (by rw [Complex.conj_im]; linarith)).1.1
  have hGzero : ∀ z ∈ ball (c : ℂ) r, z.im = 0 →
      ∃ x : ℝ, x < -1 ∧ ∃ u' : ℝ → ℂ, IsForwardSol W (x : ℂ) T u' ∧ u' T = z.re ∧ G z = x := by
    intro z hz hz0
    obtain ⟨x, hx, u', hu', hu'T⟩ := hpre z.re (by have := re_lt_of_mem_ball_ofReal hz; linarith)
    have hz' : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
    refine ⟨x, hx, u', hu', by rw [hu'T], ?_⟩
    rw [hGF ⟨(show (0 : ℝ) ≤ z.im from hz0.ge), hz⟩, hz', ← hu'T, hFx hu']
  -- injectivity
  have hinjpos : ∀ z₁ ∈ ball (c : ℂ) r, ∀ z₂ ∈ ball (c : ℂ) r, 0 < z₁.im → 0 < z₂.im →
      G z₁ = G z₂ → z₁ = z₂ := by
    intro z₁ h₁ z₂ h₂ p₁ p₂ heq
    rw [(hGpos z₁ h₁ p₁).2, (hGpos z₂ h₂ p₂).2] at heq
    exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hT p₁ p₂ heq
  have hinj : InjOn G (ball (c : ℂ) r) := by
    intro z₁ h₁ z₂ h₂ heq
    have himeq := congrArg Complex.im heq
    rcases lt_trichotomy z₁.im 0 with n₁ | z₁0 | p₁ <;>
      rcases lt_trichotomy z₂.im 0 with n₂ | z₂0 | p₂
    · have e₁ := (hGneg z₁ h₁ n₁).1
      have e₂ := (hGneg z₂ h₂ n₂).1
      rw [e₁, e₂] at heq
      have := hinjpos _ (conj_mem_ball_real h₁) _ (conj_mem_ball_real h₂)
        (by rw [Complex.conj_im]; linarith) (by rw [Complex.conj_im]; linarith)
        ((RingHom.injective _) heq)
      exact (RingHom.injective _) this
    · obtain ⟨x, -, u', -, -, hGx⟩ := hGzero z₂ h₂ z₂0
      have := (hGneg z₁ h₁ n₁).2
      rw [himeq, hGx, ofReal_im] at this; exact absurd this (lt_irrefl _)
    · have := (hGneg z₁ h₁ n₁).2
      have h2 : 0 < (G z₂).im := (hGpos z₂ h₂ p₂).1.1
      rw [himeq] at this
      exact absurd (h2.trans this) (lt_irrefl _)
    · obtain ⟨x, -, u', -, -, hGx⟩ := hGzero z₁ h₁ z₁0
      have := (hGneg z₂ h₂ n₂).2
      rw [← himeq, hGx, ofReal_im] at this; exact absurd this (lt_irrefl _)
    · obtain ⟨x₁, -, u₁, hu₁, hu₁T, hG₁⟩ := hGzero z₁ h₁ z₁0
      obtain ⟨x₂, -, u₂, hu₂, hu₂T, hG₂⟩ := hGzero z₂ h₂ z₂0
      rw [hG₁, hG₂, ofReal_inj] at heq
      subst heq
      have := eqOn_of_isForwardSol hW hu₁ hu₂ hTT
      rw [hu₁T, hu₂T, ofReal_inj] at this
      apply Complex.ext
      · exact this
      · rw [z₁0, z₂0]
    · obtain ⟨x, -, u', -, -, hGx⟩ := hGzero z₁ h₁ z₁0
      have : 0 < (G z₂).im := (hGpos z₂ h₂ p₂).1.1
      rw [← himeq, hGx, ofReal_im] at this; exact absurd this (lt_irrefl _)
    · have := (hGneg z₂ h₂ n₂).2
      have h1 : 0 < (G z₁).im := (hGpos z₁ h₁ p₁).1.1
      rw [← himeq] at this
      exact absurd (h1.trans this) (lt_irrefl _)
    · obtain ⟨x, -, u', -, -, hGx⟩ := hGzero z₂ h₂ z₂0
      have : 0 < (G z₁).im := (hGpos z₁ h₁ p₁).1.1
      rw [himeq, hGx, ofReal_im] at this; exact absurd this (lt_irrefl _)
    · exact hinjpos z₁ h₁ z₂ h₂ p₁ p₂ heq
  -- the image avoids the hull
  have hdisj : Disjoint (G '' ball (c : ℂ) r) (fwdHull W T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hK
    rcases lt_trichotomy z.im 0 with n | z0 | p
    · have := (hGneg z hz n).2
      have h2 : 0 < (G z).im := (QuantumZipper.fwdHull_mono.2 T) hK
      linarith
    · obtain ⟨x, -, u', -, -, hGx⟩ := hGzero z hz z0
      have h2 : 0 < (G z).im := (QuantumZipper.fwdHull_mono.2 T) hK
      rw [hGx, ofReal_im] at h2; exact lt_irrefl _ h2
    · exact (hGpos z hz p).1.2 hK
  have hcB : (c : ℂ) ∈ ball (c : ℂ) r := mem_ball_self hr0
  have hGc : G (c : ℂ) = y := by
    rw [hGF ⟨(show (0 : ℝ) ≤ (c : ℂ).im by rw [ofReal_im]), hcB⟩, ← hcuy, hFx huy]
  -- Koebe
  have hK := QuantumZipper.CA.Koebe.ball_subset_image_koebe hGd hinj
  rw [hGc] at hK
  -- the derivative at `c`: real difference quotients
  have hGdc : DifferentiableAt ℂ G (c : ℂ) := hGd.differentiableAt (isOpen_ball.mem_nhds hcB)
  have hR : HasDerivAt (fun s : ℝ => G (s : ℂ)) (deriv G (c : ℂ)) c := hGdc.hasDerivAt.comp_ofReal
  obtain ⟨ε, hε, hεG⟩ := Metric.continuousAt_iff.1 hR.continuousAt δ hδ
  -- real points near `c` are images of flows
  have hval : ∀ t : ℝ, |t| < min ε r → ∃ x : ℝ, x < -1 ∧ ∃ u' : ℝ → ℂ, IsForwardSol W (x : ℂ) T u' ∧
      (u' T).re = c + t ∧ G ((c + t : ℝ) : ℂ) = x ∧ |x - y| < δ := by
    intro t ht
    have htr : |t| < r := ht.trans_le (min_le_right _ _)
    have hmem : (((c + t : ℝ)) : ℂ) ∈ ball (c : ℂ) r := by
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simpa using htr
    obtain ⟨x, hx, u', hu', hu'T, hGx⟩ := hGzero _ hmem (ofReal_im _)
    refine ⟨x, hx, u', hu', by rw [hu'T]; simp, hGx, ?_⟩
    have hd' := hεG (show dist (c + t) c < ε by
      rw [Real.dist_eq, add_sub_cancel_left]; exact ht.trans_le (min_le_left _ _))
    rw [hGx, hGc, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hd'
    exact hd'
  have hmin : 0 < min ε r := lt_min hε hr0
  have hder : M⁻¹ ≤ ‖deriv G (c : ℂ)‖ := by
    rcases hslope with hL | hRt
    · have hlim := (hR.tendsto_slope_zero_left).norm
      refine ge_of_tendsto hlim ?_
      have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ∈ Ioo (-min ε r) 0 :=
        Ioo_mem_nhdsLT (by linarith)
      filter_upwards [hev] with t ht
      have hta : |t| < min ε r := by rw [abs_of_neg ht.2]; linarith [ht.1]
      obtain ⟨x, -, u', hu', hu'T, hGx, hxy⟩ := hval t hta
      have hxy' : x < y := by
        rcases lt_trichotomy x y with h | h | h
        · exact h
        · subst h
          have := eqOn_of_isForwardSol hW hu' huy hTT
          have h2 := congrArg Complex.re this
          linarith [ht.2, hc]
        · have := flow_re_lt_flow_re hW huy hu' h hTT
          linarith [ht.2, hc]
      have hsl := hL x (by linarith [(abs_lt.1 hxy).1]) hxy' u' hu'
      rw [hu'T] at hsl
      rw [hGx, hGc, norm_smul, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_inv, abs_of_neg ht.2, abs_of_neg (sub_neg.2 hxy')]
      rw [inv_le_iff_one_le_mul₀ hM]
      have htn : 0 < -t := neg_pos.2 ht.2
      have e : (-t)⁻¹ * -(x - y) * M = M * (y - x) / (-t) := by field_simp; ring
      rw [e, one_le_div htn]
      linarith
    · have hlim := (hR.tendsto_slope_zero_right).norm
      refine ge_of_tendsto hlim ?_
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (min ε r) := Ioo_mem_nhdsGT hmin
      filter_upwards [hev] with t ht
      have hta : |t| < min ε r := by rw [abs_of_pos ht.1]; exact ht.2
      obtain ⟨x, -, u', hu', hu'T, hGx, hxy⟩ := hval t hta
      have hxy' : y < x := by
        rcases lt_trichotomy x y with h | h | h
        · have := flow_re_lt_flow_re hW hu' huy h hTT
          linarith [ht.1, hc]
        · subst h
          have := eqOn_of_isForwardSol hW hu' huy hTT
          have h2 := congrArg Complex.re this
          linarith [ht.1, hc]
        · exact h
      have hsl := hRt x hxy' (by linarith [(abs_lt.1 hxy).2]) u' hu'
      rw [hu'T] at hsl
      rw [hGx, hGc, norm_smul, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_inv, abs_of_pos ht.1, abs_of_pos (sub_pos.2 hxy')]
      rw [inv_le_iff_one_le_mul₀ hM]
      have e : t⁻¹ * (x - y) * M = M * (x - y) / t := by field_simp
      rw [e, one_le_div ht.1]
      linarith
  -- conclusion
  refine Disjoint.mono_left (fun z hz => hK ?_) hdisj
  rw [mem_ball] at hz ⊢
  refine lt_of_lt_of_le hz ?_
  rw [div_eq_mul_inv]
  have hk := QuantumZipper.CA.Koebe.koebeCovConst_pos
  exact mul_le_mul_of_nonneg_left hder (by positivity)

/-- **Koebe at an upper point, the case `X → +∞`.** If `∫₀ᵀ 2/((u_V − u_y)(−u_V)) ≤ K` (in strip time,
`∫ 2e^{−X}`, `X` the upper gap of `y`), then `dist(y, K_T) ≥ (−1 − y) e^{−K}/48`. -/
theorem disjoint_ball_fwdHull_left (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    {uV : ℝ → ℂ} (huV : IsForwardSol W ((-1 : ℝ) : ℂ) T uV) {y : ℝ} (hy : y < -1) {uy : ℝ → ℂ}
    (huy : IsForwardSol W (y : ℂ) T uy) {K : ℝ}
    (hK : ∫ s in (0 : ℝ)..T, 2 / (((uV s).re - (uy s).re) * -(uV s).re) ≤ K) :
    Disjoint (ball (y : ℂ) (QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K))))
      (fwdHull W T) := by
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hgap : 0 < (uV T).re - (uy T).re := sub_pos.2 (flow_re_lt_flow_re hW huy huV hy hTT)
  have hy1 : 0 < -1 - y := by linarith
  set M := ((uV T).re - (uy T).re) * Real.exp K / (-1 - y) with hM
  have hM0 : 0 < M := by positivity
  have h := disjoint_ball_fwdHull_of_slope hW hW0 hT hFeq hFc huV hy huy hM0 one_pos (Or.inl
    fun x _ hxy ux hux => by
      have h1 := re_sub_re_le_left hW hW0 hxy hy hux huy huV hTT
      have h2 : Real.exp (∫ s in (0 : ℝ)..T, 2 / (((uV s).re - (uy s).re) * -(uV s).re)) ≤ Real.exp K :=
        Real.exp_le_exp.2 hK
      calc (uy T).re - (ux T).re ≤ (y - x) / (-1 - y) * ((uV T).re - (uy T).re) *
            Real.exp (∫ s in (0 : ℝ)..T, 2 / (((uV s).re - (uy s).re) * -(uV s).re)) := h1
        _ ≤ (y - x) / (-1 - y) * ((uV T).re - (uy T).re) * Real.exp K := by
            gcongr
        _ = M * (y - x) := by rw [hM]; ring)
  have e : QuantumZipper.CA.Koebe.koebeCovConst * ((uV T).re - (uy T).re) / M =
      QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K)) := by
    rw [hM, Real.exp_neg]
    field_simp
  rwa [e] at h

/-- **Koebe at an upper point, the case `X → −∞`.** If `∫₀ᵀ 2(u_V − u_y)/(−u_V)³ ≤ K` (in strip time,
`∫ 2e^{X}`), then `dist(y, K_T) ≥ (−1 − y) e^{−K}/96`. -/
theorem disjoint_ball_fwdHull_right (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    {uV : ℝ → ℂ} (huV : IsForwardSol W ((-1 : ℝ) : ℂ) T uV) {y : ℝ} (hy : y < -1) {uy : ℝ → ℂ}
    (huy : IsForwardSol W (y : ℂ) T uy) {K : ℝ}
    (hK : ∫ s in (0 : ℝ)..T, 2 * ((uV s).re - (uy s).re) / (-(uV s).re) ^ 3 ≤ K) :
    Disjoint (ball (y : ℂ) (QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K) / 2)))
      (fwdHull W T) := by
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hgap : 0 < (uV T).re - (uy T).re := sub_pos.2 (flow_re_lt_flow_re hW huy huV hy hTT)
  have hy1 : 0 < -1 - y := by linarith
  set M := 2 * (((uV T).re - (uy T).re) * Real.exp K) / (-1 - y) with hM
  have hM0 : 0 < M := by positivity
  have h := disjoint_ball_fwdHull_of_slope hW hW0 hT hFeq hFc huV hy huy hM0
    (show 0 < (-1 - y) / 2 by linarith) (Or.inr fun x hyx hxδ ux hux => by
      have hx1 : x < -1 := by linarith
      have h1 := re_sub_re_le_right hW hW0 hyx hx1 hux huy huV hTT
      have h2 : Real.exp (∫ s in (0 : ℝ)..T, 2 * ((uV s).re - (uy s).re) / (-(uV s).re) ^ 3) ≤
          Real.exp K := Real.exp_le_exp.2 hK
      have hx1' : (-1 - y) / 2 ≤ -1 - x := by linarith
      have hq : (x - y) / (-1 - x) ≤ 2 * (x - y) / (-1 - y) := by
        rw [div_le_div_iff₀ (by linarith) hy1]
        nlinarith
      calc (ux T).re - (uy T).re ≤ (x - y) / (-1 - x) * ((uV T).re - (uy T).re) *
            Real.exp (∫ s in (0 : ℝ)..T, 2 * ((uV s).re - (uy s).re) / (-(uV s).re) ^ 3) := h1
        _ ≤ 2 * (x - y) / (-1 - y) * ((uV T).re - (uy T).re) * Real.exp K := by
            gcongr
        _ = M * (x - y) := by rw [hM]; ring)
  have e : QuantumZipper.CA.Koebe.koebeCovConst * ((uV T).re - (uy T).re) / M =
      QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K) / 2) := by
    rw [hM, Real.exp_neg]
    field_simp
  rwa [e] at h

/-- **Koebe at an upper point, the derivative identity (3.23).** If
`∫₀ᵀ (2/(u_y u_V) − 2/u_y²) ≤ K` (in strip time `½∫ sech²(X/2)`, `X` the upper gap of `y`), then
`dist(y, K_T) ≥ (−1 − y) e^{−K}/48`. The right difference quotients `(u_b − u_y)/(b − y) = exp(−∫ 2/(u_y u_b))` are
at most `exp(−∫ 2/u_y²) = 1/F_T'(u_y)`. -/
theorem disjoint_ball_fwdHull_sech (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W T) H) (hFc : ContinuousOn F Hbar)
    {uV : ℝ → ℂ} (huV : IsForwardSol W ((-1 : ℝ) : ℂ) T uV) {y : ℝ} (hy : y < -1) {uy : ℝ → ℂ}
    (huy : IsForwardSol W (y : ℂ) T uy) {K : ℝ}
    (hK : ∫ s in (0 : ℝ)..T, (2 / ((uy s).re * (uV s).re) - 2 / (uy s).re ^ 2) ≤ K) :
    Disjoint (ball (y : ℂ) (QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K))))
      (fwdHull W T) := by
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hy1 : 0 < -1 - y := by linarith
  have hVn := re_neg_of_isForwardSol hW hW0 (show (-1 : ℝ) < 0 by norm_num) huV
  have hyn := re_neg_of_isForwardSol hW hW0 (show y < 0 by linarith) huy
  have hcy := continuousOn_re_of_isForwardSol huy
  have hcV := continuousOn_re_of_isForwardSol huV
  have hny : ∀ s ∈ Icc 0 T, (uy s).re ≠ 0 := fun s hs => (hyn s hs).ne
  have hi2 : IntervalIntegrable (fun s => 2 / (uy s).re ^ 2) MeasureTheory.volume 0 T :=
    (continuousOn_const.div (hcy.pow 2) fun s hs => pow_ne_zero 2 (hny s hs)).intervalIntegrable_of_Icc hT
  have hi1 : IntervalIntegrable (fun s => 2 / ((uy s).re * (uV s).re)) MeasureTheory.volume 0 T :=
    (continuousOn_const.div (hcy.mul hcV) fun s hs => mul_ne_zero (hny s hs) (hVn s hs).ne).intervalIntegrable_of_Icc hT
  set M := Real.exp (-∫ s in (0 : ℝ)..T, 2 / (uy s).re ^ 2) with hM
  have hM0 : 0 < M := Real.exp_pos _
  have h := disjoint_ball_fwdHull_of_slope hW hW0 hT hFeq hFc huV hy huy hM0 hy1 (Or.inr
    fun b hyb hbδ ub hub => by
      have hb0 : b < 0 := by linarith
      have hbn := re_neg_of_isForwardSol hW hW0 hb0 hub
      have hcb := continuousOn_re_of_isForwardSol hub
      have hlt := fun s (hs : s ∈ Icc 0 T) => flow_re_lt_flow_re hW huy hub hyb hs
      have hi3 : IntervalIntegrable (fun s => 2 / ((uy s).re * (ub s).re)) MeasureTheory.volume 0 T :=
        (continuousOn_const.div (hcy.mul hcb) fun s hs =>
          mul_ne_zero (hny s hs) (hbn s hs).ne).intervalIntegrable_of_Icc hT
      have e := re_sub_re_eq_of_isForwardSol hW huy hub hTT
      rw [e, mul_comm (b - y), hM]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg ?_)) (by linarith)
      refine intervalIntegral.integral_mono_on hT hi2 hi3 fun s hs => ?_
      have h1 := hyn s hs
      have h2 := hbn s hs
      have h3 := hlt s hs
      rw [div_le_div_iff₀ (pow_pos (neg_pos.2 h1) 2 |>.trans_eq (by ring)) (by nlinarith)]
      nlinarith)
  -- the radius
  have e := re_sub_re_eq_of_isForwardSol hW huy huV hTT
  have hle : QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K)) ≤
      QuantumZipper.CA.Koebe.koebeCovConst * ((uV T).re - (uy T).re) / M := by
    rw [e, hM, mul_div_assoc]
    have hk := QuantumZipper.CA.Koebe.koebeCovConst_pos
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    rw [show (-1 - y) * Real.exp (-∫ s in (0 : ℝ)..T, 2 / ((uy s).re * (uV s).re)) /
        Real.exp (-∫ s in (0 : ℝ)..T, 2 / (uy s).re ^ 2) =
        (-1 - y) * Real.exp (-((∫ s in (0 : ℝ)..T, 2 / ((uy s).re * (uV s).re)) -
          ∫ s in (0 : ℝ)..T, 2 / (uy s).re ^ 2)) by
      rw [mul_div_assoc, ← Real.exp_sub]; ring_nf]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hy1.le
    rw [← intervalIntegral.integral_sub hi1 hi2]
    exact hK
  exact Disjoint.mono_left (ball_subset_ball hle) h

end Zhan

end InteractingSLE
