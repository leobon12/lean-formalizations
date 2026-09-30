import QuantumZipper.Proofs.Zipper.RegContEnergy
import QuantumZipper.Proofs.Thm12.TwoPointExpansion
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.GFF.FrostmanReg

/-!
# REG-CONT, deterministic continuity in time (steps 4–5)

Blueprint `E_BRANCH_BLUEPRINT.md` §3, node REG-CONT; handoff `handoff/REG-CONT.md`, steps 4–5.
With `ψ_s = fwdMapInv W s` and `ν_s = (fc(w,r)).map ψ_s` (`νT W w r s`):

* `norm_fwdMapInv_add_sub_le`, `abs_log_deriv_fwdMapInv_add_sub_le`: for `u ∈ ℍ`, `ψ_s(u)` and
  `log ‖ψ_s'(u)‖` move by `O(ε + h)` between the times `s` and `s + h`, where `ε` bounds the
  oscillation of `W` on `[s, s+h]` (flow property `ψ_{s+h} = ψ_s ∘ ψ̃`, `ψ̃` near the identity,
  and the Lipschitz bounds of `revMap` and of `log ‖revMap'‖` on `{Im ≥ δ}`);
* `continuousOn_of_flow_bound`: such a bound gives continuity on `[0,T]`;
* `continuousOn_integral_νT`: `s ↦ ∫ G dν_s` is continuous for `G` continuous on `Hbar`;
* `continuousOn_integral_log_deriv_fwdMapInv`: the `Q`-term `s ↦ ∫ log ‖ψ_s'‖ dfc(w,r)` is
  continuous (dominated convergence with the bound `|log √(R²+4T)| + |log Im u|`);
* `continuousOn_integral_log_νT`: `s ↦ ∫ log ‖z‖ dν_s` is continuous (uniform limit of
  `∫ log max(2^{-k}, ‖z‖) dν_s`, the error being `≤ 3 C 2^{-k/3}` by the Frostman bound);
* `continuousOn_evalReg_of_uc`: if the field `x` has continuous regularized averages
  (`RegAvgGood`) and the averages `Ψ_k(s) = ∫ avgReg x k dν_s` are uniformly Cauchy over the
  rational times (`UCq`), then `s ↦ evalReg (ofFun (h0rev κ) + x) ν_s` is continuous on `[0,T]`.

The flow and Lipschitz estimates are elementary (own arguments, no source needed); the
continuity statements are the standard dominated/uniform convergence arguments.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegCont

open TwoPoint UnzipInvariance

variable {W : ℝ → ℝ}

/-! ## Lipschitz bounds for the reverse flow -/

theorem inv_sum_le_of_le {δ A B : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) (hB : δ ≤ B) :
    (A + B) / (A ^ 2 * B ^ 2) ≤ 2 / δ ^ 3 := by
  have hA0 : 0 < A := hδ.trans_le hA
  have hB0 : 0 < B := hδ.trans_le hB
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : δ ^ 3 ≤ A * B ^ 2 := by
    rw [show δ ^ 3 = δ * δ ^ 2 by ring]
    exact mul_le_mul hA (pow_le_pow_left₀ hδ.le hB 2) (by positivity) hA0.le
  have h2 : δ ^ 3 ≤ A ^ 2 * B := by
    rw [show δ ^ 3 = δ ^ 2 * δ by ring]
    exact mul_le_mul (pow_le_pow_left₀ hδ.le hA 2) hB hδ.le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 hA0.le, mul_le_mul_of_nonneg_left h2 hB0.le]

theorem norm_two_div_sq_sub_le {δ : ℝ} (hδ : 0 < δ) {a b : ℂ} (ha : δ ≤ ‖a‖) (hb : δ ≤ ‖b‖) :
    ‖2 / a ^ 2 - 2 / b ^ 2‖ ≤ 4 * ‖a - b‖ / δ ^ 3 := by
  have ha0 : a ≠ 0 := norm_pos_iff.1 (hδ.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.1 (hδ.trans_le hb)
  have e : 2 / a ^ 2 - 2 / b ^ 2 = 2 * (b - a) * (b + a) / (a ^ 2 * b ^ 2) := by
    field_simp; ring
  rw [e, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_two,
    norm_sub_rev b a]
  have h1 : ‖b + a‖ ≤ ‖a‖ + ‖b‖ := (norm_add_le _ _).trans_eq (add_comm _ _)
  have hA0 : 0 < ‖a‖ := hδ.trans_le ha
  have hB0 : 0 < ‖b‖ := hδ.trans_le hb
  calc 2 * ‖a - b‖ * ‖b + a‖ / (‖a‖ ^ 2 * ‖b‖ ^ 2)
      ≤ 2 * ‖a - b‖ * (‖a‖ + ‖b‖) / (‖a‖ ^ 2 * ‖b‖ ^ 2) := by gcongr
    _ = 2 * ‖a - b‖ * ((‖a‖ + ‖b‖) / (‖a‖ ^ 2 * ‖b‖ ^ 2)) := by ring
    _ ≤ 2 * ‖a - b‖ * (2 / δ ^ 3) :=
        mul_le_mul_of_nonneg_left (inv_sum_le_of_le hδ ha hb) (by positivity)
    _ = 4 * ‖a - b‖ / δ ^ 3 := by ring

theorem intervalIntegrable_two_div_sq_revMap {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ}
    (hz : 0 < z.im) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (fun r => 2 / revMap V r z ^ 2) volume 0 s := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hs]
  exact continuousOn_const.div ((TwoPointExp.revMap_continuousOn hV hz hs).pow 2) fun r hr =>
    pow_ne_zero 2 (TwoPointExp.revMap_ne_zero' hV hz hr.1)

/-- `log ‖(revMap V s)'‖` is Lipschitz on `{Im ≥ δ}`. -/
theorem abs_log_norm_deriv_revMap_sub_le {V : ℝ → ℝ} (hV : Continuous V) {s δ : ℝ} (hs : 0 ≤ s)
    (hδ : 0 < δ) {u v : ℂ} (hu : δ ≤ u.im) (hv : δ ≤ v.im) :
    |Real.log ‖deriv (revMap V s) v‖ - Real.log ‖deriv (revMap V s) u‖| ≤
      4 * Real.exp (2 / δ ^ 2 * s) / δ ^ 3 * ‖v - u‖ * s := by
  have huH : u ∈ H := show 0 < u.im from hδ.trans_le hu
  have hvH : v ∈ H := show 0 < v.im from hδ.trans_le hv
  rw [log_norm_deriv_revMap V hV hs hvH, log_norm_deriv_revMap V hV hs huH, ← Complex.sub_re,
    ← intervalIntegral.integral_sub (intervalIntegrable_two_div_sq_revMap hV hvH hs)
      (intervalIntegrable_two_div_sq_revMap hV huH hs)]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) s, ‖2 / revMap V r v ^ 2 - 2 / revMap V r u ^ 2‖ ≤
      4 * Real.exp (2 / δ ^ 2 * s) / δ ^ 3 * ‖v - u‖ := by
    intro r hr
    rw [uIoc_of_le hs] at hr
    have hr0 : 0 ≤ r := hr.1.le
    refine (norm_two_div_sq_sub_le hδ (TwoPointExp.le_norm_revMap hV hδ hv hr0)
      (TwoPointExp.le_norm_revMap hV hδ hu hr0)).trans ?_
    have hL := (TwoPointExp.norm_revMap_sub_revMap_le hV hδ hv hu hr0).1
    have hE : Real.exp (2 / δ ^ 2 * r) ≤ Real.exp (2 / δ ^ 2 * s) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2 (by positivity))
    have h3 : ‖revMap V r v - revMap V r u‖ ≤ ‖v - u‖ * Real.exp (2 / δ ^ 2 * s) :=
      hL.trans (mul_le_mul_of_nonneg_left hE (norm_nonneg _))
    calc 4 * ‖revMap V r v - revMap V r u‖ / δ ^ 3
        ≤ 4 * (‖v - u‖ * Real.exp (2 / δ ^ 2 * s)) / δ ^ 3 := by gcongr
      _ = 4 * Real.exp (2 / δ ^ 2 * s) / δ ^ 3 * ‖v - u‖ := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg hs]

/-- Small-time bound `|log ‖(revMap V h)' u‖| ≤ 2h/(Im u)²`. -/
theorem abs_log_norm_deriv_revMap_le_small {V : ℝ → ℝ} (hV : Continuous V) {h : ℝ} (hh : 0 ≤ h)
    {u : ℂ} (hu : u ∈ H) : |Real.log ‖deriv (revMap V h) u‖| ≤ 2 * h / u.im ^ 2 := by
  have hu0 : 0 < u.im := hu
  rw [log_norm_deriv_revMap V hV hh hu]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) h, ‖2 / revMap V r u ^ 2‖ ≤ 2 / u.im ^ 2 := by
    intro r hr
    rw [uIoc_of_le hh] at hr
    have hn := TwoPointExp.le_norm_revMap hV hu0 le_rfl hr.1.le
    rw [norm_div, norm_pow, Complex.norm_two]
    gcongr
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg hh]; ring

/-! ## The unzip maps in time -/

/-- The time-reversed driver at time `s`. -/
abbrev vRev (W : ℝ → ℝ) (s : ℝ) : ℝ → ℝ := fun q => W (s - q) - W s

theorem continuous_vRev (hW : Continuous W) (s : ℝ) : Continuous (vRev W s) := by
  unfold vRev; fun_prop

/-- **Displacement of `ψ_s(u)` in time.** -/
theorem norm_fwdMapInv_add_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {s h ε : ℝ} (hs : 0 ≤ s)
    (hh : 0 ≤ h) (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) {u : ℂ}
    (hu : u ∈ H) :
    ‖fwdMapInv W (s + h) u - fwdMapInv W s u‖ ≤
      (ε + 2 * h / u.im) * Real.exp (2 / u.im ^ 2 * s) := by
  have hu0 : 0 < u.im := hu
  set V' : ℝ → ℝ := fun q => W (s + h - q) - W (s + h) with hV'
  have hV'c : Continuous V' := by rw [hV']; fun_prop
  set φ := revMap V' h u with hφ
  have hφH : φ ∈ H := im_revMap_pos hV'c hu hh
  have hφim : u.im ≤ φ.im := im_le_im_revMap V' hV'c u hu hh
  rw [fwdMapInv_add hW hW0 hs hh hu, ← hφ, fwdMapInv_eq_revMap_timeRev W hW hW0 hs hφH,
    fwdMapInv_eq_revMap_timeRev W hW hW0 hs hu]
  have hL := (TwoPointExp.norm_revMap_sub_revMap_le (continuous_vRev hW s) hu0 hφim le_rfl hs).1
  have hd : ‖φ - u‖ ≤ ε + 2 * h / u.im := norm_revMap_sub_self_le hV'c hu hh hε
  exact hL.trans (mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le)

theorem deriv_fwdMapInv_eq (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {u : ℂ}
    (hu : u ∈ H) : deriv (fwdMapInv W s) u = deriv (revMap (vRev W s) s) u := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_H.mem_nhds hu] with z hz
  exact fwdMapInv_eq_revMap_timeRev W hW hW0 hs hz

/-- **Displacement of `log ‖ψ_s'(u)‖` in time.** -/
theorem abs_log_deriv_fwdMapInv_add_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {s h ε : ℝ}
    (hs : 0 ≤ s) (hh : 0 ≤ h) (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε)
    {u : ℂ} (hu : u ∈ H) :
    |Real.log ‖deriv (fwdMapInv W (s + h)) u‖ - Real.log ‖deriv (fwdMapInv W s) u‖| ≤
      4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 * (ε + 2 * h / u.im) * s +
        2 * h / u.im ^ 2 := by
  have hu0 : 0 < u.im := hu
  set V' : ℝ → ℝ := fun q => W (s + h - q) - W (s + h) with hV'
  have hV'c : Continuous V' := by rw [hV']; fun_prop
  have hVc := continuous_vRev hW s
  set φ := revMap V' h u with hφ
  have hφH : φ ∈ H := im_revMap_pos hV'c hu hh
  have hφim : u.im ≤ φ.im := im_le_im_revMap V' hV'c u hu hh
  -- the derivative of `ψ_{s+h}` at `u` by the chain rule
  have hd1 := hasDerivAt_revMap (vRev W s) hVc hs hφH
  have hd2 := hasDerivAt_revMap V' hV'c hh hu
  have hcomp := hd1.comp u hd2
  have heq : deriv (fwdMapInv W (s + h)) u = deriv (fun z => revMap (vRev W s) s (revMap V' h z)) u := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_H.mem_nhds hu] with z hz
    rw [fwdMapInv_add hW hW0 hs hh hz,
      fwdMapInv_eq_revMap_timeRev W hW hW0 hs (im_revMap_pos hV'c hz hh)]
  rw [heq, show (fun z => revMap (vRev W s) s (revMap V' h z)) =
      (revMap (vRev W s) s ∘ revMap V' h) from rfl, hcomp.deriv, deriv_fwdMapInv_eq hW hW0 hs hu, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (Complex.exp_ne_zero _))
      (norm_ne_zero_iff.2 (Complex.exp_ne_zero _))]
  rw [← (hasDerivAt_revMap (vRev W s) hVc hs hφH).deriv, ← hd2.deriv]
  have h1 := abs_log_norm_deriv_revMap_sub_le hVc hs hu0 le_rfl hφim
  have h2 := abs_log_norm_deriv_revMap_le_small hV'c hh hu
  have hd : ‖φ - u‖ ≤ ε + 2 * h / u.im := norm_revMap_sub_self_le hV'c hu hh hε
  have hK : 0 ≤ 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 := by positivity
  have h1' : |Real.log ‖deriv (revMap (vRev W s) s) φ‖ - Real.log ‖deriv (revMap (vRev W s) s) u‖|
      ≤ 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 * (ε + 2 * h / u.im) * s :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hK) hs)
  calc |Real.log ‖deriv (revMap (vRev W s) s) φ‖ + Real.log ‖deriv (revMap V' h) u‖ -
        Real.log ‖deriv (revMap (vRev W s) s) u‖|
      = |(Real.log ‖deriv (revMap (vRev W s) s) φ‖ - Real.log ‖deriv (revMap (vRev W s) s) u‖) +
          Real.log ‖deriv (revMap V' h) u‖| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1' h2)

/-! ## From displacement bounds to continuity -/

/-- A displacement bound `dist (f (s+h)) (f s) ≤ C (ε + h)`, `ε` the oscillation of `W` on
`[s, s+h]`, gives continuity on `[0,T]`. -/
theorem continuousOn_of_flow_bound {E : Type*} [PseudoMetricSpace E] (hW : Continuous W)
    {T C : ℝ} {f : ℝ → E}
    (hf : ∀ s h ε : ℝ, 0 ≤ s → 0 ≤ h → s + h ≤ T → 0 ≤ ε →
      (∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) → dist (f (s + h)) (f s) ≤ C * (ε + h)) :
    ContinuousOn f (Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro b hb η hη
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set ε₀ := η / (2 * C') with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  have hU := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hW.continuousOn
  obtain ⟨δ₁, hδ₁, hU'⟩ := Metric.uniformContinuousOn_iff.1 hU ε₀ hε₀0
  refine ⟨min δ₁ ε₀, lt_min hδ₁ hε₀0, fun a ha hab => ?_⟩
  have hab1 : dist a b < δ₁ := hab.trans_le (min_le_left _ _)
  have hab2 : dist a b < ε₀ := hab.trans_le (min_le_right _ _)
  -- the generic step: `x ≤ y` in `[0,T]`, `y - x < min δ₁ ε₀`
  have step : ∀ x y, x ∈ Icc (0 : ℝ) T → y ∈ Icc (0 : ℝ) T → x ≤ y → y - x < δ₁ → y - x < ε₀ →
      dist (f y) (f x) < η := by
    intro x y hx hy hxy h1 h2
    have hosc : ∀ q ∈ Icc (0 : ℝ) (y - x), |W (x + (y - x) - q) - W (x + (y - x))| ≤ ε₀ := by
      intro q hq
      have e : x + (y - x) = y := by ring
      rw [e]
      have hmem : y - q ∈ Icc (0 : ℝ) T := ⟨by linarith [hq.2, hx.1], by linarith [hq.1, hy.2]⟩
      have hd : dist (y - q) y < δ₁ := by
        rw [Real.dist_eq, show y - q - y = -q by ring, abs_neg, abs_of_nonneg hq.1]
        linarith [hq.2]
      have := hU' (y - q) hmem y hy hd
      rw [Real.dist_eq] at this
      exact this.le
    have hb := hf x (y - x) ε₀ hx.1 (by linarith) (by linarith [hy.2]) hε₀0.le hosc
    rw [show x + (y - x) = y by ring] at hb
    refine hb.trans_lt ?_
    have hpos : 0 < ε₀ + (y - x) := by linarith
    calc C * (ε₀ + (y - x)) ≤ |C| * (ε₀ + (y - x)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le
      _ ≤ C' * (ε₀ + (y - x)) := mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ < C' * (2 * ε₀) := mul_lt_mul_of_pos_left (by linarith) hC'0
      _ = η := by rw [hε₀]; field_simp
  rcases le_total a b with h | h
  · have hd : b - a = dist a b := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
    rw [dist_comm]
    exact step a b ha hb h (hd ▸ hab1) (hd ▸ hab2)
  · have hd : a - b = dist a b := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    exact step b a hb ha h (hd ▸ hab1) (hd ▸ hab2)

/-- `s ↦ ψ_s(u)` is continuous on `[0,T]` for `u ∈ ℍ`. -/
theorem continuousOn_fwdMapInv_time (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} {u : ℂ}
    (hu : u ∈ H) : ContinuousOn (fun s => fwdMapInv W s u) (Icc 0 T) := by
  have hu0 : 0 < u.im := hu
  refine continuousOn_of_flow_bound hW (C := (1 + 2 / u.im) * Real.exp (2 / u.im ^ 2 * T))
    fun s h ε hs hh hsh hε0 hε => ?_
  rw [dist_eq_norm]
  refine (norm_fwdMapInv_add_sub_le hW hW0 hs hh hε hu).trans ?_
  have hE : Real.exp (2 / u.im ^ 2 * s) ≤ Real.exp (2 / u.im ^ 2 * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have h1 : ε + 2 * h / u.im ≤ (1 + 2 / u.im) * (ε + h) := by
    have : 2 * h / u.im = 2 / u.im * h := by ring
    rw [this]; nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu0.le]
  calc (ε + 2 * h / u.im) * Real.exp (2 / u.im ^ 2 * s)
      ≤ ((1 + 2 / u.im) * (ε + h)) * Real.exp (2 / u.im ^ 2 * T) :=
        mul_le_mul h1 hE (Real.exp_pos _).le (by positivity)
    _ = (1 + 2 / u.im) * Real.exp (2 / u.im ^ 2 * T) * (ε + h) := by ring

/-- `s ↦ log ‖ψ_s'(u)‖` is continuous on `[0,T]` for `u ∈ ℍ`. -/
theorem continuousOn_log_deriv_fwdMapInv_time (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {u : ℂ} (hu : u ∈ H) :
    ContinuousOn (fun s => Real.log ‖deriv (fwdMapInv W s) u‖) (Icc 0 T) := by
  have hu0 : 0 < u.im := hu
  set K := 4 * Real.exp (2 / u.im ^ 2 * |T|) / u.im ^ 3 * |T| with hK
  have hK0 : 0 ≤ K := by positivity
  refine continuousOn_of_flow_bound hW (C := K * (1 + 2 / u.im) + 2 / u.im ^ 2)
    fun s h ε hs hh hsh hε0 hε => ?_
  rw [Real.dist_eq]
  refine (abs_log_deriv_fwdMapInv_add_sub_le hW hW0 hs hh hε hu).trans ?_
  have hsT : s ≤ |T| := (by linarith : s ≤ T).trans (le_abs_self T)
  have hE : Real.exp (2 / u.im ^ 2 * s) ≤ Real.exp (2 / u.im ^ 2 * |T|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsT (by positivity))
  have h1 : ε + 2 * h / u.im ≤ (1 + 2 / u.im) * (ε + h) := by
    have : 2 * h / u.im = 2 / u.im * h := by ring
    rw [this]; nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu0.le]
  have hA : 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 * (ε + 2 * h / u.im) * s ≤
      K * ((1 + 2 / u.im) * (ε + h)) := by
    rw [hK]
    have e1 : 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 ≤ 4 * Real.exp (2 / u.im ^ 2 * |T|) / u.im ^ 3 := by
      gcongr
    have hpos : 0 ≤ ε + 2 * h / u.im := by positivity
    calc 4 * Real.exp (2 / u.im ^ 2 * s) / u.im ^ 3 * (ε + 2 * h / u.im) * s
        ≤ 4 * Real.exp (2 / u.im ^ 2 * |T|) / u.im ^ 3 * ((1 + 2 / u.im) * (ε + h)) * |T| := by
          gcongr
      _ = _ := by ring
  have hB : 2 * h / u.im ^ 2 ≤ 2 / u.im ^ 2 * (ε + h) := by
    rw [show 2 * h / u.im ^ 2 = 2 / u.im ^ 2 * h by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc _ ≤ K * ((1 + 2 / u.im) * (ε + h)) + 2 / u.im ^ 2 * (ε + h) := add_le_add hA hB
    _ = (K * (1 + 2 / u.im) + 2 / u.im ^ 2) * (ε + h) := by ring

/-! ## The pushed circles `ν_s` -/

theorem fwdMapInv_mem_H_bound (hW : Continuous W) (hW0 : W 0 = 0) {T M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) {R : ℝ} {u : ℂ}
    (hu : u ∈ H) (huR : ‖u‖ ≤ R) :
    fwdMapInv W s u ∈ H ∧ ‖fwdMapInv W s u‖ ≤ revBound (2 * M) T R := by
  have hVc := continuous_vRev hW s
  have hVb : ∀ q ∈ Icc (0 : ℝ) s, |vRev W s q| ≤ 2 * M := fun q hq => by
    have h1 := abs_le.1 (hM (s - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have h2 := abs_le.1 (hM s ⟨hs, hsT⟩)
    show |W (s - q) - W s| ≤ 2 * M
    rw [abs_le]; constructor <;> linarith
  rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hs hu]
  exact ⟨im_revMap_pos hVc hu hs,
    (norm_revMap_le_revBound hVc hs hVb R huR).trans (revBound_mono hsT)⟩

theorem exists_abs_le_on_Icc (hW : Continuous W) (T : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hW.continuousOn
  exact ⟨M, fun t ht => by simpa [Real.norm_eq_abs] using hM t ht⟩

theorem aemeasurable_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (w : ℂ)
    {r : ℝ} (hr : 0 < r) : AEMeasurable (fwdMapInv W s) (foldedCircle w r) := by
  refine (measurable_revMap (continuous_vRev hW s) hs).aemeasurable.congr ?_
  filter_upwards [foldedCircle_ae_mem_H w hr] with u hu
  exact (fwdMapInv_eq_revMap_timeRev W hW hW0 hs hu).symm

/-- Uniform facts on `ν_s`, `s ∈ [0,T]`: probability, `1/3`-Frostman, supported in
`ℍ ∩ closedBall 0 B`. -/
theorem νT_facts (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ s ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (νT W w r s) ∧
      TwoPoint.IsFrostman (νT W w r s) (1 / 3) C ∧ ∀ᵐ z ∂νT W w r s, z ∈ H ∧ ‖z‖ ≤ B := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  refine ⟨frostC T r (‖w‖ + r), max (revBound (2 * M) T (‖w‖ + r)) 0, ?_, le_max_right _ _,
    fun s hs => ⟨?_, ?_, ?_⟩⟩
  · unfold frostC; positivity
  · exact (Measure.isProbabilityMeasure_map_iff (aemeasurable_fwdMapInv hW hW0 hs.1 w hr)).2
      inferInstance
  · exact isFrostman_fwdMapInv_foldedCircle hW hW0 hs.1 hs.2 hr le_rfl le_rfl
  · refine (ae_map_iff (aemeasurable_fwdMapInv hW hW0 hs.1 w hr)
      (show MeasurableSet {z : ℂ | z ∈ H ∧ ‖z‖ ≤ max (revBound (2 * M) T (‖w‖ + r)) 0} from
        (isOpen_H.measurableSet).inter
          (isClosed_le continuous_norm continuous_const).measurableSet)).2 ?_
    filter_upwards [foldedCircle_ae_mem_H w hr, foldedCircle_ae_norm_le w hr.le] with u hu hun
    obtain ⟨h1, h2⟩ := fwdMapInv_mem_H_bound hW hW0 hM hs.1 hs.2 hu hun
    exact ⟨h1, h2.trans (le_max_left _ _)⟩

/-- **Continuity of `s ↦ ∫ G dν_s`** for `G` measurable and continuous on `Hbar`. -/
theorem continuousOn_integral_νT (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {G : ℂ → ℝ} (hGm : Measurable G) (hGc : ContinuousOn G Hbar) :
    ContinuousOn (fun s => ∫ z, G z ∂νT W w r s) (Icc 0 T) := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set Bf := revBound (2 * M) T (‖w‖ + r)
  have hK : IsCompact (Metric.closedBall (0 : ℂ) Bf ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn (hGc.mono inter_subset_right)
  have e : EqOn (fun s => ∫ z, G z ∂νT W w r s)
      (fun s => ∫ u, G (fwdMapInv W s u) ∂foldedCircle w r) (Icc 0 T) := fun s hs => by
    simp only [νT]
    rw [integral_map (aemeasurable_fwdMapInv hW hW0 hs.1 w hr) hGm.aestronglyMeasurable]
  refine ContinuousOn.congr ?_ e
  refine continuousOn_of_dominated (bound := fun _ => Cb)
    (fun s hs => (hGm.comp_aemeasurable (aemeasurable_fwdMapInv hW hW0 hs.1 w hr)).aestronglyMeasurable)
    (fun s hs => ?_) (integrable_const Cb) ?_
  · filter_upwards [foldedCircle_ae_mem_H w hr, foldedCircle_ae_norm_le w hr.le] with u hu hun
    obtain ⟨h1, h2⟩ := fwdMapInv_mem_H_bound hW hW0 hM hs.1 hs.2 hu hun
    exact hCb _ ⟨mem_closedBall_zero_iff.2 h2, (show 0 < (fwdMapInv W s u).im from h1).le⟩
  · filter_upwards [foldedCircle_ae_mem_H w hr] with u hu
    refine hGc.comp (continuousOn_fwdMapInv_time hW hW0 hu) fun s hs => ?_
    have := fwdMapInv_eq_revMap_timeRev W hW hW0 hs.1 hu
    show 0 ≤ (fwdMapInv W s u).im
    rw [this]; exact (im_revMap_pos (continuous_vRev hW s) hu hs.1).le

/-- **The `Q`-term is continuous in time.** -/
theorem continuousOn_integral_log_deriv_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun s => ∫ u, Real.log ‖deriv (fwdMapInv W s) u‖ ∂foldedCircle w r)
      (Icc 0 T) := by
  set R := ‖w‖ + r + 1 with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg w]
  refine continuousOn_of_dominated
    (bound := fun u => Real.log (Real.sqrt (R ^ 2 + 4 * |T|)) + |Real.log u.im|)
    (fun s _ => (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable)
    (fun s hs => ?_) ((integrable_const _).add (integrable_log_im_foldedCircle w hr).abs) ?_
  · filter_upwards [foldedCircle_ae_mem_H w hr, foldedCircle_ae_abs_im_le w hr.le] with u hu hui
    rw [Real.norm_eq_abs, deriv_fwdMapInv_eq hW hW0 hs.1 hu]
    have huR : u.im ≤ R := (le_abs_self _).trans (by linarith)
    have hb := abs_log_norm_deriv_revMap_le (continuous_vRev hW s) hs.1 hu huR
    have hsq1 : 1 ≤ Real.sqrt (R ^ 2 + 4 * s) :=
      hR1.trans ((le_abs_self R).trans (Real.abs_le_sqrt (by nlinarith [hs.1])))
    have hl0 : 0 ≤ Real.log (Real.sqrt (R ^ 2 + 4 * s)) := Real.log_nonneg hsq1
    have hmono : Real.log (Real.sqrt (R ^ 2 + 4 * s)) ≤ Real.log (Real.sqrt (R ^ 2 + 4 * |T|)) :=
      Real.log_le_log (by linarith) (Real.sqrt_le_sqrt (by
        have : s ≤ |T| := hs.2.trans (le_abs_self T)
        linarith))
    rw [abs_of_nonneg hl0] at hb
    linarith
  · filter_upwards [foldedCircle_ae_mem_H w hr] with u hu
    exact continuousOn_log_deriv_fwdMapInv_time hW hW0 hu

/-! ## The logarithmic part `∫ log ‖z‖ dν_s` -/

/-- Truncating `log` at `ρ` costs `≤ 3 C ρ^{1/3}` against a `1/3`-Frostman measure. -/
theorem integral_log_max_sub_le {ν : Measure ℂ} [IsFiniteMeasure ν] {C B ρ : ℝ}
    (hF : TwoPoint.IsFrostman ν (1 / 3) C) (hν0 : ∀ᵐ z ∂ν, z ≠ 0) (hB : ∀ᵐ z ∂ν, ‖z‖ ≤ B)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun z => Real.log ‖z‖) ν ∧
      |(∫ z, Real.log (max ρ ‖z‖) ∂ν) - ∫ z, Real.log ‖z‖ ∂ν| ≤ 3 * C * ρ ^ (1 / 3 : ℝ) := by
  have hF' : IsFrostman ν (1 / 3) C := hF
  have hC : 0 ≤ C := FrostmanReg.frostman_const_nonneg hF'
  set g : ℂ → ℝ := fun z => (ENNReal.ofReal (-Real.log (‖z - 0‖ / ρ))).toReal with hg
  have hgi : Integrable g ν := FrostmanReg.integrable_logNeg_frostman hF' (by norm_num) 0 hρ
  have hLm : Measurable fun z : ℂ => Real.log (max ρ ‖z‖) :=
    Real.measurable_log.comp (measurable_const.max measurable_norm)
  have hLi : Integrable (fun z => Real.log (max ρ ‖z‖)) ν := by
    refine Integrable.of_bound hLm.aestronglyMeasurable (|Real.log ρ| + Real.log (max 1 B)) ?_
    filter_upwards [hB] with z hz
    have h1 : ρ ≤ max ρ ‖z‖ := le_max_left _ _
    have h2 : max ρ ‖z‖ ≤ max 1 B := max_le_max hρ1 hz
    have hl1 : Real.log ρ ≤ Real.log (max ρ ‖z‖) := Real.log_le_log hρ h1
    have hl2 : Real.log (max ρ ‖z‖) ≤ Real.log (max 1 B) := Real.log_le_log (hρ.trans_le h1) h2
    have hl3 : 0 ≤ Real.log (max 1 B) := Real.log_nonneg (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le (Real.log ρ), le_abs_self (Real.log ρ)]
  have hae : ∀ᵐ z ∂ν, Real.log ‖z‖ = Real.log (max ρ ‖z‖) - g z := by
    filter_upwards [hν0] with z hz
    have h := FrostmanReg.log_max_sub_log_frostman hρ (norm_pos_iff.2 hz)
    simp only [hg, sub_zero, ENNReal.toReal_ofReal']
    rw [max_comm (-Real.log (‖z‖ / ρ)) 0]
    linarith
  have hI : Integrable (fun z => Real.log ‖z‖) ν :=
    (hLi.sub hgi).congr (hae.mono fun z hz => hz.symm)
  refine ⟨hI, ?_⟩
  have e : (∫ z, Real.log (max ρ ‖z‖) ∂ν) - ∫ z, Real.log ‖z‖ ∂ν = ∫ z, g z ∂ν := by
    rw [integral_congr_ae hae, integral_sub hLi hgi]; ring
  rw [e]
  have hg0 : 0 ≤ ∫ z, g z ∂ν := integral_nonneg fun z => ENNReal.toReal_nonneg
  rw [abs_of_nonneg hg0, hg, integral_toReal (FrostmanReg.measurable_logNeg_frostman 0 ρ).aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((FrostmanReg.frostman_lintegral_logNeg_le hF' (by norm_num) 0 hρ).trans (le_of_eq ?_))
  congr 1; field_simp

theorem tendsto_rpow_radius_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k : ℕ => radius k ^ a) atTop (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto).comp
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds)
  rwa [Real.zero_rpow ha.ne'] at h

theorem radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- `∫ log max(2^{-k}, ‖z‖) dν_s → ∫ log ‖z‖ dν_s`, uniformly in `s ∈ [0,T]`. -/
theorem tendstoUniformlyOn_integral_log_νT (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) (w : ℂ)
    {r : ℝ} (hr : 0 < r) :
    TendstoUniformlyOn (fun (k : ℕ) (s : ℝ) => ∫ z, Real.log (max (radius k) ‖z‖) ∂νT W w r s)
      (fun s => ∫ z, Real.log ‖z‖ ∂νT W w r s) atTop (Icc 0 T) := by
  obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 T w hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht := (tendsto_rpow_radius_zero (a := 1 / 3) (by norm_num)).const_mul (3 * C)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with k hk s hs
  obtain ⟨hP, hF, hae⟩ := hfacts s hs
  have hb := (integral_log_max_sub_le hF (hae.mono fun z hz h => by
    subst h; simp [H] at hz) (hae.mono fun z hz => hz.2) (radius_pos k) (radius_le_one k)).2
  rw [Real.dist_eq, abs_sub_comm]
  exact hb.trans_lt hk

/-- **The logarithmic part is continuous in time.** -/
theorem continuousOn_integral_log_νT (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) (w : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun s => ∫ z, Real.log ‖z‖ ∂νT W w r s) (Icc 0 T) :=
  (tendstoUniformlyOn_integral_log_νT hW hW0 T w hr).continuousOn (Frequently.of_forall fun k =>
    continuousOn_integral_νT hW hW0 T w hr
      (Real.measurable_log.comp (measurable_const.max measurable_norm))
      ((Continuous.log (continuous_const.max continuous_norm) fun z =>
        ((radius_pos k).trans_le (le_max_left _ _)).ne').continuousOn))

/-! ## The regularized field along `ν_s` -/

/-- The regularized averages of `x` at scale `2^{-k}`, integrated against `ν_s`. -/
def PsiK (W : ℝ → ℝ) (w : ℂ) (r s : ℝ) (k : ℕ) (x : FieldSample) : ℝ :=
  ∫ z, avgReg x k z ∂νT W w r s

/-- The field has continuous regularized averages, with raw circle values converging to them
(almost sure for the free field, `FrostmanReg.ae_circleAvg_tendsto_frostman`). -/
def RegAvgGood (x : FieldSample) : Prop :=
  ∀ k : ℕ, ContinuousOn (avgReg x k) Hbar ∧ ∀ z ∈ Hbar,
    Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 (avgReg x k z))

/-- The averages `Ψ_k(s)` are uniformly Cauchy in `k` over the rational times `s ∈ [0,T]`. -/
def UCq (W : ℝ → ℝ) (w : ℂ) (r T : ℝ) (x : FieldSample) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
    |PsiK W w r q k x - PsiK W w r q k' x| ≤ 1 / ((n : ℝ) + 1)

theorem integral_log_norm_fc (d : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ v, Real.log ‖v‖ ∂foldedCircle d ρ = Real.log (max ρ ‖d‖) := by
  have h := RegClosure.integral_neg_log_fc d hρ 0
  simp only [Complex.ofReal_zero, sub_zero, integral_neg, CircleCont.circPot, map_zero] at h
  linarith

theorem avgReg_h0rev_add (κ : ℝ) {x : FieldSample} (hx : RegAvgGood x) (k : ℕ) {z : ℂ}
    (hz : z ∈ Hbar) :
    avgReg (ofFun (h0rev κ) + x) k z =
      2 / Real.sqrt κ * Real.log (max (radius k) ‖z‖) + avgReg x k z := by
  have hraw : ∀ d : ℂ, (ofFun (h0rev κ) + x) (foldedCircle d (radius k)) =
      2 / Real.sqrt κ * Real.log (max (radius k) ‖d‖) + x (foldedCircle d (radius k)) := by
    intro d
    simp only [Pi.add_apply, ofFun, h0rev]
    rw [integral_const_mul, integral_log_norm_fc d (radius_pos k)]
  unfold avgReg
  simp_rw [hraw]
  have hc : Continuous fun d : ℂ => 2 / Real.sqrt κ * Real.log (max (radius k) ‖d‖) :=
    continuous_const.mul (Continuous.log (continuous_const.max continuous_norm) fun d =>
      ((radius_pos k).trans_le (le_max_left _ _)).ne')
  exact ((hc.tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)).add ((hx k).2 z hz)
    |>.limUnder_eq

theorem Icc_subset_closure_rat {T : ℝ} (hT : 0 < T) :
    Icc (0 : ℝ) T ⊆ closure (Ioo 0 T ∩ range ((↑) : ℚ → ℝ)) := by
  rw [← closure_Ioo hT.ne]
  exact closure_minimal (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
    isClosed_closure

/-- **Continuity of the regularized field along `ν_s`.** If `x` has continuous regularized
averages and `Ψ_k` is uniformly Cauchy over rational times, then
`s ↦ evalReg (ofFun (h0rev κ) + x) ν_s` is continuous on `[0,T]`. -/
theorem continuousOn_evalReg_of_uc (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (w : ℂ) {r : ℝ} (hr : 0 < r) (κ : ℝ) {x : FieldSample} (hx : RegAvgGood x)
    (huc : UCq W w r T x) :
    ContinuousOn (fun s => evalReg (ofFun (h0rev κ) + x) (νT W w r s)) (Icc 0 T) := by
  set S := Icc (0 : ℝ) T with hS
  set Ψ : ℕ → ℝ → ℝ := fun k s => PsiK W w r s k x with hΨ
  have hΨc : ∀ k, ContinuousOn (Ψ k) S := fun k =>
    continuousOn_integral_νT hW hW0 T w hr (RegClosure.measurable_avgReg_slice x k) (hx k).1
  have hUC : ∀ n : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ s ∈ S,
      |Ψ k s - Ψ k' s| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := huc n
    refine ⟨N, fun k hk k' hk' s hs => ?_⟩
    have hcont : ContinuousOn (fun s => |Ψ k s - Ψ k' s|) S := ((hΨc k).sub (hΨc k')).abs
    refine ContinuousWithinAt.closure_le (Icc_subset_closure_rat hT hs)
      ((hcont s hs).mono (inter_subset_left.trans Ioo_subset_Icc_self)) continuousWithinAt_const ?_
    rintro y ⟨hy, q, rfl⟩
    exact hN k hk k' hk' q (Ioo_subset_Icc_self hy)
  have hUCS : UniformCauchySeqOn Ψ atTop S := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hUC n
    exact ⟨N, fun k hk k' hk' s hs => by rw [Real.dist_eq]; exact (hN k hk k' hk' s hs).trans_lt hn⟩
  set L : ℝ → ℝ := fun s => limUnder atTop fun k => Ψ k s with hL
  have hLt : ∀ s ∈ S, Tendsto (fun k => Ψ k s) atTop (𝓝 (L s)) := fun s hs =>
    (hUCS.cauchySeq hs).tendsto_limUnder
  have hLc : ContinuousOn L S :=
    (hUCS.tendstoUniformlyOn_of_tendsto hLt).continuousOn (Eventually.of_forall hΨc).frequently
  have hlogU := tendstoUniformlyOn_integral_log_νT hW hW0 T w hr
  have hHc : ContinuousOn (fun s => ∫ z, Real.log ‖z‖ ∂νT W w r s) S :=
    continuousOn_integral_log_νT hW hW0 T w hr
  have hsum : ContinuousOn (fun s => 2 / Real.sqrt κ * (∫ z, Real.log ‖z‖ ∂νT W w r s) + L s) S :=
    (continuousOn_const.mul hHc).add hLc
  refine hsum.congr fun s hs => ?_
  obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 T w hr
  obtain ⟨hP, hF, hae⟩ := hfacts s hs
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hνK : νT W w r s (Metric.closedBall (0 : ℂ) B ∩ Hbar)ᶜ = 0 := by
    have h1 : ∀ᵐ z ∂νT W w r s, z ∈ Metric.closedBall (0 : ℂ) B ∩ Hbar :=
      hae.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    exact ae_iff.1 h1
  have hint : ∀ G : ℂ → ℝ, ContinuousOn G Hbar → Integrable G (νT W w r s) := fun G hG =>
    FrostmanReg.integrable_of_continuousOn_frostman hK inter_subset_right hνK hG
  have e : ∀ k, ∫ z, avgReg (ofFun (h0rev κ) + x) k z ∂νT W w r s =
      2 / Real.sqrt κ * (∫ z, Real.log (max (radius k) ‖z‖) ∂νT W w r s) + Ψ k s := by
    intro k
    rw [integral_congr_ae (hae.mono fun z hz => avgReg_h0rev_add κ hx k ((show (0 : ℝ) < z.im from hz.1).le)),
      integral_add ((hint _ (Continuous.log (continuous_const.max continuous_norm) fun d =>
        ((radius_pos k).trans_le (le_max_left _ _)).ne').continuousOn).const_mul _)
        (hint _ (hx k).1), integral_const_mul]
    rfl
  unfold evalReg
  simp_rw [e]
  exact (((hlogU.tendsto_at hs).const_mul _).add (hLt s hs)).limUnder_eq

/-- **Continuity of the zipped field in time, deterministic form.** Under the hypotheses of
`continuousOn_evalReg_of_uc`, `s ↦ coordChange (ofFun (h0rev κ) + x) ψ_s Q (fc w r)` is
continuous on `[0,T]`. -/
theorem continuousOn_coordChange_of_uc (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (w : ℂ) {r : ℝ} (hr : 0 < r) (κ Q : ℝ) {x : FieldSample} (hx : RegAvgGood x)
    (huc : UCq W w r T x) :
    ContinuousOn (fun s => coordChange (ofFun (h0rev κ) + x) (fwdMapInv W s) Q
      (foldedCircle w r)) (Icc 0 T) :=
  (continuousOn_evalReg_of_uc hW hW0 hT w hr κ hx huc).add
    (continuousOn_const.mul (continuousOn_integral_log_deriv_fwdMapInv hW hW0 T w hr))

end RegCont
end QuantumZipper
