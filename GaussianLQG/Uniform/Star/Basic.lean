import GaussianLQG.Uniform.FieldComparison
import GaussianLQG.Uniform.Limit.Basic
import GaussianLQG.Uniform.InterfacesLFPP
import LQGMetric.Papers.DFGPS.L2_1Ratio

/-!
# Route U, step U15 (★), part 1: shared machinery

Deterministic and measure-theoretic tools for the proof of the uniform LFPP moment bounds (★)
(`blueprint/phaseB/uniform-ledger.tex`, statement U15 `star_bound`, and audit B-0b, finding M-2).

* AM–GM in `[0, ∞]`: `mul_le_sq_add_sq` (`ab ≤ a² + b²`) and `mul_rpow_le_add`
  (`(xy)^p ≤ x^{2p} + y^{2p}`).
* Exponential moments from a Gaussian tail, **without measurability** of the random variable:
  `exists_measurable_exp_majorant` produces a measurable majorant `G ≥ e^{aY}` (on `{Y < ∞}`) with
  `∫ G ≤ 2C e^{a + (a + log 2)²/(4c)}` whenever `P(Y ≥ k) ≤ C e^{-ck²}` for `k ∈ ℕ`. The majorant
  is `G = Σ_k e^{a(k+1)} 1_{E_k}`, where `E_k` is a measurable hull of `{Y ≥ k}` with the same
  measure. This replaces the AEMeasurability of `S_n = sup_V |h*_ε − φ_{0,n}|` (B-0b, M-2 (a)):
  the AM–GM split `∫(G + H) = ∫G + ∫H` only needs `G` measurable.
* `measure_eq_top_eq_zero_of_tail`: under the same tail, `Y < ∞` almost surely (B-0b, M-2 (b)).
* Internal LFPP distances: global `≤` internal (`lfppDOn_univ_le`), finiteness on a convex set
  for a continuous weight (`lfppDOn_ne_top`, B-0b, M-2 (c)), and the comparison
  `D_f(z,w) ≤ e^{|ξ|s} D_φ(z,w; Q)` when `|f − φ| ≤ s` on `Q` (`lfppDOn_univ_toReal_le`).
* Monotonicity of `holderConst` in the set and of `sepInf` in `δ`; the boxes `boxOut R` are
  compact and convex, and every compact set lies in some `boxIn R`.

All proofs are elementary (own arguments).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GaussianLQG
namespace StarBound

open LQGMetric LQGMetric.DDDF

/-! ### AM–GM in `[0, ∞]` -/

/-- `ab ≤ a² + b²` in `[0, ∞]`. -/
theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with hab | hab
  · calc a * b ≤ b * b := mul_le_mul_left hab b
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right hab a
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem rpow_sq_eq (x : ℝ≥0∞) (p : ℝ) : (x ^ p) ^ 2 = x ^ (2 * p) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- `(xy)^p ≤ x^{2p} + y^{2p}` in `[0, ∞]`, for `p ≥ 0`. -/
theorem mul_rpow_le_add (x y : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) :
    (x * y) ^ p ≤ x ^ (2 * p) + y ^ (2 * p) := by
  rw [ENNReal.mul_rpow_of_nonneg x y hp, ← rpow_sq_eq, ← rpow_sq_eq]
  exact mul_le_sq_add_sq _ _

/-- `(e^t)^{2p} = e^{2pt}` for the `ofReal` embedding. -/
theorem ofReal_exp_rpow (t : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (Real.exp t) ^ p = ENNReal.ofReal (Real.exp (p * t)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos t).le hp, ← Real.exp_mul, mul_comm]

/-! ### Exponential moments from a Gaussian tail -/

/-- The exponent bound `a(k+1) − ck² ≤ B − k log 2`, `B = a + (a + log 2)²/(4c)`. -/
theorem exp_bound_aux {a c : ℝ} (hc : 0 < c) (k : ℝ) :
    a * (k + 1) + -c * k ^ 2 ≤ (a + (a + Real.log 2) ^ 2 / (4 * c)) + -(k * Real.log 2) := by
  have key : (a + Real.log 2) * k - c * k ^ 2 ≤ (a + Real.log 2) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * c * k - (a + Real.log 2))]
  linarith

theorem exp_neg_mul_log_two (k : ℕ) : Real.exp (-((k : ℝ) * Real.log 2)) = (2⁻¹ : ℝ) ^ k := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, inv_pow]

/-- **A measurable exponential majorant from a Gaussian tail.** If `P(Y ≥ k) ≤ C e^{-ck²}` for
every `k ∈ ℕ` (outer measure; `Y` need not be measurable), then there is a measurable `G` with
`e^{aY} ≤ G` on `{Y < ∞}` and `∫ G ≤ 2C e^{a + (a + log 2)²/(4c)}`. -/
theorem exists_measurable_exp_majorant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ≥0∞) {a C c : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hc : 0 < c)
    (htail : ∀ k : ℕ, P {ω | ENNReal.ofReal k ≤ Y ω} ≤
      ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ 2))) :
    ∃ G : Ω → ℝ≥0∞, Measurable G ∧
      (∀ ω, Y ω ≠ ⊤ → ENNReal.ofReal (Real.exp (a * (Y ω).toReal)) ≤ G ω) ∧
      ∫⁻ ω, G ω ∂P ≤ ENNReal.ofReal (2 * C * Real.exp (a + (a + Real.log 2) ^ 2 / (4 * c))) := by
  set E : ℕ → Set Ω := fun k => toMeasurable P {ω | ENNReal.ofReal k ≤ Y ω} with hE
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (a * ((k : ℝ) + 1))) with hw
  have hEm : ∀ k, MeasurableSet (E k) := fun k => measurableSet_toMeasurable _ _
  refine ⟨fun ω => ∑' k, (E k).indicator (fun _ => w k) ω,
    Measurable.tsum fun k => measurable_const.indicator (hEm k), fun ω hω => ?_, ?_⟩
  · have hy0 : 0 ≤ (Y ω).toReal := ENNReal.toReal_nonneg
    have hm : ω ∈ E ⌊(Y ω).toReal⌋₊ := by
      refine subset_toMeasurable _ _ ?_
      show ENNReal.ofReal (⌊(Y ω).toReal⌋₊ : ℝ) ≤ Y ω
      exact (ENNReal.ofReal_le_ofReal (Nat.floor_le hy0)).trans_eq (ENNReal.ofReal_toReal hω)
    calc ENNReal.ofReal (Real.exp (a * (Y ω).toReal)) ≤ w ⌊(Y ω).toReal⌋₊ :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le ha))
      _ = (E ⌊(Y ω).toReal⌋₊).indicator (fun _ => w ⌊(Y ω).toReal⌋₊) ω :=
          (indicator_of_mem hm (fun _ => w ⌊(Y ω).toReal⌋₊)).symm
      _ ≤ ∑' k, (E k).indicator (fun _ => w k) ω :=
          ENNReal.le_tsum (f := fun k => (E k).indicator (fun _ => w k) ω) _
  · rw [lintegral_tsum fun k => (measurable_const.indicator (hEm k)).aemeasurable]
    simp_rw [lintegral_indicator_const (hEm _), hE, measure_toMeasurable]
    set B : ℝ := a + (a + Real.log 2) ^ 2 / (4 * c) with hB
    have hk : ∀ k : ℕ, w k * P {ω | ENNReal.ofReal k ≤ Y ω} ≤
        ENNReal.ofReal (C * Real.exp B) * 2⁻¹ ^ k := by
      intro k
      calc w k * P {ω | ENNReal.ofReal k ≤ Y ω}
          ≤ w k * ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ 2)) := mul_le_mul_right (htail k) _
        _ = ENNReal.ofReal (C * Real.exp (a * ((k : ℝ) + 1) + -c * (k : ℝ) ^ 2)) := by
            rw [hw, ← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_add]
            ring_nf
        _ ≤ ENNReal.ofReal (C * (Real.exp B * (2⁻¹ : ℝ) ^ k)) := by
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC)
            rw [← exp_neg_mul_log_two, ← Real.exp_add]
            exact Real.exp_le_exp.2 (exp_bound_aux hc k)
        _ = ENNReal.ofReal (C * Real.exp B) * 2⁻¹ ^ k := by
            rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
              ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    calc ∑' k, w k * P {ω | ENNReal.ofReal k ≤ Y ω}
        ≤ ∑' k : ℕ, ENNReal.ofReal (C * Real.exp B) * 2⁻¹ ^ k := ENNReal.tsum_le_tsum hk
      _ = ENNReal.ofReal (C * Real.exp B) * 2 := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      _ = ENNReal.ofReal (2 * C * Real.exp B) := by
          rw [mul_comm, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), mul_assoc]

/-- Under a Gaussian tail, `Y < ∞` almost surely. -/
theorem measure_eq_top_eq_zero_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ≥0∞) {C c : ℝ} (hc : 0 < c)
    (htail : ∀ k : ℕ, P {ω | ENNReal.ofReal k ≤ Y ω} ≤
      ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ 2))) :
    P {ω | Y ω = ⊤} = 0 := by
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ 2))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => -c * (k : ℝ) ^ 2) atTop atBot := by
      have : Tendsto (fun k : ℕ => c * (k : ℝ) ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop hc
          ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
      refine (tendsto_neg_atTop_atBot.comp this).congr fun k => ?_
      simp only [Function.comp_apply, neg_mul]
    have h2 : Tendsto (fun k : ℕ => C * Real.exp (-c * (k : ℝ) ^ 2)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp h1).const_mul C
      rw [mul_zero] at this
      exact this
    have h3 := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at h3
  refine le_antisymm (ge_of_tendsto' ht fun k => (measure_mono fun ω hω => ?_).trans (htail k))
    bot_le
  simp only [mem_ofPred_eq] at hω ⊢
  rw [hω]
  exact le_top

/-! ### Internal LFPP distances -/

/-- Global `≤` internal: `D_φ(z, w) ≤ D_φ(z, w; S)`. -/
theorem lfppDOn_univ_le {ξ : ℝ} {φ : ℂ → ℝ} (S : Set ℂ) (z w : ℂ) :
    LFPP.lfppDOn ξ φ univ z w ≤ LFPP.lfppDOn ξ φ S z w :=
  le_iInf fun P => iInf_le_of_le ⟨P.1, P.2.1, fun _ _ => mem_univ _⟩ le_rfl

/-- The internal distance of a continuous weight on a convex set is finite. -/
theorem lfppDOn_ne_top {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ} (hS : Convex ℝ S)
    {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) : LFPP.lfppDOn ξ φ S z w ≠ ⊤ := by
  have hK : IsCompact (Metric.closedBall z ‖w - z‖) := isCompact_closedBall z _
  obtain ⟨B, hB⟩ := (hK.image (Real.continuous_exp.comp (continuous_const.mul hφ))).bddAbove
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((LFPP.lfppDOn_le_segCost hS hz hw).trans (LFPP.segCost_le (B := B) fun x hx => ?_))
  exact hB ⟨x, hx, rfl⟩

/-- **Weight comparison through an internal distance**: if `|f − φ| ≤ s` on `Q`, with `φ`
continuous and `Q` convex, then for `z, w ∈ Q`,
`D_f(z, w) ≤ e^{|ξ| s} D_φ(z, w; Q)`, as real numbers (`toReal`). -/
theorem lfppDOn_univ_toReal_le {ξ : ℝ} {f φ : ℂ → ℝ} (hφ : Continuous φ) {Q : Set ℂ}
    (hQ : Convex ℝ Q) {s : ℝ} (hs : ∀ x ∈ Q, |f x - φ x| ≤ s) {z w : ℂ}
    (hz : z ∈ Q) (hw : w ∈ Q) :
    (LFPP.lfppDOn ξ f univ z w).toReal ≤
      Real.exp (|ξ| * s) * (LFPP.lfppDOn ξ φ Q z w).toReal := by
  have hfin := lfppDOn_ne_top (ξ := ξ) hφ hQ hz hw
  have h1 : LFPP.lfppDOn ξ f univ z w ≤
      ENNReal.ofReal (Real.exp (|ξ| * s)) * LFPP.lfppDOn ξ φ Q z w :=
    (lfppDOn_univ_le Q z w).trans (DFGPS.lfppDOn_le_of_abs_sub_le hs z w)
  calc (LFPP.lfppDOn ξ f univ z w).toReal
      ≤ (ENNReal.ofReal (Real.exp (|ξ| * s)) * LFPP.lfppDOn ξ φ Q z w).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
    _ = Real.exp (|ξ| * s) * (LFPP.lfppDOn ξ φ Q z w).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-! ### The Hölder constant and the separated infimum -/

/-- `A_d(K)` is monotone in `K`. -/
theorem holderConst_mono_set (d : ℂ × ℂ → ℝ) {K K' : Set ℂ} (hK : K ⊆ K') :
    holderConst d K ≤ holderConst d K' :=
  UniformLimit.holderConst_le fun _ hz _ hw hzw =>
    UniformLimit.ofReal_le_holderConst (hK hz) (hK hw) hzw

/-- `I_d(K, δ)` is monotone in `δ`, so `I_d(K, δ)⁻¹ ≤ I_d(K, δ')⁻¹` for `δ' ≤ δ`. -/
theorem sepInf_inv_anti (d : ℂ × ℂ → ℝ) (K : Set ℂ) {δ δ' : ℝ} (hδ : δ' ≤ δ) :
    (sepInf d K δ)⁻¹ ≤ (sepInf d K δ')⁻¹ :=
  ENNReal.inv_le_inv.2 (UniformLimit.le_sepInf fun _ hz _ hw hzw =>
    UniformLimit.sepInf_le_ofReal hz hw (hδ.trans hzw))

/-! ### Boxes -/

theorem boxOut_eq_reProdIm (R : ℝ) :
    Uniform.boxOut R = Icc (-(R + 1)) (R + 1) ×ℂ Icc (-(R + 1)) (R + 1) := by
  ext z
  simp only [Uniform.boxOut, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc, abs_le]

theorem isCompact_boxOut (R : ℝ) : IsCompact (Uniform.boxOut R) := by
  rw [boxOut_eq_reProdIm]
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

theorem convex_boxOut (R : ℝ) : Convex ℝ (Uniform.boxOut R) := by
  have e : Uniform.boxOut R =
      Complex.reLm ⁻¹' Icc (-(R + 1)) (R + 1) ∩ Complex.imLm ⁻¹' Icc (-(R + 1)) (R + 1) := by
    ext z
    simp only [Uniform.boxOut, mem_ofPred_eq, mem_inter_iff, mem_preimage, Complex.reLm_coe,
      Complex.imLm_coe, mem_Icc, abs_le]
  rw [e]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

theorem boxIn_subset_boxOut (R : ℝ) : Uniform.boxIn R ⊆ Uniform.boxOut R := fun _ hz =>
  ⟨hz.1.trans (by linarith), hz.2.trans (by linarith)⟩

/-- Every bounded set lies in some `boxIn R` with `R > 0`. -/
theorem exists_subset_boxIn {K : Set ℂ} (hK : Bornology.IsBounded K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Uniform.boxIn R := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  have hn : ‖z‖ ≤ max R 1 :=
    (mem_closedBall_zero_iff.1 (hR hz)).trans (le_max_left _ _)
  exact ⟨(Complex.abs_re_le_norm z).trans hn, (Complex.abs_im_le_norm z).trans hn⟩

end StarBound
end GaussianLQG
