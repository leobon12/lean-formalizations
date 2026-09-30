import QuantumZipper.Proofs.Thm18.G1FMBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE: first-mode bound with a Hölder-`1/3` time parameter

Task CFGFM-BLOCKH (helper of CFG-FIRSTMODE). A variant of the 5D chain
`Thm18/G1FMBlock.lean` in which the fifth parameter is a time `t ∈ [0, T]` along which the
increment variances are only Hölder of order `1/3`: `var (V q − V q') ≤ c ‖q − q'‖^{1/3}`.
The time coordinate is rescaled by `2^{3n}` (`fmParamH`), so that the lattice box has side
`R = (m+1) 2^{3n}`.

Constants: moments `p = 60` (`E|N(0,v)|^{60} = v^{30} E|N(0,1)|^{60}`,
`KolmG.lintegral_pow_two_mul_of_map_eq`), Hölder exponent `a = 10`, `d = 5`, `θ = 19/20`
(`32 · 2^{-10} / (19/20)^{60} < 1`), chaining constant `5/(1-θ) + 1 = 101`, level
`l = 2^{n/2}/202`. The block probability is `≲ (m+1)^5 2^{15n} · 2^{-30n}`, summable, and
Borel–Cantelli gives `fmH_bound_of_var`.

Sources: dyadic chaining + Borel–Cantelli as in Hu–Miller–Peres, *Thick points of the Gaussian
free field*, Ann. Probab. 38 (2010), proof of Prop. 2.1; the quantitative Kolmogorov–Čentsov
estimate of Revuz–Yor, *Continuous Martingales and Brownian Motion*, Ch. I, Thm (2.1)
(`kolm_sup_tail_N`); the bookkeeping is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace E6
namespace CfgFM

open D3Plus KolmD KolmG
open Thm18Asm.G1FM (kolm_sup_tail_N fmBox_mono)

/-- Rescaled block coordinates with the fifth (time) coordinate rescaled by `2^{3n}`. -/
def fmParamH (n : ℕ) (w : ℂ) (τ s t : ℝ) : Fin 5 → ℝ :=
  ![(2 : ℝ) ^ n * w.re, (2 : ℝ) ^ n * w.im, (2 : ℝ) ^ n * τ, (2 : ℝ) ^ n * s,
    (2 : ℝ) ^ (3 * n) * t]

/-- Variance hypothesis: increments Hölder-`1/3` in variance on the rescaled box. -/
def FMHVarHyp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (T : ℝ)
    (F : Ω → ℝ → ℂ × ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : Fin 2,
    ∃ V : (Fin 5 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => V q ω) ∧ (∀ q, Measurable (V q)) ∧
      (∀ q ∈ boxD (d := 5) ((m + 1) * 2 ^ (3 * n) + 1),
        ∀ q' ∈ boxD (d := 5) ((m + 1) * 2 ^ (3 * n) + 1),
        ∃ v : ℝ≥0, P.map (fun ω => V q ω - V q' ω) = gaussianReal 0 v ∧
          (v : ℝ) ≤ c * ‖q - q'‖ ^ ((1 : ℝ) / 3)) ∧
      (∀ q ∈ boxD (d := 5) ((m + 1) * 2 ^ (3 * n)),
        ∃ v : ℝ≥0, P.map (V q) = gaussianReal 0 v ∧ (v : ℝ) ≤ c) ∧
      ∀ᵐ ω ∂P, ∀ w ∈ D3Plus.fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n),
        ∀ s ∈ Ioo 0 τ, ∀ t ∈ Icc (0 : ℝ) T,
          D3Plus.fmPart k (D3Plus.fmInt (F ω t) w τ s) = V (fmParamH n w τ s t) ω

/-- Dyadic block event (time-indexed). -/
def fmHBlockEvent {Ω : Type} (F : Ω → ℝ → ℂ × ℝ → ℝ) (T : ℝ) (m n : ℕ) : Set Ω :=
  {ω | ∃ w ∈ D3Plus.fmBox m, ∃ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∃ s ∈ Ioo 0 τ,
    ∃ t ∈ Icc (0 : ℝ) T, Real.sqrt ((2 : ℝ) ^ n) < ‖D3Plus.fmInt (F ω t) w τ s‖}

theorem fmHBlockEvent_mono {Ω : Type} {F : Ω → ℝ → ℂ × ℝ → ℝ} {T : ℝ} {m m' : ℕ}
    (hmm : m ≤ m') (n : ℕ) : fmHBlockEvent F T m n ⊆ fmHBlockEvent F T m' n := by
  rintro ω ⟨w, hw, τ, hτ, s, hs, t, ht, hb⟩
  exact ⟨w, fmBox_mono hmm hw, τ, hτ, s, hs, t, ht, hb⟩

/-- 60th increment moments from Hölder-`1/3` increment variances. -/
theorem fmH_momentBound_of_var {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {V : (Fin d → ℝ) → Ω → ℝ} (hVm : ∀ q, Measurable (V q)) {c : ℝ} {R : ℕ}
    (hinc : ∀ q ∈ boxD (d := d) R, ∀ q' ∈ boxD (d := d) R,
      ∃ v : ℝ≥0, P.map (fun ω => V q ω - V q' ω) = gaussianReal 0 v ∧
        (v : ℝ) ≤ c * ‖q - q'‖ ^ ((1 : ℝ) / 3)) :
    MomentBoundG V P 60 10 (c ^ 30 * gaussianAbsMoment 60) R := by
  have hg := gaussianAbsMoment_nonneg 60
  intro q hq q' hq'
  obtain ⟨v, hlaw, hv⟩ := hinc q hq q' hq'
  have e := KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
    (U := fun ω => V q ω - V q' ω) ((hVm q).sub (hVm q')) 30 hlaw
  rw [show 2 * 30 = 60 from rfl] at e
  rw [e]
  apply ENNReal.ofReal_le_ofReal
  have h30 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 30
  have hr : (‖q - q'‖ ^ ((1 : ℝ) / 3)) ^ 30 = ‖q - q'‖ ^ (10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
  calc (v : ℝ) ^ 30 * gaussianAbsMoment 60
      ≤ (c * ‖q - q'‖ ^ ((1 : ℝ) / 3)) ^ 30 * gaussianAbsMoment 60 :=
        mul_le_mul_of_nonneg_right h30 hg
    _ = c ^ 30 * gaussianAbsMoment 60 * ‖q - q'‖ ^ (10 : ℝ) := by rw [mul_pow, hr]; ring

/-- Pointwise 60th moments from pointwise variances. -/
theorem fmH_ptMoment_of_var {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) {c : ℝ} (h : ∃ v : ℝ≥0, P.map U = gaussianReal 0 v ∧ (v : ℝ) ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ 60) ∂P ≤ ENNReal.ofReal (c ^ 30 * gaussianAbsMoment 60) := by
  obtain ⟨v, hlaw, hv⟩ := h
  have e := KolmG.lintegral_pow_two_mul_of_map_eq (P := P) hU 30 hlaw
  rw [show 2 * 30 = 60 from rfl] at e
  rw [e]
  apply ENNReal.ofReal_le_ofReal
  have h30 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 30
  exact mul_le_mul_of_nonneg_right h30 (gaussianAbsMoment_nonneg 60)

theorem fmParamH_mem_boxD {m n : ℕ} {T : ℝ} (hTm : T ≤ (m : ℝ) + 1) {w : ℂ} (hw : w ∈ fmBox m)
    {τ s t : ℝ} (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) (hs : s ∈ Ioo 0 τ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    fmParamH n w τ s t ∈ boxD (d := 5) ((m + 1) * 2 ^ (3 * n)) := by
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  have hY : (0 : ℝ) < 2 ^ (3 * n) := by positivity
  have hxY : (2 : ℝ) ^ n ≤ 2 ^ (3 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hY1 : (1 : ℝ) ≤ 2 ^ (3 * n) := one_le_pow₀ (by norm_num)
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ.1
  have hτ1 : (2 : ℝ) ^ n * τ ≤ 1 := by
    have h := hτ.2
    rw [inv_pow] at h
    calc (2 : ℝ) ^ n * τ ≤ 2 ^ n * (2 ^ n)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hx.ne'
  have hR : ((((m + 1) * 2 ^ (3 * n) : ℕ)) : ℝ) = ((m : ℝ) + 1) * 2 ^ (3 * n) := by
    push_cast; ring
  have hm : ‖w‖ ≤ m := hw.1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hRm : (2 : ℝ) ^ n * m ≤ ((m : ℝ) + 1) * 2 ^ (3 * n) := by
    nlinarith [mul_le_mul_of_nonneg_right hxY hm0]
  have hR1 : (1 : ℝ) ≤ ((m : ℝ) + 1) * 2 ^ (3 * n) := by nlinarith
  intro i
  rw [hR]
  fin_cases i
  · show |(2 : ℝ) ^ n * w.re| ≤ _
    rw [abs_mul, abs_of_pos hx]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm w).trans hm) hx.le).trans hRm
  · show |(2 : ℝ) ^ n * w.im| ≤ _
    rw [abs_mul, abs_of_pos hx]
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm w).trans hm) hx.le).trans hRm
  · show |(2 : ℝ) ^ n * τ| ≤ _
    rw [abs_of_pos (mul_pos hx hτ0)]; linarith
  · show |(2 : ℝ) ^ n * s| ≤ _
    rw [abs_of_pos (mul_pos hx hs.1)]
    nlinarith [hs.2]
  · show |(2 : ℝ) ^ (3 * n) * t| ≤ _
    rw [abs_of_nonneg (mul_nonneg hY.le ht.1)]
    have := mul_le_mul_of_nonneg_left (ht.2.trans hTm) hY.le
    linarith

/-- Final arithmetic of the block bound. -/
theorem fmH_block_arith {K A x M R L : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hx : 1 ≤ x) (hL : 0 < L)
    (hR0 : 0 ≤ R) (hR : 2 * R + 1 ≤ 3 * (M + 1) * x ^ 3) :
    2 * (K / (Real.sqrt x / L) ^ 60 * ((2 * R + 1) ^ 5 * A)) ≤
      2 * K * A * 243 * (M + 1) ^ 5 * L ^ 60 * (1 / x ^ 15) := by
  have hx0 : 0 < x := by linarith
  have hs : (Real.sqrt x / L) ^ 60 = x ^ 30 / L ^ 60 := by
    rw [div_pow, show (60 : ℕ) = 2 * 30 by norm_num, pow_mul, Real.sq_sqrt hx0.le]
  have hp : (2 * R + 1) ^ 5 ≤ 243 * (M + 1) ^ 5 * x ^ 15 := by
    calc (2 * R + 1) ^ 5 ≤ (3 * (M + 1) * x ^ 3) ^ 5 := pow_le_pow_left₀ (by positivity) hR 5
      _ = 243 * (M + 1) ^ 5 * x ^ 15 := by ring
  rw [hs]
  have e1 : 2 * (K / (x ^ 30 / L ^ 60) * ((2 * R + 1) ^ 5 * A)) =
      2 * K * L ^ 60 * A * (2 * R + 1) ^ 5 / x ^ 30 := by
    field_simp
  have e2 : 2 * K * A * 243 * (M + 1) ^ 5 * L ^ 60 * (1 / x ^ 15) =
      2 * K * L ^ 60 * A * (243 * (M + 1) ^ 5 * x ^ 15) / x ^ 30 := by
    field_simp
  rw [e1, e2]
  gcongr

/-- Summable block tails when the time range is inside the box (`T ≤ m + 1`). -/
theorem fmH_block_summable_of_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : ℝ} {F : Ω → ℝ → ℂ × ℝ → ℝ} (h : FMHVarHyp P T F) {m : ℕ}
    (hTm : T ≤ (m : ℝ) + 1) :
    ∑' n, P (fmHBlockEvent F T m n) ≠ ∞ := by
  obtain ⟨c, hc, n₀, hn⟩ := h m
  set K : ℝ := c ^ 30 * gaussianAbsMoment 60 with hKdef
  have hK : 0 ≤ K := by have := gaussianAbsMoment_nonneg 60; positivity
  set ρ : ℝ := (2 : ℝ) ^ 5 * ((1 / 2 : ℝ) ^ (10 : ℝ) / (19 / 20 : ℝ) ^ 60) with hρdef
  have hρ : ρ < 1 := by
    rw [hρdef, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1ρ : 0 < 1 - ρ := by linarith
  set A : ℝ := 1 + 5 / (1 - ρ) with hAdef
  have hA : 0 ≤ A := by positivity
  set L : ℝ := 202 with hLdef
  have hL : (0 : ℝ) < L := by norm_num
  set r : ℝ := (2 : ℝ) ^ 15 with hrdef
  have hr1 : (1 : ℝ) ≤ r := by norm_num
  set C₁ : ℝ := 2 * K * A * 243 * ((m : ℝ) + 1) ^ 5 * L ^ 60 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have key : ∀ n ≥ n₀, P (fmHBlockEvent F T m n) ≤ ENNReal.ofReal (C₁ * (1 / r) ^ n) := by
    intro n hn₀
    choose V hVc hVm hinc hpt hVae using hn n hn₀
    set R : ℕ := (m + 1) * 2 ^ (3 * n) with hRdef
    have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    set l : ℝ := Real.sqrt ((2 : ℝ) ^ n) / L with hl
    have hl0 : 0 < l := by positivity
    have hc101 : ((5 : ℕ) : ℝ) / (1 - 19 / 20) + 1 = 101 := by norm_num
    set S : Fin 2 → Set Ω := fun k =>
      {ω | ∃ q ∈ boxD (d := 5) R, (((5 : ℕ) : ℝ) / (1 - 19 / 20) + 1) * l < |V k q ω|}
      with hS
    have hSb : ∀ k, P (S k) ≤ ENNReal.ofReal (K / l ^ 60 * ((2 * R + 1) ^ 5 +
        (5 : ℕ) * (2 * R + 1) ^ 5 / (1 - ρ))) := fun k =>
      kolm_sup_tail_N (d := 5) (by norm_num : (0 : ℝ) < 19 / 20) (by norm_num) (hVc k)
        (fun q => (hVm k q).aemeasurable) (by norm_num) hK hρ
        (fmH_momentBound_of_var (hVm k) (hinc k))
        (fun q hq => fmH_ptMoment_of_var (hVm k q) (hpt k q hq)) hl0
    set N : Set Ω := {ω | ¬ ∀ k : Fin 2, ∀ w ∈ fmBox m,
      ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∀ s ∈ Ioo 0 τ,
        ∀ t ∈ Icc (0 : ℝ) T,
          fmPart k (fmInt (F ω t) w τ s) = V k (fmParamH n w τ s t) ω} with hN
    have hN0 : P N = 0 := ae_iff.1 (ae_all_iff.2 hVae)
    have hsub : fmHBlockEvent F T m n ⊆ N ∪ (S 0 ∪ S 1) := by
      intro ω hω
      by_contra hc'
      simp only [mem_union, not_or] at hc'
      obtain ⟨hNω, hS0, hS1⟩ := hc'
      simp only [hN, mem_ofPred_eq, not_not] at hNω
      obtain ⟨w, hw, τ, hτ, s, hs, t, ht, hbig⟩ := hω
      have hq := fmParamH_mem_boxD hTm hw hτ hs ht
      have hsmall : ∀ k, |V k (fmParamH n w τ s t) ω| ≤ Real.sqrt ((2 : ℝ) ^ n) / 2 := by
        intro k
        by_contra hk
        push Not at hk
        have hLl : 101 * l = Real.sqrt ((2 : ℝ) ^ n) / 2 := by
          rw [hl, hLdef]; ring
        have hmem : ω ∈ S k := ⟨_, hq, by rw [hc101, hLl]; exact hk⟩
        fin_cases k
        · exact hS0 hmem
        · exact hS1 hmem
      have h0 : (fmInt (F ω t) w τ s).re = V 0 (fmParamH n w τ s t) ω := by
        simpa [fmPart] using hNω 0 w hw τ hτ s hs t ht
      have h1 : (fmInt (F ω t) w τ s).im = V 1 (fmParamH n w τ s t) ω := by
        simpa [fmPart] using hNω 1 w hw τ hτ s hs t ht
      have hn := Complex.norm_le_abs_re_add_abs_im (fmInt (F ω t) w τ s)
      rw [h0, h1] at hn
      linarith [hsmall 0, hsmall 1]
    have hRc : ((R : ℕ) : ℝ) = ((m : ℝ) + 1) * ((2 : ℝ) ^ n) ^ 3 := by
      rw [hRdef]; push_cast; rw [← pow_mul, mul_comm n 3]
    have hR' : 2 * (R : ℝ) + 1 ≤ 3 * ((m : ℝ) + 1) * ((2 : ℝ) ^ n) ^ 3 := by
      have hy3 : (1 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 3 := one_le_pow₀ hx1
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [hRc]; nlinarith
    calc P (fmHBlockEvent F T m n) ≤ P (N ∪ (S 0 ∪ S 1)) := measure_mono hsub
      _ ≤ P N + (P (S 0) + P (S 1)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (K / l ^ 60 * ((2 * R + 1) ^ 5 +
            (5 : ℕ) * (2 * R + 1) ^ 5 / (1 - ρ))) + ENNReal.ofReal (K / l ^ 60 *
            ((2 * R + 1) ^ 5 + (5 : ℕ) * (2 * R + 1) ^ 5 / (1 - ρ)))) := by
          rw [hN0]; exact add_le_add le_rfl (add_le_add (hSb 0) (hSb 1))
      _ = ENNReal.ofReal (2 * (K / l ^ 60 * ((2 * R + 1) ^ 5 * A))) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hAdef]; push_cast; ring
      _ ≤ ENNReal.ofReal (C₁ * (1 / r) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have e : (1 / r) ^ n = 1 / ((2 : ℝ) ^ n) ^ 15 := by
            rw [hrdef, one_div_pow, ← pow_mul, ← pow_mul, mul_comm]
          rw [e, hC₁, hl]
          exact fmH_block_arith hK hA hx1 hL (Nat.cast_nonneg _) hR'
  have key' : ∀ n, P (fmHBlockEvent F T m n) ≤
      ENNReal.ofReal ((C₁ + r ^ n₀) * (1 / r) ^ n) := by
    intro n
    by_cases hn₀ : n₀ ≤ n
    · refine (key n hn₀).trans (ENNReal.ofReal_le_ofReal ?_)
      have : (0 : ℝ) ≤ r ^ n₀ * (1 / r) ^ n := by positivity
      nlinarith
    · push Not at hn₀
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1 : ℝ) ≤ r ^ n₀ * (1 / r) ^ n := by
        rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ hr1 hn₀.le
      have : (0 : ℝ) ≤ C₁ * (1 / r) ^ n := by positivity
      nlinarith
  exact ne_top_of_le_ne_top
    (CircleCont.tsum_geom_ne_top (by positivity) (by positivity)
      (by rw [hrdef]; norm_num))
    (ENNReal.tsum_le_tsum key')

/-- **Summable block tails** from the variance hypothesis. -/
theorem fmH_block_summable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} {F : Ω → ℝ → ℂ × ℝ → ℝ} (h : FMHVarHyp P T F) (m : ℕ) :
    ∑' n, P (fmHBlockEvent F T m n) ≠ ∞ := by
  set m' : ℕ := max m ⌈T⌉₊ with hm'
  have hTm : T ≤ (m' : ℝ) + 1 := by
    have h1 := Nat.le_ceil T
    have h2 : ((⌈T⌉₊ : ℕ) : ℝ) ≤ m' := by exact_mod_cast le_max_right m ⌈T⌉₊
    linarith
  exact ne_top_of_le_ne_top (fmH_block_summable_of_le h hTm)
    (ENNReal.tsum_le_tsum fun n => measure_mono (fmHBlockEvent_mono (le_max_left _ _) n))

/-- Deterministic step: eventually leaving every block family gives the bound. -/
theorem fmH_bound_of_eventually {Ω : Type} {T : ℝ} {F : Ω → ℝ → ℂ × ℝ → ℝ} {ω : Ω}
    (h : ∀ m : ℕ, ∀ᶠ n in atTop, ω ∉ fmHBlockEvent F T m n) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ, ∀ t ∈ Icc (0 : ℝ) T,
        ‖D3Plus.fmInt (F ω t) w τ s‖ ≤ C / Real.sqrt τ := by
  intro K hK hKH
  obtain ⟨m, hm⟩ := exists_subset_fmBox hK hKH
  obtain ⟨N', hN'⟩ := (h m).exists_forall_of_atTop
  refine ⟨1, (2 : ℝ)⁻¹ ^ N', by positivity, fun w hw τ hτ s hs t ht => ?_⟩
  obtain ⟨n, hnN, hτn⟩ := exists_block_of_lt hτ.1 hτ.2
  have hnot := hN' n hnN
  simp only [fmHBlockEvent, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
  exact (hnot w (hm hw) τ hτn s hs t ht).trans (sqrt_two_pow_le_of_block hτn)

end CfgFM
end E6
end QuantumZipper
