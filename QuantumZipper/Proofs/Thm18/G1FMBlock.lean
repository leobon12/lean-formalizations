import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeVar
import QuantumZipper.Proofs.Thm18.G1FMKolm5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE: 5-parameter first-mode bound from Gaussian variance bounds

Task G1-FM-BLOCK5 (helper of G1-FIRSTMODE). The 5-parameter copy of the proved 4-parameter
chain `D3PlusN2FirstMode{BC,Block,Var}.lean`: an extra parameter `S` ranging over
`[1/(m+1), m+1]` is added to the rescaled coordinates, `fmParam5 n w τ s S = 2^n (Re w, Im w,
τ, s, S)`.

From the variance hypothesis `FM5VarHyp` (`V q − V q'` centred Gaussian of variance
`≤ c ‖q − q'‖`, `V q` of variance `≤ c`), we get 16th moments (`RegSample.lintegral_pow16_of_map_eq`),
then `kolm_sup_tail_N` with `d = 5`, `p = 16`, `a = 8`, `θ = 15/16`
(`32 · 2^{-8} / (15/16)^{16} < 1`, constant `5/(1-θ) + 1 = 81`) at level `l = 2^{n/2}/162`
gives block probabilities `≤ C_m 8^{-n}`, and Borel–Cantelli (`ae_eventually_notMem`) gives
`fm5_bound_of_var`. This is the dyadic chaining + Borel–Cantelli of Hu–Miller–Peres, *Thick
points of the Gaussian free field*, Ann. Probab. 38 (2010), proof of Prop. 2.1, and the
Kolmogorov–Čentsov estimate of Revuz–Yor, Ch. I, Thm (2.1); the bookkeeping is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM

open D3Plus KolmD KolmG

/-- Rescaled 5D block coordinates `2^n (Re w, Im w, τ, s, S)`. -/
def fmParam5 (n : ℕ) (w : ℂ) (τ s S : ℝ) : Fin 5 → ℝ :=
  ![(2 : ℝ) ^ n * w.re, (2 : ℝ) ^ n * w.im, (2 : ℝ) ^ n * τ, (2 : ℝ) ^ n * s, (2 : ℝ) ^ n * S]

/-- Variance hypothesis for an `S`-indexed family of functions `F ω S : ℂ × ℝ → ℝ`. -/
def FM5VarHyp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ → ℂ × ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : Fin 2,
    ∃ V : (Fin 5 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => V q ω) ∧ (∀ q, Measurable (V q)) ∧
      (∀ q ∈ boxD (d := 5) ((m + 1) * 2 ^ n + 1), ∀ q' ∈ boxD (d := 5) ((m + 1) * 2 ^ n + 1),
        ∃ v : ℝ≥0, P.map (fun ω => V q ω - V q' ω) = gaussianReal 0 v ∧ (v : ℝ) ≤ c * ‖q - q'‖) ∧
      (∀ q ∈ boxD (d := 5) ((m + 1) * 2 ^ n),
        ∃ v : ℝ≥0, P.map (V q) = gaussianReal 0 v ∧ (v : ℝ) ≤ c) ∧
      ∀ᵐ ω ∂P, ∀ w ∈ fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n),
        ∀ s ∈ Ioo 0 τ, ∀ S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1),
          fmPart k (fmInt (F ω S) w τ s) = V (fmParam5 n w τ s S) ω

/-- 5D dyadic block event. -/
def fm5BlockEvent {Ω : Type} (F : Ω → ℝ → ℂ × ℝ → ℝ) (m n : ℕ) : Set Ω :=
  {ω | ∃ w ∈ fmBox m, ∃ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∃ s ∈ Ioo 0 τ,
    ∃ S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1),
      Real.sqrt ((2 : ℝ) ^ n) < ‖fmInt (F ω S) w τ s‖}

/-- `fmBox` is monotone in `m`. -/
theorem fmBox_mono {m m' : ℕ} (h : m ≤ m') : fmBox m ⊆ fmBox m' := by
  intro z hz
  have hmm : (m : ℝ) ≤ m' := by exact_mod_cast h
  refine ⟨hz.1.trans hmm, le_trans ?_ hz.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Increment moments from increment variances. -/
theorem fm5_momentBound_of_var {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {V : (Fin d → ℝ) → Ω → ℝ} (hVm : ∀ q, Measurable (V q)) {c : ℝ} {R : ℕ}
    (hinc : ∀ q ∈ boxD (d := d) R, ∀ q' ∈ boxD (d := d) R,
      ∃ v : ℝ≥0, P.map (fun ω => V q ω - V q' ω) = gaussianReal 0 v ∧ (v : ℝ) ≤ c * ‖q - q'‖) :
    MomentBoundG V P 16 8 (c ^ 8 * gaussianAbsMoment 16) R := by
  have hg := gaussianAbsMoment_nonneg 16
  intro q hq q' hq'
  obtain ⟨v, hlaw, hv⟩ := hinc q hq q' hq'
  rw [RegSample.lintegral_pow16_of_map_eq (U := fun ω => V q ω - V q' ω)
    ((hVm q).sub (hVm q')) hlaw]
  apply ENNReal.ofReal_le_ofReal
  have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 8
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (v : ℝ) ^ 8 * gaussianAbsMoment 16 ≤ (c * ‖q - q'‖) ^ 8 * gaussianAbsMoment 16 :=
        mul_le_mul_of_nonneg_right h8 hg
    _ = c ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring

/-- Pointwise moments from pointwise variances. -/
theorem fm5_ptMoment_of_var {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hU : Measurable U) {c : ℝ} (h : ∃ v : ℝ≥0, P.map U = gaussianReal 0 v ∧ (v : ℝ) ≤ c) :
    ∫⁻ ω, ENNReal.ofReal (|U ω| ^ 16) ∂P ≤ ENNReal.ofReal (c ^ 8 * gaussianAbsMoment 16) := by
  obtain ⟨v, hlaw, hv⟩ := h
  rw [RegSample.lintegral_pow16_of_map_eq hU hlaw]
  apply ENNReal.ofReal_le_ofReal
  have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 8
  exact mul_le_mul_of_nonneg_right h8 (gaussianAbsMoment_nonneg 16)

theorem fmParam5_mem_boxD {m n : ℕ} {w : ℂ} (hw : w ∈ fmBox m) {τ s S : ℝ}
    (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) (hs : s ∈ Ioo 0 τ)
    (hS : S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)) :
    fmParam5 n w τ s S ∈ boxD (d := 5) ((m + 1) * 2 ^ n) := by
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ.1
  have hτ1 : (2 : ℝ) ^ n * τ ≤ 1 := by
    have h := hτ.2
    rw [inv_pow] at h
    calc (2 : ℝ) ^ n * τ ≤ 2 ^ n * (2 ^ n)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hx.ne'
  have hR : ((((m + 1) * 2 ^ n : ℕ)) : ℝ) = ((m : ℝ) + 1) * 2 ^ n := by push_cast; ring
  have hm : ‖w‖ ≤ m := hw.1
  have hRm : (2 : ℝ) ^ n * m ≤ ((m : ℝ) + 1) * 2 ^ n := by nlinarith
  have hR1 : (1 : ℝ) ≤ ((m : ℝ) + 1) * 2 ^ n := by
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS.1
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
  · show |(2 : ℝ) ^ n * S| ≤ _
    rw [abs_of_pos (mul_pos hx hS0)]
    nlinarith [hS.2]

/-- Final arithmetic of the 5D block bound. -/
theorem fm5_block_arith {K A x M R : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hx : 1 ≤ x) (hR0 : 0 ≤ R)
    (hR : 2 * R + 1 ≤ 3 * (M + 1) * x) :
    2 * (K / (Real.sqrt x / 162) ^ 16 * ((2 * R + 1) ^ 5 * A)) ≤
      2 * K * A * 243 * (M + 1) ^ 5 * 162 ^ 16 * (1 / x ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hs : (Real.sqrt x / 162) ^ 16 = x ^ 8 / 162 ^ 16 := by
    rw [div_pow, show (16 : ℕ) = 2 * 8 by norm_num, pow_mul, Real.sq_sqrt hx0.le]
  have hp : (2 * R + 1) ^ 5 ≤ 243 * (M + 1) ^ 5 * x ^ 5 := by
    calc (2 * R + 1) ^ 5 ≤ (3 * (M + 1) * x) ^ 5 := pow_le_pow_left₀ (by positivity) hR 5
      _ = 243 * (M + 1) ^ 5 * x ^ 5 := by ring
  rw [hs]
  have e1 : 2 * (K / (x ^ 8 / 162 ^ 16) * ((2 * R + 1) ^ 5 * A)) =
      2 * K * 162 ^ 16 * A * (2 * R + 1) ^ 5 / x ^ 8 := by
    field_simp
  have e2 : 2 * K * A * 243 * (M + 1) ^ 5 * 162 ^ 16 * (1 / x ^ 3) =
      2 * K * 162 ^ 16 * A * (243 * (M + 1) ^ 5 * x ^ 5) / x ^ 8 := by
    field_simp
  rw [e1, e2]
  gcongr

/-- **Summable block tails** from the variance hypothesis. -/
theorem fm5_block_summable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Ω → ℝ → ℂ × ℝ → ℝ} (h : FM5VarHyp P F) (m : ℕ) :
    ∑' n, P (fm5BlockEvent F m n) ≠ ∞ := by
  obtain ⟨c, hc, n₀, hn⟩ := h m
  set K : ℝ := c ^ 8 * gaussianAbsMoment 16 with hKdef
  have hK : 0 ≤ K := by have := gaussianAbsMoment_nonneg 16; positivity
  set ρ : ℝ := (2 : ℝ) ^ 5 * ((1 / 2 : ℝ) ^ (8 : ℝ) / (15 / 16 : ℝ) ^ 16) with hρdef
  have hρ : ρ < 1 := by
    rw [hρdef, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1ρ : 0 < 1 - ρ := by linarith
  set A : ℝ := 1 + 5 / (1 - ρ) with hAdef
  have hA : 0 ≤ A := by positivity
  set C₁ : ℝ := 2 * K * A * 243 * ((m : ℝ) + 1) ^ 5 * 162 ^ 16 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have key : ∀ n ≥ n₀, P (fm5BlockEvent F m n) ≤ ENNReal.ofReal (C₁ * (1 / 8) ^ n) := by
    intro n hn₀
    choose V hVc hVm hinc hpt hVae using hn n hn₀
    set R : ℕ := (m + 1) * 2 ^ n with hRdef
    have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    set l : ℝ := Real.sqrt ((2 : ℝ) ^ n) / 162 with hl
    have hl0 : 0 < l := by positivity
    have hc81 : ((5 : ℕ) : ℝ) / (1 - 15 / 16) + 1 = 81 := by norm_num
    set T : Fin 2 → Set Ω := fun k =>
      {ω | ∃ q ∈ boxD (d := 5) R, (((5 : ℕ) : ℝ) / (1 - 15 / 16) + 1) * l < |V k q ω|} with hT
    have hTb : ∀ k, P (T k) ≤ ENNReal.ofReal (K / l ^ 16 * ((2 * R + 1) ^ 5 +
        (5 : ℕ) * (2 * R + 1) ^ 5 / (1 - ρ))) := fun k =>
      kolm_sup_tail_N (d := 5) (by norm_num : (0 : ℝ) < 15 / 16) (by norm_num) (hVc k)
        (fun q => (hVm k q).aemeasurable) (by norm_num) hK hρ
        (fm5_momentBound_of_var (hVm k) (hinc k))
        (fun q hq => fm5_ptMoment_of_var (hVm k q) (hpt k q hq)) hl0
    set N : Set Ω := {ω | ¬ ∀ k : Fin 2, ∀ w ∈ fmBox m,
      ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∀ s ∈ Ioo 0 τ,
        ∀ S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1),
          fmPart k (fmInt (F ω S) w τ s) = V k (fmParam5 n w τ s S) ω} with hN
    have hN0 : P N = 0 := ae_iff.1 (ae_all_iff.2 hVae)
    have hsub : fm5BlockEvent F m n ⊆ N ∪ (T 0 ∪ T 1) := by
      intro ω hω
      by_contra hc'
      simp only [mem_union, not_or] at hc'
      obtain ⟨hNω, hT0, hT1⟩ := hc'
      simp only [hN, mem_ofPred_eq, not_not] at hNω
      obtain ⟨w, hw, τ, hτ, s, hs, S, hS, hbig⟩ := hω
      have hq := fmParam5_mem_boxD hw hτ hs hS
      have hsmall : ∀ k, |V k (fmParam5 n w τ s S) ω| ≤ Real.sqrt ((2 : ℝ) ^ n) / 2 := by
        intro k
        by_contra hk
        push Not at hk
        have hmem : ω ∈ T k := ⟨_, hq, by rw [hc81, hl]; linarith⟩
        fin_cases k
        · exact hT0 hmem
        · exact hT1 hmem
      have h0 : (fmInt (F ω S) w τ s).re = V 0 (fmParam5 n w τ s S) ω := by
        simpa [fmPart] using hNω 0 w hw τ hτ s hs S hS
      have h1 : (fmInt (F ω S) w τ s).im = V 1 (fmParam5 n w τ s S) ω := by
        simpa [fmPart] using hNω 1 w hw τ hτ s hs S hS
      have hn := Complex.norm_le_abs_re_add_abs_im (fmInt (F ω S) w τ s)
      rw [h0, h1] at hn
      linarith [hsmall 0, hsmall 1]
    have hR' : 2 * (R : ℝ) + 1 ≤ 3 * ((m : ℝ) + 1) * 2 ^ n := by
      rw [hRdef]; push_cast; nlinarith
    calc P (fm5BlockEvent F m n) ≤ P (N ∪ (T 0 ∪ T 1)) := measure_mono hsub
      _ ≤ P N + (P (T 0) + P (T 1)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (K / l ^ 16 * ((2 * R + 1) ^ 5 +
            (5 : ℕ) * (2 * R + 1) ^ 5 / (1 - ρ))) + ENNReal.ofReal (K / l ^ 16 *
            ((2 * R + 1) ^ 5 + (5 : ℕ) * (2 * R + 1) ^ 5 / (1 - ρ)))) := by
          rw [hN0]; exact add_le_add le_rfl (add_le_add (hTb 0) (hTb 1))
      _ = ENNReal.ofReal (2 * (K / l ^ 16 * ((2 * R + 1) ^ 5 * A))) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hAdef]; push_cast; ring
      _ ≤ ENNReal.ofReal (C₁ * (1 / 8) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have e : (1 / 8 : ℝ) ^ n = 1 / ((2 : ℝ) ^ n) ^ 3 := by
            rw [← pow_mul, one_div_pow, mul_comm, pow_mul]; norm_num
          rw [e, hC₁, hl]
          exact fm5_block_arith hK hA hx1 (Nat.cast_nonneg _) hR'
  have key' : ∀ n, P (fm5BlockEvent F m n) ≤
      ENNReal.ofReal ((C₁ + 8 ^ n₀) * (1 / 8) ^ n) := by
    intro n
    by_cases hn₀ : n₀ ≤ n
    · refine (key n hn₀).trans (ENNReal.ofReal_le_ofReal ?_)
      have : (0 : ℝ) ≤ 8 ^ n₀ * (1 / 8) ^ n := by positivity
      nlinarith
    · push Not at hn₀
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1 : ℝ) ≤ 8 ^ n₀ * (1 / 8) ^ n := by
        rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ (by norm_num) hn₀.le
      have : (0 : ℝ) ≤ C₁ * (1 / 8) ^ n := by positivity
      nlinarith
  exact ne_top_of_le_ne_top
    (CircleCont.tsum_geom_ne_top (by positivity) (by norm_num) (by norm_num))
    (ENNReal.tsum_le_tsum key')

/-- **5D first-mode bound from the variance hypothesis.** -/
theorem fm5_bound_of_var {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ → ℂ × ℝ → ℝ} (h : FM5VarHyp P F) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ N : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ, ∀ S ∈ Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1),
        ‖fmInt (F ω S) w τ s‖ ≤ C / Real.sqrt τ := by
  have hev : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ᶠ n in atTop, ω ∉ fm5BlockEvent F m n :=
    ae_all_iff.2 fun m => ae_eventually_notMem (fm5_block_summable h m)
  filter_upwards [hev] with ω hω K hK hKH N
  obtain ⟨m₀, hm₀⟩ := exists_subset_fmBox hK hKH
  set m : ℕ := max m₀ N with hmdef
  have hm : K ⊆ fmBox m := hm₀.trans (fmBox_mono (le_max_left _ _))
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast le_max_right m₀ N
  obtain ⟨N', hN'⟩ := (hω m).exists_forall_of_atTop
  refine ⟨1, (2 : ℝ)⁻¹ ^ N', by positivity, fun w hw τ hτ s hs S hS => ?_⟩
  obtain ⟨n, hnN, hτn⟩ := exists_block_of_lt hτ.1 hτ.2
  have hnot := hN' n hnN
  simp only [fm5BlockEvent, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
  have hSm : S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) :=
    ⟨le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hS.1,
      hS.2.trans (by linarith)⟩
  have hle := hnot w (hm hw) τ hτn s hs S hSm
  exact hle.trans (sqrt_two_pow_le_of_block hτn)

end G1FM
end Thm18Asm
end QuantumZipper
