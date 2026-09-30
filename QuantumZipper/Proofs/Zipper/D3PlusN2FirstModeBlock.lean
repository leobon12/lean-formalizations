import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeBC
import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FIRSTMODE, step 3: block tails from rescaled moment bounds

Task N2Z-FIRSTMODE. We reduce the block-tail node `N2ZFirstModeBlockStmt`
(`D3PlusN2FirstModeBC.lean`) to the **moment node** `N2ZFirstModeMomStmt`: for every box
`fmBox m` there are `K` and `n₀` such that for each block `n ≥ n₀` the real and imaginary parts of
the first mode, in the rescaled coordinates `q = 2^n (Re w, Im w, τ, s)`, agree a.s. (on the
block) with continuous processes `V` on the box `[-R, R]^4`, `R = (m+1) 2^n`, satisfying
`E|V q − V q'|^16 ≤ K ‖q − q'‖^8` and `E|V q|^16 ≤ K` (constants independent of `n`: this is the
scale invariance of the log-kernel after the first mode kills the constant).

Proof (`n2ZFirstModeBlock_of_mom`): `kolm_sup_tail` with `d = 4`, `θ = 7/8`, `p = 16`, `a = 8`
at level `l = 2^{n/2}/66` gives `P(E_{m,n}) ≤ C_m 16^{-n}`, summable. This is the dyadic-scale
chaining + Borel–Cantelli of Hu–Miller–Peres, *Thick points of the Gaussian free field*,
Ann. Probab. 38 (2010), proof of Prop. 2.1; the bookkeeping is own.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real ENNReal

namespace QuantumZipper
namespace D3Plus

open KolmD KolmG

/-- Real (`k = 0`) or imaginary (`k = 1`) part. -/
def fmPart (k : Fin 2) (z : ℂ) : ℝ := if k = 0 then z.re else z.im

/-- Rescaled block coordinates `2^n (Re w, Im w, τ, s)`. -/
def fmParam (n : ℕ) (w : ℂ) (τ s : ℝ) : Fin 4 → ℝ :=
  ![(2 : ℝ) ^ n * w.re, (2 : ℝ) ^ n * w.im, (2 : ℝ) ^ n * τ, (2 : ℝ) ^ n * s]

/-- **Node N2Z-FIRSTMODE-MOM** (rescaled moment bounds for the first mode). -/
def N2ZFirstModeMomStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : Fin 2,
        ∃ V : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => V q ω) ∧
          (∀ q, AEMeasurable (V q) P) ∧
          MomentBoundG V P 16 8 K ((m + 1) * 2 ^ n + 1) ∧
          (∀ q ∈ boxD (d := 4) ((m + 1) * 2 ^ n),
            ∫⁻ ω, ENNReal.ofReal (|V q ω| ^ 16) ∂P ≤ ENNReal.ofReal K) ∧
          ∀ᵐ ω ∂P, ∀ w ∈ fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n),
            ∀ s ∈ Ioo 0 τ, fmPart k (fmInt (G ω) w τ s) = V (fmParam n w τ s) ω

theorem fmParam_mem_boxD {m n : ℕ} {w : ℂ} (hw : w ∈ fmBox m) {τ s : ℝ}
    (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) (hs : s ∈ Ioo 0 τ) :
    fmParam n w τ s ∈ boxD (d := 4) ((m + 1) * 2 ^ n) := by
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

/-- Final arithmetic of the block bound. -/
theorem fm_block_arith {K A x M R : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hx : 1 ≤ x) (hR0 : 0 ≤ R)
    (hR : 2 * R + 1 ≤ 3 * (M + 1) * x) :
    2 * (K / (Real.sqrt x / 66) ^ 16 * ((2 * R + 1) ^ 4 * A)) ≤
      2 * K * A * 81 * (M + 1) ^ 4 * 66 ^ 16 * (1 / x ^ 4) := by
  have hx0 : 0 < x := by linarith
  have hs : (Real.sqrt x / 66) ^ 16 = x ^ 8 / 66 ^ 16 := by
    rw [div_pow, show (16 : ℕ) = 2 * 8 by norm_num, pow_mul, Real.sq_sqrt hx0.le]
  have hp : (2 * R + 1) ^ 4 ≤ 81 * (M + 1) ^ 4 * x ^ 4 := by
    calc (2 * R + 1) ^ 4 ≤ (3 * (M + 1) * x) ^ 4 := pow_le_pow_left₀ (by positivity) hR 4
      _ = 81 * (M + 1) ^ 4 * x ^ 4 := by ring
  rw [hs]
  have e1 : 2 * (K / (x ^ 8 / 66 ^ 16) * ((2 * R + 1) ^ 4 * A)) =
      2 * K * 66 ^ 16 * A * (2 * R + 1) ^ 4 / x ^ 8 := by
    field_simp
  have e2 : 2 * K * A * 81 * (M + 1) ^ 4 * 66 ^ 16 * (1 / x ^ 4) =
      2 * K * 66 ^ 16 * A * (81 * (M + 1) ^ 4 * x ^ 4) / x ^ 8 := by
    field_simp
  rw [e1, e2]
  gcongr

/-- **Reduction**: the moment node implies the block-tail node. -/
theorem n2ZFirstModeBlock_of_mom (hM : N2ZFirstModeMomStmt) : N2ZFirstModeBlockStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hG, hmom⟩ := hM P X hX
  refine ⟨G, hG, fun m => ?_⟩
  obtain ⟨K, hK, n₀, hn⟩ := hmom m
  set ρ : ℝ := 16 * ((1 / 2 : ℝ) ^ (8 : ℝ) / (7 / 8 : ℝ) ^ 16) with hρdef
  have hρ : ρ < 1 := by
    rw [hρdef, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h1ρ : 0 < 1 - ρ := by linarith
  set A : ℝ := 1 + 4 / (1 - ρ) with hAdef
  have hA : 0 ≤ A := by positivity
  set C₁ : ℝ := 2 * K * A * 81 * ((m : ℝ) + 1) ^ 4 * 66 ^ 16 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have key : ∀ n ≥ n₀, P (fmBlockEvent G m n) ≤ ENNReal.ofReal (C₁ * (1 / 16) ^ n) := by
    intro n hn₀
    have hV := hn n hn₀
    choose V hVc hVm hVmom hVpt hVae using hV
    set R : ℕ := (m + 1) * 2 ^ n with hRdef
    have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    set l : ℝ := Real.sqrt ((2 : ℝ) ^ n) / 66 with hl
    have hl0 : 0 < l := by positivity
    have hc : ((4 : ℕ) : ℝ) / (1 - 7 / 8) + 1 = 33 := by norm_num
    set T : Fin 2 → Set Ω := fun k =>
      {ω | ∃ q ∈ boxD (d := 4) R, (((4 : ℕ) : ℝ) / (1 - 7 / 8) + 1) * l < |V k q ω|} with hT
    have hTb : ∀ k, P (T k) ≤ ENNReal.ofReal (K / l ^ 16 * ((2 * R + 1) ^ 4 +
        (4 : ℕ) * (2 * R + 1) ^ 4 / (1 - ρ))) := fun k =>
      kolm_sup_tail (d := 4) le_rfl (by norm_num : (0 : ℝ) < 7 / 8) (by norm_num) (hVc k)
        (hVm k) (by norm_num) hK hρ (hVmom k) (hVpt k) hl0
    set N : Set Ω := {ω | ¬ ∀ k : Fin 2, ∀ w ∈ fmBox m,
      ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n),
        ∀ s ∈ Ioo 0 τ, fmPart k (fmInt (G ω) w τ s) = V k (fmParam n w τ s) ω} with hN
    have hN0 : P N = 0 := ae_iff.1 (ae_all_iff.2 hVae)
    have hsub : fmBlockEvent G m n ⊆ N ∪ (T 0 ∪ T 1) := by
      intro ω hω
      by_contra hc'
      simp only [mem_union, not_or] at hc'
      obtain ⟨hNω, hT0, hT1⟩ := hc'
      simp only [hN, mem_ofPred_eq, not_not] at hNω
      obtain ⟨w, hw, τ, hτ, s, hs, hbig⟩ := hω
      have hq := fmParam_mem_boxD hw hτ hs
      have hsmall : ∀ k, |V k (fmParam n w τ s) ω| ≤ Real.sqrt ((2 : ℝ) ^ n) / 2 := by
        intro k
        by_contra hk
        push Not at hk
        have hmem : ω ∈ T k := ⟨_, hq, by rw [hc, hl]; linarith⟩
        fin_cases k
        · exact hT0 hmem
        · exact hT1 hmem
      have h0 : (fmInt (G ω) w τ s).re = V 0 (fmParam n w τ s) ω := by
        simpa [fmPart] using hNω 0 w hw τ hτ s hs
      have h1 : (fmInt (G ω) w τ s).im = V 1 (fmParam n w τ s) ω := by
        simpa [fmPart] using hNω 1 w hw τ hτ s hs
      have hn := Complex.norm_le_abs_re_add_abs_im (fmInt (G ω) w τ s)
      rw [h0, h1] at hn
      linarith [hsmall 0, hsmall 1]
    have hR' : 2 * (R : ℝ) + 1 ≤ 3 * ((m : ℝ) + 1) * 2 ^ n := by
      rw [hRdef]; push_cast; nlinarith
    calc P (fmBlockEvent G m n) ≤ P (N ∪ (T 0 ∪ T 1)) := measure_mono hsub
      _ ≤ P N + (P (T 0) + P (T 1)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (K / l ^ 16 * ((2 * R + 1) ^ 4 +
            (4 : ℕ) * (2 * R + 1) ^ 4 / (1 - ρ))) + ENNReal.ofReal (K / l ^ 16 *
            ((2 * R + 1) ^ 4 + (4 : ℕ) * (2 * R + 1) ^ 4 / (1 - ρ)))) := by
          rw [hN0]; exact add_le_add le_rfl (add_le_add (hTb 0) (hTb 1))
      _ = ENNReal.ofReal (2 * (K / l ^ 16 * ((2 * R + 1) ^ 4 * A))) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hAdef]; push_cast; ring
      _ ≤ ENNReal.ofReal (C₁ * (1 / 16) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have e : (1 / 16 : ℝ) ^ n = 1 / ((2 : ℝ) ^ n) ^ 4 := by
            rw [← pow_mul, one_div_pow, mul_comm, pow_mul]; norm_num
          rw [e, hC₁, hl]
          exact fm_block_arith hK hA hx1 (Nat.cast_nonneg _) hR'
  have key' : ∀ n, P (fmBlockEvent G m n) ≤
      ENNReal.ofReal ((C₁ + 16 ^ n₀) * (1 / 16) ^ n) := by
    intro n
    by_cases hn₀ : n₀ ≤ n
    · refine (key n hn₀).trans (ENNReal.ofReal_le_ofReal ?_)
      have : (0 : ℝ) ≤ 16 ^ n₀ * (1 / 16) ^ n := by positivity
      nlinarith
    · push Not at hn₀
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1 : ℝ) ≤ 16 ^ n₀ * (1 / 16) ^ n := by
        rw [one_div_pow, mul_one_div, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ (by norm_num) hn₀.le
      have : (0 : ℝ) ≤ C₁ * (1 / 16) ^ n := by positivity
      nlinarith
  exact ne_top_of_le_ne_top
    (CircleCont.tsum_geom_ne_top (by positivity) (by norm_num) (by norm_num))
    (ENNReal.tsum_le_tsum key')

/-- **N2Z-FIRSTMODE from the moment node.** -/
theorem n2ZFirstMode_of_mom (hM : N2ZFirstModeMomStmt) : N2ZFirstModeStmt :=
  n2ZFirstMode_of_block (n2ZFirstModeBlock_of_mom hM)

end D3Plus
end QuantumZipper
