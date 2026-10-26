import HigherDimLFPPAS.Gauss.Window
import HigherDimLFPPAS.Gauss.Summable

/-!
# Lemma 2.3(iii), equation (2.8) (packet F2b)

For every `a > 0`, almost surely, for every `R` and `η > 0`, for all sufficiently large `n`,
`|h ∗ K_ε(x) - h ∗ K_δ(x)| ≤ η` for all `ε, δ ∈ [(n+1)^{-a}, n^{-a}]` and `x ∈ B̄_R`
(`lemma23_iii_F2b`; signed admissible seeds, `d ≥ 2`).

Proof (planning audit MA3, Details P6, derivative-free, with cells of mesh `e^{-t_n} τ_n`; see
`Gauss/Window.lean`). The window suprema have tails `c exp(-η²/(16 K τ_n))` with `τ_n ≤ a/n`, the
number of cells is `O((n+1)^J)`, so the union bounds are summable; Borel–Cantelli; and
`|H_ε(x) - H_δ(x)| ≤ |Y_{n,k}(σ, v)| + |Y_{n,k}(σ', v)|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- The window cell count is polynomial: `(2⌈R/ℓ_n⌉ + 1)^d ≤ (2R/a + 3)^d (n+1)^{(⌈a⌉+1) d}`. -/
lemma card_box_win_le_F2b {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    ((boxF2b d ⌈R / winMeshF2b a n⌉₊).card : ℝ) ≤
      (2 * R / a + 3) ^ d * ((n : ℝ) + 1) ^ ((⌈a⌉₊ + 1) * d) := by
  have hτ0 := winSpanF2b_pos ha hn
  have hℓ0 : 0 < winMeshF2b a n := mul_pos (Real.exp_pos _) hτ0
  refine (card_boxF2b_le (div_nonneg hR hℓ0.le)).trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  set m : ℕ := ⌈a⌉₊ with hm
  -- `e^{t_n} ≤ (n+1)^m`
  have hexp : Real.exp (winTimeF2b a n) ≤ ((n : ℝ) + 1) ^ m := by
    rw [← Real.exp_log (show (0 : ℝ) < ((n : ℝ) + 1) ^ m by positivity), Real.log_pow]
    refine Real.exp_le_exp.2 ?_
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hl1 : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
    have ham : a ≤ m := Nat.le_ceil a
    calc winTimeF2b a n = a * Real.log n := rfl
      _ ≤ m * Real.log ((n : ℝ) + 1) := by
          have := Real.log_nonneg hn1
          nlinarith
  -- `1/ℓ_n ≤ (n+1)^{m+1}/a`
  have hinv : R / winMeshF2b a n ≤ R / a * ((n : ℝ) + 1) ^ (m + 1) := by
    have hτ := winSpanF2b_ge ha hn
    rw [winMeshF2b, Real.exp_neg, div_eq_mul_inv, mul_inv, inv_inv]
    have h1 : (winSpanF2b a n)⁻¹ ≤ ((n : ℝ) + 1) / a := by
      rw [inv_le_comm₀ hτ0 (by positivity), inv_div]
      exact hτ
    calc R * (Real.exp (winTimeF2b a n) * (winSpanF2b a n)⁻¹)
        ≤ R * (((n : ℝ) + 1) ^ m * (((n : ℝ) + 1) / a)) := by
          gcongr
      _ = R / a * ((n : ℝ) + 1) ^ (m + 1) := by rw [pow_succ]; ring
  have hpow1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (m + 1) := one_le_pow₀ hn1
  calc (2 * (R / winMeshF2b a n) + 3) ^ d
      ≤ ((2 * R / a + 3) * ((n : ℝ) + 1) ^ (m + 1)) ^ d := by
        refine pow_le_pow_left₀ (by positivity) ?_ d
        calc 2 * (R / winMeshF2b a n) + 3
            ≤ 2 * (R / a * ((n : ℝ) + 1) ^ (m + 1)) + 3 * ((n : ℝ) + 1) ^ (m + 1) := by
              linarith
          _ = (2 * R / a + 3) * ((n : ℝ) + 1) ^ (m + 1) := by ring
    _ = (2 * R / a + 3) ^ d * ((n : ℝ) + 1) ^ ((m + 1) * d) := by
        rw [mul_pow, ← pow_mul]

/-- `∑ (n+1)^J e^{-βn} < ∞`. -/
lemma summable_succ_pow_mul_exp_F2b (J : ℕ) {β : ℝ} (hβ : 0 < β) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ J * Real.exp (-β * n) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul J hβ)
  refine (h.mul_left (Real.exp β)).congr fun n => ?_
  push_cast
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- **Lemma 2.3(iii), (2.8)**, for fixed `R` and `η`. -/
theorem lemma23_iii_fixed_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {a : ℝ} (ha : 0 < a) (R η : ℝ) (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
        |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ η := by
  wlog hR : 0 ≤ R generalizing R
  · filter_upwards [this 0 le_rfl] with ω hω
    filter_upwards [hω] with n hn ε hε δ hδ x hx
    have : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    exact absurd ((norm_nonneg x).trans this) hR
  obtain ⟨K, hK0, hKtail⟩ := exists_win_sup_tail_F2b hd hκ
  set η' : ℝ := η / 2 with hη'
  have hη'0 : 0 < η' := by positivity
  set n₀ : ℕ := max 1 ⌈a⌉₊ with hn₀
  have hn₀1 : 1 ≤ n₀ := le_max_left _ _
  have hτ1 : ∀ n : ℕ, n₀ ≤ n → winSpanF2b a n ≤ 1 := by
    intro n hn
    have hn1 : 1 ≤ n := hn₀1.trans hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    refine (winSpanF2b_le ha hn1).trans ?_
    rw [div_le_one hn0]
    exact (Nat.le_ceil a).trans (by exact_mod_cast (le_max_right 1 ⌈a⌉₊).trans hn)
  set cW : ℝ := 2 * Real.exp (1000 * ((d : ℝ) + 2)) with hcW
  set β : ℝ := η' ^ 2 / (4 * K * a) with hβ
  have hβ0 : 0 < β := by positivity
  set J : ℕ := (⌈a⌉₊ + 1) * d with hJ
  let B : ℕ → Finset (Fin d → ℤ) := fun n => boxF2b d ⌈R / winMeshF2b a n⌉₊
  let E : ℕ → Set Ω := fun n => if n₀ ≤ n then
    ⋃ k ∈ B n, {ω | η' ≤ ⨆ p, |winProcF2b κ h a n k p ω|} else ∅
  let f : ℕ → ℝ := fun n => (2 * R / a + 3) ^ d * cW * (((n : ℝ) + 1) ^ J * Real.exp (-β * n))
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hfsum : Summable f := (summable_succ_pow_mul_exp_F2b J hβ0).mul_left _
  have hE : ∀ n, P (E n) ≤ ENNReal.ofReal (f n) := by
    intro n
    by_cases hn : n₀ ≤ n
    · have hn1 : 1 ≤ n := hn₀1.trans hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hτ0 := winSpanF2b_pos ha hn1
      have hcard := card_box_win_le_F2b (d := d) hR ha hn1
      -- the tail of one window
      have htail : ∀ k, P.real {ω | η' ≤ ⨆ p, |winProcF2b κ h a n k p ω|} ≤
          cW * Real.exp (-β * n) := by
        intro k
        refine (hKtail hh ha hn1 (hτ1 n hn) k hη'0.le).trans ?_
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        have hτle := winSpanF2b_le ha hn1
        -- `η'² / (4 K τ_n) ≥ β n`
        rw [neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity), hβ]
        calc η' ^ 2 / (4 * K * a) * n * (2 * (2 * (K * winSpanF2b a n)))
            = η' ^ 2 * (n * winSpanF2b a n) / a := by field_simp; ring
          _ ≤ η' ^ 2 * a / a := by
              gcongr
              rw [le_div_iff₀ hn0] at hτle
              linarith
          _ = η' ^ 2 := by field_simp
      simp only [E, hn, ↓reduceIte]
      calc P (⋃ k ∈ B n, {ω | η' ≤ ⨆ p, |winProcF2b κ h a n k p ω|})
          ≤ ∑ k ∈ B n, P {ω | η' ≤ ⨆ p, |winProcF2b κ h a n k p ω|} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ k ∈ B n, ENNReal.ofReal (cW * Real.exp (-β * n)) := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [← ofReal_measureReal]
            exact ENNReal.ofReal_le_ofReal (htail k)
        _ = ENNReal.ofReal ((B n).card * (cW * Real.exp (-β * n))) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (f n) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc ((B n).card : ℝ) * (cW * Real.exp (-β * n))
                ≤ (2 * R / a + 3) ^ d * ((n : ℝ) + 1) ^ J * (cW * Real.exp (-β * n)) :=
                  mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = f n := by simp only [f]; ring
    · simp only [E, hn, ↓reduceIte, measure_empty, zero_le]
  have hsum : ∑' n, P (E n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hE)
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum, ae_continuous_fieldF2b hd hκ hh] with ω hω hcont
  filter_upwards [hω, eventually_ge_atTop n₀] with n hωn hn ε hε δ hδ x hx
  have hn1 : 1 ≤ n := hn₀1.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hτ0 := winSpanF2b_pos ha hn1
  have hℓ0 : 0 < winMeshF2b a n := mul_pos (Real.exp_pos _) hτ0
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  obtain ⟨k, hk, v, hxv⟩ := exists_cell_F2b hℓ0 hxR
  have hnot : ¬ η' ≤ ⨆ p, |winProcF2b κ h a n k p ω| := by
    intro hmem
    apply hωn
    simp only [E, hn, ↓reduceIte]
    exact mem_biUnion hk hmem
  rw [not_le] at hnot
  have hcY : Continuous fun p' => |winProcF2b κ h a n k p' ω| :=
    ((hcont.comp (continuous_winTopF2b a n k)).sub
      (hcont.comp (continuous_winBaseF2b a n k))).abs
  -- one scale in the window
  have hone : ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      |convMollify κ ε (h ω) x - fieldF2b κ h (winTimeF2b a n, x) ω| < η' := by
    intro ε hε
    have hε0 : 0 < ε := (Real.rpow_pos_of_pos (by positivity) _).trans_le hε.1
    set t : ℝ := Real.log ε⁻¹ with ht
    have ht1 : winTimeF2b a n ≤ t := by
      have hle := Real.log_le_log hε0 hε.2
      rw [Real.log_rpow hn0] at hle
      rw [ht, Real.log_inv, winTimeF2b]
      linarith
    have ht2 : t ≤ winTimeF2b a n + winSpanF2b a n := by
      have hle := Real.log_le_log (Real.rpow_pos_of_pos (by positivity) _) hε.1
      rw [Real.log_rpow (by positivity)] at hle
      rw [ht, Real.log_inv, winTimeF2b, winSpanF2b]
      linarith
    set σ : unitInterval := ⟨(t - winTimeF2b a n) / winSpanF2b a n,
      div_nonneg (by linarith) hτ0.le, (div_le_one hτ0).2 (by linarith)⟩ with hσ
    set p : Fin (d + 1) → unitInterval := Fin.cons σ v with hp
    have hspace : cubeSpaceF2b p = fun i => (v i : ℝ) := by
      funext i
      simp only [cubeSpaceF2b, hp, Fin.cons_succ]
    have htop : winTopF2b a n k p = (t, x) := by
      simp only [winTopF2b, hp, Fin.cons_zero, hσ]
      refine Prod.ext ?_ hxv.symm
      simp only
      field_simp
      ring
    have hbase : winBaseF2b a n k p = (winTimeF2b a n, x) := by
      simp only [winBaseF2b, hspace]
      exact Prod.ext rfl hxv.symm
    have hεt : Real.exp (-t) = ε := by
      rw [ht, Real.log_inv, neg_neg, Real.exp_log hε0]
    have hval : convMollify κ ε (h ω) x - fieldF2b κ h (winTimeF2b a n, x) ω =
        winProcF2b κ h a n k p ω := by
      simp only [winProcF2b, htop, hbase, fieldF2b, hεt]
    rw [hval]
    exact (le_ciSup (isCompact_range hcY).bddAbove p).trans_lt hnot
  have h1 := hone ε hε
  have h2 := hone δ hδ
  calc |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x|
      = |(convMollify κ ε (h ω) x - fieldF2b κ h (winTimeF2b a n, x) ω) -
          (convMollify κ δ (h ω) x - fieldF2b κ h (winTimeF2b a n, x) ω)| := by ring_nf
    _ ≤ |convMollify κ ε (h ω) x - fieldF2b κ h (winTimeF2b a n, x) ω| +
          |convMollify κ δ (h ω) x - fieldF2b κ h (winTimeF2b a n, x) ω| := abs_sub _ _
    _ ≤ η := by linarith

/-- **Lemma 2.3(iii), (2.8)**: for every `a > 0`, almost surely, for every `R` and every `η > 0`,
for all large `n`, `|h ∗ K_ε(x) - h ∗ K_δ(x)| ≤ η` for `ε, δ ∈ [(n+1)^{-a}, n^{-a}]`,
`x ∈ B̄_R`. -/
theorem lemma23_iii_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ R η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
        |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ η := by
  have hall : ∀ᵐ ω ∂P, ∀ N j : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ δ ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)),
      ∀ x ∈ Metric.closedBall (0 : Rd d) N,
        |convMollify κ ε (h ω) x - convMollify κ δ (h ω) x| ≤ 1 / (j + 1) := by
    rw [ae_all_iff]
    intro N
    rw [ae_all_iff]
    intro j
    exact lemma23_iii_fixed_F2b hd hκ hh ha N (1 / (j + 1)) (by positivity)
  filter_upwards [hall] with ω hω
  intro R η hη
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω N j] with n hn ε hε δ hδ x hx
  exact (hn ε hε δ hδ x (Metric.closedBall_subset_closedBall hN hx)).trans hj.le

end HigherDimLFPPAS.Gauss
