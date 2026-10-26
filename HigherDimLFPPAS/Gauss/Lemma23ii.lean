import HigherDimLFPPAS.Gauss.Cell
import HigherDimLFPPAS.Gauss.Summable

/-!
# Lemma 2.3(ii), equation (2.7) (packet F2b)

For every `η > 0` and `R`, almost surely, for all sufficiently small `ε > 0`,
`sup_{x ∈ B̄_R} |h ∗ K_ε(x)| ≤ (√(2d) + η) log ε⁻¹` (`lemma23_ii_F2b`; signed admissible seeds,
`d ≥ 2`); and the version with one almost-sure event for all `R` and `η` (`lemma23_ii_all_F2b`).

Proof (planning audit MA3, Details P5). Cubes `e^{-n}(k + [0,1]^d)`, `k` in the box
`{‖k‖_∞ ≤ ⌈R e^n⌉}` (`≤ (2R + 3)^d e^{dn}` cubes). Events `A_{n,k} = {|H_n(e^{-n}k)| ≥ (√(2d) + η/2) n}`
(sharp Gaussian tail with `Var ≤ n + C`, (A.4)) and `B_{n,k} = {sup |X_{n,k}| ≥ η n / 2}` (uniform
Gaussian tail of the cell suprema). Both union bounds are summable; Borel–Cantelli; then for
`log ε⁻¹ ∈ [n, n + 1)`, `|H_t(x)| ≤ |H_n(e^{-n}k)| + |X_{n,k}(t - n, v)| ≤ (√(2d) + η) n`.
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

/-- The cube count at scale `e^{-n}`: `(2⌈R e^n⌉ + 1)^d ≤ (2R + 3)^d e^{dn}`. -/
lemma card_box_exp_le_F2b {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((boxF2b d ⌈R / Real.exp (-(n : ℝ))⌉₊).card : ℝ) ≤ (2 * R + 3) ^ d * Real.exp (d * n) := by
  refine (card_boxF2b_le (by positivity)).trans ?_
  have he : 1 ≤ Real.exp (n : ℝ) := Real.one_le_exp (Nat.cast_nonneg n)
  have h1 : 2 * (R / Real.exp (-(n : ℝ))) + 3 ≤ (2 * R + 3) * Real.exp (n : ℝ) := by
    rw [Real.exp_neg, div_inv_eq_mul]
    nlinarith
  calc (2 * (R / Real.exp (-(n : ℝ))) + 3) ^ d ≤ ((2 * R + 3) * Real.exp (n : ℝ)) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 d
    _ = (2 * R + 3) ^ d * Real.exp (d * n) := by
        rw [mul_pow, ← Real.exp_nat_mul]

/-- **Lemma 2.3(ii), (2.7)**, for fixed `R` and `η`. -/
theorem lemma23_ii_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) (R η : ℝ) (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) x| ≤ (Real.sqrt (2 * d) + η) * Real.log ε⁻¹ := by
  -- reduce to `R ≥ 0`
  wlog hR : 0 ≤ R generalizing R
  · filter_upwards [this 0 le_rfl] with ω hω
    filter_upwards [hω] with ε hε x hx
    have : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    exact absurd ((norm_nonneg x).trans this) hR
  obtain ⟨CA, hCA⟩ := exists_abs_variance_convMollify_sub_le_F2b hd hκ (√d * (R + 1))
  obtain ⟨L, hL0, hLtail⟩ := exists_cell_sup_tail_F2b hd hκ
  set C' : ℝ := max CA 0 + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set M : ℝ := 20 * √5 * L * √((((d + 1 : ℕ) : ℝ) + 1) * 1) with hM
  set c₂ : ℝ := 2 * Real.exp (M ^ 2 / (2 * L ^ 2)) with hc₂
  set lam : ℕ → ℝ := fun n => (Real.sqrt (2 * d) + η / 2) * n with hlam
  let B : ℕ → Finset (Fin d → ℤ) := fun n => boxF2b d ⌈R / Real.exp (-(n : ℝ))⌉₊
  let Aset : ℕ → (Fin d → ℤ) → Set Ω := fun n k =>
    {ω | lam n ≤ |fieldF2b κ h (cellBaseF2b n k) ω|}
  let Bset : ℕ → (Fin d → ℤ) → Set Ω := fun n k =>
    {ω | η * n / 2 ≤ ⨆ p, |cellProcF2b κ h n k p ω|}
  let E : ℕ → Set Ω := fun n => ⋃ k ∈ B n, (Aset n k ∪ Bset n k)
  -- the real bound
  let f : ℕ → ℝ := fun n => (2 * R + 3) ^ d *
    (2 * (Real.exp (d * n) * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 / (2 * (n + C')))) +
      c₂ * (Real.exp (d * n) * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2)))))
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hfsum : Summable f := by
    have h1 := summable_exp_mul_exp_sharp_F2b (D := (d : ℝ)) (Nat.cast_nonneg d) hη hC'0
    have h2 := summable_exp_mul_exp_sq_F2b (D := (d : ℝ)) (b := η / 2) (c := 2 * (2 * L ^ 2))
      (by positivity) (by positivity)
    exact ((h1.mul_left 2).add (h2.mul_left c₂)).mul_left _
  -- the probability bound for one cube
  have hA : ∀ (n : ℕ) (k : Fin d → ℤ), k ∈ B n →
      P.real (Aset n k) ≤ 2 * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 / (2 * (n + C'))) := by
    intro n k hk
    have hnorm : ‖(cellBaseF2b n k).2‖ ≤ √d * (R + 1) := by
      refine (norm_cellPtF2b_zero_le (Real.exp_pos _) hR hk).trans ?_
      have : Real.exp (-(n : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    have hvar := hCA hh (n : ℝ) (Nat.cast_nonneg n) _ hnorm
    have hV : Var[fieldF2b κ h (cellBaseF2b n k); P] ≤ (n : ℝ) + C' := by
      have := (abs_le.mp hvar).2
      have hm : CA ≤ max CA 0 := le_max_left _ _
      change Var[fun ω => convMollify κ (Real.exp (-(n : ℝ))) (h ω) (cellBaseF2b n k).2; P] ≤ _
      linarith
    exact tail_abs_fieldF2b_le hd hκ hh _ (by positivity) hV (by positivity)
  have hB : ∀ (n : ℕ) (k : Fin d → ℤ),
      P.real (Bset n k) ≤ c₂ * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2))) := by
    intro n k
    have h := hLtail hh n k (x := η * n / 2) (by positivity)
    have he : η * (n : ℝ) / 2 = η / 2 * n := by ring
    refine h.trans (le_of_eq ?_)
    rw [he]
  have hE : ∀ n, P (E n) ≤ ENNReal.ofReal (f n) := by
    intro n
    have hcard := card_box_exp_le_F2b (d := d) hR n
    calc P (E n) ≤ ∑ k ∈ B n, P (Aset n k ∪ Bset n k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ B n, ENNReal.ofReal
            (2 * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 / (2 * (n + C'))) +
              c₂ * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2)))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          refine (measure_union_le _ _).trans ?_
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ← ofReal_measureReal,
            ← ofReal_measureReal]
          exact add_le_add (ENNReal.ofReal_le_ofReal (hA n k hk))
            (ENNReal.ofReal_le_ofReal (hB n k))
      _ = ENNReal.ofReal ((B n).card *
            (2 * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 / (2 * (n + C'))) +
              c₂ * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2))))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (f n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpos : 0 ≤ 2 * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 /
              (2 * (n + C'))) + c₂ * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2))) := by
            positivity
          calc ((B n).card : ℝ) *
                (2 * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 / (2 * (n + C'))) +
                  c₂ * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2))))
              ≤ (2 * R + 3) ^ d * Real.exp (d * n) *
                (2 * Real.exp (-((Real.sqrt (2 * d) + η / 2) * n) ^ 2 / (2 * (n + C'))) +
                  c₂ * Real.exp (-(η / 2 * n) ^ 2 / (2 * (2 * L ^ 2)))) :=
                mul_le_mul_of_nonneg_right hcard hpos
            _ = f n := by simp only [f]; ring
  have hsum : ∑' n, P (E n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hE)
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum,
    ae_continuous_fieldF2b hd hκ hh] with ω hω hcont
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hω
  filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-(n₁ : ℝ)))] with ε hε x hx
  obtain ⟨hε0, hε1⟩ := hε
  set t : ℝ := Real.log ε⁻¹ with ht
  have htn₁ : (n₁ : ℝ) < t := by
    rw [ht, Real.log_inv, lt_neg]
    calc Real.log ε < Real.log (Real.exp (-(n₁ : ℝ))) := Real.log_lt_log hε0 hε1
      _ = -(n₁ : ℝ) := Real.log_exp _
  have ht0 : 0 ≤ t := (Nat.cast_nonneg n₁).trans htn₁.le
  set n : ℕ := ⌊t⌋₊ with hn
  have hnn₁ : n₁ ≤ n := Nat.le_floor htn₁.le
  have hnt : (n : ℝ) ≤ t := Nat.floor_le ht0
  have htn : t < n + 1 := Nat.lt_floor_add_one t
  have hωn : ω ∉ E n := hn₁ n hnn₁
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  obtain ⟨k, hk, v, hxv⟩ := exists_cell_F2b (Real.exp_pos (-(n : ℝ))) hxR
  set s : unitInterval := ⟨t - n, by linarith, by linarith⟩ with hs
  set p : Fin (d + 1) → unitInterval := Fin.cons s v with hp
  have htop : cellTopF2b n k p = (t, x) := by
    simp only [cellTopF2b, hp, Fin.cons_zero, hs]
    refine Prod.ext (by simp) ?_
    simp only
    rw [hxv]
    congr 1
  have hεt : Real.exp (-t) = ε := by
    rw [ht, Real.log_inv, neg_neg, Real.exp_log hε0]
  have hval : convMollify κ ε (h ω) x =
      fieldF2b κ h (cellBaseF2b n k) ω + cellProcF2b κ h n k p ω := by
    simp only [cellProcF2b, htop, fieldF2b, hεt]
    ring
  have hAk : ω ∉ Aset n k := fun hmem => hωn (mem_biUnion hk (Or.inl hmem))
  have hBk : ω ∉ Bset n k := fun hmem => hωn (mem_biUnion hk (Or.inr hmem))
  simp only [Aset, Bset, mem_ofPred_eq, not_le] at hAk hBk
  have hcX : Continuous fun p' => |cellProcF2b κ h n k p' ω| :=
    ((hcont.comp (continuous_cellTopF2b n k)).sub continuous_const).abs
  have hXp : |cellProcF2b κ h n k p ω| ≤ ⨆ p', |cellProcF2b κ h n k p' ω| :=
    le_ciSup (isCompact_range hcX).bddAbove p
  rw [hval]
  have hsd : 0 ≤ Real.sqrt (2 * d) + η := by positivity
  calc |fieldF2b κ h (cellBaseF2b n k) ω + cellProcF2b κ h n k p ω|
      ≤ |fieldF2b κ h (cellBaseF2b n k) ω| + |cellProcF2b κ h n k p ω| := abs_add_le _ _
    _ ≤ lam n + η * n / 2 := by linarith
    _ = (Real.sqrt (2 * d) + η) * n := by simp only [hlam]; ring
    _ ≤ (Real.sqrt (2 * d) + η) * t := mul_le_mul_of_nonneg_left hnt hsd

/-- **Lemma 2.3(ii), (2.7)**, on one almost-sure event for all radii `R` and all `η > 0`. -/
theorem lemma23_ii_all_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ R η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) x| ≤ (Real.sqrt (2 * d) + η) * Real.log ε⁻¹ := by
  have hall : ∀ᵐ ω ∂P, ∀ N j : ℕ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ x ∈ Metric.closedBall (0 : Rd d) N,
        |convMollify κ ε (h ω) x| ≤ (Real.sqrt (2 * d) + 1 / (j + 1)) * Real.log ε⁻¹ := by
    rw [ae_all_iff]
    intro N
    rw [ae_all_iff]
    intro j
    exact lemma23_ii_F2b hd hκ hh N (1 / (j + 1)) (by positivity)
  filter_upwards [hall] with ω hω
  intro R η hη
  obtain ⟨N, hN⟩ := exists_nat_ge R
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω N j, Ioo_mem_nhdsGT one_pos] with ε hε hε1 x hx
  have hx' : x ∈ Metric.closedBall (0 : Rd d) N := Metric.closedBall_subset_closedBall hN hx
  have hlog : 0 ≤ Real.log ε⁻¹ := by
    rw [Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hε1.1.le hε1.2.le
  refine (hε x hx').trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hlog

end HigherDimLFPPAS.Gauss
