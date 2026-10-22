import HigherDimLQGMetric.DGZ.NondegLambdaEventually

/-! DGZ (6.5), including the finitely many indices before the asymptotic estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

private theorem nd_aQ_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℕ → Rd d → Ω → ℝ) (ξ : ℝ) (n : ℕ) :
    aQ P H ξ n 0 = 0 := by
  unfold aQ LQGMetric.lowerQuantile
  simp only [zero_le, Set.ofPred_true]
  exact Real.sInf_univ

theorem lambdaComparableShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) :
    LambdaComparableShape d κ ξ Q := by
  intro h q hq1
  by_cases hq0 : q = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro Ω _ P W H hH n
    rw [hq0, nd_aQ_zero, mul_zero]
    have hd0 : 0 < d := by have hh := h.dim; omega
    exact (tight_aQ_pos hd0 hH ξ n (by norm_num) (by norm_num)).le
  · have hqpos : 0 < q := pos_iff_ne_zero.mpr hq0
    obtain ⟨q₀, hq₀0, hq₀1, hevent⟩ := nd_lambda_eventually h
    let q' : ℝ≥0∞ := max q q₀
    have hq'0 : 0 < q' := hqpos.trans_le (le_max_left _ _)
    have hq'1 : q' < 1 := max_lt hq1 hq₀1
    obtain ⟨δ, hδ, N, hN⟩ := hevent q' (le_max_right _ _) hq'1
    have hd0 : 0 < d := by have hh := h.dim; omega
    obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
    obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization h.kernel hW₀
    let P₀ : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
    let F : Finset ℕ := Finset.range (N + 1)
    have hFne : F.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
    let f : ℕ → ℝ := fun k => aQ P₀ H₀ ξ k 2⁻¹ / aQ P₀ H₀ ξ k q'
    have hfpos : ∀ k ∈ F, 0 < f k := by
      intro k _
      dsimp [f]
      exact div_pos (tight_aQ_pos hd0 hH₀ ξ k (by norm_num) (by norm_num))
        (tight_aQ_pos hd0 hH₀ ξ k hq'0 hq'1)
    have hinfpos : 0 < F.inf' hFne f :=
      (Finset.lt_inf'_iff hFne).2 hfpos
    let c : ℝ := min δ (F.inf' hFne f)
    have hc : 0 < c := lt_min hδ hinfpos
    refine ⟨c, hc, ?_⟩
    intro Ω _ P W H hH n
    have hqmono : aQ P H ξ n q ≤ aQ P H ξ n q' :=
      tight_aQ_mono hH ξ n hqpos (le_max_left _ _) hq'1
    have haQnonneg : 0 ≤ aQ P H ξ n q' :=
      (tight_aQ_pos hd0 hH ξ n hq'0 hq'1).le
    have hfirst : c * aQ P H ξ n q ≤ c * aQ P H ξ n q' :=
      mul_le_mul_of_nonneg_left hqmono hc.le
    refine hfirst.trans ?_
    by_cases hn : N ≤ n
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) haQnonneg).trans
        (hN Ω P W H hH n hn)
    · have hnF : n ∈ F := Finset.mem_range.mpr (by omega)
      have hqeq : aQ P H ξ n q' = aQ P₀ H₀ ξ n q' :=
        nd_aQ_eq_of_realizations hH hH₀ ξ n q'
      have hmedeq : aQ P H ξ n 2⁻¹ = aQ P₀ H₀ ξ n 2⁻¹ :=
        nd_aQ_eq_of_realizations hH hH₀ ξ n 2⁻¹
      rw [hqeq, hmedeq]
      have hcf : c ≤ f n := (min_le_right _ _).trans (Finset.inf'_le _ hnF)
      have hqpos₀ : 0 < aQ P₀ H₀ ξ n q' := tight_aQ_pos hd0 hH₀ ξ n hq'0 hq'1
      exact (le_div_iff₀ hqpos₀).1 hcf

end HigherDimLQGMetric.DGZ
