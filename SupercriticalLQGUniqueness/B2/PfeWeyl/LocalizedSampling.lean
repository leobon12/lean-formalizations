import SupercriticalLQGUniqueness.B2.PfeWeyl.CurveOscillation
import SupercriticalLQGUniqueness.B2.PfeWeyl.PathEstimate

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 


theorem exists_localized_near_min_weyl_curve
    (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    {K K' : Set ℂ} (hloc : LocalizedNearMinPaths D ξ f K K')
    (z : ℂ) (hz : z ∈ K) (w : ℂ) (hw : w ∈ K)
    (hfin : weylScale ξ f D (z, w) ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (P : ℝ → ℂ) (L : ℝ), D.IsCurve P 0 L ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) ∧
      P 0 = z ∧ P L = w ∧ P '' Icc 0 L ⊆ K' ∧
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) <
        weylScale ξ f D (z, w) + ENNReal.ofReal δ := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hcost⟩ :=
    exists_near_min_weyl_curve D ξ f z w hfin hδ
  have hδle : ENNReal.ofReal δ ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hδ1
  have hcost1 :
      (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) <
        weylScale ξ f D (z, w) + 1 :=
    hcost.trans_le (add_le_add_right hδle _)
  exact ⟨P, L, hP, hu, hP0, hPL,
    hloc z hz w hw P L hP hu hP0 hPL (Or.inr hcost1), hcost⟩

 

theorem exists_localized_weyl_sampling
    (D : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    {K K' : Set ℂ} (hloc : LocalizedNearMinPaths D ξ f K K')
    (z : ℂ) (hz : z ∈ K) (w : ℂ) (hw : w ∈ K)
    (hfin : weylScale ξ f D (z, w) ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (N : ℕ) (v : ℕ → ℂ), 0 < N ∧ v 0 = z ∧ v N = w ∧
      (∀ j ≤ N, v j ∈ K') ∧
      (∀ j < N, D (v j, v (j + 1)) < ENNReal.ofReal δ) ∧
      (∑ j ∈ Finset.range N, weylScale ξ f D (v j, v (j + 1))) <
        weylScale ξ f D (z, w) + ENNReal.ofReal δ := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hPK, hcost⟩ :=
    exists_localized_near_min_weyl_curve D ξ f hloc z hz w hw hfin hδ hδ1
  obtain ⟨N, t, hN, ht, ht0, htN, hstep⟩ :=
    exists_short_step_sampling_with_times D hP hu hδ
  refine ⟨N, P ∘ t, hN, ?_, ?_, ?_, hstep, ?_⟩
  · simp [ht0, hP0]
  · simp [htN, hPL]
  · intro j hj
    apply hPK
    refine ⟨t j, ?_, rfl⟩
    exact ⟨ht0 ▸ ht (Nat.zero_le j), htN ▸ ht hj⟩
  · exact (weyl_chain_le_cost D ξ f hforget hP hu t ht N ht0 htN).trans_lt hcost

 





theorem unitSpeed_weyl_cost_bounds
    (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    {P : ℝ → ℂ} {L : ℝ} (hP : D.IsCurve P 0 L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (m M : ℝ)
    (hlo : ∀ t ∈ Icc 0 L, m ≤ f (P t))
    (hhi : ∀ t ∈ Icc 0 L, f (P t) ≤ M) :
    ENNReal.ofReal (Real.exp (ξ * m)) * D.len P 0 L ≤
      (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) ∧
      (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) ≤
        ENNReal.ofReal (Real.exp (ξ * M)) * D.len P 0 L := by
  have hbound :=
    Uniqueness.Toolkit.WeylLength.weylCurveLength_factor_bounds
      D ξ hξ f hforget hP m M hlo hhi
  rw [Uniqueness.Toolkit.WeylLength.weylCurveLength_eq_weightedLength
    D ξ f hforget hP] at hbound
  have hw : ContinuousOn
      (fun t => Real.exp (ξ * f (euclidForget D ((D.pt ∘ P) t))))
      (Icc 0 L) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (f.continuous.comp hforget))).continuousOn.comp
      hP.2 (fun _ _ => Set.mem_univ _)
  rw [HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hP.1 hu hw] at hbound
  exact hbound

end SupercriticalLQGUniqueness.B2.PfeWeyl
