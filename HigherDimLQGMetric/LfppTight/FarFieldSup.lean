import HigherDimLQGMetric.LfppTight.SmallTight
import HigherDimLQGMetric.LfppTight.SphereMeanFar
import HigherDimLQGMetric.Main.LFPPMedian

/-! Uniform compact-space supremum tails of the convolution field away from zero cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_far_field_sup_tail {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {a R θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧
      P {ω | ∃ ε ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) R,
        M < |convMollify κ ε (h ω) z|} ≤ ENNReal.ofReal θ := by
  classical
  let K : Set (ℝ × Rd d) := Icc a 1 ×ˢ closedBall (0 : Rd d) R
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_Icc.prod (isCompact_closedBall _ _))
  let X : K → Ω → ℝ := fun p ω => convMollify κ p.1.1 (h ω) p.1.2
  have hc : ∀ᵐ ω ∂P, Continuous fun p : K => X p ω := by
    filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh]
      with ω hω
    have hsub : K ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) := by
      intro p hp
      exact ⟨ha.trans_le hp.1.1, trivial⟩
    exact continuousOn_iff_continuous_domRestrict.mp (hω.mono hsub)
  let Y : K → Ω → ℝ := fun p ω =>
    if hcont : Continuous (fun p : K => X p ω) then X p ω else 0
  have hYc : ∀ ω, Continuous fun p : K => Y p ω := by
    intro ω
    by_cases hcont : Continuous (fun p : K => X p ω)
    · have heq : (fun p : K => Y p ω) = fun p => X p ω := by
        funext p
        exact dite_eq_left hcont
      rw [heq]
      exact hcont
    · have heq : (fun p : K => Y p ω) = fun _ => 0 := by
        funext p
        exact dite_eq_right hcont
      rw [heq]
      exact continuous_const
  have hYm (p : K) : AEMeasurable (Y p) P := by
    have hX : AEMeasurable (X p) P :=
      ((l10a_measurable_convMollify_apply κ p.1.1 p.1.2).comp
        hh.1.measurable).aemeasurable
    have heq : Y p =ᵐ[P] X p := by
      filter_upwards [hc] with ω hω
      exact dite_eq_left hω
    exact (aemeasurable_congr heq.symm).1 hX
  let F : Ω → C(K, ℝ) := fun ω => ⟨fun p => Y p ω, hYc ω⟩
  have hFm : AEMeasurable F P := by
    have key : @Measurable (NullMeasurableSpace Ω P) C(K, ℝ) _ _ F := by
      refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2
        fun p => ?_
      exact (hYm p).nullMeasurable
    exact (show NullMeasurable F P from fun s hs => key hs).aemeasurable
  let N : Ω → ℝ := fun ω => ‖F ω‖
  have hNm : AEMeasurable N P := continuous_norm.measurable.comp_aemeasurable hFm
  have ht : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < N ω}) atTop (𝓝 0) := by
    have hm : Antitone fun n : ℕ => {ω | (n : ℝ) < N ω} := by
      intro m n hmn ω hω
      change (n : ℝ) < N ω at hω
      change (m : ℝ) < N ω
      exact lt_of_le_of_lt (by exact_mod_cast hmn) hω
    have hI : (⋂ n : ℕ, {ω | (n : ℝ) < N ω}) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      exact exists_nat_ge (N ω)
    have hset (n : ℕ) : NullMeasurableSet {ω | (n : ℝ) < N ω} P := by
      change NullMeasurableSet (N ⁻¹' Ioi (n : ℝ)) P
      exact hNm.nullMeasurable measurableSet_Ioi
    have h := tendsto_measure_iInter_atTop (μ := P) hset hm
      ⟨0, measure_ne_top _ _⟩
    simp only [Function.comp_def] at h
    rwa [hI, measure_empty] at h
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds
    (show (0 : ℝ≥0∞) < ENNReal.ofReal θ by simp [hθ]))).exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  have hsub : {ω | ∃ ε ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) R,
      (n : ℝ) + 1 < |convMollify κ ε (h ω) z|} ⊆
      {ω | (n : ℝ) < N ω} ∪
        {ω | ¬ Continuous fun p : K => X p ω} := by
    intro ω hω
    obtain ⟨ε, hε, z, hz, hbad⟩ := hω
    by_cases hgood : Continuous (fun p : K => X p ω)
    · left
      have hp : (ε, z) ∈ K := ⟨hε, hz⟩
      have hle : |X ⟨(ε, z), hp⟩ ω| ≤ N ω := by
        simpa [F, N, Y, hgood, Real.norm_eq_abs] using
          (ContinuousMap.norm_coe_le_norm (F ω) ⟨(ε, z), hp⟩)
      dsimp [X] at hle
      change (n : ℝ) < N ω
      linarith
    · right
      exact hgood
  have hnull : P {ω | ¬ Continuous fun p : K => X p ω} = 0 := by
    simpa only [compl_ofPred] using (ae_iff.mp hc)
  calc
    P {ω | ∃ ε ∈ Icc a 1, ∃ z ∈ closedBall (0 : Rd d) R,
      (n : ℝ) + 1 < |convMollify κ ε (h ω) z|} ≤
        P ({ω | (n : ℝ) < N ω} ∪
          {ω | ¬ Continuous fun p : K => X p ω}) := measure_mono hsub
    _ ≤ P {ω | (n : ℝ) < N ω} +
          P {ω | ¬ Continuous fun p : K => X p ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal θ := by rw [hnull, add_zero]; exact hn.le

end HigherDimLQGMetric
