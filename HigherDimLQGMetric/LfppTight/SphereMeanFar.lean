import HigherDimLQGMetric.LfppTight.SphereMeanMeas
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact

/-! A7(2), cutoffs bounded away from zero: path continuity implies uniform tails. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_far_sphereMean_tail {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧
      P {ω | ∃ ε ∈ Icc a 1, M < |l6a_convSphereMean κ ε (h ω)|} ≤
        ENNReal.ofReal θ := by
  classical
  let K : Set ℝ := Icc a 1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let X : K → Ω → ℝ := fun ε ω => l6a_convSphereMean κ ε.1 (h ω)
  have hc : ∀ᵐ ω ∂P, Continuous fun ε : K => X ε ω := by
    filter_upwards [l6a_ae_sphereMean_continuousOn hd κ hκ P h hh]
      with ω hω
    have hsub : K ⊆ Ioi (0 : ℝ) := fun ε hε => lt_of_lt_of_le ha hε.1
    exact continuousOn_iff_continuous_domRestrict.mp (hω.mono hsub)
  let Y : K → Ω → ℝ := fun ε ω =>
    if he : Continuous (fun ε : K => X ε ω) then X ε ω else 0
  have hYc : ∀ ω, Continuous fun ε : K => Y ε ω := by
    intro ω
    by_cases he : Continuous (fun ε : K => X ε ω)
    · have hEq : (fun ε : K => Y ε ω) = fun ε => X ε ω := by
        funext ε
        dsimp [Y]
        exact dite_eq_left he
      rw [hEq]
      exact he
    · have hEq : (fun ε : K => Y ε ω) = fun _ => 0 := by
        funext ε
        dsimp [Y]
        exact dite_eq_right he
      rw [hEq]
      exact continuous_const
  have hYm (ε : K) : AEMeasurable (Y ε) P := by
    have hX : AEMeasurable (X ε) P :=
      l6a_aemeasurable_sphereMean hd κ hκ P h hh (lt_of_lt_of_le ha ε.2.1)
    have heq : Y ε =ᵐ[P] X ε := by
      filter_upwards [hc] with ω hω
      dsimp [Y]
      exact dite_eq_left hω
    exact (aemeasurable_congr heq.symm).1 hX
  let F : Ω → C(K, ℝ) := fun ω => ⟨fun ε => Y ε ω, hYc ω⟩
  have hFm : AEMeasurable F P := by
    have key : @Measurable (NullMeasurableSpace Ω P) C(K, ℝ) _ _ F := by
      refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2 fun ε => ?_
      exact (hYm ε).nullMeasurable
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
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_lt]
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
  have hsub : {ω | ∃ ε ∈ Icc a 1,
      (n : ℝ) + 1 < |l6a_convSphereMean κ ε (h ω)|} ⊆
      {ω | (n : ℝ) < N ω} ∪ {ω | ¬ Continuous fun ε : K => X ε ω} := by
    intro ω hω
    obtain ⟨ε, hε, hbad⟩ := hω
    by_cases hgood : Continuous (fun ε : K => X ε ω)
    · left
      have hle : |X ⟨ε, hε⟩ ω| ≤ N ω := by
        simpa [F, N, Y, hgood, Real.norm_eq_abs] using
          (ContinuousMap.norm_coe_le_norm (F ω) ⟨ε, hε⟩)
      dsimp [X] at hle
      change (n : ℝ) < N ω
      linarith
    · right
      exact hgood
  have hnull : P {ω | ¬ Continuous fun ε : K => X ε ω} = 0 := by
    simpa only [compl_ofPred] using (ae_iff.mp hc)
  calc
    P {ω | ∃ ε ∈ Icc a 1, (n : ℝ) + 1 < |l6a_convSphereMean κ ε (h ω)|} ≤
        P ({ω | (n : ℝ) < N ω} ∪
          {ω | ¬ Continuous fun ε : K => X ε ω}) := measure_mono hsub
    _ ≤ P {ω | (n : ℝ) < N ω} +
          P {ω | ¬ Continuous fun ε : K => X ε ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal θ := by rw [hnull, add_zero]; exact hn.le

end HigherDimLQGMetric
