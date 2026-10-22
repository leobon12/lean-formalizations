import HigherDimLQGMetric.LfppTight.MetricAlgRaw

/-! Every closure law of normalized LGF LFPP is carried by continuous metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_pure_closure_metric (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hμ : μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd
            ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}) :
    ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContinuousMetric D := by
  classical
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) := fun ε ω =>
    toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
  let S : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
    {ν | ∃ ε ∈ Ioo (0 : ℝ) 1,
      (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (B ε)}
  change μ ∈ closure S at hμ
  have hAlgPre (ν : ProbabilityMeasure C(Rd d × Rd d, ℝ)) (hν : ν ∈ S) :
      (1 : ℝ≥0∞) ≤ (ν : Measure C(Rd d × Rd d, ℝ)) metricAlgSet_select := by
    obtain ⟨ε, hε, hνeq⟩ := hν
    rw [hνeq, Measure.map_apply_of_aemeasurable
      (l6a_aemeasurable_raw_metric hDGZ.dim κ hDGZ.kernel ξ hε.1 P h hh)
      (isClosed_metricAlgSet_select d).measurableSet]
    have hAE := l6a_ae_raw_mem_alg hDGZ.dim κ hDGZ.kernel ξ P h hh hε.1
    have hmass : P (B ε ⁻¹' metricAlgSet_select) = 1 := by
      calc
        P (B ε ⁻¹' metricAlgSet_select) = P (univ : Set Ω) := by
          apply measure_congr
          filter_upwards [hAE] with ω hω
          exact eq_true hω
        _ = 1 := measure_univ
    change (1 : ℝ≥0∞) ≤ P (B ε ⁻¹' metricAlgSet_select)
    rw [hmass]
  have hAlgMass := l6a_closed_prob_lower_of_closure S
    (isClosed_metricAlgSet_select d) 1 hAlgPre μ hμ
  have hAlg : ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)),
      D ∈ metricAlgSet_select := by
    rw [ae_iff]
    change (μ : Measure C(Rd d × Rd d, ℝ)) metricAlgSet_selectᶜ = 0
    rw [prob_compl_eq_one_sub (isClosed_metricAlgSet_select d).measurableSet]
    exact tsub_eq_zero_of_le hAlgMass
  have hSep (R m : ℕ) :
      ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)),
        ∃ k : ℕ, D ∈ metricSepSet_select R m k := by
    apply l6a_ae_exists_closed_of_uniform_tail S
      (fun k => metricSepSet_select R m k)
      (fun k => isClosed_metricSepSet_select d R m k) ?_ μ hμ
    intro θ hθ
    obtain ⟨k, htail⟩ := l6a_metricSep_tail hL1e hDGZ hAdapter
      P h hh R m hθ
    refine ⟨k, ?_⟩
    intro ν hν
    obtain ⟨ε, hε, hνeq⟩ := hν
    rw [hνeq, Measure.map_apply_of_aemeasurable
      (l6a_aemeasurable_raw_metric hDGZ.dim κ hDGZ.kernel ξ hε.1 P h hh)
      (isClosed_metricSepSet_select d R m k).isOpen_compl.measurableSet]
    exact htail ε hε
  have hSepAll : ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)),
      ∀ R m : ℕ, ∃ k : ℕ, D ∈ metricSepSet_select R m k :=
    ae_all_iff.2 (fun R => ae_all_iff.2 (hSep R))
  filter_upwards [hAlg, hSepAll] with D hA hS
  exact (isContinuousMetric_iff_select D).2 ⟨hA, hS⟩

end HigherDimLQGMetric
