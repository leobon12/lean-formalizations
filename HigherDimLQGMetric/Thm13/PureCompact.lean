import HigherDimLQGMetric.Thm13.PureUniformSep

/-! A tight family of length metrics whose closure laws are genuine metrics has
uniform compact approximations consisting entirely of genuine metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Topology Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

local instance (d : ℕ) : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

theorem l8_tightFamily_compact_metrics
    {d : ℕ} (hd : 2 ≤ d) {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hT : TightFamily P X S)
    (hLen : ∀ i ∈ S, ∀ᵐ ω ∂P,
      ∃ M : ContMetric d, M.IsLength ∧ M.1 = X i ω)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set C(Rd d × Rd d, ℝ), IsCompact K ∧
      K ⊆ {M | IsContinuousMetric M} ∧
      ∀ i ∈ S, (P.map (X i)) Kᶜ ≤ ε := by
  classical
  have hhalf : 0 < ε / 2 := by
    simpa using ENNReal.div_pos hε.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  obtain ⟨K₀, hK₀, hK₀mass⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hT.2.1)
      (ε / 2) hhalf
  obtain ⟨δ, hδ, hsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hhalf.ne' (ℕ × ℕ)
  have hk' (nm : ℕ × ℕ) :=
    l8_tightFamily_localSep_tail hd P X S hT nm.1 nm.2 (hδ nm)
  choose k hk using hk'
  let F : ℕ × ℕ → Set C(Rd d × Rd d, ℝ) :=
    fun nm => metricSepSet_select nm.1 nm.2 (k nm)
  let O : ℕ × ℕ → Set C(Rd d × Rd d, ℝ) :=
    fun nm => l8_localSepOpen nm.1 nm.2 (k nm)
  have hFc (nm : ℕ × ℕ) : IsClosed (F nm) :=
    isClosed_metricSepSet_select d nm.1 nm.2 (k nm)
  let K : Set C(Rd d × Rd d, ℝ) :=
    K₀ ∩ (metricAlgSet_select ∩ ⋂ nm : ℕ × ℕ, F nm)
  have hKc : IsCompact K :=
    hK₀.inter_right ((isClosed_metricAlgSet_select d).inter
      (isClosed_iInter hFc))
  have hKm : K ⊆ {M | IsContinuousMetric M} := by
    intro E hE
    have hA : E ∈ metricAlgSet_select := hE.2.1
    have hS : ∀ n m : ℕ, ∃ j : ℕ, E ∈ metricSepSet_select n m j := by
      intro n m
      exact ⟨k (n,m), mem_iInter.mp hE.2.2 (n,m)⟩
    exact (isContinuousMetric_iff_select E).2 ⟨hA, hS⟩
  refine ⟨K, hKc, hKm, ?_⟩
  intro i hi
  let μ : Measure C(Rd d × Rd d, ℝ) := P.map (X i)
  have hAlg : μ metricAlgSet_selectᶜ = 0 := by
    rw [Measure.map_apply₀ (hT.1 i hi)
      (isClosed_metricAlgSet_select d).isOpen_compl.measurableSet.nullMeasurableSet]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hLen i hi] with ω ⟨M, _, hM⟩ hbad
    have hMalg := ((isContinuousMetric_iff_select M.1).1 M.2).1
    exact hbad (by simpa only [← hM] using hMalg)
  have hFmass (nm : ℕ × ℕ) : μ (F nm)ᶜ ≤ δ nm := by
    have hsub : ∀ᵐ ω ∂P,
        ω ∈ (X i) ⁻¹' (F nm)ᶜ → ω ∈ (X i) ⁻¹' (O nm)ᶜ := by
      filter_upwards [hLen i hi] with ω ⟨M, hMl, hM⟩ hbad hgood
      have hmem : M.1 ∈ O nm := by simpa only [hM] using hgood
      have hF := l8_localSepOpen_global_of_length M hMl nm.1 nm.2 (k nm) hmem
      exact hbad (by simpa only [F, hM] using hF)
    calc
      μ (F nm)ᶜ = P ((X i) ⁻¹' (F nm)ᶜ) :=
        Measure.map_apply₀ (hT.1 i hi) (hFc nm).isOpen_compl.measurableSet.nullMeasurableSet
      _ ≤ P ((X i) ⁻¹' (O nm)ᶜ) := measure_mono_ae hsub
      _ = μ (O nm)ᶜ :=
        (Measure.map_apply₀ (hT.1 i hi)
          (l8_localSepOpen_isOpen nm.1 nm.2 (k nm)).isClosed_compl.measurableSet.nullMeasurableSet).symm
      _ ≤ δ nm := hk nm i hi
  have hcomp : Kᶜ = K₀ᶜ ∪ metricAlgSet_selectᶜ ∪
      ⋃ nm : ℕ × ℕ, (F nm)ᶜ := by
    ext E
    simp only [K, mem_compl_iff, mem_inter_iff, mem_iInter,
      mem_union, mem_iUnion, not_and_or, not_forall]
    tauto
  rw [hcomp]
  calc
    μ (K₀ᶜ ∪ metricAlgSet_selectᶜ ∪ ⋃ nm, (F nm)ᶜ)
      ≤ (μ K₀ᶜ + μ metricAlgSet_selectᶜ) +
          μ (⋃ nm, (F nm)ᶜ) :=
        (measure_union_le _ _).trans
          (add_le_add_left (measure_union_le _ _) _)
    _ = μ K₀ᶜ + μ (⋃ nm, (F nm)ᶜ) := by rw [hAlg, add_zero]
    _ ≤ ε / 2 + ∑' nm : ℕ × ℕ, μ (F nm)ᶜ :=
      add_le_add (hK₀mass μ ⟨i, hi, rfl⟩) (measure_iUnion_le _)
    _ ≤ ε / 2 + ∑' nm : ℕ × ℕ, δ nm :=
      add_le_add_right (ENNReal.tsum_le_tsum hFmass) _
    _ ≤ ε / 2 + ε / 2 := add_le_add_right hsum.le _
    _ = ε := by
      rw [← two_mul]
      exact ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

end HigherDimLQGMetric
