import HigherDimLQGMetric.Limits.PseudoEnvelope
import HigherDimLQGMetric.Sec10.TightBounded
import HigherDimLQGMetric.Limits.TightScales

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
open scoped ENNReal
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Two-sided random comparison transfers tightness from a tight family of
ambient metric laws, even though the pure laws vary with the index. -/
theorem l6c_tight_of_randomCompare {d : ℕ}
    {ι Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hA : TightFamily P A S)
    (hBm : ∀ i ∈ S, AEMeasurable (B i) P)
    (hAalg : ∀ i ∈ S, ∀ᵐ ω ∂P, A i ω ∈ metricAlgSet_select)
    (hBalg : ∀ i ∈ S, ∀ᵐ ω ∂P, B i ω ∈ metricAlgSet_select)
    (M : Ω → ℝ) (hM : Measurable M)
    (hcmp : ∀ i ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A i ω p ≤ B i ω p ∧
      B i ω p ≤ Real.exp (M ω) * A i ω p) :
    IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, ν = P.map (B i)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hhalf : 0 < ε / 2 := by
    simpa using ENNReal.div_pos hε.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  obtain ⟨K, hK, hKmass⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hA.2.1) (ε / 2) hhalf
  obtain ⟨N, hN0, hNmass⟩ := s8a_exists_random_bound P M hM hhalf
  let K' : Set C(Rd d × Rd d, ℝ) := K ∩ metricAlgSet_select
  have hK' : IsCompact K' := hK.inter_right (isClosed_metricAlgSet_select d)
  have hK'alg : K' ⊆ metricAlgSet_select := fun _ h => h.2
  let C := s8a_envelope K' (Real.exp (-N)) (Real.exp N)
  have hCcompact : IsCompact C :=
    l6c_pseudoEnvelope_isCompact hK' hK'alg (Real.exp_pos _) (Real.exp_pos _).le
  refine ⟨C, hCcompact, ?_⟩
  intro ν hν
  obtain ⟨i, hi, rfl⟩ := hν
  have hbadA : P (A i ⁻¹' Kᶜ) ≤ ε / 2 := by
    rw [← Measure.map_apply₀ (hA.1 i hi)
      hK.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
    exact hKmass _ ⟨i, hi, rfl⟩
  have hsub : ∀ᵐ ω ∂P, ω ∈ B i ⁻¹' Cᶜ →
      ω ∈ A i ⁻¹' Kᶜ ∪ {ω | N < M ω} := by
    filter_upwards [hAalg i hi, hBalg i hi, hcmp i hi] with ω hAω hBω hbound hbad
    by_contra hnot
    simp only [mem_union, mem_preimage, mem_compl_iff, mem_ofPred_eq, not_or, not_not,
      not_lt] at hnot
    have hAK : A i ω ∈ K' := ⟨hnot.1, hAω⟩
    have hMN : M ω ≤ N := hnot.2
    have hnonneg : ∀ p : Rd d × Rd d, 0 ≤ A i ω p := by
      intro p
      have htri := hAω.2.2 p.1 p.2 p.1
      rw [hAω.1, hAω.2.1 p.2 p.1] at htri
      linarith
    have hgood : B i ω ∈ C := by
      refine ⟨hBω, A i ω, hAK, fun p => ?_⟩
      have hleft : Real.exp (-N) ≤ Real.exp (-M ω) :=
        Real.exp_le_exp.mpr (by linarith)
      have hright : Real.exp (M ω) ≤ Real.exp N := Real.exp_le_exp.mpr hMN
      exact ⟨(mul_le_mul_of_nonneg_right hleft (hnonneg p)).trans (hbound p).1,
        (hbound p).2.trans (mul_le_mul_of_nonneg_right hright (hnonneg p))⟩
    exact hbad hgood
  have hbad : P (B i ⁻¹' Cᶜ) ≤ P (A i ⁻¹' Kᶜ ∪ {ω | N < M ω}) :=
    measure_mono_ae hsub
  rw [Measure.map_apply₀ (hBm i hi)
    hCcompact.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
  calc P (B i ⁻¹' Cᶜ) ≤ P (A i ⁻¹' Kᶜ ∪ {ω | N < M ω}) := hbad
    _ ≤ P (A i ⁻¹' Kᶜ) + P {ω | N < M ω} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hbadA hNmass.le
    _ = ε := by
      rw [← two_mul]
      exact ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

end HigherDimLQGMetric
