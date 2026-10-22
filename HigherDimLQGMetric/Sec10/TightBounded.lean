import HigherDimLQGMetric.Sec10.Envelope
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Tightness transfer for bounded continuous perturbations

The fixed law of the pure normalized metric is approximated by compact sets of genuine metrics.
Its uniformly Weyl-comparable perturbations lie in compact metric envelopes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

local instance : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

/-- A probability law carried by continuous metrics has compact metric sets of arbitrarily
large probability. -/
theorem s8a_exists_compact_metrics (μ : Measure C(Rd d × Rd d, ℝ))
    [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ E ∂μ, IsContinuousMetric E) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set C(Rd d × Rd d, ℝ), IsCompact K ∧
      K ⊆ {E | IsContinuousMetric E} ∧ μ Kᶜ < ε := by
  let A : Set C(Rd d × Rd d, ℝ) := {E | IsContinuousMetric E}
  have hA : MeasurableSet A := measurableSet_isContinuousMetric_select d
  have hAc : μ Aᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hμ] with E hE
    simpa only [mem_compl_iff, not_not, A, mem_ofPred_eq] using hE
  obtain ⟨K, hKA, hK, hdiff⟩ :=
    hA.exists_isCompact_sdiff_lt (measure_ne_top μ A) hε.ne'
  refine ⟨K, hK, hKA, ?_⟩
  have hsub : Kᶜ ⊆ Aᶜ ∪ (A \ K) := by
    intro E hE
    by_cases hEA : E ∈ A
    · exact Or.inr ⟨hEA, hE⟩
    · exact Or.inl hEA
  calc μ Kᶜ ≤ μ (Aᶜ ∪ (A \ K)) := measure_mono hsub
    _ ≤ μ Aᶜ + μ (A \ K) := measure_union_le _ _
    _ = μ (A \ K) := by rw [hAc, zero_add]
    _ < ε := hdiff

/-- A finite measurable random real is bounded outside an event of arbitrarily small
probability. -/
theorem s8a_exists_random_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (M : Ω → ℝ)
    (hM : Measurable M) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ P {ω | B < M ω} < ε := by
  have hanti : Antitone fun n : ℕ => {ω | (n : ℝ) < M ω} := by
    intro m n hmn ω hω
    change (n : ℝ) < M ω at hω
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hω
  have hinter : (⋂ n : ℕ, {ω | (n : ℝ) < M ω}) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact exists_nat_ge (M ω)
  have hlim : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < M ω}) atTop (𝓝 0) := by
    have ht := tendsto_measure_iInter_atTop (μ := P)
      (fun n : ℕ => (measurableSet_lt measurable_const hM).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    simp only [Function.comp_def] at ht
    rwa [hinter, measure_empty] at ht
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨n, Nat.cast_nonneg _, hn⟩

/-- A common pure law and random comparison constants give compact sets of genuine metrics
carrying almost all perturbed laws uniformly. -/
theorem s8a_exists_compact_metric_of_randomCompare
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set ℝ} (A B : ℝ → Ω → C(Rd d × Rd d, ℝ))
    (μ : Measure C(Rd d × Rd d, ℝ)) [IsProbabilityMeasure μ]
    (hAm : ∀ r ∈ S, AEMeasurable (A r) P)
    (hBm : ∀ r ∈ S, AEMeasurable (B r) P)
    (hAlaw : ∀ r ∈ S, P.map (A r) = μ)
    (hμ : ∀ᵐ E ∂μ, IsContinuousMetric E)
    (M : Ω → ℝ) (hM : Measurable M)
    (hBmet : ∀ r ∈ S, ∀ᵐ ω ∂P, IsContinuousMetric (B r ω))
    (hcmp : ∀ r ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A r ω p ≤ B r ω p ∧
      B r ω p ≤ Real.exp (M ω) * A r ω p)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : Set C(Rd d × Rd d, ℝ), IsCompact C ∧
      C ⊆ {E | IsContinuousMetric E} ∧
      ∀ r ∈ S, (P.map (B r)) Cᶜ ≤ ε := by
  have hhalf : 0 < ε / 2 := by simpa using ENNReal.div_pos hε.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  obtain ⟨K, hK, hKm, hKmass⟩ := s8a_exists_compact_metrics μ hμ hhalf
  obtain ⟨N, hN0, hNmass⟩ := s8a_exists_random_bound P M hM hhalf
  let C := s8a_envelope K (Real.exp (-N)) (Real.exp N)
  have hCcompact : IsCompact C :=
    s8a_envelope_isCompact hK hKm (Real.exp_pos _) (Real.exp_pos _).le
  refine ⟨C, hCcompact,
    (fun E hE => s8a_envelope_isContinuousMetric hKm (Real.exp_pos _) hE), ?_⟩
  intro r hr
  have hbadA : P (A r ⁻¹' Kᶜ) < ε / 2 := by
    rw [← Measure.map_apply₀ (hAm r hr) hK.isClosed.isOpen_compl.measurableSet.nullMeasurableSet,
      hAlaw r hr]
    exact hKmass
  have hsub : ∀ᵐ ω ∂P, ω ∈ B r ⁻¹' Cᶜ →
      ω ∈ A r ⁻¹' Kᶜ ∪ {ω | N < M ω} := by
    filter_upwards [hBmet r hr, hcmp r hr] with ω hmetric hbound hbad
    by_contra hnot
    simp only [mem_union, mem_preimage, mem_compl_iff, mem_ofPred_eq, not_or, not_not,
      not_lt] at hnot
    have hAK : A r ω ∈ K := hnot.1
    have hMN : M ω ≤ N := hnot.2
    have hAmet : IsContinuousMetric (A r ω) := hKm hAK
    have hgood : B r ω ∈ C := by
      refine ⟨⟨hmetric.self_eq_zero, hmetric.symm, hmetric.triangle⟩,
        A r ω, hAK, fun p => ?_⟩
      have hA0 := s8a_metricFn_nonneg hAmet p.1 p.2
      have hleft : Real.exp (-N) ≤ Real.exp (-M ω) :=
        Real.exp_le_exp.mpr (by linarith)
      have hright : Real.exp (M ω) ≤ Real.exp N :=
        Real.exp_le_exp.mpr hMN
      exact ⟨(mul_le_mul_of_nonneg_right hleft hA0).trans (hbound p).1,
        (hbound p).2.trans (mul_le_mul_of_nonneg_right hright hA0)⟩
    exact hbad hgood
  have hbad : P (B r ⁻¹' Cᶜ) ≤ P (A r ⁻¹' Kᶜ ∪ {ω | N < M ω}) :=
    measure_mono_ae hsub
  rw [Measure.map_apply₀ (hBm r hr)
    hCcompact.isClosed.isOpen_compl.measurableSet.nullMeasurableSet]
  calc P (B r ⁻¹' Cᶜ) ≤ P (A r ⁻¹' Kᶜ ∪ {ω | N < M ω}) := hbad
    _ ≤ P (A r ⁻¹' Kᶜ) + P {ω | N < M ω} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hbadA.le hNmass.le
    _ = ε := by
      rw [← two_mul]
      exact ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

/-- Tightness transfers from one common pure law through random, scale-independent
two-sided comparison constants. -/
theorem s8a_isTightMeasureSet_of_randomCompare
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set ℝ} (A B : ℝ → Ω → C(Rd d × Rd d, ℝ))
    (μ : Measure C(Rd d × Rd d, ℝ)) [IsProbabilityMeasure μ]
    (hAm : ∀ r ∈ S, AEMeasurable (A r) P)
    (hBm : ∀ r ∈ S, AEMeasurable (B r) P)
    (hAlaw : ∀ r ∈ S, P.map (A r) = μ)
    (hμ : ∀ᵐ E ∂μ, IsContinuousMetric E)
    (M : Ω → ℝ) (hM : Measurable M)
    (hBmet : ∀ r ∈ S, ∀ᵐ ω ∂P, IsContinuousMetric (B r ω))
    (hcmp : ∀ r ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A r ω p ≤ B r ω p ∧
      B r ω p ≤ Real.exp (M ω) * A r ω p) :
    IsTightMeasureSet {ν | ∃ r ∈ S, ν = P.map (B r)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨C, hC, _, hbound⟩ := s8a_exists_compact_metric_of_randomCompare
    P A B μ hAm hBm hAlaw hμ M hM hBmet hcmp hε
  exact ⟨C, hC, fun ν ⟨r, hr, hν⟩ => hν ▸ hbound r hr⟩

/-- Every weak limit of the compared laws is still carried by continuous metrics. -/
theorem s8a_closure_metric_of_randomCompare
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set ℝ} (A B : ℝ → Ω → C(Rd d × Rd d, ℝ))
    (μ : Measure C(Rd d × Rd d, ℝ)) [IsProbabilityMeasure μ]
    (hAm : ∀ r ∈ S, AEMeasurable (A r) P)
    (hBm : ∀ r ∈ S, AEMeasurable (B r) P)
    (hAlaw : ∀ r ∈ S, P.map (A r) = μ)
    (hμ : ∀ᵐ E ∂μ, IsContinuousMetric E)
    (M : Ω → ℝ) (hM : Measurable M)
    (hBmet : ∀ r ∈ S, ∀ᵐ ω ∂P, IsContinuousMetric (B r ω))
    (hcmp : ∀ r ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A r ω p ≤ B r ω p ∧
      B r ω p ≤ Real.exp (M ω) * A r ω p)
    (ν : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hν : ν ∈ closure {ν' : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ S, (ν' : Measure C(Rd d × Rd d, ℝ)) = P.map (B r)}) :
    ∀ᵐ E ∂(ν : Measure C(Rd d × Rd d, ℝ)), IsContinuousMetric E := by
  let T : Set C(Rd d × Rd d, ℝ) := {E | IsContinuousMetric E}
  have hzero : (ν : Measure C(Rd d × Rd d, ℝ)) Tᶜ = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨C, hC, hCm, hbound⟩ := s8a_exists_compact_metric_of_randomCompare
      P A B μ hAm hBm hAlaw hμ M hM hBmet hcmp hε
    obtain ⟨νs, hνs, hlim⟩ := mem_closure_iff_seq_limit.mp hν
    have hseq : ∀ n, (νs n : Measure C(Rd d × Rd d, ℝ)) Cᶜ ≤ ε := by
      intro n
      obtain ⟨r, hr, heq⟩ := hνs n
      rw [heq]
      exact hbound r hr
    have hliminf : (atTop.liminf fun n =>
        (νs n : Measure C(Rd d × Rd d, ℝ)) Cᶜ) ≤ ε := by
      calc (atTop.liminf fun n =>
            (νs n : Measure C(Rd d × Rd d, ℝ)) Cᶜ)
          ≤ atTop.liminf (fun _ : ℕ => ε) :=
            Filter.liminf_le_liminf (Filter.Eventually.of_forall hseq)
        _ = ε := Filter.liminf_const ε
    have hνC : (ν : Measure C(Rd d × Rd d, ℝ)) Cᶜ ≤ ε :=
      (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
        hC.isClosed.isOpen_compl).trans hliminf
    have hTC : Tᶜ ⊆ Cᶜ := compl_subset_compl.mpr hCm
    simpa using (measure_mono hTC).trans hνC
  apply measure_eq_zero_iff_ae_notMem.mp hzero |>.mono
  intro E hE
  simpa only [T, mem_compl_iff, mem_ofPred_eq, not_not] using hE

/-- The complete frozen `TightOver` predicate for a family with one pure law and random
global comparison constants. -/
theorem s8a_tightOver_of_randomCompare
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Set ℝ} (A B : ℝ → Ω → C(Rd d × Rd d, ℝ))
    (μ : Measure C(Rd d × Rd d, ℝ)) [IsProbabilityMeasure μ]
    (hAm : ∀ r ∈ S, AEMeasurable (A r) P)
    (hBm : ∀ r ∈ S, AEMeasurable (B r) P)
    (hAlaw : ∀ r ∈ S, P.map (A r) = μ)
    (hμ : ∀ᵐ E ∂μ, IsContinuousMetric E)
    (M : Ω → ℝ) (hM : Measurable M)
    (hBmet : ∀ r ∈ S, ∀ᵐ ω ∂P, IsContinuousMetric (B r ω))
    (hcmp : ∀ r ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A r ω p ≤ B r ω p ∧
      B r ω p ≤ Real.exp (M ω) * A r ω p) : TightOver P B S := by
  exact ⟨hBm,
    s8a_isTightMeasureSet_of_randomCompare P A B μ hAm hBm hAlaw hμ M hM hBmet hcmp,
    s8a_closure_metric_of_randomCompare P A B μ hAm hBm hAlaw hμ M hM hBmet hcmp⟩

end HigherDimLQGMetric
