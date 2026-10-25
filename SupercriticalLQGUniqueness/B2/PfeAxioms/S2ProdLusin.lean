import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdCoupling
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableHeatVersion
import SupercriticalLQGUniqueness.B2.PfeAxioms.VaryingJointCoordLaw
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3LemProbLusin
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Reference
import LQGMetric.Field.RandomDistVersion
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.HeineCantor

 




















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal
open LQGMetric (DistC normGFFLaw heatMollify CoordJ pairJ pairJInv)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem exists_isCompact_continuousOn_of_measurable
    {S T : Type*} [TopologicalSpace S] [SecondCountableTopology S]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace S] [MeasurableSpace S] [BorelSpace S] [T2Space S]
    [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [OpensMeasurableSpace T]
    (μ : Measure S) [IsFiniteMeasure μ] {Φ : S → T} (hΦ : Measurable Φ)
    {κ : ℝ≥0∞} (hκ : κ ≠ 0) :
    ∃ K : Set S, IsCompact K ∧ μ Kᶜ < κ ∧ ContinuousOn Φ K := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis T
  haveI : Countable B := hBc.to_subtype
  have hκ2 : κ / 2 ≠ 0 := (ENNReal.half_pos hκ).ne'
  have hκ4 : κ / 2 / 2 ≠ 0 := (ENNReal.half_pos hκ2).ne'
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hκ4 B
  have hδne : ∀ U : B, ((δ U : ℝ≥0) : ℝ≥0∞) ≠ 0 := fun U => by
    exact_mod_cast (hδpos U).ne'
  have hA : ∀ U : B, MeasurableSet (Φ ⁻¹' (U : Set T)) := fun U =>
    hΦ (hB.isOpen U.2).measurableSet
  choose K₁ hK₁A hK₁c hK₁μ using fun U : B =>
    (hA U).exists_isCompact_sdiff_lt (measure_ne_top μ _) (hδne U)
  choose K₂ hK₂A hK₂c hK₂μ using fun U : B =>
    (hA U).compl.exists_isCompact_sdiff_lt (measure_ne_top μ _) (hδne U)
  obtain ⟨K₀, -, hK₀c, hK₀μ⟩ :=
    MeasurableSet.univ.exists_isCompact_sdiff_lt (measure_ne_top μ _) hκ2
  set K : Set S := K₀ ∩ ⋂ U : B, (K₁ U ∪ K₂ U) with hKdef
  refine ⟨K, hK₀c.inter_right (isClosed_iInter fun U =>
    (hK₁c U).isClosed.union (hK₂c U).isClosed), ?_, ?_⟩
  · have hsub : Kᶜ ⊆ (univ \ K₀) ∪ ⋃ U : B,
        ((Φ ⁻¹' (U : Set T) \ K₁ U) ∪ ((Φ ⁻¹' (U : Set T))ᶜ \ K₂ U)) := by
      intro x hx
      simp only [hKdef, mem_compl_iff, mem_inter_iff, mem_iInter, mem_union, not_and,
        not_forall, not_or] at hx
      by_cases hx₀ : x ∈ K₀
      · obtain ⟨U, h1, h2⟩ := hx hx₀
        refine Or.inr (mem_iUnion.2 ⟨U, ?_⟩)
        by_cases hxU : x ∈ Φ ⁻¹' (U : Set T)
        · exact Or.inl ⟨hxU, h1⟩
        · exact Or.inr ⟨hxU, h2⟩
      · exact Or.inl ⟨mem_univ x, hx₀⟩
    calc μ Kᶜ
        ≤ μ (univ \ K₀) + ∑' U : B,
            μ ((Φ ⁻¹' (U : Set T) \ K₁ U) ∪ ((Φ ⁻¹' (U : Set T))ᶜ \ K₂ U)) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_iUnion_le _)))
      _ ≤ μ (univ \ K₀) + ∑' U : B, (((δ U : ℝ≥0) : ℝ≥0∞) + ((δ U : ℝ≥0) : ℝ≥0∞)) := by
          refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun U => ?_)
          exact (measure_union_le _ _).trans (add_le_add (hK₁μ U).le (hK₂μ U).le)
      _ < κ / 2 + κ / 2 := by
          rw [ENNReal.tsum_add]
          refine ENNReal.add_lt_add_of_lt_of_le
            (ENNReal.add_ne_top.2 ⟨hδsum.ne_top, hδsum.ne_top⟩) hK₀μ ?_
          calc ∑' U : B, ((δ U : ℝ≥0) : ℝ≥0∞) + ∑' U : B, ((δ U : ℝ≥0) : ℝ≥0∞)
              ≤ κ / 2 / 2 + κ / 2 / 2 := add_le_add hδsum.le hδsum.le
            _ = κ / 2 := ENNReal.add_halves _
      _ = κ := ENNReal.add_halves κ
  · rw [continuousOn_iff]
    intro x hx t ht hxt
    obtain ⟨U, hUB, hxU, hUt⟩ := hB.exists_subset_of_mem_open hxt ht
    refine ⟨(K₂ ⟨U, hUB⟩)ᶜ, (hK₂c ⟨U, hUB⟩).isClosed.isOpen_compl, ?_, ?_⟩
    · intro hx2
      exact hK₂A ⟨U, hUB⟩ hx2 hxU
    · rintro y ⟨hy2, hyK⟩
      have hy := mem_iInter.1 hyK.2 ⟨U, hUB⟩
      rcases hy with hy1 | hy2'
      · exact hUt (hK₁A ⟨U, hUB⟩ hy1)
      · exact absurd hy2' hy2

 

theorem lusin_uniform_of_measurable
    {S T : Type*} [PseudoMetricSpace S] [SecondCountableTopology S]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace S] [MeasurableSpace S] [BorelSpace S] [T2Space S]
    [PseudoMetricSpace T] [SecondCountableTopology T] [MeasurableSpace T] [OpensMeasurableSpace T]
    (μ : Measure S) [IsFiniteMeasure μ] {Φ : S → T} (hΦ : Measurable Φ) :
    ∀ κ : ℝ≥0∞, 0 < κ → ∃ K : Set S, IsClosed K ∧ μ Kᶜ < κ ∧
      ∀ a : ℝ, 0 < a → ∃ η : ℝ, 0 < η ∧
        ∀ x ∈ K, ∀ x' ∈ K, dist x x' < η → dist (Φ x) (Φ x') < a := by
  intro κ hκ
  obtain ⟨K, hKc, hKμ, hcont⟩ := exists_isCompact_continuousOn_of_measurable μ hΦ hκ.ne'
  refine ⟨K, hKc.isClosed, hKμ, fun a ha => ?_⟩
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hcont) a ha
  exact ⟨η, hη, hu⟩

 

theorem exists_subseq_ae_of_coords
    (μ : Measure (CoordJ → ℝ)) [IsProbabilityMeasure μ]
    (R : ℕ → (CoordJ → ℝ) → LSCMetric) (Φ' : (CoordJ → ℝ) → LSCMetric)
    (hR : ∀ n, Measurable (R n)) (hΦ' : Measurable Φ')
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → CoordJ → ℝ) (Xl : Ω' → CoordJ → ℝ) (hXm : ∀ n, Measurable (X n))
    (hXlm : Measurable Xl) (hXlaw : ∀ n, P'.map (X n) = μ) (hXllaw : P'.map Xl = μ)
    (hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => X n ω) atTop (𝓝 (Xl ω)))
    (hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => R n (X n ω)) atTop (𝓝 (Φ' (Xl ω)))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → CoordJ → ℝ), AEMeasurable h P →
        P.map h = μ → ∀ᵐ ω ∂P, Tendsto (fun k => R (ns k) (h ω)) atTop (𝓝 (Φ' (h ω))) := by
  let _ : MetricSpace LSCMetric := TopologicalSpace.metrizableSpaceMetric LSCMetric
  have : BorelSpace LSCMetric := ⟨rfl⟩
  let _ : MetricSpace (CoordJ → ℝ) := TopologicalSpace.metrizableSpaceMetric (CoordJ → ℝ)
  exact PfeWeyl.exists_subseq_ae_of_coupling_lusin.{0, 0, 0, 0} μ R Φ' hR P' X Xl hXm hXlm
    hXlaw hXllaw (fun n ω => R n (X n ω)) (fun n => (hR n).comp (hXm n))
    (fun n => Filter.EventuallyEq.rfl) hXconv hYconv (lusin_uniform_of_measurable μ hΦ')

 


theorem normalizedLscLimit_of_identified_coupling
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (e : ℕ → Ioi (0 : ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric)
    (hC : IdentifiedDG20Coupling ξ m e B2.DG20Lim.canonicalHeatVersion P' h' hN L)
    (Φ : DistC → LSCMetric) (hΦm : Measurable Φ) (hΦ : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ PfeWeyl.NormalizedLscLimit ξ m (e ∘ ns) Φ := by
  obtain ⟨hh', hNm, hNlaw, hField, -, hconv, -, -⟩ := hC
  have _ : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hμ : IsProbabilityMeasure (normGFFLaw.map (pairJ ⊤)) :=
    (Measure.isProbabilityMeasure_map_iff (LQGMetric.measurable_pairJ ⊤).aemeasurable).2
      inferInstance
  have hR : ∀ n, Measurable fun a : CoordJ → ℝ =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
        (B2.DG20Lim.canonicalHeatVersion (e n) (pairJInv ⊤ a)) := fun n =>
    measurable_normalizedLFPPMetric_comp (ξ : ℝ) _
      (fun z => (continuous_eval_const z).measurable.comp
        ((B2.DG20Lim.canonicalHeatVersion_measurable (e n)).comp (LQGMetric.measurable_pairJInv ⊤)))
  have hh'm : Measurable h' := hh'.1.measurable
  have hXlaw : ∀ n, P'.map (fun ω => pairJ ⊤ (hN n ω)) = normGFFLaw.map (pairJ ⊤) := fun n => by
    change P'.map (pairJ ⊤ ∘ hN n) = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) (hNm n), hNlaw n]
  have hXllaw : P'.map (fun ω => pairJ ⊤ (h' ω)) = normGFFLaw.map (pairJ ⊤) := by
    change P'.map (pairJ ⊤ ∘ h') = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh'm,
      ← normGFFLaw_eq_of_normalized P' h' hh']
  have hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => pairJ ⊤ (hN n ω)) atTop (𝓝 (pairJ ⊤ (h' ω))) := by
    filter_upwards [hField] with ω hω
    exact (continuous_pairJ_top.tendsto _).comp hω
  have hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (B2.DG20Lim.canonicalHeatVersion (e n) (pairJInv ⊤ (pairJ ⊤ (hN n ω))))) atTop
      (𝓝 (Φ (pairJInv ⊤ (pairJ ⊤ (h' ω))))) := by
    filter_upwards [hconv, hΦ] with ω hω hL
    simp only [LQGMetric.pairJInv_pairJ]
    rw [← hL]
    exact hω
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_coords (normGFFLaw.map (pairJ ⊤))
    (fun n a => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n))
      (B2.DG20Lim.canonicalHeatVersion (e n) (pairJInv ⊤ a)))
    (fun a => Φ (pairJInv ⊤ a)) hR (hΦm.comp (LQGMetric.measurable_pairJInv ⊤)) P'
    (fun n ω => pairJ ⊤ (hN n ω)) (fun ω => pairJ ⊤ (h' ω))
    (fun n => (LQGMetric.measurable_pairJ ⊤).comp (hNm n)) ((LQGMetric.measurable_pairJ ⊤).comp hh'm)
    hXlaw hXllaw hXconv hYconv
  refine ⟨ns, hns, ?_⟩
  intro Ω _ P _ h hh X hX
  have hlaw : P.map (fun ω => pairJ ⊤ (h ω)) = normGFFLaw.map (pairJ ⊤) := by
    change P.map (pairJ ⊤ ∘ h) = _
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh.1.measurable,
      ← normGFFLaw_eq_of_normalized P h hh]
  have h1 := hae P (fun ω => pairJ ⊤ (h ω))
    ((LQGMetric.measurable_pairJ ⊤).comp hh.1.measurable).aemeasurable hlaw
  have hXe := ae_heat_smoothing_sequence_eq P h hh (e ∘ ns) X hX
  have hVe : ∀ᵐ ω ∂P, ∀ n z, B2.DG20Lim.canonicalHeatVersion (e (ns n)) (h ω) z =
      heatMollify (e (ns n) : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    have h2 := B2.DG20Lim.canonicalHeatVersion_ae (e (ns n))
    rw [normGFFLaw_eq_of_normalized P h hh] at h2
    filter_upwards [ae_of_ae_map hh.1.measurable.aemeasurable h2] with ω hω z
    exact congrFun hω z
  filter_upwards [h1, hXe, hVe] with ω hω hXω hVω
  have heq : ∀ k, X (e (ns k)) ω = B2.DG20Lim.canonicalHeatVersion (e (ns k)) (h ω) := fun k =>
    ContinuousMap.ext fun z => (hXω k z).trans (hVω k z).symm
  have hT : Tendsto (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e (ns k)))
      (X (e (ns k)) ω)) atTop (𝓝 (Φ (h ω))) := by
    simp only [LQGMetric.pairJInv_pairJ] at hω
    simpa only [heq] using hω
  exact (PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (fun k => m (e (ns k)))
    (fun k => X (e (ns k)) ω) (Φ (h ω))).1 hT

end SupercriticalLQGUniqueness.B2.PfeAxioms
