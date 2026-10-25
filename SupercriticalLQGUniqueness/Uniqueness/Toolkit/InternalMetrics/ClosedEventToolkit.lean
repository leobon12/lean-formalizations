import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf




 







set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.Blueprint
open LQGMetric (DistC DistOn restrictTo pairJ)
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics

 

theorem internal_eq_compactPathInf (D : LSCMetric) (K : Set ℂ) (p : K × K) :
    D.internal K p =
      Toolkit.CompactPathInfimum.compactPathInf D K {p.1.1} {p.2.1} := by
  simp only [LSCMetric.internal, Toolkit.CompactPathInfimum.compactPathInf, Set.mem_singleton_iff]

 

theorem measurable_internal_compact (K : Set ℂ) (hK : IsCompact K)
    (p : K × K) :
    Measurable (fun D : LSCMetric => D.internal K p) := by
  have h := Toolkit.CompactPathInfimum.compactPathInf_measurable hK
    (isCompact_singleton (x := p.1.1))
    (isCompact_singleton (x := p.2.1))
  simpa only [internal_eq_compactPathInf] using h

 

theorem measurable_internal_compact_whole (K : Set ℂ) (hK : IsCompact K) :
    Measurable (fun D : LSCMetric => D.internal K) :=
  measurable_pi_iff.2 (fun p => measurable_internal_compact K hK p)


 


theorem aeEventIn_internal_subset
    {ι : Type} [Fintype ι] (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (K : Set ℂ) (U : TopologicalSpace.Opens ℂ)
    (hKU : K ⊆ (U : Set ℂ))
    (Φ : (ι → (K × K → ℝ≥0∞)) → Prop)
    (hB : NullMeasurableSet
      {g : DistC | Φ (fun i => (D i g).internal K)} μ) :
    AEEventIn μ (fieldSigma id U)
      {g : DistC | Φ (fun i => (D i g).internal K)} := by
  classical
  let B : Set DistC := {g | Φ (fun i => (D i g).internal K)}
  have hLoc : ∀ i : ι, ∃ F : DistOn U →
      (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞),
      ∀ᵐ g ∂μ, (D i g).internal (U : Set ℂ) = F (restrictTo U g) := by
    intro i
    obtain ⟨F, _, hF⟩ := (hD i).locality μ id hμ U
    exact ⟨F, hF⟩
  choose F hF using hLoc
  let Wraw : Set DistC :=
    {g | ∀ i, (D i g).internal (U : Set ℂ) = F i (restrictTo U g)}
  have hWraw : ∀ᵐ g ∂μ, g ∈ Wraw := by
    change ∀ᵐ g ∂μ, ∀ i,
      (D i g).internal (U : Set ℂ) = F i (restrictTo U g)
    exact ae_all_iff.mpr hF
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ :=
    fun g => pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W,
      R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ he hB₁
    have hRes : restrictTo U g₁ = restrictTo U g₂ :=
      LQGMetric.injective_pairJ U he
    have hIntU : ∀ i, (D i g₁).internal (U : Set ℂ) =
        (D i g₂).internal (U : Set ℂ) := by
      intro i
      calc
        _ = F i (restrictTo U g₁) := hWsub g₁ hg₁ i
        _ = F i (restrictTo U g₂) := by rw [hRes]
        _ = _ := (hWsub g₂ hg₂ i).symm
    have hIntK : ∀ i, (D i g₁).internal K = (D i g₂).internal K := by
      intro i
      exact internal_eq_of_internal_eq (D i g₁) (D i g₂) hKU (hIntU i)
    change Φ (fun i => (D i g₁).internal K) at hB₁
    change Φ (fun i => (D i g₂).internal K)
    rw [show (fun i => (D i g₂).internal K) =
      (fun i => (D i g₁).internal K) from (funext fun i => (hIntK i).symm)]
    exact hB₁
  simpa only [B, Set.preimage_id] using
    (LQGMetric.LocalEvent.aeEventIn_of_saturated
      (Y := id) (R := R) (V := R) (B := B) (W := W)
      measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
      hWm (by simpa only [B, Measure.map_id] using hB) hWae hSat)


 


theorem aeEventIn_closed_internal_family
    {ι : Type} [Fintype ι] (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (K : Set ℂ) (Φ : (ι → (K × K → ℝ≥0∞)) → Prop)
    (hB : NullMeasurableSet
      {g : DistC | Φ (fun i => (D i g).internal K)} μ) :
    AEEventIn μ (fieldSigmaClosed id K)
      {g : DistC | Φ (fun i => (D i g).internal K)} := by
  apply LQGMetric.GM.gm_aeEventIn_fieldSigmaClosed id K
  intro n
  have hKU : K ⊆ (nbhdO (1 / ((n : ℝ) + 1)) K : Set ℂ) := by
    exact Metric.self_subset_thickening (by positivity) K
  exact aeEventIn_internal_subset μ hμ ξ Q D hD K
    (nbhdO (1 / ((n : ℝ) + 1)) K) hKU Φ hB


 

theorem aeEventIn_closed_borel_internal_family
    {ι : Type} [Fintype ι] (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (K : Set ℂ) (hK : IsCompact K)
    (Φ : (ι → (K × K → ℝ≥0∞)) → Prop)
    (hΦ : MeasurableSet {ρ | Φ ρ}) :
    AEEventIn μ (fieldSigmaClosed id K)
      {g : DistC | Φ (fun i => (D i g).internal K)} := by
  have hMap : Measurable
      (fun g : DistC => (fun i => (D i g).internal K)) :=
    measurable_pi_iff.2 fun i =>
      (measurable_internal_compact_whole K hK).comp (hD i).measurable
  have hB : NullMeasurableSet
      {g : DistC | Φ (fun i => (D i g).internal K)} μ :=
    (hΦ.preimage hMap).nullMeasurableSet
  exact aeEventIn_closed_internal_family μ hμ ξ Q D hD K Φ hB


end SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics
