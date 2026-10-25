import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RepairedInterfaces.RepairedAssembly
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Regularity




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
open LQGMetric (DistC)

 

theorem metric_le_iff_basisInf {B : Set (Set (ℂ × ℂ))}
    (hB : IsTopologicalBasis B) (c : ℝ) (hc : 0 < c)
    (d d' : LSCMetric) :
    (∀ u v : ℂ, d' (u, v) ≤ ENNReal.ofReal c * d (u, v)) ↔
      ∀ b ∈ B, (⨅ p ∈ b, d' p) ≤ ENNReal.ofReal c * (⨅ p ∈ b, d p) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hc
  have hmul : ∀ b : Set (ℂ × ℂ),
      ENNReal.ofReal c * (⨅ p ∈ b, d p) =
        (⨅ p ∈ b, ENNReal.ofReal c * d p) := fun b => by
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    exact iInf_congr fun p => ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top
  constructor
  · intro h b hb
    rw [hmul]
    refine le_iInf fun p => le_iInf fun hp => ?_
    exact (iInf₂_le p hp).trans (h p.1 p.2)
  · intro h u v
    refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
    obtain ⟨b, hbB, hxb, hbsub⟩ :=
      hB.exists_subset_of_mem_open
        (show (u, v) ∈ d'.1 ⁻¹' Ioi t from ht)
        (d'.2.2.isOpen_preimage t)
    calc
      t ≤ ⨅ p ∈ b, d' p := le_iInf₂ fun p hp => (hbsub hp).le
      _ ≤ ENNReal.ofReal c * (⨅ p ∈ b, d p) := h b hbB
      _ ≤ ENNReal.ofReal c * d (u, v) :=
        by gcongr; exact iInf₂_le (u, v) hxb

 
theorem measurableSet_metric_upper (c : ℝ) (hc : 0 < c)
    (D D' : DistC → LSCMetric) (hD : Measurable D) (hD' : Measurable D') :
    MeasurableSet {g : DistC | ∀ u v : ℂ,
      D' g (u, v) ≤ ENNReal.ofReal c * D g (u, v)} := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis (ℂ × ℂ)
  have hset : {g : DistC | ∀ u v : ℂ,
      D' g (u, v) ≤ ENNReal.ofReal c * D g (u, v)} =
      ⋂ b ∈ B, {g : DistC | (⨅ p ∈ b, D' g p) ≤
        ENNReal.ofReal c * (⨅ p ∈ b, D g p)} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
    exact metric_le_iff_basisInf hB c hc (D g) (D' g)
  rw [hset]
  refine MeasurableSet.biInter hBc fun b hb => ?_
  have hbOpen : IsOpen b := hB.isOpen hb
  exact measurableSet_le
    ((LSCMetric.measurable_iInf_of_isOpen hbOpen).comp hD')
    (((LSCMetric.measurable_iInf_of_isOpen hbOpen).comp hD).const_mul _)

 
theorem ae_optimal_upper_field
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus) (hPlusFin : cPlus < ⊤)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    ∀ᵐ g ∂(P.map h), ∀ z w : ℂ,
      D' g (z, w) ≤ ENNReal.ofReal cPlus.toReal * D g (z, w) := by
  have hreal : 0 < cPlus.toReal := ENNReal.toReal_pos hPlusPos.ne' hPlusFin.ne
  have hmeas := measurableSet_metric_upper cPlus.toReal hreal D D' hD.1 hD'.1
  apply (ae_map_iff hGFF.1.measurable.aemeasurable hmeas).2
  filter_upwards [EndSaving.RepairedInterfaces.optimal_global_upper P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hPlusPos hMinus hPlus] with ω hω z w
  rw [ENNReal.ofReal_toReal hPlusFin.ne]
  exact hω z w

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
