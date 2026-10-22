import HigherDimLQGMetric.Determ.VarMeasure
import HigherDimLQGMetric.Determ.ChainBound
import LQGMetric.Papers.LM.T1_7L1

/-! Exhaustion of the full internal metric by Euclidean balls. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_internal_eq_iInf (D : ContMetric dim) (z w : Rd dim) :
    D.internal univ z w = ⨅ m : ℕ, D.internal (Metric.ball 0 ((m : ℝ) + 1)) z w := by
  refine le_antisymm (le_iInf fun m =>
    LQGMetric.MetricGeometry.internalEDist_anti (Set.image_mono (subset_univ _)) _ _) ?_
  unfold ContMetric.internal LQGMetric.MetricGeometry.internalEDist
  refine le_iInf fun γ => ?_
  set K : Set (Rd dim) := range (D.unpt ∘ γ.1)
  have hKc : IsCompact K := isCompact_range (D.continuous_unpt.comp γ.1.continuous)
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball (0 : Rd dim)
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hKm : K ⊆ Metric.ball (0 : Rd dim) ((m : ℝ) + 1) := fun x hx =>
    Metric.mem_ball.2 ((Metric.mem_ball.1 (hR hx)).trans_le (by linarith))
  exact iInf_le_of_le m (iInf_le_of_le ⟨γ.1, fun t =>
    ⟨D.unpt (γ.1 t), hKm ⟨t, rfl⟩, ContMetric.pt_unpt _ _⟩⟩ le_rfl)

theorem determ_iInf_F {D : ContMetric dim} (hD : D.IsLength)
    (n₀ : ℕ) (z w : Rd dim) :
    ⨅ m : ℕ, determF (n₀ + m) z w D = ENNReal.ofReal (D.1 (z, w)) := by
  rw [← D.internal_univ_of_isLength hD]
  have e : ∀ m : ℕ, determF (n₀ + m) z w D =
      D.internal (Metric.ball 0 ((n₀ + m : ℕ) : ℝ)) z w :=
    fun m => (D.internal_eq_chainInf hD Metric.isOpen_ball z w).symm
  simp_rw [e]
  refine le_antisymm ?_ (le_iInf fun m =>
    LQGMetric.MetricGeometry.internalEDist_anti (Set.image_mono (subset_univ _)) _ _)
  have h := determ_internal_eq_iInf D z w
  rw [h]
  refine le_iInf fun m => iInf_le_of_le (m + 1) ?_
  refine LQGMetric.MetricGeometry.internalEDist_anti (Set.image_mono fun x hx => ?_) _ _
  exact Metric.mem_ball.2 ((Metric.mem_ball.1 hx).trans_le (by
    push_cast
    linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]))

theorem determ_ae_kernel [Nonempty (ContMetric dim)] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {h : Ω → DistRd dim} {D : Ω → ContMetric dim}
    (hh : Measurable h) (hD : Measurable D)
    {S : Set (DistRd dim × ContMetric dim)} (hS : MeasurableSet S)
    (H : ∀ᵐ ω ∂P, (h ω, D ω) ∈ S) :
    ∀ᵐ g ∂P.map h, ∀ᵐ d ∂condDistrib D h P g, (g, d) ∈ S := by
  have h1 : ∀ᵐ p ∂P.map (fun ω => (h ω, D ω)), p ∈ S :=
    (ae_map_iff (hh.prodMk hD).aemeasurable hS).2 H
  rw [← compProd_map_condDistrib hh.aemeasurable hD.aemeasurable] at h1
  exact (Measure.ae_compProd_iff hS).1 h1

end HigherDimLQGMetric
