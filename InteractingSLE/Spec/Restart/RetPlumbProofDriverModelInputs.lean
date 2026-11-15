/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverAnnounce
import InteractingSLE.Spec.Restart.FCK2RealizeLaws

/-!
# Analytic reductions for the retained stopped model

Packet PROVE-RETPLUMB. These exact named source obligations concern the initial
Gaussian pairing law and pre-lifetime force geometry. They are not asserted to
follow from driver reconstruction. Their consequences discharge integrability
and the stopped-K2 threshold bound.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Sec7.PocketTraversal FCDet
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Exact initial Gaussian source input, with bounded conditional mean for
each event-supported field pairing. This is a hypothesis, not a new axiom. -/
def RetInitialPairingGaussian (P : Measure Ω) (𝒢 : MeasurableSpace Ω) (M : Set Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ φ : TestOn upperHalfPlaneOpens, ∃ (μ V : Ω → ℝ) (K C : ℝ),
    @Sec6.Prop65.IsCondGaussian Ω 𝒢 mΩ P (M.indicator (fun ω => X ω φ)) μ V K ∧
      ∀ ω, ‖μ ω‖ ≤ C

/-- The landed conditional Gaussian estimate supplies all required pairings. -/
theorem integrable_restrict_of_retInitialPairingGaussian [IsProbabilityMeasure P]
    {𝒢 : MeasurableSpace Ω} {M : Set Ω} {X : Ω → DistOn upperHalfPlaneOpens}
    (hM : MeasurableSet[mΩ] M) (hg : @RetInitialPairingGaussian Ω mΩ P 𝒢 M X) :
    ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) (P.restrict M) := by
  let _ : MeasurableSpace Ω := mΩ
  intro φ
  obtain ⟨μ, V, K, C, hgauss, hbound⟩ := hg φ
  exact FCPlumb.integrable_restrict_of_condGaussian_indicator hM hgauss hbound

/-- Exact remaining force-geometry input: before the boundary-stopped lifetime
the retained force word has not reached its collision threshold. -/
def RetPrelifeNonThreshold {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    (V : Ω → ℝ≥0∞) (M : Set Ω) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω →
    ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
      (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω)

/-- The attained-threshold theorem turns pre-lifetime noncollision into the
weak threshold bound needed by stopped K2. Equality of lifetimes is unnecessary. -/
theorem life_le_thr_of_retPrelifeNonThreshold {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {V : Ω → ℝ≥0∞} {M : Set Ω} (hc : ∀ ω, Continuous fun t => W t ω)
    (hn : RetPrelifeNonThreshold (P := P) ρL ρR W xL xR V M) :
    ∀ᵐ ω ∂P, ω ∈ M → V ω ≤ thr ρL ρR W xL xR ω := by
  filter_upwards [hn] with ω hω hM
  by_contra h
  have hlt : thr ρL ρR W xL xR ω < V ω := lt_of_not_ge h
  have hfin := ne_top_of_lt hlt
  have he : ((thr ρL ρR W xL xR ω).toNNReal : ℝ≥0∞) = thr ρL ρR W xL xR ω :=
    ENNReal.coe_toNNReal hfin
  exact hω hM _ (he ▸ hlt) (thr_mem_thresholdSet hc xL xR he.symm)

end InteractingSLE.Restart.RetAux79
