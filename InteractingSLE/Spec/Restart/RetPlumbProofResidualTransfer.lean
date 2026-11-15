/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualSafe
import InteractingSLE.Spec.Sec7.PocketMartLife

/-!
# Safe laws for the continuous adapted stopped version

Packet PROVE-RETPLUMB. Both K2 safe inputs only see the driver before its
lifetime. Transfer them to the explicit continuous adapted stopped reader,
using the landed congruences for killed driving data and geometric force images.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open DomainMarkov DomainMarkov.K2 Coupling Sec7.PocketTraversal
open LQGMetric (DistOn TestOn)
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω} {V : Ω → ℝ≥0∞}
    {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W W' : ℝ≥0 → Ω → ℝ}
    {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens}

omit mΩ in
/-- Agreement of continuous drivers before death gives agreement of all their
geometric force images there. -/
theorem agreeBefore_geom_of_eq {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hc : ∀ ω, Continuous fun q => W q ω)
    (he : ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V ω → W' q ω = W q ω) :
    StoppedK2.AgreeBefore V W (geomLW W xL) (geomRW W xR) W' (geomLW W' xL) (geomRW W' xR) := by
  intro ω q hq
  have hpre : ∀ s ≤ q, W' s ω = W s ω :=
    fun s hs => he ω s ((ENNReal.coe_le_coe.2 hs).trans_lt hq)
  exact ⟨he ω q hq, fun i => Sec7.PocketMartLife.geomLW_congr (hc ω) hpre xL i,
    fun j => Sec7.PocketMartLife.geomRW_congr (hc ω) hpre xR j⟩

/-- The safe Gaussian law is invariant under a change of driver and force
coordinates after their lifetime. -/
theorem hasSafeLaw_congr_before
    (he : StoppedK2.AgreeBefore V W VL VR W' VL' VR')
    (hS : HasSafeLaw κ ρL ρR P 𝓗 F V W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓗 F V W' VL' VR' X := by
  intro ψ q D hD hs
  have hs' : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ ω ∈ avoidSet W V ψ q := by
    filter_upwards [hs] with ω hω hωD
    exact ⟨(hω hωD).1, (StoppedK2.mem_avoidSet_congr he ψ q ω).1 (hω hωD).2⟩
  apply (hS ψ q D hD hs').trans
  apply setIntegral_congr_ae (𝓗.le q _ hD)
  filter_upwards [hs] with ω hω hωD
  exact (StoppedK2.cfAt_congr_of_agree he ψ (hω hωD).2.1).symm

/-- The safe member identities are invariant under a post-lifetime change of
the driver. The hull congruence is the landed pre-lifetime congruence. -/
theorem hasSafeMembers_congr_before
    (he : ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V ω → W' q ω = W q ω)
    (hL : HasSafeMembers P 𝓗 F V W X) : HasSafeMembers P 𝓗 F V W' X := by
  intro s Fb hFb D hD hs
  apply hL s Fb hFb D hD
  filter_upwards [hs] with ω hω hωD
  obtain ⟨hF, hV, hdj⟩ := hω hωD
  refine ⟨hF, hV, ?_⟩
  rwa [DomainMarkov.fwdHull_rpath_congr_of_lt (he ω) hV] at hdj

/-- Construct an adapted safe version once killed-driver observability is
available. No measurability of the chosen post-lifetime extension is assumed. -/
theorem exists_adapted_safe_version {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hc : ∀ ω, Continuous fun q => W q ω) (h0 : ∀ ω, W 0 ω = 0)
    (ha : AdaptedBefore 𝓗 V W)
    (hS : HasSafeLaw κ ρL ρR P 𝓗 F V W (geomLW W xL) (geomRW W xR) X)
    (hL : HasSafeMembers P 𝓗 F V W X) :
    ∃ W' : ℝ≥0 → Ω → ℝ, (∀ ω, W' 0 ω = 0) ∧
      (∀ ω, Continuous fun q => W' q ω) ∧ StronglyAdapted 𝓗 W' ∧
      (∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V ω → W' q ω = W q ω) ∧
      HasSafeLaw κ ρL ρR P 𝓗 F V W' (geomLW W' xL) (geomRW W' xR) X ∧
      HasSafeMembers P 𝓗 F V W' X := by
  obtain ⟨W', hW0, hWc, hWa, he⟩ := exists_continuous_adapted_stopped hc h0 ha
  exact ⟨W', hW0, hWc, hWa, he,
    hasSafeLaw_congr_before (agreeBefore_geom_of_eq hc he) hS,
    hasSafeMembers_congr_before he hL⟩

end InteractingSLE.Restart.RetAux79
