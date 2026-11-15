import InteractingSLE.Spec.Sec5.Aux61RestartComponent
import InteractingSLE.Spec.Sec6.Prop61Compare

/-!
# Relative boundary limits in the retained component's disc chart

Packet PROVE-AUX61-R1. This is the component adapter to the already proved
prime-end comparison `Sec6.tendsto_comp_of_tendsto_nhdsWithin`. The physical
impression limit is an explicit hypothesis. No identification of the old
harmonic mean on the kissing set is asserted.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

/-- A relative mean vanishing at an old physical boundary point also vanishes
at a restart-chart prime end whose impression is that point. -/
theorem tendsto_relative_mean_at_restart_primeEnd {K L : Set ℂ} {η : ℝ → ℂ}
    {r : ℝ} {b p q : ℂ} {F : ℂ → ℂ} {u : ℂ → ℝ}
    (hF : IsConformalBijection F (ball 0 1) (restartComponent K η r b))
    (hFq : Tendsto F (𝓝[ball 0 1] q) (𝓝 p))
    (hlocal : ∃ ρ > 0, L ∩ ball p ρ ⊆ K ∪ η '' Icc 0 r)
    (hu : Tendsto u (𝓝[H \ L] p) (𝓝 0)) :
    Tendsto (u ∘ F) (𝓝[ball 0 1] q) (𝓝 0) := by
  have hmaps : MapsTo F (ball 0 1) (H \ (K ∪ η '' Icc 0 r)) :=
    fun z hz => connectedComponentIn_subset _ _ (hF.2.mapsTo hz)
  exact Sec6.tendsto_comp_of_tendsto_nhdsWithin hmaps hFq hlocal hu

end InteractingSLE.Sec5.Aux61Restart
