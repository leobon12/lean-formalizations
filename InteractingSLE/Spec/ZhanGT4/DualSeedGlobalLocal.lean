/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalLinear

/-!
# Localizing the actual regular map field on a seed-band event

Packet PROVE-ZHAN-GT4-A22. Keep the source driver unchanged, use the
actual field on the band event, and use the zero field with singleton
horizon on its complement. No zero generator is imposed on the map.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} {E : Set Ω}

/-- Event localization of a regular drifted field, with no generator premise. -/
theorem seedDriftField_localize (hK : 0 ≤ K)
    (hpt : ∀ ω ∈ E, IsSeedDriftField σ ρ K (atPath B ω) (atPath D ω) (fun _ => b ω)
      ε (fun _ => S ω) (fun _ => ℓ ω) (fun _ => ℓx ω) (fun _ => ℓxx ω)
      (fun _ => ℓxxx ω) (fun _ => ℓt ω)) :
    IsSeedDriftField σ ρ K B D (onEvB E b) ε (onEvS E ε S)
      (onEv E ℓ) (onEv E ℓx) (onEv E ℓxx) (onEv E ℓxxx) (onEv E ℓt) := by
  refine ⟨fun ω => ?_, hK, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_,
    fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_,
    fun ω => ?_, fun ω => ?_⟩ <;>
    by_cases hω : ω ∈ E <;>
    simp only [onEv_of_mem, onEv_of_notMem, onEvB_of_mem, onEvB_of_notMem,
      onEvS_of_mem, onEvS_of_notMem, hω, not_false_eq_true]
  · exact (hpt ω hω).le ()
  · exact le_rfl
  · exact (hpt ω hω).dD ()
  · exact fun t ht => hasDerivWithinAt_Icc_self _ _ ht
  · exact (hpt ω hω).contb ()
  · exact continuousOn_const
  · exact (hpt ω hω).bound_b ()
  · intro t _
    rw [abs_zero]
    exact hK
  · exact (hpt ω hω).dx ()
  · exact fun _ _ => hasDerivAt_const _ _
  · exact (hpt ω hω).dxx ()
  · exact fun _ _ => hasDerivAt_const _ _
  · exact (hpt ω hω).dxxx ()
  · exact fun _ _ => hasDerivAt_const _ _
  · exact (hpt ω hω).dt ()
  · exact fun _ _ => hasDerivWithinAt_const _ _ _
  · exact (hpt ω hω).cont ()
  · exact continuousOn_const
  · exact (hpt ω hω).contX ()
  · exact continuousOn_const
  · exact (hpt ω hω).contXX ()
  · exact continuousOn_const
  · exact (hpt ω hω).contT ()
  · exact continuousOn_const
  · exact (hpt ω hω).bound ()
  · intro _ _
    simp only [abs_zero]
    exact ⟨hK, hK, hK, hK, hK⟩

end InteractingSLE.ZhanGT4
