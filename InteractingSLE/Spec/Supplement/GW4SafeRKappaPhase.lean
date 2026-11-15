/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaTime
import InteractingSLE.Spec.Supplement.GW4SafeRThetaCompare

/-! # GW4: the actual common lattice phase, including the source inversions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar.RealFlow Sec7.PhaseSel

/-- The actual physical charts determine a phase process constant in time
and in the RepD lattice. Its lift comparison includes the fixed two-source
inversion term, so a winding integer `n` gives the lattice integer `-n-1`.
No mean-representation or reflected-time-branch hypothesis is assumed. -/
theorem exists_component_lattice_phase {Ω : Type*} [MeasurableSpace Ω]
    {F : Frame} (hF : F.IsOk) {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {ν : Measure Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) (k : ℝ) :
    ∃ d : ℝ≥0 → Ω → ℝ,
      (∀ ω, ∃ j : ℤ, ∀ q, d q ω = j * phaseStep k) ∧
      ∀ᵐ ω ∂ν, ∀ t q : ℝ≥0, F.ent (fun r => Wd r ω) ≤ t →
        (t : ℝ≥0∞) < F.exit (fun r => Wd r ω) → 0 < q → (q : ℝ≥0∞) < V ω →
        (q : ℝ) = F.rcap (fun r => Wd r ω) t → ∀ ξ ∈ Ioo
          (-rightImg (fun s : ℝ => -R s.toNNReal ω) 0 q - R q ω)
          (rightImg (fun s : ℝ => R s.toNNReal ω) 0 q - R q ω),
        Tendsto (fun y => chiC k *
          ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal ω) q).2.2
            ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal ω) q).2.1 y) -
          (logDerivFwd (fun s : ℝ => Wd s.toNNReal ω) t
            ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal ω) q).2.1 y)).im) +
          2 * Real.pi * chiC k) (𝓝[H] (ξ : ℂ)) (𝓝 (d q ω)) := by
  classical
  let P : Ω → ℤ → Prop := fun ω n => ∀ t q : ℝ≥0,
    F.ent (fun r => Wd r ω) ≤ t → (t : ℝ≥0∞) < F.exit (fun r => Wd r ω) →
    0 < q → (q : ℝ≥0∞) < V ω → (q : ℝ) = F.rcap (fun r => Wd r ω) t →
    ∀ ξ ∈ Ioo (-rightImg (fun s : ℝ => -R s.toNNReal ω) 0 q - R q ω)
      (rightImg (fun s : ℝ => R s.toNNReal ω) 0 q - R q ω),
    Tendsto (fun y =>
      (componentAmbientChart F.c (fun s : ℝ => R s.toNNReal ω) q).2.2
        ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal ω) q).2.1 y) -
      (logDerivFwd (fun s : ℝ => Wd s.toNNReal ω) t
        ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal ω) q).2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n))
  have hExists : ∀ᵐ ω ∂ν, ∃ n, P ω n := by
    filter_upwards [hGTae, hver.1.1.2.2.2.2] with ω hω hHull
    exact Frame.exists_time_common_current_phase_int hF (hGT ω hω)
      (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω) hHull
  let N : Ω → ℤ := fun ω => if h : ∃ n, P ω n then h.choose else 0
  refine ⟨fun _ ω => ((-N ω - 1 : ℤ) : ℝ) * phaseStep k, fun ω => ⟨-N ω - 1, fun _ => rfl⟩, ?_⟩
  filter_upwards [hExists] with ω hω t q htEnt htExit hq hqV hqt ξ hξ
  have hN : P ω (N ω) := by
    dsimp only [N]
    rw [dite_eq_left hω]
    exact hω.choose_spec
  have h := ((hN t q htEnt htExit hq hqV hqt ξ hξ).const_mul (chiC k)).add_const
    (2 * Real.pi * chiC k)
  rwa [component_phase_offset] at h

end InteractingSLE.Theorem14.GW4Fix
