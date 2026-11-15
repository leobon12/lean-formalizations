/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXLanding

/-! # Transfer constant unit-space access data to an actual selected sample -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61FibData
variable {X : Type*} {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}

/-- Constant unit data define the same selected chart path as the actual sample. -/
theorem inPath_unit_eq {x : X} (hx : x ∈ E) :
    inPath (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) () =
      inPath E c ρ T x := by
  funext v
  simp only [inPath, mem_univ, hx, true_and]

/-- The two descriptions have the same exit time for every window. -/
theorem exitTime_unit_eq {x : X} (hx : x ∈ E) (V : Set ℂ) :
    Aux61FibData.exitTime (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) V () =
      Aux61FibData.exitTime E c ρ T V x := by
  unfold Aux61FibData.exitTime
  congr 1
  funext a
  have hm : () ∈ winEv (univ : Set Unit) (fun _ => c x) (fun _ => ρ x) (fun _ => T x) V a ↔
      x ∈ winEv E c ρ T V a := by
    simp only [winEv, mem_ofPred_eq, mem_univ, hx, true_and, inPath_unit_eq hx]
  rw [hm]

end InteractingSLE.Sec5.Aux61SlitWAA
