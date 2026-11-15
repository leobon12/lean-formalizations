/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45ClockReference
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCollision

/-! # Automatic reference threshold bound for a precontact trace -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart Sec7.PocketTraversal

/-- An interior positive-time trace cannot reach a geometric force threshold.
At zero only the reference seed condition is needed. The force weights are
arbitrary, and the actual driver need not satisfy a finite-word equation. -/
theorem threshold_of_interior_trace {S : Type u} [MeasurableSpace S] {P : Measure S}
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {W : ℝ≥0 → S → ℝ} {e : S → ℝ≥0∞} {γ : S → ℝ≥0 → ℂ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hg : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (γ ω))
    (hinterior : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < e ω → γ ω t ∈ QuantumZipper.H) :
    ∀ᵐ ω ∂P, e ω ≤ MartChar.thresholdTime ρL ρR (W · ω)
      (fun i t => geomLW W (fun _ => xL) i t ω)
      (fun j t => geomRW W (fun _ => xR) j t ω) := by
  filter_upwards [hg, hinterior] with ω hgω hH
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω →
      ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
        (fun i => geomLW W (fun _ => xL) i t ω)
        (fun j => geomRW W (fun _ => xR) j t ω) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hL : (fun i => geomLW W (fun _ => xL) i 0 ω) = xL :=
        funext fun i => geomLW_zero hWc hW0 (hxL i)
      have hR : (fun j => geomRW W (fun _ => xR) j 0 ω) = xR :=
        funext fun j => geomRW_zero hWc hW0 (hxR j)
      simpa only [hL, hR, hW0] using hseed
    · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
      obtain ⟨hL, hR⟩ := RetAux79.geom_images_ne_of_tip_mem_H (fun _ => xL) (fun _ => xR)
        (hWc ω) (hW0 ω) hgω htpos ht.le (hH t htpos ht)
      exact RetAux79.not_threshold_of_images_ne hL hR
  by_contra hle
  have hlt := lt_of_not_ge hle
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  have hmem := MartChar.thresholdTime_mem_thresholdSet (hWc ω)
    (fun i => (isForcePath_geomLW hWc (fun _ => xL) ω i).1)
    (fun j => (isForcePath_geomRW hWc (fun _ => xR) ω j).1)
    (fun i j s t hst => geomLW_merge hWc (fun _ => xL) ω i j s t hst)
    (fun i j s t hst => geomRW_merge hWc (fun _ => xR) ω i j s t hst) ht.symm
  have hte : (t : ℝ≥0∞) = MartChar.thresholdTime ρL ρR (W · ω)
      (fun i t => geomLW W (fun _ => xL) i t ω)
      (fun j t => geomRW W (fun _ => xR) j t ω) := ht
  exact hnot t (by rw [hte]; exact hlt) hmem

namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- Restriction and agreement transfer the actual generating trace to the
continuous reference driver through the window clock. -/
theorem generatingTrace_of_agree {e : S → ℝ≥0∞} {W : ℝ≥0 → S → ℝ}
    (heU : ∀ ω, e ω ≤ D.U ω)
    (hag : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω) :
    ∀ᵐ ω ∂D.P, IsGeneratingTrace (W · ω) (e ω) (fun t => D.Γ ω t - D.y) := by
  filter_upwards [D.trace, hag] with ω hg hω
  exact StoppedK2.isGeneratingTrace_congr (fun t ht => (hω t ht).symm)
    (LP.isGeneratingTrace_mono hg (heU ω))

end ClockSource
end InteractingSLE.Sec5.Aux61R45
