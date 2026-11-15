/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR10Evolution
import InteractingSLE.Spec.Supplement.GW2JDetR10StoppedNear

/-!
# The reference evolution can be fixed before choosing the buffer

DS3 applied to a constant word and a constant sequence of laws identifies
the buffered reach probabilities of any two reference evolutions. Thus
buffer-dependent continuations do not require buffer-dependent choices
of the near-crossing family's sequence.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem.RootN4 Supp12.DS2 Supp12.DSReach

/-- Constant-word DS3 compares any two realizations, including coincident
seed starts. This reuses the proved entrance theorem. -/
theorem reach_probability_le_of_same_word {κ : ℝ} (hκ : 0 < κ)
    {nL nR mL mR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR)
    {Rw ε g η : ℝ} (hε : 0 < ε) (hg : 0 < g) (hη : 0 < η)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hxL0 : xL ⟨0, hnL⟩ = 0) (hxR0 : xR ⟨0, hnR⟩ = 0)
    (hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hxR : ∀ j, xR j ≠ 0 → η ≤ xR j)
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR)
    (e f : EvolutionData.{u} nL nR)
    (hE : e.IsEvolution κ xL ρL xR ρR) (hF : f.IsEvolution κ xL ρL xR ρR)
    (T : ℝ≥0) (R : ℝ) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (hO : IsOpen O) (hB : IsOpen Bf)
    (hBR : ∀ p ∈ Bf, InBuffer mL mR R g p) :
    e.P (reachEvent T O Bf e.W e.VL e.VR e.lifetime) ≤
      f.P (reachEvent T O Bf f.W f.VL f.VR f.lifetime) := by
  let : MeasurableSpace e.Ω := e.mΩ
  let : MeasurableSpace f.Ω := f.mΩ
  have h := ds3ReachStatement κ hκ hnL hnR mL mR Rw ε g η hε hg hη
    xL xR (fun _ => ρL) (fun _ => ρR) ρL ρR hxL0 hxR0 hxL hxR
    (fun _ => hw) hw tendsto_const_nhds tendsto_const_nhds
    (fun _ => f.Ω) (fun _ => f.P) (fun _ => f.filtration) (fun _ => f.W)
    (fun _ => f.VL) (fun _ => f.VR) (fun _ => f.B) (fun _ => f.lifetime)
    (fun _ => hF) e.P e.filtration e.W e.VL e.VR e.B e.lifetime hE T R O Bf hO hB hBR
  simpa only [liminf_const] using h

/-- The buffered reach probability is independent of the realization of
the fixed near-extreme word. A single reference sequence therefore works
for every buffer used in the retained-history comparison. -/
theorem reach_probability_eq_of_same_word {κ : ℝ} (hκ : 0 < κ)
    {nL nR mL mR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR)
    {Rw ε g η : ℝ} (hε : 0 < ε) (hg : 0 < g) (hη : 0 < η)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hxL0 : xL ⟨0, hnL⟩ = 0) (hxR0 : xR ⟨0, hnR⟩ = 0)
    (hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hxR : ∀ j, xR j ≠ 0 → η ≤ xR j)
    (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR)
    (e f : EvolutionData.{u} nL nR)
    (hE : e.IsEvolution κ xL ρL xR ρR) (hF : f.IsEvolution κ xL ρL xR ρR)
    (T : ℝ≥0) (R : ℝ) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (hO : IsOpen O) (hB : IsOpen Bf)
    (hBR : ∀ p ∈ Bf, InBuffer mL mR R g p) :
    e.P (reachEvent T O Bf e.W e.VL e.VR e.lifetime) =
      f.P (reachEvent T O Bf f.W f.VL f.VR f.lifetime) :=
  le_antisymm
    (reach_probability_le_of_same_word hκ hnL hnR hε hg hη hxL0 hxR0 hxL hxR
      hw e f hE hF T R O Bf hO hB hBR)
    (reach_probability_le_of_same_word hκ hnL hnR hε hg hη hxL0 hxR0 hxL hxR
      hw f e hF hE T R O Bf hO hB hBR)

end InteractingSLE.Theorem14.GW2JDetR10
