/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# Deleting passive marks from announced local evolutions

The deletion lemmas in `Sec4.ZeroMarks` concern maximal integrated evolutions.
Here the same sum and threshold identities give deletion before an arbitrary
local stop, without assuming a continuation through that stop.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux65Neg

open Sec2 Sec4

variable {a : ℝ} {nL nR mL mR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- Passive-mark deletion for a local integrated path. -/
theorem path_compEmb {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {e : ℝ≥0∞}
    (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b e)
    (eL : Fin mL ↪o Fin nL) (eR : Fin mR ↪o Fin nR)
    (hL : ∀ i, i ∉ Set.range eL → ρL i = 0)
    (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsSLEPathUpTo a (fun i => xL (eL i)) (fun j => xR (eR j))
      (fun i => ρL (eL i)) (fun j => ρR (eR j)) w
      (fun i => vL (eL i)) (fun j => vR (eR j)) b e := by
  refine ⟨h.w_zero, fun i => h.vL_zero _, fun j => h.vR_zero _,
    h.continuousOn_w, fun i => h.continuousOn_vL _, fun j => h.continuousOn_vR _,
    fun ht => (h.antitone_vL ht).comp_monotone eL.monotone,
    fun ht i => h.vL_le_w ht _, fun ht j => h.w_le_vR ht _,
    fun ht => (h.monotone_vR ht).comp eR.monotone,
    fun ht i => h.integrable_gapL ht _, fun ht j => h.integrable_gapR ht _,
    fun ht => ?_, fun ht i => h.vL_eq ht _, fun ht j => h.vR_eq ht _,
    fun i => h.volume_collisionL _, fun j => h.volume_collisionR _, fun ht hh => ?_⟩
  · rw [h.w_eq ht,
      sum_comp_embedding eL eL.injective
        (fun i => ∫ s in (0 : ℝ).._, ρL i / (w s.toNNReal - vL i s.toNNReal))
        (fun i hi => by simp only [hL i hi, zero_div, intervalIntegral.integral_zero]),
      sum_comp_embedding eR eR.injective
        (fun j => ∫ s in (0 : ℝ).._, ρR j / (w s.toNNReal - vR j s.toNNReal))
        (fun j hj => by simp only [hR j hj, zero_div, intervalIntegral.integral_zero])]
  · exact h.not_threshold ht
      ((thresholdCondition_compEmb_iff eL.injective eR.injective hL hR _ _ _).1 hh)

/-- Passive-mark deletion preserves the local evolution, its noise, and its stop. -/
theorem evolution_compEmb {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} (h : IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B e)
    (eL : Fin mL ↪o Fin nL) (eR : Fin mR ↪o Fin nR)
    (hL : ∀ i, i ∉ Set.range eL → ρL i = 0)
    (hR : ∀ i, i ∉ Set.range eR → ρR i = 0) :
    IsSLEEvolutionUpTo a (fun i => xL (eL i)) (fun j => xR (eR j))
      (fun i => ρL (eL i)) (fun j => ρR (eR j)) P 𝓕 W
      (fun i => VL (eL i)) (fun j => VR (eR j)) B e :=
  ⟨h.brownian, h.adapted_W, fun _ => h.adapted_VL _, fun _ => h.adapted_VR _,
    h.ae_path.mono fun _ hp => path_compEmb hp eL eR hL hR⟩

end InteractingSLE.Sec5.Aux65Neg
