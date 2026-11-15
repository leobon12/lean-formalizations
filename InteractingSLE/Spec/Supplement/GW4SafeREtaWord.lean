/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanCoords
import InteractingSLE.Spec.Sec7.R5LiftWord

/-! # GW4: the actual typed word on the exposed interval

The geometric force positions have their innermost marks at the two typed
seed indices. Thus R.5's exposed-word identity applies to the actual GW4
positions, without an additional ordering premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Supp8.Q3Stop Supp8.GB6.RelDrv
  Sec7.PhaseSel Sec7.PocketTraversal MartChar

/-- The two seed positions are the innermost positions of the actual
component word, at every relative time. -/
theorem component_force_seed_extrema {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (q : ℝ≥0) :
    (∀ i, componentVL k c₀ X R V i q ω ≤
      componentVL k c₀ X R V (componentSeedL k c₀) q ω) ∧
    ∀ j, componentVR k c₀ X R V (componentSeedR k c₀) q ω ≤
      componentVR k c₀ X R V j q ω := by
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hL : typedXL k (wordType k c₀) c₀ (componentSeedL k c₀) = 0 := by
    rw [typedXL_self_eq]
    exact Sec4.flowLineXL_zero _ _
  have hR : typedXR k (wordType k c₀) c₀ (componentSeedR k c₀) = 0 := by
    rw [typedXR_self_eq]
    exact Sec4.flowLineXR_zero _ _
  constructor
  · intro i
    rw [componentVL_eq_geom k c₀ X R V hRc hR0,
      componentVL_eq_geom k c₀ X R V hRc hR0]
    change -RealFlow.rightImg (fun s => -wpath R ω s)
        (-typedXL k (wordType k c₀) c₀ i) q ≤
      -RealFlow.rightImg (fun s => -wpath R ω s)
        (-typedXL k (wordType k c₀) c₀ (componentSeedL k c₀)) q
    rw [hL, neg_zero]
    exact neg_le_neg (RealFlow.rightImg_mono_index hW.neg q.coe_nonneg
      (neg_nonneg.2 (typedXL_nonpos k (wordType k c₀) c₀ i)))
  · intro j
    rw [componentVR_eq_geom k c₀ X R V hRc hR0,
      componentVR_eq_geom k c₀ X R V hRc hR0]
    change RealFlow.rightImg (wpath R ω)
        (typedXR k (wordType k c₀) c₀ (componentSeedR k c₀)) q ≤
      RealFlow.rightImg (wpath R ω) (typedXR k (wordType k c₀) c₀ j) q
    rw [hR]
    exact RealFlow.rightImg_mono_index hW q.coe_nonneg
      (typedXR_nonneg k (wordType k c₀) c₀ j)

/-- The actual finite force word has the two canonical heights throughout
the exposed interval. -/
theorem component_forceData_exposed {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (q : ℝ≥0) {ξ : ℝ}
    (hξ : ξ ∈ Ioo
      (componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω)
      (componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω)) :
    forceBoundaryData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
      (fun i => componentVL k c₀ X R V i q ω - R q ω)
      (fun j => componentVR k c₀ X R V j q ω - R q ω) ξ =
        if ξ < 0 then -(Real.pi / Real.sqrt k) else Real.pi / Real.sqrt k := by
  obtain ⟨hL, hR⟩ := component_force_seed_extrema k c₀ X R V hRc hR0 q
  exact Sec7.R5Lift.forceBoundaryData_between _ _
    (fun i => sub_le_sub_right (hL i) _) (fun j => sub_le_sub_right (hR j) _) hξ

/-- Adding the common phase changes both actual exposed heights by the
same amount. No ambient lift identification is used in this word identity. -/
theorem component_phaseData_exposed {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (q : ℝ≥0) (δ : ℝ) {ξ : ℝ}
    (hξ : ξ ∈ Ioo
      (componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω)
      (componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω)) :
    phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
      (fun i => componentVL k c₀ X R V i q ω - R q ω)
      (fun j => componentVR k c₀ X R V j q ω - R q ω) δ ξ =
        (if ξ < 0 then -(Real.pi / Real.sqrt k) else Real.pi / Real.sqrt k) + δ := by
  exact (Sec7.R5Lift.phaseData_exposed _ _ δ hξ).trans
    (congrArg (fun a : ℝ => a + δ) (component_forceData_exposed k c₀ X R V hRc hR0 q hξ))

end InteractingSLE.Theorem14.GW4Fix
