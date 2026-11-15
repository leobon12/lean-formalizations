import InteractingSLE.Spec.Sec5.Aux61RestartMarkFlow

/-!
# Original-target protection on the glued space

Packet PROVE-AUX61-R1. The existing Borel good-hitting certificate transfers
target protection to the glued space. No measurability of an existential
real-ODE witness is required.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open QuantumZipper (fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 CfRegQ Prop411Q Cond44Ref

/-- Every finite stopped hull of a good hitting history protects the
physical original target 1 in Q. -/
theorem original_target_protected_of_goodHit
    {y : HistorySpace 0 0} (hy : y ∈ goodHitSet) (s : ℝ≥0) :
    (1 : ℂ) ∉ closure (negInv '' fwdHull (cfDrv0 s y) s) := by
  have heq : fwdHull (cfDrv0 s y) s = fwdHull (cfDrv y) s :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_cfDrv0 s y)
      (reg_of_mem_goodCfSet hy.1).2.1 s.coe_nonneg fun _ ht => cfDrv0_eq_cfDrv hy.1 ht
  rw [heq]
  apply original_target_not_mem_closure_negInv_image
  intro hmem
  have hzero := (isClosed_negInv_fwdHull_of_mem_goodHitSet hy s.coe_nonneg).2
    (-1 : ℂ) hmem (by norm_num)
  norm_num at hzero

/-- The original right target is protected simultaneously at all finite
retained times, almost surely on the actual glued space. This uses the
already transferred Borel hitting certificate. -/
theorem cfGlueAE_original_target_protected :
    CfGlueAE.{u} fun _ y => ∀ s : ℝ≥0,
      (1 : ℂ) ∉ closure (negInv '' fwdHull (cfDrv0 s y) s) := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC
    Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  filter_upwards [cfGlueAE_mem_goodHitSet κ hκ hκ4 xL xR ρL ρR hF h44 P
    𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk] with p hp s
  exact original_target_protected_of_goodHit hp s

/-- The pointwise form used by the history-component construction. -/
theorem history_original_target_protected_of_goodHit
    {Ω : Type*} {Y : Ω → HistorySpace 0 0}
    (hgood : ∀ ω, Y ω ∈ goodHitSet) (s : ℝ≥0) :
    ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω) :=
  fun ω => original_target_protected_of_goodHit (hgood ω) s

end InteractingSLE.Sec5.Aux61Restart
