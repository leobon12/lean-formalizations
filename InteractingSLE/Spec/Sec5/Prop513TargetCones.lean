/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetLaw

/-! # Measurable versions of the capacity-coordinate descendant cones

Only the post-terminal portions are inverted. Their continuity is needed
almost surely; the unit-interval decoder supplies everywhere continuous versions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract

/-- The Q tree read in the counterflow capacity chart. -/
def capacityTree {Ω : Type*} (ξ : ℕ → Ω → ℝ → ℂ) : ℕ → Ω → ℝ → ℂ :=
  fun n ω t => infinitySourceChart.1 (ξ n ω t)

theorem measurable_capacityTree {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {ξ : ℕ → Ω → ℝ → ℂ} (hξ : ∀ n t, Measurable[𝒢] fun ω => ξ n ω t) :
    ∀ n t, Measurable[𝒢] fun ω => capacityTree ξ n ω t :=
  fun n t => (hξ n t).inv.neg

/-- Continuous post-terminal portions suffice for a hitting-measurable version
of each cone, without an assumption about continuity at the inverted seed. -/
theorem exists_measurable_cones {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝒢 : MeasurableSpace Ω} {η : ℕ → Ω → ℝ → ℂ}
    (hm : ∀ n t, Measurable[𝒢] fun ω => η n ω t)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ : ∀ n m, τ n ≤ τ (d n m))
    (hroot : ∀ n m ω, η (d n m) ω (τ n) = extremeAngleTreeNode η τ n ω)
    (hc : ∀ᵐ ω ∂P, ∀ n m, ContinuousOn (η (d n m) ω) (Icc (τ n) (τ (d n m)))) :
    ∃ L : ℕ → Ω → Set ℂ,
      (∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n)) ∧
      ∀ᵐ ω ∂P, ∀ n, L n ω = extremeAngleTreeCone η τ d n ω := by
  let p := extremeAngleTreeNodePath η τ d
  have hpm : ∀ n m t, Measurable[𝒢] fun ω => p n m ω t := by
    rintro n (_ | m) t
    · exact hm n (τ n)
    · exact hm (d n m) _
  have hpc : ∀ n m, ∀ᵐ ω ∂P, ContinuousOn (p n m ω) (Icc 0 1) := by
    rintro n (_ | m)
    · exact Eventually.of_forall fun _ => continuousOn_const
    · filter_upwards [hc] with ω hω
      refine (hω n m).comp
        (continuous_const.add (continuous_const.mul continuous_id)).continuousOn ?_
      intro s hs
      constructor <;> nlinarith only [hτ n m, hs.1, hs.2]
  have hex := fun n m => @exists_continuous_prefix_version Ω mΩ P 𝒢 (p n m)
    (hpm n m) 1 one_pos (hpc n m)
  choose r hrm hrc hre using hex
  refine ⟨fun n ω => closure (⋃ m, r n m ω '' Icc 0 1), fun n =>
    measurable_closure_iUnion_image (hrm n) (fun m ω => (hrc n m ω).continuousOn), ?_⟩
  have he : ∀ᵐ ω ∂P, ∀ n m, EqOn (r n m ω) (p n m ω) (Icc 0 1) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun m => hre n m
  filter_upwards [he] with ω hω n
  rw [extremeAngleTree_node_closure_eq_iUnion_pathRange η τ d hτ hroot]
  congr 1
  exact iUnion_congr fun m => (hω n m).image_eq

/-- The cone version needed after inverting a tree whose positive-time points
avoid the inversion pole. -/
theorem exists_measurable_capacity_cones {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝒢 : MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ → ℂ}
    (hm : ∀ n t, Measurable[𝒢] fun ω => ξ n ω t)
    (hcont : ∀ n ω, Continuous (ξ n ω))
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ0 : ∀ n, 0 < τ n)
    (hτ : ∀ n m, τ n ≤ τ (d n m))
    (hroot : ∀ n m ω, ξ (d n m) ω (τ n) = extremeAngleTreeNode ξ τ n ω)
    (hno : ∀ᵐ ω ∂P, ∀ n t, 0 < t → t ≤ τ n → ξ n ω t ≠ 0) :
    ∃ L : ℕ → Ω → Set ℂ,
      (∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n)) ∧
      ∀ᵐ ω ∂P, ∀ n, L n ω = extremeAngleTreeCone (capacityTree ξ) τ d n ω := by
  apply @exists_measurable_cones Ω mΩ P 𝒢 (capacityTree ξ) (measurable_capacityTree hm) τ d hτ
    (fun n m ω => congrArg infinitySourceChart.1 (hroot n m ω))
  filter_upwards [hno] with ω hω n m
  exact ((hcont (d n m) ω).continuousOn.inv₀
    (fun t ht => hω (d n m) t ((hτ0 n).trans_le ht.1) ht.2)).neg

end InteractingSLE.Sec5.Prop513Target
