/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.LightCone

/-!
# Proposition 5.13: a countable representation of the rooted descendant cones

Packet PROVE-PROP513C. An enumeration of the finite prefixes supplies paths `η n`,
deterministic terminal times `τ n`, and an enumeration `d n m` of the descendants
of prefix `n`. Only the post-`τ n` portions of those descendants enter its cone.
The representation includes the root as a constant path and rescales each portion
to `[0,1]`. Evaluation measurability of the enumerated paths then gives measurable
node endpoints and hitting-measurable cones.

This representation does not assert that an arbitrary staged driver family has
such measurable trace paths; that extraction remains a separate input.
-/

set_option autoImplicit false

noncomputable section

open Set Topology MeasureTheory

namespace InteractingSLE.Sec5

/-- The endpoint of an enumerated finite extreme-angle prefix. -/
def extremeAngleTreeNode {Ω : Type*} (η : ℕ → Ω → ℝ → ℂ) (τ : ℕ → ℝ)
    (n : ℕ) (ω : Ω) : ℂ := η n ω (τ n)

/-- The post-terminal portions of the enumerated descendants of a prefix. -/
def extremeAngleTreeDescendants {Ω : Type*} (η : ℕ → Ω → ℝ → ℂ)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) (ω : Ω) : Set ℂ :=
  ⋃ m, η (d n m) ω '' Ioc (τ n) (τ (d n m))

/-- The closed descendant cone, including the root, from the proof of Prop. 5.13. -/
def extremeAngleTreeCone {Ω : Type*} (η : ℕ → Ω → ℝ → ℂ)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) (ω : Ω) : Set ℂ :=
  closure (insert (extremeAngleTreeNode η τ n ω)
    (extremeAngleTreeDescendants η τ d n ω))

/-- The constant root path followed by the rescaled post-terminal descendants. -/
def extremeAngleTreeNodePath {Ω : Type*} (η : ℕ → Ω → ℝ → ℂ)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → Ω → ℝ → ℂ
  | 0, ω, _ => extremeAngleTreeNode η τ n ω
  | m + 1, ω, s => η (d n m) ω (τ n + (τ (d n m) - τ n) * s)

/-- Affine rescaling preserves precisely the indicated closed path portion. -/
theorem image_rescaled_Icc {η : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    (fun s => η (a + (b - a) * s)) '' Icc 0 1 = η '' Icc a b := by
  have hlin : ContinuousOn (fun s : ℝ => a + (b - a) * s) (Icc 0 1) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨_, ⟨?_, ?_⟩, rfl⟩ <;> nlinarith only [hab, hs.1, hs.2]
  · rintro ⟨t, ht, rfl⟩
    have ht' : t ∈ Icc (a + (b - a) * 0) (a + (b - a) * 1) := by
      simpa only [mul_zero, add_zero, mul_one, add_sub_cancel] using ht
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hlin ht'
    exact ⟨s, hs, congrArg η he⟩

/-- The rooted cone is the closure of a countable union of unit-interval path
ranges, with index zero reserved for its root. -/
theorem extremeAngleTree_node_closure_eq_iUnion_pathRange {Ω : Type*}
    (η : ℕ → Ω → ℝ → ℂ) (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ)
    (hτ : ∀ n m, τ n ≤ τ (d n m))
    (hroot : ∀ n m ω, η (d n m) ω (τ n) = extremeAngleTreeNode η τ n ω)
    (n : ℕ) (ω : Ω) :
    extremeAngleTreeCone η τ d n ω =
      closure (⋃ m, extremeAngleTreeNodePath η τ d n m ω '' Icc 0 1) := by
  unfold extremeAngleTreeCone
  congr 1
  ext z
  constructor
  · rintro (rfl | hz)
    · exact mem_iUnion.2 ⟨0, 0, by norm_num, rfl⟩
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hz
      exact mem_iUnion.2 ⟨m + 1,
        (image_rescaled_Icc (hτ n m)).symm ▸ image_mono Ioc_subset_Icc_self hm⟩
  · rintro hz
    obtain ⟨m, hm⟩ := mem_iUnion.1 hz
    cases m with
    | zero =>
        obtain ⟨s, _, rfl⟩ := hm
        exact mem_insert _ _
    | succ m =>
        obtain ⟨t, ht, rfl⟩ := image_rescaled_Icc (hτ n m) ▸ hm
        rcases eq_or_lt_of_le ht.1 with he | he
        · rw [← he, hroot n m ω]
          exact mem_insert _ _
        · exact mem_insert_of_mem _ (mem_iUnion.2 ⟨m, t, ⟨he, ht.2⟩, rfl⟩)

/-- Measurable evaluations of the prefix paths give measurable node endpoints. -/
theorem measurable_extremeAngleTreeNode {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {η : ℕ → Ω → ℝ → ℂ} (hη : ∀ n t, Measurable[𝒢] fun ω => η n ω t)
    (τ : ℕ → ℝ) (n : ℕ) : Measurable[𝒢] (extremeAngleTreeNode η τ n) :=
  hη n (τ n)

/-- The countable representation makes every rooted cone hitting-measurable. -/
theorem measurable_extremeAngleTreeCone {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    {η : ℕ → Ω → ℝ → ℂ} (hη : ∀ n t, Measurable[𝒢] fun ω => η n ω t)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ : ∀ n m, τ n ≤ τ (d n m))
    (hroot : ∀ n m ω, η (d n m) ω (τ n) = extremeAngleTreeNode η τ n ω)
    (hc : ∀ n m ω, ContinuousOn (η (d n m) ω) (Icc (τ n) (τ (d n m))))
    (n : ℕ) : @Measurable Ω (Set ℂ) 𝒢 hittingSigma (extremeAngleTreeCone η τ d n) := by
  have hm : ∀ m t, Measurable[𝒢] fun ω => extremeAngleTreeNodePath η τ d n m ω t := by
    rintro (_ | m) t
    · exact hη n (τ n)
    · exact hη (d n m) _
  have hcont : ∀ m ω, ContinuousOn (extremeAngleTreeNodePath η τ d n m ω) (Icc 0 1) := by
    rintro (_ | m) ω
    · exact continuousOn_const
    · refine (hc n m ω).comp
        (continuous_const.add (continuous_const.mul continuous_id)).continuousOn ?_
      intro s hs
      constructor <;> nlinarith only [hτ n m, hs.1, hs.2]
  have heq : extremeAngleTreeCone η τ d n = fun ω =>
      closure (⋃ m, extremeAngleTreeNodePath η τ d n m ω '' Icc 0 1) :=
    funext (extremeAngleTree_node_closure_eq_iUnion_pathRange η τ d hτ hroot n)
  rw [heq]
  exact measurable_closure_iUnion_image hm hcont

end InteractingSLE.Sec5
