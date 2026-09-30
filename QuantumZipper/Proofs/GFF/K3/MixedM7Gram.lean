import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# K3-mixed M7-c ingredient: families with equal Gram matrices

If two families `f : ι → E`, `f' : ι → F` in real inner product spaces have the same Gram matrix,
`⟪f i, f j⟫ = ⟪f' i, f' j⟫`, then there is a linear isometry from the closed span of `f` into `F`
(complete) sending `f i` to `f' i` (`exists_linearIsometry_closure_of_gram`).

In M7-c (see `MixedM7Nodes.lean`) this identifies the local parts of the mixed and the free Hilbert
spaces: the generators `v_μ − v_{bal μ}` (mixed) and `v̂_μ − v̂_{bal μ}` (free), `μ` carried by
`closedBall t r'`, both have Gram matrix `kernelCov (halfDiscGreen t r)` (M7-a and L2).

Own elementary proof (standard fact; cost rule of AGENT_GUIDE): define the map on finite linear
combinations (`Finsupp.linearCombination`), which preserves norms by the Gram identity, and extend
it by density with mathlib's `LinearMap.extendOfIsometry`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace QuantumZipper.K3

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Finite linear combinations of two families with the same Gram matrix have the same inner
products. -/
theorem inner_linearCombination_eq_of_gram {f : ι → E} {f' : ι → F}
    (h : ∀ i j, ⟪f i, f j⟫ = ⟪f' i, f' j⟫) (a b : ι →₀ ℝ) :
    ⟪Finsupp.linearCombination ℝ f a, Finsupp.linearCombination ℝ f b⟫ =
      ⟪Finsupp.linearCombination ℝ f' a, Finsupp.linearCombination ℝ f' b⟫ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    real_inner_smul_left, real_inner_smul_right, h]

/-- Finite linear combinations of two families with the same Gram matrix have the same norm. -/
theorem norm_linearCombination_eq_of_gram {f : ι → E} {f' : ι → F}
    (h : ∀ i j, ⟪f i, f j⟫ = ⟪f' i, f' j⟫) (a : ι →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ f' a‖ = ‖Finsupp.linearCombination ℝ f a‖ := by
  have e := inner_linearCombination_eq_of_gram h a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at e
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e.symm

/-- **Gram isometry.** Two families with the same Gram matrix are related by a linear isometry
from the closed span of the first into the (complete) second space; its range lies in the closed span of the second family. -/
theorem exists_linearIsometry_closure_of_gram [CompleteSpace F] (f : ι → E) (f' : ι → F)
    (h : ∀ i j, ⟪f i, f j⟫ = ⟪f' i, f' j⟫) :
    ∃ J : (Submodule.span ℝ (Set.range f)).topologicalClosure →ₗᵢ[ℝ] F,
      (∀ i, J ⟨f i, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)⟩ = f' i) ∧
      ∀ x, J x ∈ (Submodule.span ℝ (Set.range f')).topologicalClosure := by
  set S := Submodule.span ℝ (Set.range f) with hS
  set K := S.topologicalClosure with hK
  set L := Finsupp.linearCombination ℝ f with hL
  have hLS : ∀ a, L a ∈ S := fun a => by
    rw [hS, ← Finsupp.range_linearCombination]; exact ⟨a, rfl⟩
  set e : (ι →₀ ℝ) →ₗ[ℝ] K := L.codRestrict K
    (fun a => Submodule.le_topologicalClosure S (hLS a)) with he
  have hdense : DenseRange e := by
    rw [denseRange_iff_closure_range,
      Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.eq_univ_iff_forall]
    intro x
    have hrange : Subtype.val '' Set.range e = (S : Set E) := by
      ext y
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact hLS a
      · intro hy
        rw [hS, ← Finsupp.range_linearCombination] at hy
        obtain ⟨a, rfl⟩ := hy
        exact ⟨e a, ⟨a, rfl⟩, rfl⟩
    show (x : E) ∈ closure (Subtype.val '' Set.range e)
    rw [hrange]
    exact x.2
  have hnorm : ∀ a, ‖Finsupp.linearCombination ℝ f' a‖ = ‖e a‖ := fun a =>
    norm_linearCombination_eq_of_gram h a
  refine ⟨(Finsupp.linearCombination ℝ f').extendOfIsometry hdense hnorm, fun i => ?_, fun x => ?_⟩
  swap
  · refine hdense.induction_on x ?_ fun a => ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage
        ((Finsupp.linearCombination ℝ f').extendOfIsometry hdense hnorm).continuous
    · show _ ∈ _
      rw [LinearMap.extendOfIsometry_eq]
      refine Submodule.le_topologicalClosure _ ?_
      rw [← Finsupp.range_linearCombination]
      exact ⟨a, rfl⟩
  have hei : e (Finsupp.single i 1) =
      ⟨f i, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)⟩ := by
    ext
    simp [he, hL]
  rw [← hei, LinearMap.extendOfIsometry_eq]
  simp

/-- A vector orthogonal to every member of a family is orthogonal to its closed span. -/
theorem inner_eq_zero_of_mem_closure_span_of_forall {f : ι → E} {v : E}
    (hv : ∀ i, ⟪v, f i⟫ = 0) {u : E}
    (hu : u ∈ (Submodule.span ℝ (Set.range f)).topologicalClosure) : ⟪v, u⟫ = 0 := by
  have hcl : IsClosed {u : E | ⟪v, u⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hspan : ∀ u ∈ Submodule.span ℝ (Set.range f), ⟪v, u⟫ = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hv i
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]
  exact closure_minimal hspan hcl hu

/-- Pythagoras for an orthogonal projection, polarized:
`⟪x, y⟫ = ⟪P x, P y⟫ + ⟪x − P x, y − P y⟫`. -/
theorem inner_eq_inner_proj_add_inner_sub_proj (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (x y : E) :
    ⟪x, y⟫ = ⟪K.orthogonalProjectionOnto x, K.orthogonalProjectionOnto y⟫ +
      ⟪x - K.starProjection x, y - K.starProjection y⟫ := by
  have h1 := K.starProjection_inner_eq_zero x (K.starProjection y) (K.starProjection_apply_mem y)
  have h2 := K.starProjection_inner_eq_zero y (K.starProjection x) (K.starProjection_apply_mem x)
  rw [real_inner_comm] at h2
  have e : ⟪(K.orthogonalProjectionOnto x : K), K.orthogonalProjectionOnto y⟫ =
      ⟪K.starProjection x, K.starProjection y⟫ := rfl
  rw [e]
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  conv_lhs => rw [hx, inner_add_left]
  conv_lhs => rw [show y = K.starProjection y + (y - K.starProjection y) by abel]
  rw [inner_add_right, inner_add_right, h1, h2]
  ring

end QuantumZipper.K3
