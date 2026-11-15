/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux4EntranceTight
import InteractingSLE.Spec.Sec2.JacobiLaw
import InteractingSLE.Foundations.Measure.Tightness

/-!
# Aux. lemma 4, VI: weak convergence of the entrance-path laws in the weights

Packet PROVE-T14-DS3. Aux. lemma 4 (spec p. 28): "these stationary path laws are tight on `C_loc(ℝ, [0,1])`. The
martingale problem passes to every subsequential limit, and weak uniqueness for the Jacobi equation, with the limiting
invariant initial law, identifies that limit. Therefore `U^{(n)} ⇒ U`". Here, for the entrance paths
`V(y) = y U(log y)` on `[0, R]` (`Aux4.vPath`): tightness is `isTightMeasureSet_vLaw`; every subsequential limit is
identified through its finite-dimensional laws, which are determined by mixed moments on cubes
(`map_eq_of_moments`, the argument of the landed `Sec2.Jacobi.IsJacobiMP.map_eq` for any finite index type), and the
mixed moments converge (`tendsto_integral_prodPow`, the convergence counterpart of the landed moment uniqueness).

* `map_eq_of_moments`: two random vectors in `[0, 1]^ι` with the same mixed moments have the same law;
* `eq_of_fdd_eq`: two Borel probability measures on `C([0, R])` with the same finite-dimensional laws along a dense
  sequence of levels are equal (an injective continuous map into `ℝ^ℕ` is a measurable embedding; projective limits
  are unique);
* **`tendsto_vLaw`**: if `U^{(m)}` solve the Jacobi martingale problem with parameters `(κ, a_m, b_m) → (κ, a, b)` and
  `U` with `(κ, a, b)`, the laws of their entrance paths converge weakly on `C([0, R])`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology BoundedContinuousFunction
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2.Jacobi

/-! ### Laws on cubes are determined by mixed moments -/

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cube `[0, 1]^ι`. -/
def cubeI (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

omit [Fintype ι] [DecidableEq ι] in
theorem isClosed_cubeI : IsClosed (cubeI ι) := by
  simp only [cubeI, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)

instance : CompleteSpace (cubeI ι) := isClosed_cubeI.completeSpace_coe

/-- The coordinates on the cube. -/
def coordI (i : ι) : cubeI ι →ᵇ ℝ :=
  mkOfBound ⟨fun x => (x : ι → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩ 1
    fun x y => by
      have hx := x.2 i
      have hy := y.2 i
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

omit [Fintype ι] [DecidableEq ι] in
theorem coordI_apply (i : ι) (x : cubeI ι) : coordI i x = (x : ι → ℝ) i := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem star_coordI (i : ι) : star (coordI i) = coordI i := by
  ext x
  simp [coordI_apply]

theorem exists_monomial_of_mem_closureI {g : cubeI ι →ᵇ ℝ}
    (hg : g ∈ Submonoid.closure (range (coordI (ι := ι)))) :
    ∃ k : ι → ℕ, ∀ x : cubeI ι, g x = ∏ i, (x : ι → ℝ) i ^ k i := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    refine ⟨Pi.single j 1, fun x => ?_⟩
    simp only [coordI_apply, Pi.single_apply, pow_ite, pow_one, pow_zero]
    rw [Finset.prod_ite_eq' Finset.univ j]
    simp
  | one => exact ⟨0, fun x => by simp⟩
  | mul g h _ _ hg hh =>
    obtain ⟨k, hk⟩ := hg
    obtain ⟨l, hl⟩ := hh
    refine ⟨k + l, fun x => ?_⟩
    simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hk, hl, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]

/-- **Laws on the cube are determined by their mixed moments.** -/
theorem map_eq_of_moments {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {X₁ : Ω₁ → cubeI ι}
    {X₂ : Ω₂ → cubeI ι} (h₁ : Measurable X₁) (h₂ : Measurable X₂)
    (hmom : ∀ k : ι → ℕ, ∫ ω, ∏ i, (X₁ ω : ι → ℝ) i ^ k i ∂P₁ = ∫ ω, ∏ i, (X₂ ω : ι → ℝ) i ^ k i ∂P₂) :
    P₁.map X₁ = P₂.map X₂ := by
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable (𝕜 := ℝ)
    (A := StarAlgebra.adjoin ℝ (range (coordI (ι := ι)))) ?_ ?_
  · intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, (x : ι → ℝ) i ≠ (y : ι → ℝ) i := by
      by_contra h
      exact hxy (Subtype.ext (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩))
    refine ⟨coordI i, ?_, hi⟩
    simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, mem_image,
      SetLike.mem_coe, exists_exists_and_eq_and]
    exact ⟨coordI i, StarAlgebra.subset_adjoin ℝ _ ⟨i, rfl⟩, rfl⟩
  · intro g hg
    have hs : star (range (coordI (ι := ι))) = range coordI := by
      ext f
      simp only [mem_star, mem_range]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, by rw [← star_coordI, hi, star_star]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, star_coordI i⟩
    have hg' : g ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (range (coordI (ι := ι)))) := by
      have : g ∈ (StarAlgebra.adjoin ℝ (range (coordI (ι := ι)))).toSubalgebra := hg
      rwa [StarAlgebra.adjoin_toSubalgebra, hs, union_self] at this
    rw [Algebra.adjoin_eq_span] at hg'
    clear hg
    induction hg' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, hk⟩ := exists_monomial_of_mem_closureI hg
      rw [integral_map h₁.aemeasurable g.continuous.aestronglyMeasurable,
        integral_map h₂.aemeasurable g.continuous.aestronglyMeasurable]
      simp only [hk]
      exact hmom k
    | zero => simp
    | add f g _ _ hf hg =>
      simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
      rw [integral_add (f.integrable _) (g.integrable _), integral_add (f.integrable _)
        (g.integrable _), hf, hg]
    | smul c f _ hf =>
      simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, hf]

end Cube

/-! ### Measures on `C([0, R])` are determined by finite-dimensional laws along a dense sequence -/

section Embed

open scoped DSReach.PathMeas

variable {R : ℝ≥0}

/-- A dense sequence of positive levels in `[0, R]`. -/
theorem exists_dense_pos_seq (hR : 0 < R) :
    ∃ d : ℕ → Icc (0 : ℝ≥0) R, (∀ n, 0 < ((d n : ℝ≥0) : ℝ)) ∧ DenseRange d := by
  set S : Set (Icc (0 : ℝ≥0) R) := {y | 0 < (y : ℝ≥0)} with hS
  have hne : Nonempty S := ⟨⟨⟨R, zero_le, le_rfl⟩, hR⟩⟩
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq S
  refine ⟨fun n => (e n : Icc (0 : ℝ≥0) R), fun n => by exact_mod_cast (e n).2, ?_⟩
  have hSd : Dense S := by
    rw [Metric.dense_iff]
    intro y r hr
    by_cases hy : 0 < (y : ℝ≥0)
    · exact ⟨y, Metric.mem_ball_self hr, hy⟩
    · have hy0 : (y : ℝ≥0) = 0 := le_antisymm (not_lt.1 hy) zero_le
      set t : ℝ≥0 := min (⟨r / 2, by positivity⟩ : ℝ≥0) R
      have ht : 0 < t := lt_min (by show (0 : ℝ) < r / 2; positivity) hR
      refine ⟨⟨t, zero_le, min_le_right _ _⟩, ?_, ht⟩
      rw [Metric.mem_ball, Subtype.dist_eq, NNReal.dist_eq, hy0, NNReal.coe_zero, sub_zero,
        abs_of_nonneg (NNReal.coe_nonneg _)]
      calc (t : ℝ) ≤ r / 2 := by exact_mod_cast min_le_left _ _
        _ < r := by linarith
  exact hSd.denseRange_val.comp he continuous_subtype_val

/-- The restriction to the dense sequence. -/
def embD (d : ℕ → Icc (0 : ℝ≥0) R) (f : C(Icc (0 : ℝ≥0) R, ℝ)) : ℕ → ℝ := fun n => f (d n)

theorem measurableEmbedding_embD {d : ℕ → Icc (0 : ℝ≥0) R} (hd : DenseRange d) :
    MeasurableEmbedding (embD d) := by
  refine Continuous.measurableEmbedding (continuous_pi fun n => continuous_eval_const _) ?_
  intro f g hfg
  refine ContinuousMap.ext fun y => ?_
  have h : ∀ n, f (d n) = g (d n) := fun n => congrFun hfg n
  exact congrFun (hd.equalizer f.continuous g.continuous (funext h)) y

/-- **Equal finite-dimensional laws along a dense sequence give equal measures.** -/
theorem eq_of_fdd_eq {d : ℕ → Icc (0 : ℝ≥0) R} (hd : DenseRange d) {π μ : Measure C(Icc (0 : ℝ≥0) R, ℝ)}
    [IsProbabilityMeasure π] [IsProbabilityMeasure μ]
    (h : ∀ J : Finset ℕ, π.map (fun f (j : J) => f (d j)) = μ.map (fun f (j : J) => f (d j))) : π = μ := by
  have hE := measurableEmbedding_embD hd
  have hproj : ∀ (ν : Measure C(Icc (0 : ℝ≥0) R, ℝ)), IsProjectiveLimit (ν.map (embD d))
      (fun J : Finset ℕ => ν.map (fun f (j : J) => f (d j))) := fun ν J => by
    rw [Measure.map_map (Finset.measurable_restrict J) hE.measurable]
    rfl
  have heq : π.map (embD d) = μ.map (embD d) := by
    refine IsProjectiveLimit.unique (P := fun J : Finset ℕ => π.map (fun f (j : J) => f (d j))) (hproj π) ?_
    intro J
    rw [hproj μ J]
    exact (h J).symm
  have := congrArg (fun ν => ν.comap (embD d)) heq
  simpa only [hE.comap_map] using this

end Embed

/-! ### Convergence of the entrance-path laws -/

section Main

open scoped DSReach.PathMeas

variable {R : ℝ≥0}

/-- The law of the entrance path of a solution of the Jacobi martingale problem. -/
def vLaw {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {κ' a' b' : ℝ}
    {U' : ℝ → Ω' → ℝ} (hU : IsJacobiMP κ' a' b' P' U') : ProbabilityMeasure C(Icc (0 : ℝ≥0) R, ℝ) :=
  ⟨P'.map fun ω => vPath (R := R) (U' · ω) (hU.continuous ω),
    inferInstance⟩

/-- The support of the entrance laws: `0 ≤ f y ≤ y`. -/
def suppV (R : ℝ≥0) : Set C(Icc (0 : ℝ≥0) R, ℝ) := {f | ∀ y, 0 ≤ f y ∧ f y ≤ ((y : ℝ≥0) : ℝ)}

theorem isClosed_suppV : IsClosed (suppV R) := by
  simp only [suppV, ofPred_forall]
  refine isClosed_iInter fun y => ?_
  have h1 := isClosed_le (f := fun _ : C(Icc (0 : ℝ≥0) R, ℝ) => (0 : ℝ)) (g := fun x => x y) continuous_const
    (continuous_eval_const y)
  have h2 := isClosed_le (f := fun x : C(Icc (0 : ℝ≥0) R, ℝ) => x y)
    (g := fun _ => (((y : ℝ≥0) : ℝ))) (continuous_eval_const y) continuous_const
  exact h1.inter h2

theorem vLaw_suppV {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {κ' a' b' : ℝ}
    {U' : ℝ → Ω' → ℝ} (hU : IsJacobiMP κ' a' b' P' U') :
    ((vLaw (R := R) hU : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ)) (suppV R) = 1 := by
  change (P'.map _) (suppV R) = 1
  rw [Measure.map_apply (measurable_vPath hU.measurable hU.continuous) isClosed_suppV.measurableSet]
  convert measure_univ (μ := P')
  ext ω
  simp only [mem_preimage, mem_univ, iff_true]
  intro y
  have hy0 : (0 : ℝ) ≤ (y : ℝ≥0) := NNReal.coe_nonneg _
  have hc := clamp01_mem (U' (Real.log (y : ℝ≥0)) ω)
  simp only [vPath, ContinuousMap.coe_mk]
  exact ⟨mul_nonneg hy0 hc.1, mul_le_of_le_one_right hy0 hc.2⟩

/-- The normalized coordinates `clamp(f(d_j)/d_j)`, `j ∈ J`. -/
def normCoord (d : ℕ → Icc (0 : ℝ≥0) R) (J : Finset ℕ) (f : C(Icc (0 : ℝ≥0) R, ℝ)) : cubeI J :=
  ⟨fun j => clamp01 (f (d j) / ((d j : ℝ≥0) : ℝ)), fun _ => clamp01_mem _⟩

theorem continuous_normCoord (d : ℕ → Icc (0 : ℝ≥0) R) (J : Finset ℕ) : Continuous (normCoord d J) :=
  (continuous_pi fun _ => continuous_clamp01.comp ((continuous_eval_const _).div_const _)).subtype_mk _

/-- The monomials of the normalized coordinates, as bounded continuous functions. -/
def monoB (d : ℕ → Icc (0 : ℝ≥0) R) (J : Finset ℕ) (k : J → ℕ) : C(Icc (0 : ℝ≥0) R, ℝ) →ᵇ ℝ :=
  mkOfBound ⟨fun f => ∏ j, ((normCoord d J f : J → ℝ) j) ^ k j,
    continuous_finsetProd _ fun j _ => ((continuous_apply j).comp
      (continuous_subtype_val.comp (continuous_normCoord d J))).pow _⟩ 2 fun f g => by
    have h1 : ∀ f : C(Icc (0 : ℝ≥0) R, ℝ), ∏ j, ((normCoord d J f : J → ℝ) j) ^ k j ∈ Icc (0 : ℝ) 1 := fun f =>
      ⟨Finset.prod_nonneg fun j _ => pow_nonneg ((normCoord d J f).2 j).1 _,
        Finset.prod_le_one₀ (fun j _ => pow_nonneg ((normCoord d J f).2 j).1 _)
          fun j _ => pow_le_one₀ ((normCoord d J f).2 j).1 ((normCoord d J f).2 j).2⟩
    simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
    constructor <;> linarith [(h1 f).1, (h1 f).2, (h1 g).1, (h1 g).2]

theorem integral_monoB_vLaw {d : ℕ → Icc (0 : ℝ≥0) R} (hdpos : ∀ n, 0 < ((d n : ℝ≥0) : ℝ))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {κ' a' b' : ℝ}
    {U' : ℝ → Ω' → ℝ} (hU : IsJacobiMP κ' a' b' P' U') (J : Finset ℕ) (k : J → ℕ) :
    ∫ f, monoB d J k f ∂((vLaw (R := R) hU : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ)) =
      ∫ ω, ∏ j : J, U' (Real.log ((d j : ℝ≥0) : ℝ)) ω ^ k j ∂P' := by
  change ∫ f, monoB d J k f ∂(P'.map _) = _
  rw [integral_map (measurable_vPath hU.measurable hU.continuous).aemeasurable
    (monoB d J k).continuous.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [monoB, mkOfBound_coe, ContinuousMap.coe_mk, normCoord, vPath]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_div_cancel_left₀ _ (hdpos j).ne']
  have hc := hU.mem_Icc (Real.log ((d j : ℝ≥0) : ℝ)) ω
  have e1 : clamp01 (U' (Real.log ((d j : ℝ≥0) : ℝ)) ω) = U' (Real.log ((d j : ℝ≥0) : ℝ)) ω := by
    simp only [clamp01, min_eq_right hc.2, max_eq_right hc.1]
  rw [e1, e1]

/-- Mixed moments of products indexed by a finite set converge (reindexing `tendsto_integral_prodPow`). -/
theorem tendsto_integral_prod_finset {κ a b : ℝ} {am bm : ℕ → ℝ} (hκ : 0 ≤ κ) (hab : 0 < a + b)
    (habm : ∀ m, 0 < am m + bm m) (ham : Tendsto am atTop (𝓝 a)) (hbm : Tendsto bm atTop (𝓝 b))
    {Ωs : ℕ → Type*} [∀ m, MeasurableSpace (Ωs m)] {Ps : ∀ m, Measure (Ωs m)} [∀ m, IsProbabilityMeasure (Ps m)]
    {Us : ∀ m, ℝ → Ωs m → ℝ} (hUs : ∀ m, IsJacobiMP κ (am m) (bm m) (Ps m) (Us m))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ}
    (hU : IsJacobiMP κ a b P' U') (J : Finset ℕ) (t : J → ℝ) (k : J → ℕ) :
    Tendsto (fun m => ∫ ω, ∏ j : J, Us m (t j) ω ^ k j ∂(Ps m)) atTop (𝓝 (∫ ω, ∏ j : J, U' (t j) ω ^ k j ∂P')) := by
  set e := J.equivFin
  have h := tendsto_integral_prodPow hκ hab habm ham hbm hUs hU J.card (fun i => t (e.symm i))
    (fun i => k (e.symm i))
  have e1 : (fun m => ∫ ω, prodPow (Us m) (fun i => t (e.symm i)) (fun i => k (e.symm i)) ω ∂(Ps m)) =
      fun m => ∫ ω, ∏ j : J, Us m (t j) ω ^ k j ∂(Ps m) := by
    funext m
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [prodPow]
    exact Fintype.prod_equiv e.symm _ _ (fun i => rfl)
  have e2 : ∫ ω, prodPow U' (fun i => t (e.symm i)) (fun i => k (e.symm i)) ω ∂P' =
      ∫ ω, ∏ j : J, U' (t j) ω ^ k j ∂P' := by
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [prodPow]
    exact Fintype.prod_equiv e.symm _ _ (fun i => rfl)
  rw [e1, e2] at h
  exact h

/-- **Identification of the weak limits** of entrance-path laws along a subsequence. -/
theorem eq_vLaw_of_tendsto (hR : 0 < R) {κ a b : ℝ} {am bm : ℕ → ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (ham0 : ∀ m, 0 < am m) (hbm0 : ∀ m, 0 < bm m) (ham : Tendsto am atTop (𝓝 a))
    (hbm : Tendsto bm atTop (𝓝 b))
    {Ωs : ℕ → Type*} [∀ m, MeasurableSpace (Ωs m)] {Ps : ∀ m, Measure (Ωs m)} [∀ m, IsProbabilityMeasure (Ps m)]
    {Us : ∀ m, ℝ → Ωs m → ℝ} (hUs : ∀ m, IsJacobiMP κ (am m) (bm m) (Ps m) (Us m))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ}
    (hU : IsJacobiMP κ a b P' U') {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {π : ProbabilityMeasure C(Icc (0 : ℝ≥0) R, ℝ)}
    (hlim : Tendsto (fun n => vLaw (R := R) (hUs (φ n))) atTop (𝓝 π)) : π = vLaw (R := R) hU := by
  obtain ⟨d, hdpos, hd⟩ := exists_dense_pos_seq hR
  have hsupp : (π : Measure C(Icc (0 : ℝ≥0) R, ℝ)) (suppV R) = 1 :=
    Prokhorov.measure_eq_one_of_tendsto_of_isClosed hlim isClosed_suppV
      (Eventually.of_forall fun n => vLaw_suppV (hUs (φ n)))
  have hπprob : IsProbabilityMeasure (π : Measure C(Icc (0 : ℝ≥0) R, ℝ)) := π.2
  have hμprob : IsProbabilityMeasure ((vLaw (R := R) hU : ProbabilityMeasure _) :
    Measure C(Icc (0 : ℝ≥0) R, ℝ)) := (vLaw (R := R) hU).2
  apply Subtype.ext
  change (π : Measure C(Icc (0 : ℝ≥0) R, ℝ)) =
    ((vLaw (R := R) hU : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ))
  refine eq_of_fdd_eq hd fun J => ?_
  -- the normalized coordinates have the same law
  have hmom : ∀ k : J → ℕ, ∫ f, monoB d J k f ∂(π : Measure C(Icc (0 : ℝ≥0) R, ℝ)) =
      ∫ f, monoB d J k f ∂((vLaw (R := R) hU : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ)) := by
    intro k
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) (monoB d J k)
    have h2 := tendsto_integral_prod_finset hκ (by linarith) (fun m => by linarith [ham0 m, hbm0 m]) ham hbm
      hUs hU J (fun j => Real.log ((d j : ℝ≥0) : ℝ)) k
    have h3 := h2.comp hφ
    simp only [integral_monoB_vLaw hdpos] at h1
    rw [integral_monoB_vLaw hdpos]
    exact tendsto_nhds_unique h1 h3
  have hlaw : (π : Measure C(Icc (0 : ℝ≥0) R, ℝ)).map (normCoord d J) =
      ((vLaw (R := R) hU : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ)).map (normCoord d J) :=
    map_eq_of_moments (continuous_normCoord d J).measurable (continuous_normCoord d J).measurable
      fun k => hmom k
  -- on the support, the coordinates are recovered from the normalized ones
  set Lmap : cubeI J → (J → ℝ) := fun x j => ((d j : ℝ≥0) : ℝ) * (x : J → ℝ) j with hLmap
  have hLm : Measurable Lmap := by
    have : Continuous Lmap := continuous_pi fun j => continuous_const.mul
      ((continuous_apply j).comp continuous_subtype_val)
    exact this.measurable
  have hrec : ∀ f ∈ suppV R, (fun j : J => f (d j)) = Lmap (normCoord d J f) := by
    intro f hf
    funext j
    simp only [hLmap, normCoord]
    have h := hf (d j)
    have hpos := hdpos j
    have hq : f (d j) / ((d j : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg h.1 hpos.le, (div_le_one hpos).2 h.2⟩
    simp only [clamp01, min_eq_right hq.2, max_eq_right hq.1]
    rw [mul_div_cancel₀ _ hpos.ne']
  have hae : ∀ (ν : Measure C(Icc (0 : ℝ≥0) R, ℝ)), ν (suppV R)ᶜ = 0 →
      ν.map (fun f (j : J) => f (d j)) = (ν.map (normCoord d J)).map Lmap := by
    intro ν hν
    rw [Measure.map_map hLm (continuous_normCoord d J).measurable]
    refine Measure.map_congr ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with f hf
    exact hrec f (by simpa using hf)
  have hπc : (π : Measure C(Icc (0 : ℝ≥0) R, ℝ)) (suppV R)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff isClosed_suppV.measurableSet]; exact hsupp
  have hμc : ((vLaw (R := R) hU : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ)) (suppV R)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff isClosed_suppV.measurableSet]; exact vLaw_suppV hU
  rw [hae _ hπc, hae _ hμc, hlaw]

/-- **Weak convergence of the entrance-path laws** as the parameters converge. -/
theorem tendsto_vLaw (hR : 0 < R) {κ a b : ℝ} {am bm : ℕ → ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b)
    (ham0 : ∀ m, 0 < am m) (hbm0 : ∀ m, 0 < bm m) (ham : Tendsto am atTop (𝓝 a))
    (hbm : Tendsto bm atTop (𝓝 b))
    {Ωs : ℕ → Type*} [∀ m, MeasurableSpace (Ωs m)] {Ps : ∀ m, Measure (Ωs m)} [∀ m, IsProbabilityMeasure (Ps m)]
    {Us : ∀ m, ℝ → Ωs m → ℝ} (hUs : ∀ m, IsJacobiMP κ (am m) (bm m) (Ps m) (Us m))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {U' : ℝ → Ω' → ℝ}
    (hU : IsJacobiMP κ a b P' U') :
    Tendsto (fun m => vLaw (R := R) (hUs m)) atTop (𝓝 (vLaw (R := R) hU)) := by
  have hq := ((continuous_quartC κ).tendsto (a, b)).comp (ham.prodMk_nhds hbm)
  obtain ⟨Mq, hMq⟩ := hq.bddAbove_range
  have hMq' : ∀ m, quartC κ (am m) (bm m) ≤ Mq := fun m => hMq ⟨m, rfl⟩
  have htight := isTightMeasureSet_vLaw (R := R) (ι := ℕ) (Ω' := Ωs) (P' := Ps) (a' := am) (b' := bm)
    (U' := Us) hR hκ (fun m => (ham0 m).le) (fun m => (hbm0 m).le) hUs (Mq := Mq) hMq' 
  refine tendsto_of_subseq_tendsto fun φ hφ => ?_
  have htφ : IsTightMeasureSet (range fun n =>
      ((vLaw (R := R) (hUs (φ n)) : ProbabilityMeasure _) : Measure C(Icc (0 : ℝ≥0) R, ℝ))) :=
    htight.subset (by rintro _ ⟨n, rfl⟩; exact ⟨φ n, rfl⟩)
  obtain ⟨π, ψ, hψ, hlim⟩ := Prokhorov.exists_subseq_tendsto_of_isTightMeasureSet
    (fun n => vLaw (R := R) (hUs (φ n))) htφ
  refine ⟨ψ, ?_⟩
  rw [← eq_vLaw_of_tendsto hR hκ ha hb ham0 hbm0 ham hbm hUs hU (hφ.comp hψ.tendsto_atTop) hlim]
  exact hlim

end Main

end Aux4

end Supp12

end InteractingSLE
