import QuantumZipper.Proofs.GFF.K3.DualExistence
import QuantumZipper.Proofs.GFF.K3.GreenH

/-!
# GFF-K3, node E4: the conditional zero-boundary GFF on a random open set

`exists_condZeroGFF`: for a random open set `U ω ⊆ ℍ` whose events
`{ω | tsupport (testFamily j) ⊆ U ω}` are measurable, the field
`X'(ω, ξ) μ := gsLim (coefG (P_{K(ω)} v_μ)) ξ` on `Ω₀ × (ℕ → ℝ)` satisfies
`IsCondZeroBoundaryGFFH`. Here `v_μ = rieszVec H (zeroSpace H) μ`,
`K(ω) = gradClosure H (zeroSpace (U ω))` and `P_K` is the orthogonal projection.

* `gsLim a ξ` sums the Gaussian series `Σ a_k ξ_k` along an explicit subsequence `subφ a`
  depending measurably on `a` (tails `≤ 8^{-j}`); it is jointly measurable in `(a, ξ)`, and finite
  combinations have the Gram Gaussian law (`hasLaw_sum_gsLim`), as in `GFFExist.gs_process`.
* `ω ↦ ⟪P_{K(ω)} x, y⟫` is measurable: `K(ω)` is the closure of the increasing union of the
  finite-dimensional spans of `gradFeat H (testFamily j)`, `j < n`, `tsupport ⊆ U ω`
  (density: `testFamily_approx`), and projections onto these take finitely many values on
  measurable events (`starProjection_tendsto_closure_iSup`).
* `dualCov U (zeroSpace U) m m' = ⟪P_K v_m, P_K v_m'⟫` for `m, m'` admissible on `ℍ`
  (`dualCov_eq_inner_proj`); finiteness on `ℍ` of test measures comes from H3 (`GreenH`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal

namespace QuantumZipper.K3

open GFFExist LQGDimension.ExistAsm

/-! ## Gaussian series along a measurable subsequence -/

/-- `ℝ≥0∞`-valued tails of `Σ a_k²`. -/
def tailE (a : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ := ∑' k, ENNReal.ofReal (a (k + n) ^ 2)

lemma measurable_tailE (n : ℕ) : Measurable fun a : ℕ → ℝ => tailE a n :=
  Measurable.ennreal_tsum fun _ =>
    ENNReal.measurable_ofReal.comp ((measurable_pi_apply _).pow_const 2)

/-- The defining property of the `i`-th threshold. -/
def subP (a : ℕ → ℝ) (i N : ℕ) : Prop :=
  tailE a 0 = ⊤ ∨ ∀ n ≥ N, tailE a n ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ i)

lemma subP_exists (a : ℕ → ℝ) (i : ℕ) : ∃ N, subP a i N := by
  by_cases h : tailE a 0 = ⊤
  · exact ⟨0, Or.inl h⟩
  · have h' : ∑' k, ENNReal.ofReal (a k ^ 2) ≠ ⊤ := by simpa [tailE] using h
    have ht : Tendsto (fun n => tailE a n) atTop (𝓝 0) :=
      ENNReal.tendsto_sum_nat_add (fun k => ENNReal.ofReal (a k ^ 2)) h'
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (ht.eventually (Iic_mem_nhds
        (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < (1 / 8 : ℝ) ^ i))))
    exact ⟨N, Or.inr hN⟩

open Classical in
/-- The `i`-th threshold. -/
def subN (a : ℕ → ℝ) (i : ℕ) : ℕ := Nat.find (subP_exists a i)

/-- The explicit subsequence. -/
def subφ (a : ℕ → ℝ) (j : ℕ) : ℕ := (∑ i ∈ Finset.range (j + 1), subN a i) + j

lemma measurable_subN (i : ℕ) : Measurable fun a => subN a i := by
  classical
  unfold subN
  refine measurable_find (fun a => subP_exists a i) fun N => ?_
  have e : {a | subP a i N} = {a | tailE a 0 = ⊤} ∪
      ⋂ n, ⋂ (_ : N ≤ n), {a | tailE a n ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ i)} := by
    ext a; simp [subP]
  rw [e]
  exact ((measurable_tailE 0) (measurableSet_singleton ⊤)).union
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_tailE n) measurable_const)

lemma measurable_subφ (j : ℕ) : Measurable fun a => subφ a j := by
  unfold subφ
  exact (Finset.measurable_sum _ fun i _ => measurable_subN i).add measurable_const

lemma subφ_strictMono (a : ℕ → ℝ) : StrictMono (subφ a) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  simp only [subφ, Finset.sum_range_succ _ (j + 1)]
  omega

lemma subN_le_subφ (a : ℕ → ℝ) (j : ℕ) : subN a j ≤ subφ a j := by
  have := Finset.single_le_sum (f := subN a) (fun i _ => Nat.zero_le _)
    (Finset.self_mem_range_succ j)
  simp only [subφ]
  omega

lemma tail_subφ_le (a : ℕ → ℝ) (ha : Summable fun k => a k ^ 2) (j : ℕ) :
    ∑' k, a (k + subφ a j) ^ 2 ≤ (1 / 8 : ℝ) ^ j := by
  classical
  have hofR : ∀ n, tailE a n = ENNReal.ofReal (∑' k, a (k + n) ^ 2) := fun n =>
    (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) ((summable_nat_add_iff n).2 ha)).symm
  have hspec : subP a j (subN a j) := Nat.find_spec (subP_exists a j)
  rcases hspec with h | h
  · exact absurd (hofR 0 ▸ h) ENNReal.ofReal_ne_top
  · have h2 := h _ (subN_le_subφ a j)
    rw [hofR] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2

/-- Almost sure convergence along any subsequence with tails `≤ 8^{-j}`
(the argument of `GFFExist.gs_exists_subseq`). -/
theorem gs_ae_conv_of_tail (a : ℕ → ℝ) (ha : Summable fun k => a k ^ 2) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (htail : ∀ j, ∑' k, a (k + φ j) ^ 2 ≤ (1 / 8 : ℝ) ^ j) :
    ∀ᵐ ω ∂stdP, ∃ L, Tendsto (fun j => gsPartial a (φ j) ω) atTop (𝓝 L) := by
  set D : ℕ → (ℕ → ℝ) → ℝ := fun j ω => gsPartial a (φ (j + 1)) ω - gsPartial a (φ j) ω
    with hD_def
  set w : ℕ → ℕ → ℝ := fun j k => if φ j ≤ k then a k else 0 with hw_def
  have hlaw : ∀ j, HasLaw (D j) (gaussianReal 0
      (∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2).toNNReal) stdP := by
    intro j
    have e : D j = fun ω => ∑ k ∈ Finset.range (φ (j + 1)), w j k * ω k := by
      funext ω
      exact gs_diff_eq a (hφ.monotone (Nat.le_succ j)) ω
    rw [e]
    exact hasLaw_sum_mul (w j) (φ (j + 1))
  have hvar : ∀ j, ∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2 ≤ ((1 : ℝ) / 8) ^ j := fun j =>
    (gs_diff_var_le a ha (hφ.monotone (Nat.le_succ j))).trans (htail j)
  set s : ℕ → Set (ℕ → ℝ) := fun j => {ω | ((1 : ℝ) / 2) ^ j ≤ |D j ω|} with hs_def
  have hsb : ∀ j, stdP (s j) ≤ ENNReal.ofReal (1 / 2) ^ j := by
    intro j
    refine (gs_meas_ge_le (hlaw j) (by positivity : (0 : ℝ) < (1 / 2) ^ j)).trans ?_
    rw [← ENNReal.ofReal_pow (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hv0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.coe_toNNReal _ hv0, div_le_iff₀ (by positivity)]
    calc ∑ k ∈ Finset.range (φ (j + 1)), w j k ^ 2 ≤ ((1 : ℝ) / 8) ^ j := hvar j
      _ = (1 / 2) ^ j * ((1 / 2) ^ j) ^ 2 := by
          rw [← pow_mul, ← pow_add, show j + j * 2 = 3 * j by ring, pow_mul]; norm_num
  have hsum : ∑' j, stdP (s j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsb)
    exact (tsum_geometric_lt_top.2 (by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
        (by norm_num))).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  have hbd : ∀ᶠ j in cofinite, ‖D j ω‖ ≤ ((1 : ℝ) / 2) ^ j := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hω] with j hj
    simp only [hs_def, Set.mem_ofPred_eq, not_le] at hj
    rw [Real.norm_eq_abs]
    exact hj.le
  have hS : Summable fun j => D j ω :=
    Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (by norm_num)
      (by norm_num)) hbd
  refine ⟨gsPartial a (φ 0) ω + ∑' j, D j ω, ?_⟩
  have htel : ∀ n, gsPartial a (φ n) ω =
      gsPartial a (φ 0) ω + ∑ j ∈ Finset.range n, D j ω := by
    intro n
    simp only [hD_def]
    rw [Finset.sum_range_sub (fun j => gsPartial a (φ j) ω)]
    ring
  rw [show (fun j => gsPartial a (φ j) ω) =
      fun n => gsPartial a (φ 0) ω + ∑ j ∈ Finset.range n, D j ω from funext htel]
  exact tendsto_const_nhds.add hS.hasSum.tendsto_sum_nat

/-- The Gaussian series `Σ a_k ξ_k`, summed along `subφ a`. -/
def gsLim (a : ℕ → ℝ) (ξ : ℕ → ℝ) : ℝ := limUnder atTop fun j => gsPartial a (subφ a j) ξ

lemma measurable_gsLim : Measurable fun q : (ℕ → ℝ) × (ℕ → ℝ) => gsLim q.1 q.2 := by
  have hfam : ∀ n, Measurable fun q : (ℕ → ℝ) × (ℕ → ℝ) => gsPartial q.1 n q.2 := by
    intro n
    unfold gsPartial
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp measurable_fst).mul ((measurable_pi_apply k).comp measurable_snd)
  have hj : ∀ j, Measurable fun q : (ℕ → ℝ) × (ℕ → ℝ) => gsPartial q.1 (subφ q.1 j) q.2 := by
    intro j
    have h2 : Measurable fun r : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ => gsPartial r.1.1 r.2 r.1.2 :=
      measurable_from_prod_countable_left fun n => hfam n
    exact h2.comp (measurable_id.prodMk ((measurable_subφ j).comp measurable_fst))
  exact (StronglyMeasurable.limUnder fun j => (hj j).stronglyMeasurable).measurable

lemma measurable_gsLim_comp {α : Type*} [MeasurableSpace α] {a : α → ℕ → ℝ}
    (ha : Measurable a) : Measurable fun p : α × (ℕ → ℝ) => gsLim (a p.1) p.2 := by
  have hg : Measurable fun p : α × (ℕ → ℝ) => (a p.1, p.2) :=
    (ha.comp measurable_fst).prodMk measurable_snd
  have h := measurable_gsLim.comp hg
  exact h

/-- Gram law of finite combinations of `gsLim` (as in `GFFExist.gs_process`). -/
theorem hasLaw_sum_gsLim {ι : Type} [Fintype ι] (a : ι → ℕ → ℝ)
    (ha : ∀ i, Summable fun k => a i k ^ 2) (c : ι → ℝ) :
    HasLaw (fun ω => ∑ i, c i * gsLim (a i) ω)
      (gaussianReal 0 (∑ i, ∑ i', c i * c i' * ∑' k, a i k * a i' k).toNNReal) stdP := by
  classical
  set φ : ι → ℕ → ℕ := fun t => subφ (a t) with hφdef
  have hφ : ∀ t, StrictMono (φ t) := fun t => subφ_strictMono (a t)
  have hXlim : ∀ t, ∀ᵐ ω ∂stdP,
      Tendsto (fun j => gsPartial (a t) (φ t j) ω) atTop (𝓝 (gsLim (a t) ω)) := by
    intro t
    filter_upwards [gs_ae_conv_of_tail (a t) (ha t) (φ t) (hφ t)
      (tail_subφ_le (a t) (ha t))] with ω hω
    exact tendsto_nhds_limUnder hω
  set M : ℕ → ℕ := fun j => ∑ i, φ i j with hM_def
  have hMle : ∀ i j, φ i j ≤ M j := fun i j =>
    Finset.single_le_sum (f := fun i => φ i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set A : ι → ℕ → ℕ → ℝ := fun i j k => if k < φ i j then a i k else 0 with hA_def
  set w : ℕ → ℕ → ℝ := fun j k => ∑ i, c i * A i j k with hw_def
  set Y : ℕ → (ℕ → ℝ) → ℝ := fun j ω => ∑ k ∈ Finset.range (M j), w j k * ω k with hY_def
  have hYeq : ∀ j ω, Y j ω = ∑ i, c i * gsPartial (a i) (φ i j) ω := by
    intro j ω
    simp only [hY_def, hw_def, Finset.sum_mul, gsPartial]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← gs_sum_range_ite (hMle i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hA_def]
    split_ifs <;> ring
  have hVeq : ∀ j, ∑ k ∈ Finset.range (M j), w j k ^ 2 =
      ∑ i, ∑ i', c i * c i' *
        ∑ k ∈ Finset.range (min (φ i j) (φ i' j)), a i k * a i' k := by
    intro j
    simp only [hw_def, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum, ← gs_sum_range_ite (le_trans (min_le_left _ _) (hMle i j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hA_def]
    rw [mul_mul_mul_comm, gs_ite_mul_ite]
    split_ifs <;> ring
  have hlaw : ∀ j, HasLaw (Y j) (gaussianReal 0
      (∑ k ∈ Finset.range (M j), w j k ^ 2).toNNReal) stdP := fun j =>
    hasLaw_sum_mul (w j) (M j)
  refine hasLaw_gaussianReal_of_tendsto hlaw ?_ ?_
  · have hall : ∀ᵐ ω ∂stdP, ∀ i, Tendsto (fun j => gsPartial (a i) (φ i j) ω) atTop
        (𝓝 (gsLim (a i) ω)) := ae_all_iff.2 fun i => hXlim i
    filter_upwards [hall] with ω hω
    simp_rw [hYeq]
    exact tendsto_finsetSum _ fun i _ => (hω i).const_mul (c i)
  · simp_rw [hVeq]
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun i' _ => ?_
    refine Tendsto.const_mul _ ?_
    have hs := (gs_summable_mul (ha i) (ha i')).hasSum.tendsto_sum_nat
    exact hs.comp (tendsto_atTop_mono (fun j => le_min ((hφ i).id_le j)
      ((hφ i').id_le j)) tendsto_id)

/-! ## Hilbert coefficients in `GradSpace H` -/

lemma exists_coef : ∃ coef : GradSpace H → ℕ → ℝ,
    (∀ k, ∃ z : GradSpace H, ∀ y, coef y k = ⟪y, z⟫) ∧
      ∀ y z, HasSum (fun k => coef y k * coef z k) ⟪y, z⟫ := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (GradSpace H)
  have : Countable w := gs_countable_of_orthonormal b.orthonormal
  obtain ⟨e, he⟩ := Countable.exists_injective_nat w
  refine ⟨fun y => Function.extend e (fun i => ⟪y, b i⟫) 0, fun k => ?_, fun y z => ?_⟩
  · by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      exact ⟨b i, fun y => by simp only [he.extend_apply]⟩
    · exact ⟨0, fun y => by simp only [Function.extend_apply' _ _ _ h, Pi.zero_apply, inner_zero_right]⟩
  · have h1 : (fun k => Function.extend e (fun i => ⟪y, b i⟫) 0 k *
        Function.extend e (fun i => ⟪z, b i⟫) 0 k) =
        Function.extend e ((fun i => ⟪y, b i⟫) * fun i => ⟪z, b i⟫) 0 := by
      funext k
      exact gs_extend_mul he _ _ k
    rw [h1, hasSum_extend_zero he]
    have h2 := b.hasSum_inner_mul_inner y z
    have e' : ((fun i => ⟪y, b i⟫) * fun i => ⟪z, b i⟫) = fun i => ⟪y, b i⟫ * ⟪b i, z⟫ := by
      funext i
      simp only [Pi.mul_apply]
      rw [real_inner_comm (b i) z]
    rw [e']
    exact h2

/-- Fixed Hilbert coefficients on `GradSpace H`. -/
def coefG : GradSpace H → ℕ → ℝ := exists_coef.choose

lemma coefG_eq_inner (k : ℕ) : ∃ z : GradSpace H, ∀ y, coefG y k = ⟪y, z⟫ :=
  exists_coef.choose_spec.1 k

lemma coefG_hasSum (y z : GradSpace H) : HasSum (fun k => coefG y k * coefG z k) ⟪y, z⟫ :=
  exists_coef.choose_spec.2 y z

theorem hasLaw_sum_gsLimG {ι : Type} [Fintype ι] (u : ι → GradSpace H) (c : ι → ℝ) :
    HasLaw (fun ξ => ∑ i, c i * gsLim (coefG (u i)) ξ)
      (gaussianReal 0 (‖∑ i, c i • u i‖ ^ 2).toNNReal) stdP := by
  have hsq : ∀ i, Summable fun k => coefG (u i) k ^ 2 := fun i => by
    simp_rw [sq]; exact (coefG_hasSum _ _).summable
  have key : ‖∑ i, c i • u i‖ ^ 2 =
      ∑ i, ∑ i', c i * c i' * ∑' k, coefG (u i) k * coefG (u i') k := by
    simp_rw [fun s t => (coefG_hasSum s t).tsum_eq]
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  rw [key]
  exact hasLaw_sum_gsLim _ hsq c

/-! ## Projections onto `gradClosure H (zeroSpace U)` -/

/-- The orthogonal projection onto `gradClosure H V`. -/
def projK (V : Set (ℂ → ℝ)) (x : GradSpace H) : GradSpace H :=
  (gradClosure H V).starProjection x

lemma starProjection_congr_K3 {K K' : Submodule ℝ (GradSpace H)} (h : K = K')
    [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection] (x : GradSpace H) :
    K.starProjection x = K'.starProjection x := by
  subst h; rfl

/-- The gradient features of the test family. -/
def gFam (j : ℕ) : GradSpace H := gradFeat H (testFamily j)

lemma norm_sub_gradFeat_sq {f g : ℂ → ℝ} (hf : f ∈ zeroSpace H) (hg : g ∈ zeroSpace H) :
    ‖gradFeat H g - gradFeat H f‖ ^ 2 = dirichletEnergyOn H (g - f) := by
  have hVH := isDNSpace_zeroSpace H
  have e : g - f = g + (-1 : ℝ) • f := by funext z; simp [sub_eq_add_neg]
  have hs : gradFeat H g - gradFeat H f = gradFeat H (g - f) := by
    rw [e, gradFeat_add hVH hg (hVH.smul_mem _ f hf), gradFeat_smul hVH _ hf]
    simp [sub_eq_add_neg]
  rw [hs]
  exact norm_gradFeat_sq (hVH.smooth _ (zeroSpace_sub hf hg)) (hVH.energy _ (zeroSpace_sub hf hg))

lemma gradClosure_eq_testSpan {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    gradClosure H (zeroSpace U) =
      (Submodule.span ℝ (gFam '' {j | tsupport (testFamily j) ⊆ U})).topologicalClosure := by
  apply le_antisymm
  · show (Submodule.span ℝ (gradFeat H '' zeroSpace U)).topologicalClosure ≤ _
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hfH : f ∈ zeroSpace H := ⟨hf.1, hf.2.1, hf.2.2.trans hUH⟩
    rw [SetLike.mem_coe, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨j, hjU, hjE, -⟩ := testFamily_approx hU hUH hf (pow_pos hε 2)
    refine ⟨gFam j, Submodule.subset_span ⟨j, hjU, rfl⟩, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    have h := norm_sub_gradFeat_sq hfH (testFamily_mem j)
    exact lt_of_pow_lt_pow_left₀ 2 hε.le (h ▸ hjE)
  · show _ ≤ (Submodule.span ℝ (gradFeat H '' zeroSpace U)).topologicalClosure
    refine Submodule.topologicalClosure_mono ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.subset_span ⟨testFamily j, ⟨(testFamily_mem j).1, (testFamily_mem j).2.1, hj⟩, rfl⟩

/-- Finite spans (`b` selects indices `< n`). -/
def Wb (n : ℕ) (b : Fin n → Bool) : Submodule ℝ (GradSpace H) :=
  Submodule.span ℝ (gFam '' {j | ∃ h : j < n, b ⟨j, h⟩ = true})

instance (n : ℕ) (b : Fin n → Bool) : (Wb n b).HasOrthogonalProjection := by
  have hfin : {j | ∃ h : j < n, b ⟨j, h⟩ = true}.Finite :=
    (Set.finite_lt_nat n).subset fun j ⟨h, _⟩ => h
  haveI : FiniteDimensional ℝ (Wb n b) := FiniteDimensional.span_of_finite ℝ (hfin.image _)
  infer_instance

section RandomSet

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {U : Ω₀ → Set ℂ}

open Classical in
/-- The selector of test indices `< n` with `tsupport ⊆ U ω`. -/
def selB (U : Ω₀ → Set ℂ) (n : ℕ) (ω : Ω₀) : Fin n → Bool :=
  fun j => if tsupport (testFamily j.1) ⊆ U ω then true else false

lemma measurable_selB (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω}) (n : ℕ) :
    Measurable (selB U n) :=
  measurable_pi_iff.mpr fun j => by
    classical
    exact Measurable.ite (hE j.1) measurable_const measurable_const

lemma measurable_inner_projK (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω}) (x y : GradSpace H) :
    Measurable fun ω => ⟪projK (zeroSpace (U ω)) x, y⟫ := by
  set W : Ω₀ → ℕ → Submodule ℝ (GradSpace H) := fun ω n => Wb n (selB U n ω) with hW
  have hmono : ∀ ω, Monotone (W ω) := by
    intro ω
    refine monotone_nat_of_le_succ fun n => Submodule.span_mono (image_mono ?_)
    rintro j ⟨h, hb⟩
    refine ⟨Nat.lt_succ_of_lt h, ?_⟩
    simp only [selB] at hb ⊢
    exact hb
  have hsup : ∀ ω, (⨆ n, W ω n).topologicalClosure = gradClosure H (zeroSpace (U ω)) := by
    intro ω
    rw [gradClosure_eq_testSpan (hU ω).1 (hU ω).2]
    congr 1
    simp only [hW, Wb]
    rw [← Submodule.span_iUnion, ← image_iUnion]
    congr 2
    ext j
    simp only [mem_iUnion, mem_ofPred_eq, selB]
    constructor
    · rintro ⟨n, h, hb⟩
      by_contra hc; simp [hc] at hb
    · intro hj; exact ⟨j + 1, Nat.lt_succ_self j, by simp [hj]⟩
  have hlim : ∀ ω, Tendsto (fun n => ⟪(W ω n).starProjection x, y⟫) atTop
      (𝓝 ⟪projK (zeroSpace (U ω)) x, y⟫) := by
    intro ω
    have h := Submodule.starProjection_tendsto_closure_iSup (W ω) (hmono ω) x
    rw [starProjection_congr_K3 (hsup ω)] at h
    exact h.inner tendsto_const_nhds
  have hmeas : ∀ n, Measurable fun ω => ⟪(W ω n).starProjection x, y⟫ := by
    intro n
    have h1 : Measurable fun b : Fin n → Bool => ⟪(Wb n b).starProjection x, y⟫ :=
      measurable_of_countable _
    exact h1.comp (measurable_selB hE n)
  exact measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.mpr hlim)

end RandomSet

/-! ## Dual covariances on `U ⊆ ℍ` as projected Gram products -/

lemma isDNSpace_zeroSpace_on (D U : Set ℂ) : IsDNSpace D (zeroSpace U) where
  smooth f hf := (isDNSpace_zeroSpace U).smooth f hf
  energy f hf := by
    have hc : Continuous fun z => ‖fderiv ℝ f z‖ ^ 2 :=
      ((hf.1.continuous_fderiv smooth_ne_zero).norm).pow 2
    have hs : HasCompactSupport fun z => ‖fderiv ℝ f z‖ ^ 2 :=
      (hf.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L => ‖L‖ ^ 2) (by simp)
    exact (hc.integrable_of_hasCompactSupport hs).integrableOn
  zero_mem := (isDNSpace_zeroSpace U).zero_mem
  add_mem := (isDNSpace_zeroSpace U).add_mem
  smul_mem := (isDNSpace_zeroSpace U).smul_mem

lemma proj_pair {U : Set ℂ} (hUH : U ⊆ H) {v : GradSpace H} {μ : Measure ℂ}
    (hv : ∀ f ∈ zeroSpace H, ⟪v, gradFeat H f⟫ = ∫ x, f x ∂μ) :
    ∀ f ∈ zeroSpace U, ⟪projK (zeroSpace U) v, gradFeat H f⟫ = ∫ x, f x ∂μ := by
  intro f hf
  have hfK : gradFeat H f ∈ gradClosure H (zeroSpace U) := gradFeat_mem_gradClosure hf
  unfold projK
  rw [Submodule.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).mpr hfK]
  exact hv f ⟨hf.1, hf.2.1, hf.2.2.trans hUH⟩

theorem dualCov_eq_inner_proj {U : Set ℂ} (hUH : U ⊆ H) {m m' : Measure ℂ}
    (hm : IsAdmissibleDual H (zeroSpace H) m) (hm' : IsAdmissibleDual H (zeroSpace H) m') :
    dualCov U (zeroSpace U) m m' =
      ⟪projK (zeroSpace U) (rieszVec H (zeroSpace H) m),
        projK (zeroSpace U) (rieszVec H (zeroSpace H) m')⟫ := by
  have hEUH : ∀ f ∈ zeroSpace U, dirichletEnergyOn U f = dirichletEnergyOn H f := fun f hf => by
    rw [energy_eq_of_tsupport_subset hf.2.2, energy_eq_of_tsupport_subset (hf.2.2.trans hUH)]
  have hEq : ∀ μ, dualNormSq U (zeroSpace U) μ = dualNormSq H (zeroSpace U) μ := fun μ =>
    dualNormSq_congr_energy hEUH
  have hVUH := isDNSpace_zeroSpace_on H U
  have hVH := isDNSpace_zeroSpace H
  by_cases hpos : ∃ f ∈ zeroSpace H, 0 < dirichletEnergyOn H f
  · have hmem : ∀ x, projK (zeroSpace U) x ∈ gradClosure H (zeroSpace U) := fun x =>
      Submodule.starProjection_apply_mem _ x
    have hN : ∀ {μ : Measure ℂ} {v : GradSpace H},
        (∀ f ∈ zeroSpace H, ⟪v, gradFeat H f⟫ = ∫ x, f x ∂μ) →
        dualNormSq U (zeroSpace U) μ = ENNReal.ofReal (‖projK (zeroSpace U) v‖ ^ 2) := by
      intro μ v hv
      rw [hEq]
      exact dualNormSq_eq_of_pairing hVUH (hmem v) (proj_pair hUH hv)
    have h1 := hN (pair_rieszVec hVH hm hpos)
    have h2 := hN (pair_rieszVec hVH hm' hpos)
    have h3 := hN (pair_add hVH hm hm' hpos)
    have hadd : projK (zeroSpace U) (rieszVec H (zeroSpace H) m + rieszVec H (zeroSpace H) m') =
        projK (zeroSpace U) (rieszVec H (zeroSpace H) m) +
          projK (zeroSpace U) (rieszVec H (zeroSpace H) m') := by
      unfold projK; exact map_add _ _ _
    unfold dualCov
    rw [h1, h2, h3, hadd, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (sq_nonneg _), norm_add_sq_real]
    ring
  · have hposU : ¬ ∃ f ∈ zeroSpace U, 0 < dirichletEnergyOn U f := by
      rintro ⟨f, hf, hp⟩
      exact hpos ⟨f, ⟨hf.1, hf.2.1, hf.2.2.trans hUH⟩, hEUH f hf ▸ hp⟩
    have z1 : rieszVec H (zeroSpace H) m = 0 :=
      eq_zero_of_mem_gradClosure_of_nopos hVH hpos rieszVec_mem
    have z2 : rieszVec H (zeroSpace H) m' = 0 :=
      eq_zero_of_mem_gradClosure_of_nopos hVH hpos rieszVec_mem
    unfold dualCov
    rw [dualNormSq_eq_zero_of_nopos (μ := m + m') hposU, dualNormSq_eq_zero_of_nopos (μ := m) hposU,
      dualNormSq_eq_zero_of_nopos (μ := m') hposU, z1, z2]
    simp [projK]

lemma withDensity_compl_tsupport (g : ℂ → ℝ) :
    (volume.withDensity fun z => ENNReal.ofReal (g z)) (tsupport g)ᶜ = 0 := by
  have hs : MeasurableSet (tsupport g)ᶜ := (isClosed_tsupport g).measurableSet.compl
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 0) (fun z hz => by
    have : g z = 0 := by by_contra h; exact hz (subset_tsupport g h)
    simp [this])]
  simp

lemma admissible_testMeas (ρ : TestFun H) :
    IsAdmissibleDual H (zeroSpace H) (testMeasPos ρ.1) ∧
      IsAdmissibleDual H (zeroSpace H) (testMeasNeg ρ.1) := by
  obtain ⟨hp, hn⟩ := isAdmissibleH_testMeas_of_testFun ρ
  refine ⟨⟨(isGoodMeas_testMeasPos ρ).1, ⟨tsupport ρ.1, ρ.2.2.1,
      ρ.2.2.2.trans subset_closure, withDensity_compl_tsupport ρ.1⟩,
      (dualNormSq_H_le hp).trans_lt ENNReal.ofReal_lt_top⟩,
    ⟨(isGoodMeas_testMeasNeg ρ).1, ⟨tsupport (fun z => -ρ.1 z), ρ.2.2.1.neg,
      ?_, withDensity_compl_tsupport (fun z => -ρ.1 z)⟩,
      (dualNormSq_H_le hn).trans_lt ENNReal.ofReal_lt_top⟩⟩
  exact (tsupport_neg ρ.1).subset.trans (ρ.2.2.2.trans subset_closure)

/-! ## E4 -/

/-- **E4.** A conditional zero-boundary GFF on a random open set `U ω ⊆ ℍ`. -/
theorem exists_condZeroGFF {Ω₀ E : Type*} [MeasurableSpace Ω₀] [MeasurableSpace E]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (Y : Ω₀ → E) (hY : Measurable Y)
    (U : Ω₀ → Set ℂ) (hU : ∀ ω, IsOpen (U ω) ∧ U ω ⊆ H)
    (hE : ∀ j, MeasurableSet {ω | tsupport (testFamily j) ⊆ U ω}) :
    ∃ X' : Ω₀ × (ℕ → ℝ) → FieldSample,
      IsCondZeroBoundaryGFFH (fun p => U p.1) (fun p => Y p.1) X' (P₀.prod stdP) := by
  obtain ⟨v, hv⟩ : ∃ v : Measure ℂ → GradSpace H, v = fun μ => rieszVec H (zeroSpace H) μ :=
    ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X' : Ω₀ × (ℕ → ℝ) → FieldSample,
      X' = fun p μ => gsLim (coefG (projK (zeroSpace (U p.1)) (v μ))) p.2 := ⟨_, rfl⟩
  have hcoef : ∀ μ, Measurable fun ω => coefG (projK (zeroSpace (U ω)) (v μ)) := by
    intro μ
    refine measurable_pi_iff.mpr fun k => ?_
    obtain ⟨z, hz⟩ := coefG_eq_inner k
    simp_rw [hz]
    exact measurable_inner_projK hU hE _ _
  have hXm : ∀ μ, Measurable fun p => X' p μ := fun μ => by
    rw [hX']
    exact measurable_gsLim_comp (a := fun ω => coefG (projK (zeroSpace (U ω)) (v μ))) (hcoef μ)
  refine ⟨X', hXm, ?_⟩
  intro n ρ t F hF ⟨C, hC⟩
  -- the projected vectors
  obtain ⟨w, hw⟩ : ∃ w : Ω₀ → Fin n → GradSpace H, w = fun ω j =>
    projK (zeroSpace (U ω)) (v (testMeasPos (ρ j).1)) -
      projK (zeroSpace (U ω)) (v (testMeasNeg (ρ j).1)) := ⟨_, rfl⟩
  have hcov : ∀ ω j k, zeroGFFTestCov (U ω) (ρ j).1 (ρ k).1 = ⟪w ω j, w ω k⟫ := by
    intro ω j k
    obtain ⟨hjp, hjn⟩ := admissible_testMeas (ρ j)
    obtain ⟨hkp, hkn⟩ := admissible_testMeas (ρ k)
    have hUH := (hU ω).2
    unfold zeroGFFTestCov
    rw [dualCov_eq_inner_proj hUH hjp hkp, dualCov_eq_inner_proj hUH hjp hkn,
      dualCov_eq_inner_proj hUH hjn hkp, dualCov_eq_inner_proj hUH hjn hkn, hw, hv]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hvar : ∀ ω, ‖∑ j, t j • w ω j‖ ^ 2 =
      ∑ j, ∑ k, t j * t k * zeroGFFTestCov (U ω) (ρ j).1 (ρ k).1 := by
    intro ω
    simp_rw [hcov]
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  obtain ⟨S, hS⟩ : ∃ S : Ω₀ × (ℕ → ℝ) → ℝ, S = fun p => ∑ j, t j * pairRaw (X' p) (ρ j).1 :=
    ⟨_, rfl⟩
  have hSm : Measurable S := by
    rw [hS]
    refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
    exact (hXm _).sub (hXm _)
  -- law of the pairing sum for fixed ω
  have hlaw : ∀ ω, HasLaw (fun ξ => S (ω, ξ))
      (gaussianReal 0 (‖∑ j, t j • w ω j‖ ^ 2).toNNReal) stdP := by
    intro ω
    obtain ⟨u, hu⟩ : ∃ u : Fin n ⊕ Fin n → GradSpace H, u = fun i => Sum.elim
      (fun j => projK (zeroSpace (U ω)) (v (testMeasPos (ρ j).1)))
      (fun j => projK (zeroSpace (U ω)) (v (testMeasNeg (ρ j).1))) i := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin n ⊕ Fin n → ℝ, c = fun i => Sum.elim t (fun j => -t j) i :=
      ⟨_, rfl⟩
    have h := hasLaw_sum_gsLimG u c
    have e1 : (fun ξ => ∑ i, c i * gsLim (coefG (u i)) ξ) = fun ξ => S (ω, ξ) := by
      funext ξ
      simp only [hS, hX', pairRaw, Fintype.sum_sum_type, hu, hc, Sum.elim_inl, Sum.elim_inr,
        testMeasPos, testMeasNeg, neg_mul, sub_eq_add_neg, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have e2 : ∑ i, c i • u i = ∑ j, t j • w ω j := by
      simp only [hw, hu, hc, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        neg_smul, sub_eq_add_neg, smul_add, smul_neg, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
    rw [e1, e2] at h
    exact h
  have hchar : ∀ ω, ∫ ξ, Complex.exp (Complex.I * ((S (ω, ξ) : ℝ) : ℂ)) ∂stdP =
      ((Real.exp (-(1 / 2) * ∑ j, ∑ k, t j * t k * zeroGFFTestCov (U ω) (ρ j).1 (ρ k).1) : ℝ)
        : ℂ) := by
    intro ω
    have h := (hlaw ω).integral_comp (f := fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)))
      (by fun_prop)
    have h2 : ∫ x, Complex.exp (Complex.I * (x : ℂ)) ∂(gaussianReal 0
        (‖∑ j, t j • w ω j‖ ^ 2).toNNReal) = charFun (gaussianReal 0
        (‖∑ j, t j • w ω j‖ ^ 2).toNNReal) 1 := by
      rw [charFun_apply_real]
      congr 1; funext x; congr 1; push_cast; ring
    rw [Function.comp_def] at h
    rw [h, h2, charFun_gaussianReal, ← hvar ω, Real.coe_toNNReal _ (sq_nonneg _)]
    push_cast
    congr 1
    ring
  -- Fubini
  have hbd : ∀ p : Ω₀ × (ℕ → ℝ),
      ‖(F (Y p.1) : ℂ) * Complex.exp (Complex.I * ((S p : ℝ) : ℂ))‖ ≤ C := by
    intro p
    have h1 : ‖Complex.exp (Complex.I * ((S p : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hC _
  have hmeasL : Measurable fun p : Ω₀ × (ℕ → ℝ) =>
      (F (Y p.1) : ℂ) * Complex.exp (Complex.I * ((S p : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp (hF.comp (hY.comp measurable_fst))).mul
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hSm)))
  have hint : Integrable (fun p : Ω₀ × (ℕ → ℝ) =>
      (F (Y p.1) : ℂ) * Complex.exp (Complex.I * ((S p : ℝ) : ℂ))) (P₀.prod stdP) :=
    Integrable.of_bound hmeasL.aestronglyMeasurable C (Eventually.of_forall hbd)
  simp only [show ∀ p, ∑ j, t j * pairRaw (X' p) (ρ j).1 = S p from fun p => by rw [hS]]
  rw [integral_prod _ hint]
  simp_rw [integral_const_mul, hchar]
  rw [integral_fun_fst (fun ω => (F (Y ω) : ℂ) *
    ((Real.exp (-(1 / 2) * ∑ j, ∑ k, t j * t k * zeroGFFTestCov (U ω) (ρ j).1 (ρ k).1) : ℝ)
      : ℂ))]
  simp

/-- `IsCondZeroBoundaryGFFH` only depends on `U` up to `P`-a.e. equality. -/
theorem IsCondZeroBoundaryGFFH.congr_ae {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {U U' : Ω → Set ℂ} {Y : Ω → E} {X' : Ω → FieldSample} {P : Measure Ω}
    (h : IsCondZeroBoundaryGFFH U Y X' P) (hUU' : ∀ᵐ ω ∂P, U ω = U' ω) :
    IsCondZeroBoundaryGFFH U' Y X' P := by
  refine ⟨h.measurable_coord, fun n ρ t F hF hFb => ?_⟩
  rw [h.condCharFun n ρ t F hF hFb]
  refine integral_congr_ae ?_
  filter_upwards [hUU'] with ω hω
  rw [hω]

end QuantumZipper.K3
