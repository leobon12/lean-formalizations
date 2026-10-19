import GaussianLQG.Field.Realization.WhiteNoise
import LQGMetric.Field.ExistSFub2
import LQGDimension.Existence.SeriesContinuity
import Mathlib.Topology.UniformSpace.Dini

/-!
# Locally uniform convergence of the coordinate series of the antiderivative field

Let `b` be a Hilbert basis of `L²(ℝ × ℂ)` and `F_k(x) = ⟪rectL2 x, b_k⟫`, where `rectL2 x` is the
white-noise kernel of `LQGMetric`'s antiderivative field (rectangle integrals of the GFF). The
partial sums `S_N(ω)(x) = ∑_{k<N} ω_k F_k(x)` are continuous in `x`. Along a fixed subsequence
`N_j` (chosen with Dini's theorem so that the tails `∑_{k ≥ N_j} F_k(x)²` are `≤ 4^{-j}` on
`B̄_{j+1}(0)`), the partial sums converge almost surely, locally uniformly on `ℂ`.

Proof: the family `(j, x) ↦ S_{N_j}(x)`, indexed by the points `(1 + 4^{-j}, x)` of `ℝ × ℂ`, has
Hölder-½ increments (Bessel's inequality plus the tail bound), so it is almost surely uniformly
continuous on every box (`LQGDimension.SeriesCont.ae_uniformContinuousOn_box`, Lévy–Kolmogorov
chaining). Uniform continuity in the first coordinate, which accumulates at `1`, is uniform
Cauchy-ness of `j ↦ S_{N_j}` on a countable dense set, hence on every closed ball.

The convergence set `goodSet b` is measurable, has full measure and is invariant under finitely
supported shifts (only finitely many terms change). On it, `Ylim b ω` is the limit;
`Yfield b x ω` is the resulting continuous version of `x ↦ W(rectL2 x)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped RealInnerProductSpace

namespace GaussianLQG
namespace Realization

open LQGMetric.GFFExist (rectL2)

/-! ### Continuity of the rectangle kernels -/

lemma sq_norm_rectL2_sub_le {x x' : ℂ} {A : ℝ} (hx : ‖x‖ ≤ A) (hx' : ‖x'‖ ≤ A) :
    ‖rectL2 x - rectL2 x'‖ ^ 2 ≤ (2 * Real.pi + 32 * A ^ 4) * (4 * A * ‖x - x'‖) := by
  rw [LQGMetric.GFFExist.sq_norm_rectL2_sub]
  exact LQGMetric.GFFExist.integral_sq_kerFun_rect_sub_le
    ((Complex.abs_re_le_norm x).trans hx) ((Complex.abs_im_le_norm x).trans hx)
    ((Complex.abs_re_le_norm x').trans hx') ((Complex.abs_im_le_norm x').trans hx')

lemma sq_norm_rectL2_le {x : ℂ} {L : ℝ} (hx : ‖x‖ ≤ L) :
    ‖rectL2 x‖ ^ 2 ≤ (2 * Real.pi + 32 * L ^ 4) * (4 * L * L) := by
  rw [LQGMetric.GFFExist.sq_norm_rectL2]
  exact LQGMetric.GFFExist.integral_sq_kerFun_rect_le hx

lemma continuous_rectL2 : Continuous rectL2 := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set A : ℝ := ‖x₀‖ + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  set K : ℝ := (2 * Real.pi + 32 * A ^ 4) * (4 * A) with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ᶠ x in 𝓝 x₀, ‖rectL2 x - rectL2 x₀‖ ≤ √(K * ‖x - x₀‖) := by
    filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    have hxA : ‖x‖ ≤ A := by
      have h1 : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
        have := norm_add_le (x - x₀) x₀
        rwa [sub_add_cancel] at this
      have h2 : ‖x - x₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hx
      linarith
    have hx0A : ‖x₀‖ ≤ A := by linarith
    have h := sq_norm_rectL2_sub_le hxA hx0A
    rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
    calc ‖rectL2 x - rectL2 x₀‖ ^ 2 ≤ (2 * Real.pi + 32 * A ^ 4) * (4 * A * ‖x - x₀‖) := h
      _ = K * ‖x - x₀‖ := by rw [hK]; ring
  have hlim : Tendsto (fun x => √(K * ‖x - x₀‖)) (𝓝 x₀) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℂ => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_id (x := 𝓝 x₀))
    have h2 := (h1.const_mul K).sqrt
    rwa [mul_zero, Real.sqrt_zero] at h2
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

variable (b : HilbertBasis ℕ ℝ WNSpace)

/-- `F_k(x) = ⟪rectL2 x, b_k⟫`. -/
def rectCoef (x : ℂ) : ℕ → ℝ := coef b (rectL2 x)

lemma continuous_rectCoef (k : ℕ) : Continuous fun x => rectCoef b x k :=
  continuous_rectL2.inner continuous_const

lemma summable_rectCoef_sq (x : ℂ) : Summable fun k => rectCoef b x k ^ 2 :=
  summable_coef_sq b _

lemma tsum_sq_rectCoef_sub (x x' : ℂ) :
    ∑' k, (rectCoef b x k - rectCoef b x' k) ^ 2 = ‖rectL2 x - rectL2 x'‖ ^ 2 := by
  rw [← tsum_coef_sq b (rectL2 x - rectL2 x')]
  exact tsum_congr fun k => by rw [coef_sub]; rfl

/-- The partial sums `S_N(ω)(x) = ∑_{k<N} ω_k F_k(x)`. -/
def fieldSum (N : ℕ) (ω : Coord) (x : ℂ) : ℝ := psum (rectCoef b x) N ω

lemma continuous_fieldSum (N : ℕ) (ω : Coord) : Continuous (fieldSum b N ω) := by
  unfold fieldSum psum
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_rectCoef b k)

lemma measurable_fieldSum (N : ℕ) (x : ℂ) : Measurable fun ω => fieldSum b N ω x :=
  measurable_psum _ _

/-! ### Uniform smallness of the tails (Dini) -/

lemma sqTail_rectCoef_eq (x : ℂ) (N : ℕ) :
    sqTail (rectCoef b x) N = ‖rectL2 x‖ ^ 2 - ∑ k ∈ Finset.range N, rectCoef b x k ^ 2 := by
  have h := sum_range_add_sqTail (summable_rectCoef_sq b x) N
  rw [show (∑' k, rectCoef b x k ^ 2) = ‖rectL2 x‖ ^ 2 from tsum_coef_sq b _] at h
  linarith

lemma continuous_sqTail_rectCoef (N : ℕ) : Continuous fun x => sqTail (rectCoef b x) N := by
  simp_rw [sqTail_rectCoef_eq]
  exact (continuous_rectL2.norm.pow 2).sub
    (continuous_finsetSum _ fun k _ => (continuous_rectCoef b k).pow 2)

lemma sqTail_rectCoef_le (x : ℂ) (N : ℕ) : sqTail (rectCoef b x) N ≤ ‖rectL2 x‖ ^ 2 := by
  rw [sqTail_rectCoef_eq]
  have : 0 ≤ ∑ k ∈ Finset.range N, rectCoef b x k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma exists_sqTail_le (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N ≥ M, ∀ x ∈ closedBall (0 : ℂ) r, sqTail (rectCoef b x) N ≤ ε := by
  have hU : TendstoUniformlyOn (fun N x => sqTail (rectCoef b x) N) (fun _ => (0 : ℝ)) atTop
      (closedBall (0 : ℂ) r) :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto (isCompact_closedBall _ _)
      (fun N => (continuous_sqTail_rectCoef b N).continuousOn)
      (fun x _ => fun i j hij => sqTail_anti (summable_rectCoef_sq b x) hij)
      continuousOn_const (fun x _ => tendsto_sqTail _)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hU ε hε)
  refine ⟨M, fun N hN x hx => ?_⟩
  have := hM N hN x hx
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (sqTail_nonneg _ _)] at this
  exact this.le

/-! ### The subsequence -/

/-- An index after which the tails are `≤ 4^{-j}` on `B̄_{j+1}(0)`. -/
def tailIdx (j : ℕ) : ℕ :=
  (exists_sqTail_le b ((j : ℝ) + 1) (pow_pos (by norm_num : (0 : ℝ) < 4⁻¹) j)).choose

lemma tailIdx_spec (j : ℕ) : ∀ N ≥ tailIdx b j, ∀ x ∈ closedBall (0 : ℂ) ((j : ℝ) + 1),
    sqTail (rectCoef b x) N ≤ (4⁻¹ : ℝ) ^ j :=
  (exists_sqTail_le b ((j : ℝ) + 1) (pow_pos (by norm_num : (0 : ℝ) < 4⁻¹) j)).choose_spec

/-- The subsequence `N_j`. -/
def subN (j : ℕ) : ℕ := (∑ i ∈ Finset.range (j + 1), tailIdx b i) + j

lemma strictMono_subN : StrictMono (subN b) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  simp only [subN, Finset.sum_range_succ _ (j + 1)]
  omega

lemma tailIdx_le_subN (j : ℕ) : tailIdx b j ≤ subN b j := by
  have := Finset.single_le_sum (f := tailIdx b) (fun i _ => Nat.zero_le _)
    (Finset.self_mem_range_succ j)
  simp only [subN]
  omega

lemma le_subN (j : ℕ) : j ≤ subN b j := by
  simp only [subN]
  omega

/-- A bound for the tails along the subsequence on `B̄_{m+1}(0)`, for every `j`. -/
def tailConst (m : ℕ) : ℝ :=
  max 1 ((2 * Real.pi + 32 * ((m : ℝ) + 1) ^ 4) * (4 * ((m : ℝ) + 1) * ((m : ℝ) + 1)) * 4 ^ m)

lemma one_le_tailConst (m : ℕ) : 1 ≤ tailConst m := le_max_left _ _

lemma sqTail_subN_le (m j : ℕ) {x : ℂ} (hx : ‖x‖ ≤ (m : ℝ) + 1) :
    sqTail (rectCoef b x) (subN b j) ≤ tailConst m * (4⁻¹ : ℝ) ^ j := by
  rcases le_or_gt m j with hmj | hjm
  · have hx' : x ∈ closedBall (0 : ℂ) ((j : ℝ) + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have : (m : ℝ) ≤ j := by exact_mod_cast hmj
      linarith
    have h := tailIdx_spec b j (subN b j) (tailIdx_le_subN b j) x hx'
    have h4 : 0 ≤ (4⁻¹ : ℝ) ^ j := by positivity
    calc sqTail (rectCoef b x) (subN b j) ≤ (4⁻¹ : ℝ) ^ j := h
      _ = 1 * (4⁻¹ : ℝ) ^ j := (one_mul _).symm
      _ ≤ tailConst m * (4⁻¹ : ℝ) ^ j := mul_le_mul_of_nonneg_right (one_le_tailConst m) h4
  · have h1 := (sqTail_rectCoef_le b x (subN b j)).trans (sq_norm_rectL2_le hx)
    set Q := (2 * Real.pi + 32 * ((m : ℝ) + 1) ^ 4) * (4 * ((m : ℝ) + 1) * ((m : ℝ) + 1))
      with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have h4 : (1 : ℝ) ≤ 4 ^ m * (4⁻¹ : ℝ) ^ j := by
      have : (4 : ℝ) ^ m * (4⁻¹ : ℝ) ^ j = 4 ^ (m - j) := by
        rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (by positivity), ← pow_add,
          Nat.sub_add_cancel hjm.le]
      rw [this]
      exact one_le_pow₀ (by norm_num)
    calc sqTail (rectCoef b x) (subN b j) ≤ Q := h1
      _ = Q * 1 := (mul_one _).symm
      _ ≤ Q * (4 ^ m * (4⁻¹ : ℝ) ^ j) := mul_le_mul_of_nonneg_left h4 hQ0
      _ = (Q * 4 ^ m) * (4⁻¹ : ℝ) ^ j := by ring
      _ ≤ tailConst m * (4⁻¹ : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ### Increments of the truncated coefficient families -/

lemma tsum_sq_truncCoef_sub_le {a a' : ℕ → ℝ} (ha' : Summable fun k => a' k ^ 2)
    (hd : Summable fun k => (a k - a' k) ^ 2) {i i' : ℕ} (hii' : i ≤ i') :
    ∑' k, (truncCoef a i k - truncCoef a' i' k) ^ 2 ≤
      ∑' k, (a k - a' k) ^ 2 + (sqTail a' i - sqTail a' i') := by
  rw [tsum_eq_sum (s := Finset.range i') fun k hk => by
    have hk' : i' ≤ k := by simpa using hk
    rw [truncCoef_eq_zero a (hii'.trans hk'), truncCoef_eq_zero a' hk', sub_zero,
      zero_pow two_ne_zero]]
  rw [← Finset.sum_range_add_sum_Ico _ hii', sqTail_sub_sqTail ha' hii']
  refine add_le_add ?_ (le_of_eq ?_)
  · have e : ∑ k ∈ Finset.range i, (truncCoef a i k - truncCoef a' i' k) ^ 2 =
        ∑ k ∈ Finset.range i, (a k - a' k) ^ 2 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < i := Finset.mem_range.mp hk
      simp [truncCoef, hk', lt_of_lt_of_le hk' hii']
    rw [e]
    exact hd.sum_le_tsum _ fun _ _ => sq_nonneg _
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    simp [truncCoef, not_lt.mpr hk1, hk2]

/-! ### The embedding into the index space `ℝ × ℂ` of `LQGDimension` -/

/-- The first coordinate `1 + 4^{-j}` encoding the subsequence index `j`. -/
def epsJ (j : ℕ) : ℝ := 1 + (4⁻¹ : ℝ) ^ j

lemma epsJ_strictAnti : StrictAnti epsJ := fun i j hij => by
  simp only [epsJ]
  have := pow_lt_pow_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 4⁻¹) (by norm_num) hij
  linarith

lemma epsJ_injective : Function.Injective epsJ := epsJ_strictAnti.injective

lemma one_lt_epsJ (j : ℕ) : 1 < epsJ j := by
  simp only [epsJ]; have : (0 : ℝ) < (4⁻¹ : ℝ) ^ j := by positivity
  linarith

lemma epsJ_le_two (j : ℕ) : epsJ j ≤ 2 := by
  simp only [epsJ]; have : (4⁻¹ : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma sub_epsJ_ge {j j' : ℕ} (h : j < j') : (3 / 4 : ℝ) * (4⁻¹ : ℝ) ^ j ≤ epsJ j - epsJ j' := by
  simp only [epsJ]
  have h1 : (4⁻¹ : ℝ) ^ j' ≤ (4⁻¹ : ℝ) ^ (j + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  rw [pow_succ] at h1
  linarith

open Classical in
/-- The coefficient family indexed by `ℝ × ℂ`: at `(1 + 4^{-j}, x)` it is the truncation of
`(F_k(x))_k` at `N_j`; elsewhere it vanishes. -/
def vCoef (t : ℝ × ℂ) (k : ℕ) : ℝ :=
  if h : ∃ j, epsJ j = t.1 then truncCoef (rectCoef b t.2) (subN b h.choose) k else 0

lemma vCoef_apply (j : ℕ) (x : ℂ) (k : ℕ) :
    vCoef b (epsJ j, x) k = truncCoef (rectCoef b x) (subN b j) k := by
  have h : ∃ j', epsJ j' = (epsJ j, x).1 := ⟨j, rfl⟩
  have hc : h.choose = j := epsJ_injective h.choose_spec
  simp only [vCoef, dite_eq_left h, hc]

lemma vCoef_fin (t : ℝ × ℂ) : ∃ N, ∀ k ≥ N, vCoef b t k = 0 := by
  classical
  by_cases h : ∃ j, epsJ j = t.1
  · obtain ⟨j, hj⟩ := h
    refine ⟨subN b j, fun k hk => ?_⟩
    have ht : t = (epsJ j, t.2) := by rw [hj]
    rw [ht, vCoef_apply]
    exact truncCoef_eq_zero _ hk
  · refine ⟨0, fun k _ => ?_⟩
    simp only [vCoef, dite_eq_right h]

lemma tsum_vCoef_mul (j : ℕ) (x : ℂ) (ω : Coord) :
    ∑' k, vCoef b (epsJ j, x) k * ω k = fieldSum b (subN b j) ω x := by
  simp_rw [vCoef_apply]
  exact tsum_truncCoef_mul _ _ _

/-- The fixed countable dense set of `ℂ`. -/
def denseSet : Set ℂ := (TopologicalSpace.exists_countable_dense ℂ).choose

lemma denseSet_countable : denseSet.Countable :=
  (TopologicalSpace.exists_countable_dense ℂ).choose_spec.1

lemma denseSet_dense : Dense denseSet :=
  (TopologicalSpace.exists_countable_dense ℂ).choose_spec.2

/-- The countable index set `{(1 + 4^{-j}, x) : j ∈ ℕ, x ∈ D}`. -/
def idxSet : Set (ℝ × ℂ) := (fun p : ℕ × ℂ => (epsJ p.1, p.2)) '' (univ ×ˢ denseSet)

lemma idxSet_countable : idxSet.Countable :=
  ((countable_univ (α := ℕ)).prod denseSet_countable).image _

lemma variance_bound (m : ℕ) :
    ∀ s ∈ idxSet, ∀ t ∈ idxSet, s ∈ LQGDimension.Blueprint.Existence.box m →
      t ∈ LQGDimension.Blueprint.Existence.box m →
      ∑' k, (vCoef b s k - vCoef b t k) ^ 2 ≤
        ((2 * Real.pi + 32 * ((m : ℝ) + 1) ^ 4) * (4 * ((m : ℝ) + 1)) +
          4 / 3 * tailConst m) * ‖s - t‖ := by
  rintro s ⟨⟨j, x⟩, -, rfl⟩ t ⟨⟨j', x'⟩, -, rfl⟩ hs ht
  simp only at hs ht ⊢
  have hxm : ‖x‖ ≤ (m : ℝ) + 1 := by
    have := (mem_prod.mp hs).2; rwa [mem_closedBall, dist_zero_right] at this
  have hx'm : ‖x'‖ ≤ (m : ℝ) + 1 := by
    have := (mem_prod.mp ht).2; rwa [mem_closedBall, dist_zero_right] at this
  set K := (2 * Real.pi + 32 * ((m : ℝ) + 1) ^ 4) * (4 * ((m : ℝ) + 1)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hT0 : 0 ≤ tailConst m := zero_le_one.trans (one_le_tailConst m)
  have hnorm1 : ‖x - x'‖ ≤ ‖(epsJ j, x) - (epsJ j', x')‖ := by
    rw [Prod.norm_def]; exact le_max_right _ _
  have hnorm2 : |epsJ j - epsJ j'| ≤ ‖(epsJ j, x) - (epsJ j', x')‖ := by
    rw [Prod.norm_def]; exact le_trans (le_of_eq (Real.norm_eq_abs _).symm) (le_max_left _ _)
  have hbes : ∑' k, (rectCoef b x k - rectCoef b x' k) ^ 2 ≤ K * ‖x - x'‖ := by
    rw [tsum_sq_rectCoef_sub]
    calc ‖rectL2 x - rectL2 x'‖ ^ 2
        ≤ (2 * Real.pi + 32 * ((m : ℝ) + 1) ^ 4) * (4 * ((m : ℝ) + 1) * ‖x - x'‖) :=
          sq_norm_rectL2_sub_le hxm hx'm
      _ = K * ‖x - x'‖ := by rw [hK]; ring
  have hd : Summable fun k => (rectCoef b x k - rectCoef b x' k) ^ 2 :=
    summable_sq_sub (summable_rectCoef_sq b x) (summable_rectCoef_sq b x')
  simp_rw [vCoef_apply]
  -- the tail term
  have htail : ∀ {y : ℂ} {i i' : ℕ}, ‖y‖ ≤ (m : ℝ) + 1 → i ≤ i' →
      sqTail (rectCoef b y) (subN b i) - sqTail (rectCoef b y) (subN b i') ≤
        4 / 3 * tailConst m * |epsJ i - epsJ i'| := by
    intro y i i' hy hii'
    rcases hii'.lt_or_eq with hlt | heq
    · have h1 := sqTail_subN_le b m i hy
      have h2 := sqTail_nonneg (rectCoef b y) (subN b i')
      have h3 := sub_epsJ_ge hlt
      rw [abs_of_pos (by linarith [h3, show (0 : ℝ) < (4⁻¹ : ℝ) ^ i by positivity])]
      nlinarith
    · subst heq; simp
  rcases le_total j j' with hjj | hjj
  · have h := tsum_sq_truncCoef_sub_le (summable_rectCoef_sq b x') hd
      ((strictMono_subN b).monotone hjj)
    have ht' := htail hx'm hjj
    calc ∑' k, (truncCoef (rectCoef b x) (subN b j) k -
          truncCoef (rectCoef b x') (subN b j') k) ^ 2
        ≤ K * ‖x - x'‖ + 4 / 3 * tailConst m * |epsJ j - epsJ j'| := by linarith
      _ ≤ K * ‖(epsJ j, x) - (epsJ j', x')‖ +
          4 / 3 * tailConst m * ‖(epsJ j, x) - (epsJ j', x')‖ := by
          gcongr
      _ = _ := by ring
  · have hd' : Summable fun k => (rectCoef b x' k - rectCoef b x k) ^ 2 :=
      summable_sq_sub (summable_rectCoef_sq b x') (summable_rectCoef_sq b x)
    have h := tsum_sq_truncCoef_sub_le (summable_rectCoef_sq b x) hd'
      ((strictMono_subN b).monotone hjj)
    have ht' := htail hxm hjj
    have e1 : ∑' k, (truncCoef (rectCoef b x) (subN b j) k -
        truncCoef (rectCoef b x') (subN b j') k) ^ 2 =
        ∑' k, (truncCoef (rectCoef b x') (subN b j') k -
          truncCoef (rectCoef b x) (subN b j) k) ^ 2 := tsum_congr fun k => by ring
    have e2 : ∑' k, (rectCoef b x' k - rectCoef b x k) ^ 2 =
        ∑' k, (rectCoef b x k - rectCoef b x' k) ^ 2 := tsum_congr fun k => by ring
    rw [abs_sub_comm] at ht'
    rw [e1]
    calc ∑' k, (truncCoef (rectCoef b x') (subN b j') k -
          truncCoef (rectCoef b x) (subN b j) k) ^ 2
        ≤ K * ‖x - x'‖ + 4 / 3 * tailConst m * |epsJ j - epsJ j'| := by linarith
      _ ≤ K * ‖(epsJ j, x) - (epsJ j', x')‖ +
          4 / 3 * tailConst m * ‖(epsJ j, x) - (epsJ j', x')‖ := by
          gcongr
      _ = _ := by ring

/-! ### The convergence set -/

/-- The partial sums along the subsequence are uniformly Cauchy on every `D ∩ B̄_{m+1}(0)`. -/
def goodSet : Set Coord :=
  {ω | ∀ m i : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ j' : ℕ, J ≤ j' →
    ∀ x : ↥(denseSet ∩ closedBall (0 : ℂ) ((m : ℝ) + 1)),
      |fieldSum b (subN b j) ω x - fieldSum b (subN b j') ω x| ≤ 1 / ((i : ℝ) + 1)}

lemma measurableSet_goodSet : MeasurableSet (goodSet b) := by
  have hc : ∀ m : ℕ, Countable ↥(denseSet ∩ closedBall (0 : ℂ) ((m : ℝ) + 1)) := fun m =>
    (denseSet_countable.mono inter_subset_left).to_subtype
  refine measurableSet_setOfPred.mpr ?_
  refine Measurable.forall fun m => Measurable.forall fun i => Measurable.exists fun J =>
    Measurable.forall fun j => ?_
  refine Measurable.forall fun hj => Measurable.forall fun j' => Measurable.forall fun hj' => ?_
  have := hc m
  refine Measurable.forall fun x => ?_
  refine measurableSet_setOfPred.mp (measurableSet_le ?_ measurable_const)
  exact continuous_abs.measurable.comp ((measurable_fieldSum b _ _).sub (measurable_fieldSum b _ _))

theorem ae_mem_goodSet : ∀ᵐ ω ∂stdP, ω ∈ goodSet b := by
  have hall : ∀ᵐ ω ∂stdP, ∀ m : ℕ, UniformContinuousOn (fun t => ∑' k, vCoef b t k * ω k)
      (idxSet ∩ LQGDimension.Blueprint.Existence.box (m + 1)) := by
    rw [ae_all_iff]
    intro m
    exact LQGDimension.SeriesCont.ae_uniformContinuousOn_box idxSet idxSet_countable (vCoef b)
      (vCoef_fin b) (m + 1) _ (variance_bound b (m + 1))
  filter_upwards [hall] with ω hω
  intro m i
  have hU := Metric.uniformContinuousOn_iff.mp (hω m) (1 / ((i : ℝ) + 1)) (by positivity)
  obtain ⟨δ, hδ, hδU⟩ := hU
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (4⁻¹ : ℝ) < 1)
  refine ⟨J, fun j hj j' hj' x => ?_⟩
  have hmem : ∀ l : ℕ, (epsJ l, (x : ℂ)) ∈ idxSet ∩ LQGDimension.Blueprint.Existence.box (m + 1) := by
    intro l
    refine ⟨⟨(l, x), ⟨mem_univ _, x.2.1⟩, rfl⟩, ?_⟩
    refine mk_mem_prod ⟨?_, ?_⟩ ?_
    · have h1 := one_lt_epsJ l
      have h2 : 1 / (((m + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
      linarith
    · have h1 := epsJ_le_two l
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
    · have h := x.2.2
      rw [mem_closedBall] at h ⊢
      push_cast; linarith
  have hdist : dist (epsJ j, (x : ℂ)) (epsJ j', (x : ℂ)) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
    have hb : ∀ l, J ≤ l → epsJ l ∈ Icc 1 (1 + (4⁻¹ : ℝ) ^ J) := by
      intro l hl
      refine ⟨(one_lt_epsJ l).le, ?_⟩
      simp only [epsJ]
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 4⁻¹) (by norm_num) hl
      linarith
    have h1 := hb j hj
    have h2 := hb j' hj'
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have := hδU _ (hmem j) _ (hmem j') hdist
  rw [Real.dist_eq, tsum_vCoef_mul, tsum_vCoef_mul] at this
  exact this.le

/-! ### Shift invariance -/

lemma fieldSum_shift (N : ℕ) (ω : Coord) (v : ℕ →₀ ℝ) (x : ℂ) (hN : suppBound v ≤ N) :
    fieldSum b N (shiftBy ω v) x = fieldSum b N ω x + v.sum fun k c => c * rectCoef b x k := by
  unfold fieldSum
  rw [psum_shift, psum_finsupp _ v hN]

theorem shiftBy_mem_goodSet {ω : Coord} (hω : ω ∈ goodSet b) (v : ℕ →₀ ℝ) :
    shiftBy ω v ∈ goodSet b := by
  intro m i
  obtain ⟨J, hJ⟩ := hω m i
  refine ⟨max J (suppBound v), fun j hj j' hj' x => ?_⟩
  have h1 : suppBound v ≤ subN b j := (le_of_max_le_right hj).trans (le_subN b j)
  have h2 : suppBound v ≤ subN b j' := (le_of_max_le_right hj').trans (le_subN b j')
  rw [fieldSum_shift b _ ω v x h1, fieldSum_shift b _ ω v x h2]
  have := hJ j (le_of_max_le_left hj) j' (le_of_max_le_left hj') x
  rwa [add_sub_add_right_eq_sub]

/-! ### The limit -/

/-- The limit of the partial sums along the subsequence. -/
def Ylim (ω : Coord) (x : ℂ) : ℝ := limUnder atTop fun j => fieldSum b (subN b j) ω x

lemma uniformCauchySeqOn_of_mem {ω : Coord} (hω : ω ∈ goodSet b) (m : ℕ) :
    UniformCauchySeqOn (fun j => fieldSum b (subN b j) ω) atTop (closedBall (0 : ℂ) m) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
  obtain ⟨J, hJ⟩ := hω m i
  refine ⟨J, fun j hj j' hj' x hx => ?_⟩
  rw [Real.dist_eq]
  refine lt_of_le_of_lt ?_ hi
  -- density: the bound holds on `D ∩ B_{m+1}(0)`, hence on its closure
  set g : ℂ → ℝ := fun y => |fieldSum b (subN b j) ω y - fieldSum b (subN b j') ω y| with hg
  have hgc : Continuous g :=
    ((continuous_fieldSum b _ ω).sub (continuous_fieldSum b _ ω)).abs
  have hclosed : IsClosed {y | g y ≤ 1 / ((i : ℝ) + 1)} := isClosed_le hgc continuous_const
  have hsub : ball (0 : ℂ) ((m : ℝ) + 1) ∩ denseSet ⊆ {y | g y ≤ 1 / ((i : ℝ) + 1)} := by
    intro y hy
    exact hJ j hj j' hj' ⟨y, hy.2, ball_subset_closedBall hy.1⟩
  have hx' : x ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_ball]; rw [mem_closedBall] at hx; linarith
  have := denseSet_dense.open_subset_closure_inter isOpen_ball hx'
  exact (closure_minimal hsub hclosed) this

lemma tendsto_Ylim {ω : Coord} (hω : ω ∈ goodSet b) (x : ℂ) :
    Tendsto (fun j => fieldSum b (subN b j) ω x) atTop (𝓝 (Ylim b ω x)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  have hx : x ∈ closedBall (0 : ℂ) m := by rwa [mem_closedBall, dist_zero_right]
  have hC := (uniformCauchySeqOn_of_mem b hω m).cauchySeq hx
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hC)

lemma tendstoUniformlyOn_Ylim {ω : Coord} (hω : ω ∈ goodSet b) (m : ℕ) :
    TendstoUniformlyOn (fun j => fieldSum b (subN b j) ω) (Ylim b ω) atTop
      (closedBall (0 : ℂ) m) :=
  (uniformCauchySeqOn_of_mem b hω m).tendstoUniformlyOn_of_tendsto fun x _ =>
    tendsto_Ylim b hω x

lemma tendstoLocallyUniformly_Ylim {ω : Coord} (hω : ω ∈ goodSet b) :
    TendstoLocallyUniformly (fun j => fieldSum b (subN b j) ω) (Ylim b ω) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨m, hm⟩ := exists_nat_ge r
  exact (tendstoUniformlyOn_Ylim b hω m).mono (hr.trans (closedBall_subset_closedBall hm))

lemma continuous_Ylim {ω : Coord} (hω : ω ∈ goodSet b) : Continuous (Ylim b ω) :=
  (tendstoLocallyUniformly_Ylim b hω).continuous
    (Frequently.of_forall fun _ => continuous_fieldSum b _ ω)

/-- The continuous version of the antiderivative field (zero off the convergence set). -/
def Yfield (x : ℂ) (ω : Coord) : ℝ := (goodSet b).indicator (fun ω => Ylim b ω x) ω

lemma Yfield_of_mem {ω : Coord} (hω : ω ∈ goodSet b) (x : ℂ) : Yfield b x ω = Ylim b ω x := by
  simp only [Yfield, indicator_of_mem hω]

theorem continuous_Yfield (ω : Coord) : Continuous fun x => Yfield b x ω := by
  by_cases hω : ω ∈ goodSet b
  · simp only [Yfield, indicator_of_mem hω]; exact continuous_Ylim b hω
  · simp only [Yfield, indicator_of_notMem hω]; exact continuous_const

theorem measurable_Yfield (x : ℂ) : Measurable (Yfield b x) := by
  refine Measurable.indicator ?_ (measurableSet_goodSet b)
  exact (StronglyMeasurable.limUnder fun j =>
    (measurable_fieldSum b (subN b j) x).stronglyMeasurable).measurable

/-- The continuous field is a version of `x ↦ W(rectL2 x)`. -/
theorem ae_Yfield_eq (x : ℂ) :
    (fun ω => Yfield b x ω) =ᵐ[stdP] wnOf b (rectL2 x) := by
  filter_upwards [ae_mem_goodSet b, ae_tendsto_wnOf b (rectL2 x)] with ω hω hW
  rw [Yfield_of_mem b hω]
  have h1 := tendsto_Ylim b hω x
  have h2 : Tendsto (fun j => fieldSum b (subN b j) ω x) atTop (𝓝 (wnOf b (rectL2 x) ω)) :=
    hW.comp (strictMono_subN b).tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-- **Shift compatibility of the continuous field.** -/
theorem Yfield_shift {ω : Coord} (hω : ω ∈ goodSet b) (v : ℕ →₀ ℝ) (x : ℂ) :
    Yfield b x (shiftBy ω v) = Yfield b x ω + v.sum fun k c => c * rectCoef b x k := by
  have hω' := shiftBy_mem_goodSet b hω v
  rw [Yfield_of_mem b hω', Yfield_of_mem b hω]
  have h1 := tendsto_Ylim b hω' x
  have h2 : Tendsto (fun j => fieldSum b (subN b j) (shiftBy ω v) x) atTop
      (𝓝 (Ylim b ω x + v.sum fun k c => c * rectCoef b x k)) := by
    have h := (tendsto_Ylim b hω x).add_const (v.sum fun k c => c * rectCoef b x k)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (suppBound v)] with j hj
    exact (fieldSum_shift b _ ω v x (hj.trans (le_subN b j))).symm
  exact tendsto_nhds_unique h1 h2

end Realization
end GaussianLQG
