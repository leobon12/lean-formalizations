import GaussianLQG.Probability.GaussianLp.Split

/-!
# Coordinate derivatives and their almost-sure existence

Blueprint Proposition `prop:gaussian-Lp`, part (a). For `F : ℝ^ℕ → ℝ` the coordinate derivative is
`∂_j F(ω) = d/dt|_{t=0} F(ω + t δ_j)`, with the junk value `0` where the derivative does not exist
(`coordDeriv`, matching the blueprint's convention).

Hypothesis (H): a measurable set `𝒢` of full measure and constants `L_j` with
`|F(ω + v) - F(ω + v')| ≤ ∑_j L_j |v_j - v'_j|` for `ω ∈ 𝒢` and finitely supported `v, v'`
(`ShiftLipschitzOn`; the points `ω + v` need not lie in `𝒢`).

* `ShiftLipschitzOn.line`, `ShiftLipschitzOn.joinN_le`: (H) along a coordinate line through a
  point of `𝒢`, and along the first `n` coordinates through a point `(x₀, y) ∈ 𝒢`;
  `ae_exists_joinN_mem`: for a.e. `y` some `(x₀, y)` lies in `𝒢`, so `x ↦ F(x, y)` is Lipschitz on
  all of `ℝⁿ`.
* `ratCauchySet`: the measurable set where the difference quotients at `0` along rational
  increments satisfy the Cauchy condition. It contains every point where the line derivative exists,
  and at points where the line function is continuous the converse holds.
* `ae_differentiableAt_coord` (part (a)): `∂_j F(ω)` exists for a.e. `ω`.
  Proof: split `ω = (x, y)` with `x ∈ ℝ^{j+1}`. For a.e. `y`, `x ↦ F(x, y)` is Lipschitz, hence
  differentiable at Lebesgue-a.e. (so Gaussian-a.e.) `x` by Rademacher's theorem, and then the line
  derivative at `(x, y)` exists. By Fubini (`ratCauchySet` is measurable) a.e. `ω` lies in
  `ratCauchySet`, and on `𝒢 ∩ ratCauchySet` the line derivative exists.
* `aestronglyMeasurable_coordDeriv`: `∂_j F` is a.e. the limit of the measurable difference
  quotients `(k+1)(F(ω + δ_j/(k+1)) - F(ω))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

/-- The coordinate derivative `∂_j F(ω) = d/dt|_{t=0} F(ω + t δ_j)`; junk value `0` where the
derivative does not exist (blueprint §2, "The Gaussian `L^p` inequality"). -/
def coordDeriv (F : Coord → ℝ) (j : ℕ) (ω : Coord) : ℝ :=
  deriv (fun t : ℝ => F (shiftBy ω (Finsupp.single j t))) 0

namespace GaussLp

/-- Hypothesis (H) of blueprint Proposition `prop:gaussian-Lp`: for every `ω ∈ 𝒢` and finitely
supported `v, v'`, `|F(ω + v) - F(ω + v')| ≤ ∑_j L_j |v_j - v'_j|`. -/
def ShiftLipschitzOn (F : Coord → ℝ) (𝒢 : Set Coord) (L : ℕ → ℝ) : Prop :=
  ∀ ω ∈ 𝒢, ∀ v v' : ℕ →₀ ℝ,
    |F (shiftBy ω v) - F (shiftBy ω v')| ≤ ∑ j ∈ v.support ∪ v'.support, L j * |v j - v' j|

lemma shiftBy_apply (ω : Coord) (v : ℕ →₀ ℝ) (i : ℕ) : shiftBy ω v i = ω i + v i := rfl

@[simp] lemma shiftBy_zero (ω : Coord) : shiftBy ω 0 = ω := by
  funext i
  simp [shiftBy_apply]

@[simp] lemma shiftBy_single_zero (ω : Coord) (j : ℕ) : shiftBy ω (Finsupp.single j 0) = ω := by
  simp

/-- The weighted `ℓ¹` sum over the union of the supports equals the sum over any finite set
containing both supports. -/
lemma sum_support_union_eq {S : Finset ℕ} {v v' : ℕ →₀ ℝ} (hv : v.support ⊆ S)
    (hv' : v'.support ⊆ S) (L : ℕ → ℝ) :
    ∑ j ∈ v.support ∪ v'.support, L j * |v j - v' j| = ∑ j ∈ S, L j * |v j - v' j| := by
  refine Finset.sum_subset (Finset.union_subset hv hv') fun i _ hi => ?_
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hi
  rw [hi.1, hi.2, sub_self, abs_zero, mul_zero]

/-- The finitely supported vector whose first `n` coordinates are `x`. -/
def blockVec (n : ℕ) (x : Fin n → ℝ) : ℕ →₀ ℝ :=
  Finsupp.onFinset (Finset.range n) (fun i => if h : i < n then x ⟨i, h⟩ else 0) (by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    simp [h] at hi)

lemma blockVec_apply (n : ℕ) (x : Fin n → ℝ) (i : ℕ) :
    blockVec n x i = if h : i < n then x ⟨i, h⟩ else 0 :=
  Finsupp.onFinset_apply

lemma support_blockVec (n : ℕ) (x : Fin n → ℝ) : (blockVec n x).support ⊆ Finset.range n :=
  Finsupp.support_onFinset_subset

lemma shiftBy_joinN_blockVec (n : ℕ) (x₀ x : Fin n → ℝ) (y : Coord) :
    shiftBy (joinN n x₀ y) (blockVec n (x - x₀)) = joinN n x y := by
  funext i
  rw [shiftBy_apply, blockVec_apply]
  by_cases h : i < n
  · simp [joinN, h]
  · simp [joinN, h]

lemma shiftBy_joinN_single {n j : ℕ} (hj : j < n) (x : Fin n → ℝ) (y : Coord) (t : ℝ) :
    shiftBy (joinN n x y) (Finsupp.single j t) =
      joinN n (x + t • Pi.single (⟨j, hj⟩ : Fin n) (1 : ℝ)) y := by
  funext i
  rw [shiftBy_apply, Finsupp.single_apply]
  by_cases h : i < n
  · rw [joinN_apply_of_lt n _ _ h, joinN_apply_of_lt n _ _ h]
    by_cases hji : j = i
    · subst hji
      simp
    · have hne : (⟨i, h⟩ : Fin n) ≠ ⟨j, hj⟩ := fun e => hji (congrArg Fin.val e).symm
      simp [hji, hne]
  · have hji : j ≠ i := by omega
    rw [joinN_apply_of_le n _ _ (not_lt.1 h), joinN_apply_of_le n _ _ (not_lt.1 h)]
    simp [hji]

/-- `∑ L_i |x_i - x'_i| ≤ (∑ L_i) ‖x - x'‖_∞` for nonnegative weights. -/
lemma sum_mul_abs_le_mul_dist {n : ℕ} {L : ℕ → ℝ} (hL : ∀ i, 0 ≤ L i) (x x' : Fin n → ℝ) :
    ∑ i : Fin n, L i * |x i - x' i| ≤ (∑ i : Fin n, L i) * dist x x' := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hL i)
  rw [← Real.dist_eq]
  exact dist_le_pi_dist x x' i

namespace ShiftLipschitzOn

variable {F : Coord → ℝ} {𝒢 : Set Coord} {L : ℕ → ℝ}

/-- (H) along the coordinate line through a point of `𝒢`. -/
lemma line (hH : ShiftLipschitzOn F 𝒢 L) {ω : Coord} (hω : ω ∈ 𝒢) (j : ℕ) (t t' : ℝ) :
    |F (shiftBy ω (Finsupp.single j t)) - F (shiftBy ω (Finsupp.single j t'))| ≤
      L j * |t - t'| := by
  have h := hH ω hω (Finsupp.single j t) (Finsupp.single j t')
  rwa [sum_support_union_eq Finsupp.support_single_subset Finsupp.support_single_subset,
    Finset.sum_singleton, Finsupp.single_eq_same, Finsupp.single_eq_same] at h

/-- The constants `L_j` are nonnegative as soon as `𝒢` is nonempty. -/
lemma nonneg (hH : ShiftLipschitzOn F 𝒢 L) (h𝒢 : 𝒢.Nonempty) (j : ℕ) : 0 ≤ L j := by
  obtain ⟨ω, hω⟩ := h𝒢
  have h := hH.line hω j 1 0
  rw [sub_zero, abs_one, mul_one] at h
  exact (abs_nonneg _).trans h

/-- (H) along the first `n` coordinates through a point `(x₀, y) ∈ 𝒢`: for all `x, x' ∈ ℝⁿ`,
`|F(x, y) - F(x', y)| ≤ ∑_{i<n} L_i |x_i - x'_i|`. -/
lemma joinN_le (hH : ShiftLipschitzOn F 𝒢 L) {n : ℕ} {x₀ : Fin n → ℝ} {y : Coord}
    (hx₀ : joinN n x₀ y ∈ 𝒢) (x x' : Fin n → ℝ) :
    |F (joinN n x y) - F (joinN n x' y)| ≤ ∑ i : Fin n, L i * |x i - x' i| := by
  have h := hH _ hx₀ (blockVec n (x - x₀)) (blockVec n (x' - x₀))
  rw [shiftBy_joinN_blockVec, shiftBy_joinN_blockVec,
    sum_support_union_eq (support_blockVec n _) (support_blockVec n _)] at h
  refine h.trans (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => L i * |blockVec n (x - x₀) i - blockVec n (x' - x₀) i|)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [blockVec_apply, i.isLt]

/-- Through a point `(x₀, y) ∈ 𝒢`, `x ↦ F(x, y)` is Lipschitz on `ℝⁿ`. -/
lemma lipschitzWith_joinN (hH : ShiftLipschitzOn F 𝒢 L) (hL : ∀ i, 0 ≤ L i) {n : ℕ}
    {x₀ : Fin n → ℝ} {y : Coord} (hx₀ : joinN n x₀ y ∈ 𝒢) :
    LipschitzWith (∑ i : Fin n, L i).toNNReal (fun x => F (joinN n x y)) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, Real.coe_toNNReal (∑ i : Fin n, L i) (Finset.sum_nonneg fun i _ => hL i)]
  exact (hH.joinN_le hx₀ x x').trans (sum_mul_abs_le_mul_dist hL x x')

/-- Through a point `(x₀, y) ∈ 𝒢`, the coordinate lines `t ↦ F((x, y) + t δ_j)` with `j < n` are
`L_j`-Lipschitz, for every `x`. -/
lemma lipschitzWith_line_joinN (hH : ShiftLipschitzOn F 𝒢 L) (hL : ∀ i, 0 ≤ L i) {n j : ℕ}
    (hj : j < n) {x₀ : Fin n → ℝ} {y : Coord} (hx₀ : joinN n x₀ y ∈ 𝒢) (x : Fin n → ℝ) :
    LipschitzWith (L j).toNNReal fun t : ℝ => F (shiftBy (joinN n x y) (Finsupp.single j t)) := by
  refine LipschitzWith.of_dist_le_mul fun t t' => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (hL j), shiftBy_joinN_single hj,
    shiftBy_joinN_single hj]
  refine (hH.joinN_le hx₀ _ _).trans (le_of_eq ?_)
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- Through a point of `𝒢`, the coordinate lines are `L_j`-Lipschitz. -/
lemma lipschitzWith_line (hH : ShiftLipschitzOn F 𝒢 L) {ω : Coord} (hω : ω ∈ 𝒢) (j : ℕ) :
    LipschitzWith (L j).toNNReal fun t : ℝ => F (shiftBy ω (Finsupp.single j t)) := by
  refine LipschitzWith.of_dist_le_mul fun t t' => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (hH.nonneg ⟨ω, hω⟩ j)]
  exact hH.line hω j t t'

end ShiftLipschitzOn

/-- For a.e. `y`, some point `(x₀, y)` lies in `𝒢`. -/
lemma ae_exists_joinN_mem {𝒢 : Set Coord} (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0) (n : ℕ) :
    ∀ᵐ y ∂stdP, ∃ x₀, joinN n x₀ y ∈ 𝒢 := by
  have h1 : ∀ᵐ ω ∂stdP, ω ∈ 𝒢 := mem_ae_iff.2 h𝒢c
  have h2 := ae_joinN_of_ae n h1
  have hmeas : MeasurableSet {z : (Fin n → ℝ) × Coord | joinN n z.1 z.2 ∈ 𝒢} :=
    measurable_joinN n h𝒢
  have h3 : ∀ᵐ y ∂stdP, ∀ᵐ x ∂gaussPi n, joinN n x y ∈ 𝒢 :=
    (Measure.ae_ae_comm hmeas).1 (Measure.ae_ae_of_ae_prod h2)
  filter_upwards [h3] with y hy
  exact hy.exists

/-- A set of full measure is nonempty. -/
lemma nonempty_of_measure_compl_eq_zero {𝒢 : Set Coord} (h𝒢c : stdP 𝒢ᶜ = 0) :
    𝒢.Nonempty := by
  have h : ∀ᵐ ω ∂stdP, ω ∈ 𝒢 := mem_ae_iff.2 h𝒢c
  exact h.exists

/-! ### Difference quotients along a coordinate line -/

/-- The difference quotient `(F(ω + h δ_j) - F(ω)) / h`. -/
def lineSlope (F : Coord → ℝ) (j : ℕ) (ω : Coord) (h : ℝ) : ℝ :=
  (F (shiftBy ω (Finsupp.single j h)) - F ω) / h

lemma lineSlope_eq (F : Coord → ℝ) (j : ℕ) (ω : Coord) :
    (fun t : ℝ => t⁻¹ • ((fun s : ℝ => F (shiftBy ω (Finsupp.single j s))) (0 + t) -
      (fun s : ℝ => F (shiftBy ω (Finsupp.single j s))) 0)) = lineSlope F j ω := by
  funext t
  simp [lineSlope, div_eq_inv_mul]

lemma measurable_lineSlope {F : Coord → ℝ} (hF : Measurable F) (j : ℕ) (h : ℝ) :
    Measurable fun ω => lineSlope F j ω h := by
  unfold lineSlope shiftBy
  exact ((hF.comp (measurable_id.add_const _)).sub hF).div_const _

/-- The set where the difference quotients at `0` along rational increments are Cauchy. -/
def ratCauchySet (F : Coord → ℝ) (j : ℕ) : Set Coord :=
  {ω | ∀ m : ℕ, ∃ k : ℕ, ∀ q q' : ℚ, (q : ℝ) ≠ 0 → (q' : ℝ) ≠ 0 →
    |(q : ℝ)| < 1 / (k + 1) → |(q' : ℝ)| < 1 / (k + 1) →
      |lineSlope F j ω q - lineSlope F j ω q'| ≤ 1 / (m + 1)}

lemma measurableSet_ratCauchySet {F : Coord → ℝ} (hF : Measurable F) (j : ℕ) :
    MeasurableSet (ratCauchySet F j) := by
  unfold ratCauchySet
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.forall fun m => Measurable.exists fun k => Measurable.forall fun q =>
    Measurable.forall fun q' => ?_
  refine measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurable_const.imp ?_)))
  exact measurableSet_setOfPred.1 (measurableSet_le
    (continuous_abs.measurable.comp ((measurable_lineSlope hF j _).sub
      (measurable_lineSlope hF j _))) measurable_const)

/-- Where the line derivative exists, the rational difference quotients are Cauchy. -/
lemma mem_ratCauchySet_of_differentiableAt {F : Coord → ℝ} {j : ℕ} {ω : Coord}
    (h : DifferentiableAt ℝ (fun t : ℝ => F (shiftBy ω (Finsupp.single j t))) 0) :
    ω ∈ ratCauchySet F j := by
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 h.hasDerivAt
  rw [lineSlope_eq] at ht
  set D := deriv (fun t : ℝ => F (shiftBy ω (Finsupp.single j t))) 0
  intro m
  have hε : (0 : ℝ) < 1 / (m + 1) / 2 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.1 ht _ hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k, fun q q' hq hq' hqk hq'k => ?_⟩
  have h1 := hball (x := (q : ℝ)) (Set.mem_compl_singleton_iff.2 hq)
    (by rw [Real.dist_eq, sub_zero]; linarith)
  have h2 := hball (x := (q' : ℝ)) (Set.mem_compl_singleton_iff.2 hq')
    (by rw [Real.dist_eq, sub_zero]; linarith)
  rw [Real.dist_eq] at h1 h2
  calc |lineSlope F j ω q - lineSlope F j ω q'|
      ≤ |lineSlope F j ω q - D| + |D - lineSlope F j ω q'| := abs_sub_le _ _ _
    _ = |lineSlope F j ω q - D| + |lineSlope F j ω q' - D| := by rw [abs_sub_comm D]
    _ ≤ 1 / (m + 1) := by linarith

/-- Where the line function is continuous, rational Cauchy difference quotients give the line
derivative. -/
lemma differentiableAt_of_mem_ratCauchySet {F : Coord → ℝ} {j : ℕ} {ω : Coord}
    (hcont : Continuous fun t : ℝ => F (shiftBy ω (Finsupp.single j t)))
    (hω : ω ∈ ratCauchySet F j) :
    DifferentiableAt ℝ (fun t : ℝ => F (shiftBy ω (Finsupp.single j t))) 0 := by
  set g : ℝ → ℝ := fun t => F (shiftBy ω (Finsupp.single j t)) with hg
  set S : ℝ → ℝ := lineSlope F j ω with hS
  have hSg : ∀ h, S h = (g h - g 0) / h := by
    intro h
    simp [hS, lineSlope, hg]
  have hScont : ∀ h : ℝ, h ≠ 0 → ContinuousAt S h := by
    intro h hh
    have : ContinuousAt (fun t => (g t - g 0) / t) h :=
      ((hcont.continuousAt.sub continuousAt_const).div continuousAt_id hh)
    exact this.congr (Eventually.of_forall fun t => (hSg t).symm)
  -- the Cauchy condition for real increments
  have hreal : ∀ m : ℕ, ∃ k : ℕ, ∀ h h' : ℝ, h ≠ 0 → h' ≠ 0 → |h| < 1 / (k + 1) →
      |h'| < 1 / (k + 1) → |S h - S h'| ≤ 1 / (m + 1) := by
    intro m
    obtain ⟨k, hk⟩ := hω m
    refine ⟨k, fun h h' hh hh' hhk hh'k => ?_⟩
    by_contra hcon'
    have hcon := not_le.1 hcon'
    set U : Set (ℝ × ℝ) := {z | z.1 ≠ 0 ∧ z.2 ≠ 0 ∧ |z.1| < 1 / (k + 1) ∧ |z.2| < 1 / (k + 1)}
    have hUo : IsOpen U := by
      refine (isOpen_ne_fun continuous_fst continuous_const).inter
        ((isOpen_ne_fun continuous_snd continuous_const).inter
          ((isOpen_lt continuous_fst.abs continuous_const).inter
            (isOpen_lt continuous_snd.abs continuous_const)))
    have hΦ : ContinuousOn (fun z : ℝ × ℝ => |S z.1 - S z.2|) U := by
      intro z hz
      exact ((((hScont z.1 hz.1).comp continuous_fst.continuousAt).sub
        ((hScont z.2 hz.2.1).comp continuous_snd.continuousAt)).abs).continuousWithinAt
    have hO := hΦ.isOpen_inter_preimage hUo (isOpen_Ioi (a := 1 / ((m : ℝ) + 1)))
    obtain ⟨⟨q, q'⟩, hqq⟩ := (Rat.denseRange_cast.prodMap Rat.denseRange_cast).exists_mem_open hO
      ⟨(h, h'), ⟨hh, hh', hhk, hh'k⟩, hcon⟩
    obtain ⟨⟨hq, hq', hqk, hq'k⟩, hlt⟩ := hqq
    have := hk q q' hq hq' hqk hq'k
    exact absurd this (not_le.2 hlt)
  -- hence the difference quotients converge
  have hcauchy : Cauchy (map S (𝓝[≠] (0 : ℝ))) := by
    rw [cauchy_map_iff', Metric.uniformity_basis_dist.tendsto_right_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk⟩ := hreal m
    have hV : {0}ᶜ ∩ Metric.ball (0 : ℝ) (1 / (k + 1)) ∈ 𝓝[≠] (0 : ℝ) :=
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [Filter.prod_mem_prod hV hV] with z hz
    obtain ⟨⟨hz1', hz1⟩, ⟨hz2', hz2⟩⟩ := hz
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz1 hz2
    have := hk z.1 z.2 hz1' hz2' hz1 hz2
    simp only [Real.dist_eq]
    linarith
  obtain ⟨D, hD⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  have hder : HasDerivAt g D 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero, lineSlope_eq]
    exact hD
  exact hder.differentiableAt

/-- If the line through `ω` in direction `j` is `K`-Lipschitz, then `|∂_j F(ω)| ≤ K`. -/
lemma abs_coordDeriv_le_of_lipschitzWith {F : Coord → ℝ} {j : ℕ} {ω : Coord} {K : ℝ≥0}
    (h : LipschitzWith K fun t : ℝ => F (shiftBy ω (Finsupp.single j t))) :
    |coordDeriv F j ω| ≤ K := by
  rw [← Real.norm_eq_abs]
  exact norm_deriv_le_of_lipschitz h

end GaussLp

/-! ### Part (a): almost-sure existence of the coordinate derivatives -/

open GaussLp

/-- **Blueprint Proposition `prop:gaussian-Lp` (a)**: under (H), for each `j`, the coordinate
derivative `∂_j F(ω)` exists for `P`-a.e. `ω`. -/
theorem ae_differentiableAt_coord {F : Coord → ℝ} (hF : Measurable F) {𝒢 : Set Coord}
    (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0) {L : ℕ → ℝ}
    (hH : ∀ ω ∈ 𝒢, ∀ v v' : ℕ →₀ ℝ,
      |F (shiftBy ω v) - F (shiftBy ω v')| ≤ ∑ j ∈ v.support ∪ v'.support, L j * |v j - v' j|)
    (j : ℕ) :
    ∀ᵐ ω ∂stdP, DifferentiableAt ℝ (fun t : ℝ => F (shiftBy ω (Finsupp.single j t))) 0 := by
  have hH' : ShiftLipschitzOn F 𝒢 L := hH
  have hL : ∀ i, 0 ≤ L i := hH'.nonneg (nonempty_of_measure_compl_eq_zero h𝒢c)
  set n := j + 1
  have hj : j < n := Nat.lt_succ_self j
  have hR : ∀ᵐ ω ∂stdP, ω ∈ ratCauchySet F j := by
    have hmeas : MeasurableSet {z : (Fin n → ℝ) × Coord | joinN n z.1 z.2 ∈ ratCauchySet F j} :=
      measurable_joinN n (measurableSet_ratCauchySet hF j)
    refine ae_of_ae_joinN n (measurableSet_ratCauchySet hF j) ?_
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    refine (Measure.ae_ae_comm hmeas).2 ?_
    filter_upwards [ae_exists_joinN_mem h𝒢 h𝒢c n] with y hy
    obtain ⟨x₀, hx₀⟩ := hy
    have hlip := hH'.lipschitzWith_joinN hL hx₀
    filter_upwards [ae_differentiableAt_gaussPi hlip] with x hx
    apply mem_ratCauchySet_of_differentiableAt
    have heq : (fun t : ℝ => F (shiftBy (joinN n x y) (Finsupp.single j t))) =
        (fun x' => F (joinN n x' y)) ∘
          (fun t : ℝ => x + t • Pi.single (⟨j, hj⟩ : Fin n) (1 : ℝ)) := by
      funext t
      simp only [Function.comp, shiftBy_joinN_single hj]
    rw [heq]
    have hx' : DifferentiableAt ℝ (fun x' => F (joinN n x' y))
        ((fun t : ℝ => x + t • Pi.single (⟨j, hj⟩ : Fin n) (1 : ℝ)) 0) := by
      simpa using hx
    exact hx'.comp (0 : ℝ) ((differentiableAt_id.smul_const _).const_add x)
  have hG : ∀ᵐ ω ∂stdP, ω ∈ 𝒢 := mem_ae_iff.2 h𝒢c
  filter_upwards [hR, hG] with ω hωR hω𝒢
  exact differentiableAt_of_mem_ratCauchySet (hH'.lipschitzWith_line hω𝒢 j).continuous hωR

/-- Under (H), `∂_j F` is almost everywhere strongly measurable: it is a.e. the limit of the
measurable difference quotients `(k+1) (F(ω + δ_j/(k+1)) - F(ω))`. -/
theorem aestronglyMeasurable_coordDeriv {F : Coord → ℝ} (hF : Measurable F) {𝒢 : Set Coord}
    (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0) {L : ℕ → ℝ}
    (hH : ∀ ω ∈ 𝒢, ∀ v v' : ℕ →₀ ℝ,
      |F (shiftBy ω v) - F (shiftBy ω v')| ≤ ∑ j ∈ v.support ∪ v'.support, L j * |v j - v' j|)
    (j : ℕ) : AEStronglyMeasurable (coordDeriv F j) stdP := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun k : ℕ => fun ω => lineSlope F j ω (1 / ((k : ℝ) + 1)))
    (fun k => (measurable_lineSlope hF j _).aestronglyMeasurable) ?_
  filter_upwards [ae_differentiableAt_coord hF h𝒢 h𝒢c hH j] with ω hω
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hω.hasDerivAt
  rw [lineSlope_eq] at ht
  have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_compl_singleton_iff.2 (by positivity)⟩
  exact ht.comp hseq

end GaussianLQG
