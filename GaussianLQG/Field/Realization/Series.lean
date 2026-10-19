import GaussianLQG.Core.Defs
import LQGDimension.Existence.SeriesContinuityAux1

/-!
# Gaussian series on the coordinate space (blueprint Lemma 1.10(a), Appendix B)

For a square-summable coefficient sequence `a`, the partial sums `∑_{k<n} ω_k a_k` of the
coordinate series converge `stdP`-almost surely (`ae_exists_tendsto_psum`). The proof is the
Lévy–Kolmogorov argument of `LQGDimension`: chaining plus Gaussian concentration
(`LQGDimension.SeriesCont.gaussSeq_osc_countable`) applied to the one-parameter family of
partial sums, parametrized by the tail `∑_{k ≥ n} a_k²`, bounds
`P(∃ n ≥ N, |S_n - S_N| ≥ η)` by a quantity that tends to `0` as `N → ∞`.

The limit `seriesLim a` is a centered Gaussian with variance `∑ a_k²` (`hasLaw_seriesLim`).
The partial sums along a finitely supported shift `ω + v` are `psum_shift` and `psum_finsupp`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG
namespace Realization

/-- The partial sums `∑_{k<n} ω_k a_k` of the coordinate series with coefficients `a`. -/
def psum (a : ℕ → ℝ) (n : ℕ) (ω : Coord) : ℝ := ∑ k ∈ Finset.range n, ω k * a k

lemma measurable_psum (a : ℕ → ℝ) (n : ℕ) : Measurable (psum a n) := by
  unfold psum
  exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).mul_const _

/-- The tail `∑_{k ≥ n} a_k²`. -/
def sqTail (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k, a (k + n) ^ 2

lemma sqTail_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ sqTail a n :=
  tsum_nonneg fun _ => sq_nonneg _

lemma sum_range_add_sqTail {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, a k ^ 2 + sqTail a n = ∑' k, a k ^ 2 :=
  ha.sum_add_tsum_nat_add n

lemma sqTail_sub_sqTail {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) {i j : ℕ} (hij : i ≤ j) :
    sqTail a i - sqTail a j = ∑ k ∈ Finset.Ico i j, a k ^ 2 := by
  have h1 := sum_range_add_sqTail ha i
  have h2 := sum_range_add_sqTail ha j
  rw [Finset.sum_Ico_eq_sub _ hij]
  linarith

lemma sqTail_anti {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) {i j : ℕ} (hij : i ≤ j) :
    sqTail a j ≤ sqTail a i := by
  have := sqTail_sub_sqTail ha hij
  have h0 : 0 ≤ ∑ k ∈ Finset.Ico i j, a k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma tendsto_sqTail (a : ℕ → ℝ) : Tendsto (sqTail a) atTop (𝓝 0) :=
  tendsto_sum_nat_add fun k => a k ^ 2

/-! ### The truncated coefficient family -/

/-- The coefficients of the `n`-th partial sum. -/
def truncCoef (a : ℕ → ℝ) (n k : ℕ) : ℝ := if k < n then a k else 0

lemma truncCoef_eq_zero (a : ℕ → ℝ) {n k : ℕ} (hk : n ≤ k) : truncCoef a n k = 0 := by
  simp [truncCoef, not_lt.mpr hk]

lemma tsum_truncCoef_mul (a : ℕ → ℝ) (n : ℕ) (ω : Coord) :
    ∑' k, truncCoef a n k * ω k = psum a n ω := by
  rw [tsum_eq_sum (s := Finset.range n) fun k hk => by
    rw [truncCoef_eq_zero a (by simpa using hk), zero_mul]]
  unfold psum
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [truncCoef, Finset.mem_range.mp hk, ite_true]
  exact mul_comm _ _

lemma tsum_sq_truncCoef_sub {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (i j : ℕ) :
    ∑' k, (truncCoef a i k - truncCoef a j k) ^ 2 = |sqTail a i - sqTail a j| := by
  wlog hij : i ≤ j generalizing i j
  · have := this j i (le_of_not_ge hij)
    rw [abs_sub_comm, ← this]
    exact tsum_congr fun k => by ring
  rw [tsum_eq_sum (s := Finset.range j) fun k hk => by
    have hk' : j ≤ k := by simpa using hk
    rw [truncCoef_eq_zero a hk', truncCoef_eq_zero a (hij.trans hk'), sub_zero,
      zero_pow two_ne_zero]]
  rw [abs_of_nonneg (by linarith [sqTail_anti ha hij]), sqTail_sub_sqTail ha hij,
    ← Finset.sum_range_add_sum_Ico _ hij]
  have h0 : ∑ k ∈ Finset.range i, (truncCoef a i k - truncCoef a j k) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < i := Finset.mem_range.mp hk
    simp [truncCoef, hk', lt_of_lt_of_le hk' hij]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  simp [truncCoef, not_lt.mpr hk1, hk2]

/-! ### Almost sure convergence -/

/-- Concentration for the oscillation of the partial sums after `N`. -/
lemma measure_osc_psum_le {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (N : ℕ) {σ s : ℝ}
    (hσ : 0 < σ) (hσa : sqTail a N ≤ σ ^ 2) (hs : 0 ≤ s) :
    stdP {ω | ∃ n ∈ Ici N, 20 * √5 * √(2 * sqTail a N) + s ≤
        |psum a n ω - psum a N ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * s ^ 2 / (Real.pi ^ 2 * σ ^ 2))) := by
  have h := LQGDimension.SeriesCont.gaussSeq_osc_countable (d := 1) (truncCoef a)
    (fun n => ⟨n, fun k hk => truncCoef_eq_zero a hk⟩) (Ici N) (Set.to_countable _)
    (fun n => fun _ => sqTail a n) (L := 1) (a := sqTail a N) (σ := σ) (s := s) zero_le_one
    (fun i hi j hj => by
      rw [pi_norm_le_iff_of_nonneg (sqTail_nonneg a N)]
      intro _
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
      have hi' := sqTail_anti ha (show N ≤ i from hi)
      have hj' := sqTail_anti ha (show N ≤ j from hj)
      have := sqTail_nonneg a i
      have := sqTail_nonneg a j
      constructor <;> linarith)
    (fun i _ j _ => by
      rw [tsum_sq_truncCoef_sub ha, one_pow, one_mul]
      exact norm_le_pi_norm (fun _ : Fin 1 => sqTail a i - sqTail a j) 0)
    hσ (by rw [one_pow, one_mul]; exact hσa) hs (i₀ := N) (Set.mem_Ici.mpr le_rfl)
  simp only [tsum_truncCoef_mul] at h
  have e : (20 : ℝ) * √5 * 1 * √((((1 : ℕ) : ℝ) + 1) * sqTail a N) =
      20 * √5 * √(2 * sqTail a N) := by
    norm_num
  rw [e] at h
  exact h

lemma exp_neg_div_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) : Real.exp (-c / x) ≤ x / c := by
  have h1 := Real.add_one_le_exp (c / x)
  have h2 : Real.exp (-c / x) * Real.exp (c / x) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have h3 : 0 < Real.exp (c / x) := Real.exp_pos _
  have h4 : 0 < c / x := div_pos hc hx
  rw [div_eq_mul_inv x c]
  have : Real.exp (-c / x) = (Real.exp (c / x))⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [this]
  have h5 : (c / x) ≤ Real.exp (c / x) := by linarith
  calc (Real.exp (c / x))⁻¹ ≤ (c / x)⁻¹ := inv_anti₀ h4 h5
    _ = x * c⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- The event that the partial sums oscillate by at least `η` after every time. -/
def oscSet (a : ℕ → ℝ) (η : ℝ) : Set Coord :=
  {ω | ∀ N, ∃ n ∈ Ici N, η ≤ |psum a n ω - psum a N ω|}

lemma measure_oscSet {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) {η : ℝ} (hη : 0 < η) :
    stdP (oscSet a η) = 0 := by
  set σ : ℕ → ℝ := fun N => √(sqTail a N) + 1 / ((N : ℝ) + 1) with hσdef
  have hσpos : ∀ N, 0 < σ N := fun N => by
    have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    simp only [hσdef]; positivity
  have hσsq : ∀ N, sqTail a N ≤ σ N ^ 2 := fun N => by
    have h1 : sqTail a N = √(sqTail a N) ^ 2 := (Real.sq_sqrt (sqTail_nonneg a N)).symm
    have h2 : 0 ≤ √(sqTail a N) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
    rw [h1]
    exact pow_le_pow_left₀ h2 (by simp only [hσdef]; linarith) 2
  have hσlim : Tendsto σ atTop (𝓝 0) := by
    have h1 := (tendsto_sqTail a).sqrt
    rw [Real.sqrt_zero] at h1
    have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  -- the chaining term eventually is below `η / 2`
  have hchain : ∀ᶠ N in atTop, 20 * √5 * √(2 * sqTail a N) ≤ η / 2 := by
    have : Tendsto (fun N => 20 * √5 * √(2 * sqTail a N)) atTop (𝓝 0) := by
      have h := ((tendsto_sqTail a).const_mul (2 : ℝ)).sqrt.const_mul (20 * √5)
      rw [mul_zero, Real.sqrt_zero, mul_zero] at h
      exact h
    exact this.eventually (ge_mem_nhds (by linarith))
  set c : ℝ := 2 * (η / 2) ^ 2 / Real.pi ^ 2 with hcdef
  have hc : 0 < c := by positivity
  have hbound : ∀ᶠ N in atTop, stdP (oscSet a η) ≤ ENNReal.ofReal (2 * (σ N ^ 2 / c)) := by
    filter_upwards [hchain] with N hN
    have hsub : oscSet a η ⊆ {ω | ∃ n ∈ Ici N, 20 * √5 * √(2 * sqTail a N) + η / 2 ≤
        |psum a n ω - psum a N ω|} := by
      intro ω hω
      obtain ⟨n, hn, h⟩ := hω N
      exact ⟨n, hn, by linarith⟩
    refine (measure_mono hsub).trans ((measure_osc_psum_le ha N (hσpos N) (hσsq N)
      (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_))
    have e : -2 * (η / 2) ^ 2 / (Real.pi ^ 2 * σ N ^ 2) = -c / σ N ^ 2 := by
      simp only [hcdef]; field_simp
    rw [e]
    have := exp_neg_div_le hc (pow_pos (hσpos N) 2)
    linarith
  have hlim : Tendsto (fun N => ENNReal.ofReal (2 * (σ N ^ 2 / c))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h := ((hσlim.pow 2).div_const c).const_mul 2
    simpa using h
  exact le_antisymm (ge_of_tendsto hlim hbound) zero_le

/-- **Almost sure convergence of the coordinate series** with square-summable coefficients. -/
theorem ae_exists_tendsto_psum {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    ∀ᵐ ω ∂stdP, ∃ L, Tendsto (fun n => psum a n ω) atTop (𝓝 L) := by
  have hnull : ∀ᵐ ω ∂stdP, ∀ j : ℕ, ω ∉ oscSet a (1 / ((j : ℝ) + 1)) := by
    rw [ae_all_iff]
    intro j
    rw [ae_iff]
    simp only [not_not, Set.ofPred_mem_eq]
    exact measure_oscSet ha (by positivity)
  filter_upwards [hnull] with ω hω
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr fun ε hε => ?_)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  have h := hω j
  simp only [oscSet, Set.mem_ofPred_eq, not_forall, not_exists, not_and, not_le] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact (hN n hn).trans hj

/-! ### The limit and its law -/

/-- The sum of the coordinate series (junk value off the convergence set). -/
def seriesLim (a : ℕ → ℝ) (ω : Coord) : ℝ := limUnder atTop fun n => psum a n ω

lemma measurable_seriesLim (a : ℕ → ℝ) : Measurable (seriesLim a) :=
  (StronglyMeasurable.limUnder fun n => (measurable_psum a n).stronglyMeasurable).measurable

theorem ae_tendsto_seriesLim {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    ∀ᵐ ω ∂stdP, Tendsto (fun n => psum a n ω) atTop (𝓝 (seriesLim a ω)) := by
  filter_upwards [ae_exists_tendsto_psum ha] with ω hω
  exact tendsto_nhds_limUnder hω

lemma seriesLim_eq_of_tendsto {a : ℕ → ℝ} {ω : Coord} {L : ℝ}
    (h : Tendsto (fun n => psum a n ω) atTop (𝓝 L)) : seriesLim a ω = L :=
  h.limUnder_eq

theorem hasLaw_psum (a : ℕ → ℝ) (n : ℕ) :
    HasLaw (psum a n) (gaussianReal 0 (∑ k ∈ Finset.range n, a k ^ 2).toNNReal) stdP := by
  have h := LQGDimension.ExistAsm.hasLaw_sum_mul a n
  have e : psum a n = fun ω : ℕ → ℝ => ∑ k ∈ Finset.range n, a k * ω k := by
    funext ω
    unfold psum
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e]
  exact h

/-- The sum of the coordinate series is a centered Gaussian with variance `∑ a_k²`. -/
theorem hasLaw_seriesLim {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    HasLaw (seriesLim a) (gaussianReal 0 (∑' k, a k ^ 2).toNNReal) stdP :=
  LQGDimension.ExistAsm.hasLaw_gaussianReal_of_tendsto (hasLaw_psum a)
    (ae_tendsto_seriesLim ha) ha.hasSum.tendsto_sum_nat

theorem memLp_seriesLim {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    MemLp (seriesLim a) 2 stdP :=
  (hasLaw_seriesLim ha).hasGaussianLaw.memLp_two

theorem integral_sq_seriesLim {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    ∫ ω, seriesLim a ω ^ 2 ∂stdP = ∑' k, a k ^ 2 := by
  have hL := hasLaw_seriesLim ha
  have hmean : ∫ ω, seriesLim a ω ∂stdP = 0 := by
    rw [hL.integral_eq, integral_id_gaussianReal]
  have hvar := hL.variance_eq
  rw [variance_id_gaussianReal, Real.coe_toNNReal _ (tsum_nonneg fun _ => sq_nonneg _),
    variance_eq_integral hL.aemeasurable, hmean] at hvar
  simpa using hvar

/-! ### Linearity -/

lemma psum_sub (a b : ℕ → ℝ) (n : ℕ) (ω : Coord) :
    psum (fun k => a k - b k) n ω = psum a n ω - psum b n ω := by
  unfold psum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma psum_smul (c : ℝ) (a : ℕ → ℝ) (n : ℕ) (ω : Coord) :
    psum (fun k => c * a k) n ω = c * psum a n ω := by
  unfold psum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma summable_sq_sub {a b : ℕ → ℝ} (ha : Summable fun k => a k ^ 2)
    (hb : Summable fun k => b k ^ 2) : Summable fun k => (a k - b k) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) ((ha.add hb).mul_left 2)
  nlinarith [sq_nonneg (a k + b k)]

/-! ### Finitely supported shifts -/

/-- The partial sums of a finitely supported shift. -/
lemma psum_shift (a : ℕ → ℝ) (N : ℕ) (ω : Coord) (v : ℕ →₀ ℝ) :
    psum a N (shiftBy ω v) = psum a N ω + psum a N ⇑v := by
  unfold psum shiftBy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp only [Pi.add_apply]; ring

/-- A bound beyond the support of `v`. -/
def suppBound (v : ℕ →₀ ℝ) : ℕ := v.support.sup id + 1

lemma psum_finsupp (a : ℕ → ℝ) (v : ℕ →₀ ℝ) {N : ℕ} (hN : suppBound v ≤ N) :
    psum a N ⇑v = v.sum fun k c => c * a k := by
  have hsub : v.support ⊆ Finset.range N := by
    intro k hk
    have : k ≤ v.support.sup id := Finset.le_sup (f := id) hk
    rw [Finset.mem_range]
    simp only [suppBound] at hN
    omega
  rw [Finsupp.sum_of_support_subset v hsub (fun k c => c * a k) (fun _ _ => zero_mul _)]
  rfl

end Realization
end GaussianLQG
