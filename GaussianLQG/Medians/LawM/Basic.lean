import GaussianLQG.Core.Setup
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Helpers for the law of `M` (blueprint Lemma `lem:law-M`)

Generic ingredients of the proof of blueprint Lemma `lem:law-M` (source Lemma 6.1):

* `infAffine h c t = inf_i (h_i + t c_i)` and `volume_pos_infAffine`: if the `h_i` are bounded
  below and the slopes satisfy `0 < m ≤ c_i ≤ L`, then `t ↦ infAffine h c t` is a continuous
  bijection of `ℝ`, so it takes values in any open interval `(a, b)` on a set of positive
  Lebesgue measure;
* `measure_pos_of_ae_volume_shift_pos`: the finite-dimensional Cameron–Martin and Fubini step. If
  the law of `ω + t v` is absolutely continuous with respect to `stdP` for every `t`, and for a.e.
  `ω` the set `{t | ω + t v ∈ B}` has positive Lebesgue measure, then `stdP B > 0`;
* `gaussianReal_Iio_zero`: a centered nondegenerate Gaussian is negative with probability `1/2`;
* the coefficient algebra of a GFF frame: `integral_frameFun` (`∫ f_v dμ = ∑_j v_j ∫ e_j dμ`),
  `frameFun_smul`, and the truncation `truncFs w n = (w_0, …, w_{n-1}, 0, …)`;
* the dyadic rationals `𝔻` of `[0,1]`: countable, contain `0` and `1`, contained in `[0,1]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

namespace LawMAux

/-! ## An infimum of increasing affine functions -/

section InfAffine

variable {ι : Type*}

/-- `inf_i (h_i + t c_i)`, an infimum of affine functions of `t`. -/
def infAffine (h c : ι → ℝ) (t : ℝ) : ℝ := ⨅ i, (h i + t * c i)

theorem bddBelow_range_add_mul {h c : ι → ℝ} {L : ℝ} (hh : BddBelow (range h))
    (hc : ∀ i, |c i| ≤ L) (t : ℝ) : BddBelow (range fun i => h i + t * c i) := by
  obtain ⟨B, hB⟩ := hh
  refine ⟨B - |t| * L, ?_⟩
  rintro _ ⟨i, rfl⟩
  have h1 : B ≤ h i := hB ⟨i, rfl⟩
  have h2 : |t * c i| ≤ |t| * L := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hc i) (abs_nonneg t)
  have h3 := neg_abs_le (t * c i)
  linarith

variable [Nonempty ι] {h c : ι → ℝ} {m L : ℝ}

/-- The two-sided increment bound: for `t ≤ t'`,
`φ(t) + m (t' - t) ≤ φ(t') ≤ φ(t) + L (t' - t)` with `φ = infAffine h c`. -/
theorem infAffine_increment (hh : BddBelow (range h)) (hc : ∀ i, m ≤ c i ∧ c i ≤ L)
    (hm : 0 < m) {t t' : ℝ} (htt : t ≤ t') :
    infAffine h c t + m * (t' - t) ≤ infAffine h c t' ∧
      infAffine h c t' ≤ infAffine h c t + L * (t' - t) := by
  have hcabs : ∀ i, |c i| ≤ L := fun i =>
    abs_le.2 ⟨by linarith [(hc i).1, (hc i).2], (hc i).2⟩
  have hb := bddBelow_range_add_mul hh hcabs
  have hd : 0 ≤ t' - t := sub_nonneg.2 htt
  constructor
  · refine le_ciInf fun i => ?_
    have h1 : infAffine h c t ≤ h i + t * c i := ciInf_le (hb t) i
    have h2 : m * (t' - t) ≤ c i * (t' - t) := mul_le_mul_of_nonneg_right (hc i).1 hd
    have e : h i + t' * c i = h i + t * c i + c i * (t' - t) := by ring
    linarith
  · have key : infAffine h c t' - L * (t' - t) ≤ infAffine h c t := by
      refine le_ciInf fun i => ?_
      have h1 : infAffine h c t' ≤ h i + t' * c i := ciInf_le (hb t') i
      have h2 : c i * (t' - t) ≤ L * (t' - t) := mul_le_mul_of_nonneg_right (hc i).2 hd
      have e : h i + t' * c i = h i + t * c i + c i * (t' - t) := by ring
      linarith
    linarith

/-- `t ↦ inf_i (h_i + t c_i)` is continuous (indeed `L`-Lipschitz). -/
theorem continuous_infAffine (hh : BddBelow (range h)) (hc : ∀ i, m ≤ c i ∧ c i ≤ L)
    (hm : 0 < m) : Continuous (infAffine h c) := by
  have hL : 0 ≤ L := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    linarith [(hc i).1, (hc i).2]
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun t t' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
  rcases le_total t t' with htt | htt
  · obtain ⟨h1, h2⟩ := infAffine_increment hh hc hm htt
    have hd : 0 ≤ t' - t := sub_nonneg.2 htt
    have hmd : 0 ≤ m * (t' - t) := mul_nonneg hm.le hd
    have hLd : 0 ≤ L * (t' - t) := mul_nonneg hL hd
    rw [abs_sub_comm t t', abs_of_nonneg hd, abs_sub_le_iff]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := infAffine_increment hh hc hm htt
    have hd : 0 ≤ t - t' := sub_nonneg.2 htt
    have hmd : 0 ≤ m * (t - t') := mul_nonneg hm.le hd
    have hLd : 0 ≤ L * (t - t') := mul_nonneg hL hd
    rw [abs_of_nonneg hd, abs_sub_le_iff]
    constructor <;> linarith

/-- `t ↦ inf_i (h_i + t c_i)` is a surjection of `ℝ` onto `ℝ`. -/
theorem surjective_infAffine (hh : BddBelow (range h)) (hc : ∀ i, m ≤ c i ∧ c i ≤ L)
    (hm : 0 < m) : Function.Surjective (infAffine h c) := by
  refine (continuous_infAffine hh hc hm).surjective ?_ ?_
  · have h0 : Tendsto (fun t : ℝ => infAffine h c 0 + m * t) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hm)
    refine tendsto_atTop_mono' _ ?_ h0
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 := (infAffine_increment hh hc hm ht).1
    rw [sub_zero] at h1
    exact h1
  · have h0 : Tendsto (fun t : ℝ => infAffine h c 0 + m * t) atBot atBot :=
      tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atBot hm)
    refine tendsto_atBot_mono' _ ?_ h0
    filter_upwards [eventually_le_atBot 0] with t ht
    have h1 := (infAffine_increment hh hc hm ht).1
    have e : m * (0 - t) = -(m * t) := by ring
    rw [e] at h1
    show infAffine h c t ≤ infAffine h c 0 + m * t
    linarith

/-- **Deterministic core of Lemma `lem:law-M` (a).** If the `h_i` are bounded below and
`0 < m ≤ c_i ≤ L`, then `{t | a < inf_i (h_i + t c_i) < b}` has positive Lebesgue measure for
every `a < b`. -/
theorem volume_pos_infAffine (hh : BddBelow (range h)) (hc : ∀ i, m ≤ c i ∧ c i ≤ L)
    (hm : 0 < m) {a b : ℝ} (hab : a < b) :
    0 < volume {t : ℝ | a < infAffine h c t ∧ infAffine h c t < b} := by
  obtain ⟨t0, ht0⟩ := surjective_infAffine hh hc hm ((a + b) / 2)
  have hopen : IsOpen {t : ℝ | a < infAffine h c t ∧ infAffine h c t < b} :=
    isOpen_Ioo.preimage (continuous_infAffine hh hc hm)
  refine hopen.measure_pos volume ⟨t0, ?_⟩
  show a < infAffine h c t0 ∧ infAffine h c t0 < b
  rw [ht0]
  constructor <;> linarith

end InfAffine

/-! ## Finite-dimensional shifts and Fubini -/

/-- `(ω, t) ↦ ω + t v` is measurable on `ℝ^ℕ × ℝ`. -/
theorem measurable_shiftBy_smul (v : ℕ →₀ ℝ) :
    Measurable fun p : Coord × ℝ => shiftBy p.1 (p.2 • v) := by
  refine Measurable.of_eval fun j => ?_
  have e : (fun p : Coord × ℝ => shiftBy p.1 (p.2 • v) j) = fun p => p.1 j + p.2 * v j := by
    funext p
    simp only [shiftBy, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact ((measurable_pi_apply j).comp measurable_fst).add (measurable_snd.mul_const _)

/-- **Cameron–Martin and Fubini step of Lemma `lem:law-M`.** Let `v` be finitely supported, and
suppose the law of `ω + t v` is absolutely continuous with respect to `stdP` for every `t`. If for
a.e. `ω` the set `{t | ω + t v ∈ B}` has positive Lebesgue measure, then `stdP B > 0`. -/
theorem measure_pos_of_ae_volume_shift_pos {B : Set Coord} (hB : MeasurableSet B)
    (v : ℕ →₀ ℝ) (hqi : ∀ t : ℝ, (stdP.map fun ω => shiftBy ω (t • v)) ≪ stdP)
    (hpos : ∀ᵐ ω ∂stdP, 0 < volume {t : ℝ | shiftBy ω (t • v) ∈ B}) : 0 < stdP B := by
  have hm := measurable_shiftBy_smul v
  set A : Set (Coord × ℝ) := (fun p : Coord × ℝ => shiftBy p.1 (p.2 • v)) ⁻¹' B with hA_def
  have hA : MeasurableSet A := hm hB
  rcases eq_or_ne (stdP B) 0 with hB0 | hB0
  swap
  · exact pos_iff_ne_zero.2 hB0
  exfalso
  -- every `t`-slice of `A` is `stdP`-null, by quasi-invariance
  have hslice : ∀ t : ℝ, stdP ((fun ω => (ω, t)) ⁻¹' A) = 0 := by
    intro t
    have hmt : Measurable fun ω : Coord => shiftBy ω (t • v) :=
      hm.comp (measurable_id.prodMk measurable_const)
    exact le_antisymm ((Measure.le_map_apply hmt.aemeasurable B).trans_eq (hqi t hB0)) zero_le
  have hprod : (stdP.prod (volume : Measure ℝ)) A = 0 := by
    rw [Measure.prod_apply_symm hA]
    simp only [hslice, lintegral_zero]
  -- hence a.e. `ω`-slice is Lebesgue-null, contradicting `hpos`
  rw [Measure.prod_apply hA, lintegral_eq_zero_iff (measurable_measure_prodMk_left hA)] at hprod
  have hfalse : ∀ᵐ ω ∂stdP, False := by
    filter_upwards [hprod, hpos] with ω h1 h2
    exact h2.ne' h1
  exact IsProbabilityMeasure.ne_zero stdP (ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse))

/-! ## A centered Gaussian is negative with probability one half -/

/-- `𝒩(0, v)(-∞, 0) = 1/2` for `v ≠ 0`. -/
theorem gaussianReal_Iio_zero {v : NNReal} (hv : v ≠ 0) : gaussianReal 0 v (Iio 0) = 2⁻¹ := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  have hsymm : gaussianReal 0 v (Iio 0) = gaussianReal 0 v (Ioi 0) := by
    have h := gaussianReal_map_neg (μ := 0) (v := v)
    rw [neg_zero] at h
    conv_lhs => rw [← h]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp only [neg_preimage, neg_Iio, neg_zero, mem_Ioi]
  have hIci : gaussianReal 0 v (Ici 0) = gaussianReal 0 v (Ioi 0) :=
    (measure_congr Ioi_ae_eq_Ici).symm
  have hsum : gaussianReal 0 v (Iio 0) + gaussianReal 0 v (Iio 0) = 1 := by
    have h := measure_add_measure_compl (μ := gaussianReal 0 v) (measurableSet_Iio (a := (0 : ℝ)))
    rw [compl_Iio, measure_univ, hIci, ← hsymm] at h
    exact h
  rw [← mul_two] at hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum

/-! ## Coefficient algebra of a GFF frame -/

section Frame

variable {e : ℕ → ℂ → ℝ}

/-- Each frame function is integrable against a finite measure. -/
theorem integrable_frame (he : IsGFFFrame e) (j : ℕ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (e j) μ := by
  obtain ⟨C, hC⟩ := he.2.1 j
  exact Integrable.of_bound (he.1 j).aestronglyMeasurable C
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)

/-- `∫ f_v dμ = ∑_j v_j ∫ e_j dμ` for a finitely supported `v` and a finite measure `μ`. -/
theorem integral_frameFun (he : IsGFFFrame e) (v : ℕ →₀ ℝ) (μ : Measure ℂ)
    [IsFiniteMeasure μ] : ∫ z, frameFun e v z ∂μ = v.sum fun j c => c * ∫ z, e j z ∂μ := by
  unfold frameFun Finsupp.sum
  rw [integral_finsetSum _ fun j _ => (integrable_frame he j μ).const_mul (v j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- `f_{t v} = t f_v`. -/
theorem frameFun_smul (e : ℕ → ℂ → ℝ) (t : ℝ) (v : ℕ →₀ ℝ) (z : ℂ) :
    frameFun e (t • v) z = t * frameFun e v z := by
  unfold frameFun
  rw [Finsupp.sum_smul_index fun i => zero_mul _, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun j _ => mul_assoc _ _ _

/-- `∫ f_{t v} dμ = t ∫ f_v dμ`. -/
theorem integral_frameFun_smul (e : ℕ → ℂ → ℝ) (t : ℝ) (v : ℕ →₀ ℝ) (μ : Measure ℂ) :
    ∫ z, frameFun e (t • v) z ∂μ = t * ∫ z, frameFun e v z ∂μ := by
  simp_rw [frameFun_smul e t v]
  exact integral_const_mul _ _

/-- The truncation `(w_0, …, w_{n-1}, 0, 0, …)` of a sequence, as a finitely supported vector. -/
def truncFs (w : ℕ → ℝ) (n : ℕ) : ℕ →₀ ℝ := ∑ j ∈ Finset.range n, Finsupp.single j (w j)

theorem truncFs_sum_mul (w : ℕ → ℝ) (n : ℕ) (K : ℕ → ℝ) :
    ((truncFs w n).sum fun j c => c * K j) = ∑ j ∈ Finset.range n, w j * K j := by
  rw [truncFs, ← Finsupp.sum_finsetSum_index (fun j => zero_mul _) (fun j a b => add_mul _ _ _)]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_mul _)

/-- `∫ f_{trunc_n w} dμ = ∑_{j<n} w_j ∫ e_j dμ`. -/
theorem integral_frameFun_truncFs (he : IsGFFFrame e) (w : ℕ → ℝ) (n : ℕ) (μ : Measure ℂ)
    [IsFiniteMeasure μ] :
    ∫ z, frameFun e (truncFs w n) z ∂μ = ∑ j ∈ Finset.range n, w j * ∫ z, e j z ∂μ := by
  rw [integral_frameFun he, truncFs_sum_mul]

end Frame

/-! ## Truncation in `ℓ²` -/

/-- **`ℓ²` truncation (blueprint proof of Lemma `lem:law-M` (a)).** Let `∑_j u_j² = E`, `c > 0` and
`τ > 0`. There is `n` such that for every sequence `a` with `∑_j a_j² = A ≤ τ` and
`∑_j u_j a_j = P ≥ c`, the truncated pairing satisfies `c/2 ≤ ∑_{j<n} u_j a_j ≤ 1 + E τ`.

The lower bound is Cauchy–Schwarz on the tail: `|∑_{n ≤ j < N} u_j a_j|² ≤ (∑_{j ≥ n} u_j²) τ ≤
(c/2)²` once `∑_{j ≥ n} u_j² ≤ c²/(4τ)`. -/
theorem exists_trunc_pairing_bounds {u : ℕ → ℝ} {E : ℝ} (hu : HasSum (fun j => u j * u j) E)
    {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ (a : ℕ → ℝ) (A P : ℝ), HasSum (fun j => a j * a j) A → A ≤ τ →
      HasSum (fun j => u j * a j) P → c ≤ P →
        c / 2 ≤ ∑ j ∈ Finset.range n, u j * a j ∧
          ∑ j ∈ Finset.range n, u j * a j ≤ 1 + E * τ := by
  set δ : ℝ := c ^ 2 / (4 * τ) with hδ_def
  have hδ : 0 < δ := by positivity
  have hE : 0 ≤ E := hu.nonneg fun j => mul_self_nonneg (u j)
  obtain ⟨n, hn⟩ := (hu.tendsto_sum_nat.eventually_const_lt (sub_lt_self E hδ)).exists
  have hn' : E - δ < ∑ j ∈ Finset.range n, u j ^ 2 := by simpa only [sq] using hn
  refine ⟨n, fun a A P ha hA hua hP => ?_⟩
  have hsu : ∀ s : Finset ℕ, ∑ j ∈ s, u j ^ 2 ≤ E := fun s => by
    simpa only [sq] using sum_le_hasSum s (fun j _ => mul_self_nonneg (u j)) hu
  have hsa : ∀ s : Finset ℕ, ∑ j ∈ s, a j ^ 2 ≤ τ := fun s => by
    have h := sum_le_hasSum s (fun j _ => mul_self_nonneg (a j)) ha
    simp only [← sq] at h
    exact h.trans hA
  -- the tail of the pairing is at most `c/2`
  have hlow : ∀ N, n ≤ N →
      ∑ j ∈ Finset.range N, u j * a j ≤ ∑ j ∈ Finset.range n, u j * a j + c / 2 := by
    intro N hN
    have e1 : ∑ j ∈ Finset.range n, u j * a j + ∑ j ∈ Finset.Ico n N, u j * a j =
        ∑ j ∈ Finset.range N, u j * a j := Finset.sum_range_add_sum_Ico _ hN
    have e2 : ∑ j ∈ Finset.range n, u j ^ 2 + ∑ j ∈ Finset.Ico n N, u j ^ 2 =
        ∑ j ∈ Finset.range N, u j ^ 2 := Finset.sum_range_add_sum_Ico _ hN
    have h1 : ∑ j ∈ Finset.Ico n N, u j ^ 2 ≤ δ := by linarith [hsu (Finset.range N)]
    have h3 : (∑ j ∈ Finset.Ico n N, u j * a j) ^ 2 ≤ (c / 2) ^ 2 := by
      calc (∑ j ∈ Finset.Ico n N, u j * a j) ^ 2
          ≤ (∑ j ∈ Finset.Ico n N, u j ^ 2) * ∑ j ∈ Finset.Ico n N, a j ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ ≤ δ * τ := mul_le_mul h1 (hsa _) (Finset.sum_nonneg fun j _ => sq_nonneg _) hδ.le
        _ = (c / 2) ^ 2 := by
            rw [hδ_def]
            field_simp
            ring
    have h4 := (abs_le_of_sq_le_sq' h3 (by positivity)).2
    linarith
  have hPle : P ≤ ∑ j ∈ Finset.range n, u j * a j + c / 2 :=
    le_of_tendsto hua.tendsto_sum_nat (eventually_atTop.2 ⟨n, hlow⟩)
  refine ⟨by linarith, ?_⟩
  -- the truncated pairing is at most `(E τ)^{1/2} ≤ 1 + E τ`
  have h3 : (∑ j ∈ Finset.range n, u j * a j) ^ 2 ≤ E * τ :=
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans
      (mul_le_mul (hsu _) (hsa _) (Finset.sum_nonneg fun j _ => sq_nonneg _) hE)
  nlinarith [sq_nonneg (∑ j ∈ Finset.range n, u j * a j - 1), mul_nonneg hE hτ.le]

/-! ## The dyadic rationals of `[0,1]` -/

theorem countable_dyadicUnit : Setup.dyadicUnit.Countable := by
  have hsub : Setup.dyadicUnit ⊆ range fun p : ℕ × ℕ => (p.2 : ℝ) / 2 ^ p.1 := by
    rintro y ⟨n, k, -, rfl⟩
    exact ⟨(n, k), rfl⟩
  exact (countable_range _).mono hsub

instance instCountableDyadicUnit : Countable Setup.dyadicUnit :=
  countable_dyadicUnit.to_subtype

theorem zero_mem_dyadicUnit : (0 : ℝ) ∈ Setup.dyadicUnit :=
  ⟨0, 0, by norm_num, by norm_num⟩

theorem one_mem_dyadicUnit : (1 : ℝ) ∈ Setup.dyadicUnit :=
  ⟨0, 1, by norm_num, by norm_num⟩

instance instNonemptyDyadicUnit : Nonempty Setup.dyadicUnit :=
  ⟨⟨0, zero_mem_dyadicUnit⟩⟩

theorem dyadicUnit_subset_Icc : Setup.dyadicUnit ⊆ Icc (0 : ℝ) 1 := by
  rintro y ⟨n, k, hk, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_one h2]
  exact_mod_cast hk

end LawMAux

end GaussianLQG
