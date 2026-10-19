import GaussianLQG.Energy.All
import GaussianLQG.Field.Realization.Series
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# The coordinate pairing: convergence, shifts, Gaussian laws (blueprint Lemma `lem:field`)

For a GFF frame `e` (`IsGFFFrame e`) and a regular measure `μ`, the pairing
`pairing e μ ω = lim_n ∑_{j<n} ω_j ∫ e_j dμ` is the sum of the coordinate series with the
square-summable coefficients `frameCoef e μ j = ∫ e_j dμ` (`∑_j (∫ e_j dμ)² = ℰ(μ, μ)`).

* `pairingSet e μ`: the (measurable) convergence set `Ω_μ`; it has full measure
  (`ae_mem_pairingSet`) and is invariant under finitely supported shifts
  (`shiftBy_mem_pairingSet_iff`), with `pairing_shiftBy`:
  `(h, μ)(ω + v) = (h, μ)(ω) + ∫ f_v dμ` on `Ω_μ`.
* `tendsto_integral_sq_sub_pairing`: the partial sums also converge in `L²`.
* `hasLaw_sum_pairing`: every finite real combination `∑ c_i (h, μ_i)` is a centered Gaussian with
  variance `∑_{i,k} c_i c_k ℰ(μ_i, μ_k)`; in particular `hasLaw_pairing`
  (`(h, μ) ∼ N(0, ℰ(μ, μ))`) and `hasLaw_pairing_sub`.

The almost sure convergence of the coordinate series is
`GaussianLQG.Realization.ae_exists_tendsto_psum` (Lévy–Kolmogorov via Gaussian chaining).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open Realization

variable {e : ℕ → ℂ → ℝ} {μ ν : Measure ℂ}

/-! ## Coefficients and the convergence set -/

/-- The frame coefficients `c_j(μ) = ∫ e_j dμ`. -/
def frameCoef (e : ℕ → ℂ → ℝ) (μ : Measure ℂ) (j : ℕ) : ℝ := ∫ z, e j z ∂μ

/-- The convergence set `Ω_μ` of the coordinate series defining `(h, μ)`. -/
def pairingSet (e : ℕ → ℂ → ℝ) (μ : Measure ℂ) : Set Coord :=
  {ω | ∃ L, Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop (𝓝 L)}

theorem psum_frameCoef (e : ℕ → ℂ → ℝ) (μ : Measure ℂ) (n : ℕ) (ω : Coord) :
    psum (frameCoef e μ) n ω = ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ := rfl

theorem mem_pairingSet_iff {ω : Coord} :
    ω ∈ pairingSet e μ ↔ ∃ L, Tendsto (fun n => psum (frameCoef e μ) n ω) atTop (𝓝 L) :=
  Iff.rfl

theorem measurable_pairing (e : ℕ → ℂ → ℝ) (μ : Measure ℂ) : Measurable (pairing e μ) :=
  measurable_seriesLim _

theorem measurableSet_pairingSet (e : ℕ → ℂ → ℝ) (μ : Measure ℂ) :
    MeasurableSet (pairingSet e μ) :=
  measurableSet_exists_tendsto fun n => measurable_psum (frameCoef e μ) n

/-- On `Ω_μ` the partial sums converge to `(h, μ)`. -/
theorem tendsto_pairing_of_mem {ω : Coord} (hω : ω ∈ pairingSet e μ) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop
      (𝓝 (pairing e μ ω)) :=
  tendsto_nhds_limUnder hω

theorem pairing_eq_of_tendsto {ω : Coord} {L : ℝ}
    (h : Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop (𝓝 L)) :
    pairing e μ ω = L :=
  h.limUnder_eq

/-! ## Frame facts -/

namespace IsGFFFrame

theorem hasSum_mul (he : IsGFFFrame e) (hμ : IsRegular μ) (hν : IsRegular ν) :
    HasSum (fun j => frameCoef e μ j * frameCoef e ν j) (energy μ ν) :=
  he.2.2 μ ν hμ hν

theorem hasSum_sq (he : IsGFFFrame e) (hμ : IsRegular μ) :
    HasSum (fun j => frameCoef e μ j ^ 2) (energy μ μ) := by
  simpa only [sq] using he.hasSum_mul hμ hμ

theorem summable_sq (he : IsGFFFrame e) (hμ : IsRegular μ) :
    Summable fun j => frameCoef e μ j ^ 2 :=
  (he.hasSum_sq hμ).summable

theorem tsum_sq (he : IsGFFFrame e) (hμ : IsRegular μ) :
    ∑' j, frameCoef e μ j ^ 2 = energy μ μ :=
  (he.hasSum_sq hμ).tsum_eq

/-- `ℰ(μ, μ) ≥ 0` for regular `μ`. -/
theorem energy_nonneg (he : IsGFFFrame e) (hμ : IsRegular μ) : 0 ≤ energy μ μ :=
  (he.hasSum_sq hμ).nonneg fun _ => sq_nonneg _

/-- Each frame function is integrable against a finite measure. -/
theorem integrable (he : IsGFFFrame e) (μ : Measure ℂ) [IsFiniteMeasure μ] (j : ℕ) :
    Integrable (e j) μ := by
  obtain ⟨C, hC⟩ := he.2.1 j
  exact Integrable.of_bound (he.1 j).aestronglyMeasurable C
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)

/-- `∫ f_v dμ = ∑_j v_j ∫ e_j dμ`. -/
theorem integral_frameFun (he : IsGFFFrame e) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (v : ℕ →₀ ℝ) : ∫ z, frameFun e v z ∂μ = v.sum fun j c => c * frameCoef e μ j := by
  unfold frameFun Finsupp.sum frameCoef
  rw [integral_finsetSum _ fun j _ => (he.integrable μ j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

end IsGFFFrame

/-- `Ω_μ` has full measure. -/
theorem ae_mem_pairingSet (he : IsGFFFrame e) (hμ : IsRegular μ) :
    ∀ᵐ ω ∂stdP, ω ∈ pairingSet e μ :=
  ae_exists_tendsto_psum (he.summable_sq hμ)

/-- **Lemma `lem:field`(a)**: the coordinate series converges almost surely to `(h, μ)`. -/
theorem ae_tendsto_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) :
    ∀ᵐ ω ∂stdP, Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop
      (𝓝 (pairing e μ ω)) := by
  filter_upwards [ae_mem_pairingSet he hμ] with ω hω
  exact tendsto_pairing_of_mem hω

/-! ## Finitely supported shifts -/

theorem eventually_psum_coe_finsupp (a : ℕ → ℝ) (v : ℕ →₀ ℝ) :
    ∀ᶠ n in atTop, psum a n ⇑v = v.sum fun k c => c * a k :=
  eventually_atTop.2 ⟨suppBound v, fun _ hn => psum_finsupp a v hn⟩

/-- **Lemma `lem:field`(a)**: `Ω_μ + v = Ω_μ` for finitely supported `v`. -/
theorem shiftBy_mem_pairingSet_iff {ω : Coord} (v : ℕ →₀ ℝ) :
    shiftBy ω v ∈ pairingSet e μ ↔ ω ∈ pairingSet e μ := by
  simp only [mem_pairingSet_iff]
  set K : ℝ := v.sum fun k c => c * frameCoef e μ k
  have hev := eventually_psum_coe_finsupp (frameCoef e μ) v
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L - K, (hL.sub_const K).congr' ?_⟩
    filter_upwards [hev] with n hn
    rw [psum_shift, hn, add_sub_cancel_right]
  · rintro ⟨L, hL⟩
    refine ⟨L + K, (hL.add_const K).congr' ?_⟩
    filter_upwards [hev] with n hn
    rw [psum_shift, hn]

/-- **Lemma `lem:field`(a)**: `(h, μ)(ω + v) = (h, μ)(ω) + ∫ f_v dμ` on `Ω_μ`. -/
theorem pairing_shiftBy (he : IsGFFFrame e) [IsFiniteMeasure μ] {ω : Coord}
    (hω : ω ∈ pairingSet e μ) (v : ℕ →₀ ℝ) :
    pairing e μ (shiftBy ω v) = pairing e μ ω + ∫ z, frameFun e v z ∂μ := by
  rw [he.integral_frameFun μ v]
  refine pairing_eq_of_tendsto (((tendsto_pairing_of_mem hω).add_const _).congr' ?_)
  filter_upwards [eventually_psum_coe_finsupp (frameCoef e μ) v] with n hn
  rw [← psum_frameCoef, ← psum_frameCoef, psum_shift, hn]

/-- **Lemma `lem:field`(a)**, a.s. form: almost surely, for every finitely supported `v`,
`(h, μ)(ω + v) = (h, μ)(ω) + ∫ f_v dμ`. -/
theorem ae_pairing_shiftBy (he : IsGFFFrame e) (hμ : IsRegular μ) :
    ∀ᵐ ω ∂stdP, ∀ v : ℕ →₀ ℝ,
      pairing e μ (shiftBy ω v) = pairing e μ ω + ∫ z, frameFun e v z ∂μ := by
  have := hμ.1
  filter_upwards [ae_mem_pairingSet he hμ] with ω hω v
  exact pairing_shiftBy he hω v

/-! ## Linearity of the partial sums -/

theorem psum_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (a : ι → ℕ → ℝ) (n : ℕ)
    (ω : Coord) :
    psum (fun j => ∑ i ∈ s, c i * a i j) n ω = ∑ i ∈ s, c i * psum (a i) n ω := by
  unfold psum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- On `⋂_i Ω_{μ_i}`, the series with coefficients `∑ c_i c_j(μ_i)` converges to
`∑ c_i (h, μ_i)`. -/
theorem tendsto_psum_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (μ : ι → Measure ℂ)
    {ω : Coord} (hω : ∀ i ∈ s, ω ∈ pairingSet e (μ i)) :
    Tendsto (fun n => psum (fun j => ∑ i ∈ s, c i * frameCoef e (μ i) j) n ω) atTop
      (𝓝 (∑ i ∈ s, c i * pairing e (μ i) ω)) := by
  simp_rw [psum_finsetSum]
  exact tendsto_finsetSum s fun i hi => (tendsto_pairing_of_mem (hω i hi)).const_mul (c i)

theorem ae_forall_mem_pairingSet (he : IsGFFFrame e) {ι : Type*} (s : Finset ι)
    (μ : ι → Measure ℂ) (hμ : ∀ i ∈ s, IsRegular (μ i)) :
    ∀ᵐ ω ∂stdP, ∀ i ∈ s, ω ∈ pairingSet e (μ i) :=
  (Filter.eventually_all_finset s).2 fun i hi => ae_mem_pairingSet he (hμ i hi)

/-! ## Gaussian laws of finite combinations -/

/-- The squared coefficients of a finite combination sum to the quadratic form of `ℰ`. -/
theorem hasSum_sq_finsetSum (he : IsGFFFrame e) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (μ : ι → Measure ℂ) (hμ : ∀ i ∈ s, IsRegular (μ i)) :
    HasSum (fun j => (∑ i ∈ s, c i * frameCoef e (μ i) j) ^ 2)
      (∑ i ∈ s, ∑ k ∈ s, c i * c k * energy (μ i) (μ k)) := by
  have h : ∀ j, (∑ i ∈ s, c i * frameCoef e (μ i) j) ^ 2 =
      ∑ i ∈ s, ∑ k ∈ s, c i * c k * (frameCoef e (μ i) j * frameCoef e (μ k) j) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h]
  exact hasSum_sum fun i hi => hasSum_sum fun k hk =>
    (he.hasSum_mul (hμ i hi) (hμ k hk)).mul_left _

/-- **Lemma `lem:field`(b)**: a finite real combination `∑ c_i (h, μ_i)` of pairings with regular
measures is a centered Gaussian with variance `∑_{i,k} c_i c_k ℰ(μ_i, μ_k)`. -/
theorem hasLaw_sum_pairing (he : IsGFFFrame e) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (μ : ι → Measure ℂ) (hμ : ∀ i ∈ s, IsRegular (μ i)) :
    HasLaw (fun ω => ∑ i ∈ s, c i * pairing e (μ i) ω)
      (gaussianReal 0 (∑ i ∈ s, ∑ k ∈ s, c i * c k * energy (μ i) (μ k)).toNNReal) stdP := by
  have hsum := hasSum_sq_finsetSum he s c μ hμ
  have hlaw := hasLaw_seriesLim hsum.summable
  rw [hsum.tsum_eq] at hlaw
  refine hlaw.congr ?_
  filter_upwards [ae_forall_mem_pairingSet he s μ hμ] with ω hω
  exact (seriesLim_eq_of_tendsto (tendsto_psum_finsetSum s c μ hω)).symm

/-- **Lemma `lem:field`(b)**: `(h, μ) ∼ N(0, ℰ(μ, μ))`. -/
theorem hasLaw_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) :
    HasLaw (pairing e μ) (gaussianReal 0 (energy μ μ).toNNReal) stdP := by
  have h := hasLaw_seriesLim (he.summable_sq hμ)
  rwa [he.tsum_sq hμ] at h

/-- `(h, μ) - (h, ν) ∼ N(0, ℰ(μ,μ) - 2ℰ(μ,ν) + ℰ(ν,ν))`. -/
theorem hasLaw_pairing_sub (he : IsGFFFrame e) (hμ : IsRegular μ) (hν : IsRegular ν) :
    HasLaw (fun ω => pairing e μ ω - pairing e ν ω)
      (gaussianReal 0 (energy μ μ - 2 * energy μ ν + energy ν ν).toNNReal) stdP := by
  have h := hasLaw_sum_pairing he Finset.univ ![1, -1] ![μ, ν]
    (fun i _ => by fin_cases i <;> assumption)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, neg_mul,
    mul_one, neg_neg] at h
  rw [energy_comm hν hμ, show energy μ μ + -energy μ ν + (-energy μ ν + energy ν ν) =
    energy μ μ - 2 * energy μ ν + energy ν ν by ring] at h
  exact h.congr (ae_of_all _ fun ω => sub_eq_add_neg _ _)

/-! ## Compatibility names (cleanup W15)

Old names of the partial-sum lemmas that now live in `GaussianLQG/Field/Realization/Series.lean`
(`Realization.suppBound`, `Realization.psum_shift`, `Realization.psum_finsupp`). -/

alias shiftBound := suppBound

theorem support_subset_range_shiftBound (v : ℕ →₀ ℝ) {n : ℕ} (hn : shiftBound v ≤ n) :
    v.support ⊆ Finset.range n :=
  (Finset.subset_range_sup_succ v.support).trans (Finset.range_subset_range.2 hn)

alias psum_shiftBy := psum_shift

theorem psum_coe_finsupp (a : ℕ → ℝ) (v : ℕ →₀ ℝ) {n : ℕ} (hn : shiftBound v ≤ n) :
    psum a n ⇑v = v.sum fun k c => c * a k :=
  psum_finsupp a v hn

end GaussianLQG
