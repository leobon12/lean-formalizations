import GaussianLQG.Field.Pairing.Basic
import GaussianLQG.Probability.Gaussian
import LQGDimension.Existence.AssemblyAux1
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# The coordinate pairing: covariance, `L²` convergence, linearity, joint Gaussianity

Blueprint Lemma `lem:field`(a),(b), for a GFF frame `e` and regular measures.

* `tendsto_integral_sq_sub_pairing`: the partial sums converge to `(h, μ)` in `L²`.
* `integral_pairing`, `integral_pairing_mul`, `covariance_pairing`: the pairings are centered with
  covariance `E[(h, μ)(h, ν)] = ℰ(μ, ν)`.
* `isGaussianProcess_pairing`: `((h, μ))_{μ regular}` is a Gaussian process.
* `pairing_add_of_mem`, `pairing_smul_of_mem`, `pairing_finsetSum_of_mem` (on the convergence
  sets) and `ae_pairing_add`, `ae_pairing_smul`, `ae_pairing_finsetSum`: a.s. linearity for finite
  positive combinations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open Realization

variable {e : ℕ → ℂ → ℝ} {μ ν : Measure ℂ}

/-! ## Mean, second moments, covariance -/

/-- `E (h, μ) = 0`. -/
theorem integral_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) :
    ∫ ω, pairing e μ ω ∂stdP = 0 :=
  integral_of_hasLaw_gaussianReal (hasLaw_pairing he hμ)

/-- `E (h, μ)² = ℰ(μ, μ)`. -/
theorem integral_pairing_sq (he : IsGFFFrame e) (hμ : IsRegular μ) :
    ∫ ω, pairing e μ ω ^ 2 ∂stdP = energy μ μ := by
  rw [integral_sq_of_hasLaw_gaussianReal (hasLaw_pairing he hμ),
    Real.coe_toNNReal _ (he.energy_nonneg hμ)]

theorem memLp_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (pairing e μ) p stdP :=
  memLp_of_hasLaw_gaussianReal (hasLaw_pairing he hμ) hp

/-- **Lemma `lem:field`(b)**: `E[(h, μ)(h, ν)] = ℰ(μ, ν)`. -/
theorem integral_pairing_mul (he : IsGFFFrame e) (hμ : IsRegular μ) (hν : IsRegular ν) :
    ∫ ω, pairing e μ ω * pairing e ν ω ∂stdP = energy μ ν := by
  have hsum := hasLaw_sum_pairing he Finset.univ ![1, 1] ![μ, ν]
    (fun i _ => by fin_cases i <;> assumption)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hsum
  have hvar := integral_sq_of_hasLaw_gaussianReal hsum
  have hnn : 0 ≤ energy μ μ + energy μ ν + (energy ν μ + energy ν ν) := by
    have := (hasSum_sq_finsetSum he Finset.univ ![1, 1] ![μ, ν]
      (fun i _ => by fin_cases i <;> assumption)).nonneg fun _ => sq_nonneg _
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] using this
  rw [Real.coe_toNNReal _ hnn, energy_comm hν hμ] at hvar
  have h2μ := memLp_pairing he hμ (p := 2) ENNReal.ofNat_ne_top
  have h2ν := memLp_pairing he hν (p := 2) ENNReal.ofNat_ne_top
  have hiμ : Integrable (fun ω => pairing e μ ω ^ 2) stdP := h2μ.integrable_sq
  have hiν : Integrable (fun ω => pairing e ν ω ^ 2) stdP := h2ν.integrable_sq
  have hiμν : Integrable (fun ω => pairing e μ ω * pairing e ν ω) stdP := h2μ.integrable_mul h2ν
  have hexp : ∫ ω, (pairing e μ ω + pairing e ν ω) ^ 2 ∂stdP =
      ∫ ω, pairing e μ ω ^ 2 ∂stdP + 2 * ∫ ω, pairing e μ ω * pairing e ν ω ∂stdP +
        ∫ ω, pairing e ν ω ^ 2 ∂stdP := by
    have h12 : Integrable (fun ω => pairing e μ ω ^ 2 + 2 * (pairing e μ ω * pairing e ν ω))
        stdP := hiμ.add (hiμν.const_mul 2)
    rw [← integral_const_mul, ← integral_add hiμ (hiμν.const_mul 2), ← integral_add h12 hiν]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  rw [hexp, integral_pairing_sq he hμ, integral_pairing_sq he hν] at hvar
  linarith

/-- **Lemma `lem:field`(b)**: the covariance of `(h, μ)` and `(h, ν)` is `ℰ(μ, ν)`. -/
theorem covariance_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) (hν : IsRegular ν) :
    cov[pairing e μ, pairing e ν; stdP] = energy μ ν := by
  rw [covariance, integral_pairing he hμ, integral_pairing he hν]
  simp only [sub_zero]
  exact integral_pairing_mul he hμ hν

/-- `E((h, μ) - (h, ν))² = ℰ(μ,μ) - 2ℰ(μ,ν) + ℰ(ν,ν)`. -/
theorem integral_sq_pairing_sub (he : IsGFFFrame e) (hμ : IsRegular μ) (hν : IsRegular ν) :
    ∫ ω, (pairing e μ ω - pairing e ν ω) ^ 2 ∂stdP =
      energy μ μ - 2 * energy μ ν + energy ν ν := by
  have h := integral_sq_of_hasLaw_gaussianReal (hasLaw_pairing_sub he hμ hν)
  have hnn : 0 ≤ energy μ μ - 2 * energy μ ν + energy ν ν := by
    have := (hasSum_sq_finsetSum he Finset.univ ![1, -1] ![μ, ν]
      (fun i _ => by fin_cases i <;> assumption)).nonneg fun _ => sq_nonneg _
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, neg_mul,
      mul_one, neg_neg] at this
    rw [energy_comm hν hμ] at this
    linarith
  rwa [Real.coe_toNNReal _ hnn] at h

/-! ## `L²` convergence of the partial sums -/

/-- The tail coefficients `a_k 1_{k ≥ n}`. -/
def tailCoef (a : ℕ → ℝ) (n k : ℕ) : ℝ := if n ≤ k then a k else 0

theorem psum_tailCoef (a : ℕ → ℝ) {n N : ℕ} (hnN : n ≤ N) (ω : Coord) :
    psum (tailCoef a n) N ω = psum a N ω - psum a n ω := by
  unfold psum
  rw [← Finset.sum_range_add_sum_Ico _ hnN, ← Finset.sum_range_add_sum_Ico _ hnN]
  have h0 : ∑ k ∈ Finset.range n, ω k * tailCoef a n k = 0 :=
    Finset.sum_eq_zero fun k hk => by
      simp [tailCoef, not_le.2 (Finset.mem_range.1 hk)]
  have h1 : ∑ k ∈ Finset.Ico n N, ω k * tailCoef a n k = ∑ k ∈ Finset.Ico n N, ω k * a k :=
    Finset.sum_congr rfl fun k hk => by simp [tailCoef, (Finset.mem_Ico.1 hk).1]
  rw [h0, h1]
  ring

theorem summable_sq_tailCoef {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (n : ℕ) :
    Summable fun k => tailCoef a n k ^ 2 :=
  ha.of_nonneg_of_le (fun _ => sq_nonneg _) fun k => by
    unfold tailCoef
    split_ifs
    · exact le_rfl
    · rw [zero_pow two_ne_zero]; exact sq_nonneg _

theorem tsum_sq_tailCoef {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) (n : ℕ) :
    ∑' k, tailCoef a n k ^ 2 = sqTail a n := by
  rw [← (summable_sq_tailCoef ha n).sum_add_tsum_nat_add n]
  have h0 : ∑ k ∈ Finset.range n, tailCoef a n k ^ 2 = 0 :=
    Finset.sum_eq_zero fun k hk => by
      simp [tailCoef, not_le.2 (Finset.mem_range.1 hk)]
  rw [h0, zero_add, sqTail]
  exact tsum_congr fun k => by simp [tailCoef]

/-- **Lemma `lem:field`(a)**: `E((h, μ) - ∑_{j<n} ω_j ∫ e_j dμ)² = ∑_{j ≥ n} (∫ e_j dμ)²`. -/
theorem integral_sq_sub_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) (n : ℕ) :
    ∫ ω, (pairing e μ ω - ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) ^ 2 ∂stdP =
      sqTail (frameCoef e μ) n := by
  have ha := he.summable_sq hμ
  have hlaw := hasLaw_seriesLim (summable_sq_tailCoef ha n)
  rw [tsum_sq_tailCoef ha n] at hlaw
  have hae : (fun ω => pairing e μ ω - ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) =ᵐ[stdP]
      seriesLim (tailCoef (frameCoef e μ) n) := by
    filter_upwards [ae_mem_pairingSet he hμ] with ω hω
    refine (seriesLim_eq_of_tendsto ?_).symm
    refine ((tendsto_pairing_of_mem hω).sub_const (psum (frameCoef e μ) n ω)).congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [psum_tailCoef _ hN]
    rfl
  rw [integral_sq_of_hasLaw_gaussianReal (hlaw.congr hae),
    Real.coe_toNNReal _ (sqTail_nonneg _ n)]

/-- **Lemma `lem:field`(a)**: the partial sums converge to `(h, μ)` in `L²`. -/
theorem tendsto_integral_sq_sub_pairing (he : IsGFFFrame e) (hμ : IsRegular μ) :
    Tendsto (fun n => ∫ ω, (pairing e μ ω - ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) ^ 2
      ∂stdP) atTop (𝓝 0) := by
  simp_rw [integral_sq_sub_pairing he hμ]
  exact tendsto_sqTail _

/-! ## Linearity -/

theorem frameCoef_add (he : IsGFFFrame e) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (j : ℕ) :
    frameCoef e (μ + ν) j = frameCoef e μ j + frameCoef e ν j :=
  integral_add_measure (he.integrable μ j) (he.integrable ν j)

theorem frameCoef_smul (c : ℝ≥0∞) (μ : Measure ℂ) (j : ℕ) :
    frameCoef e (c • μ) j = c.toReal * frameCoef e μ j := by
  unfold frameCoef
  rw [integral_smul_measure, smul_eq_mul]

theorem frameCoef_finsetSum (he : IsGFFFrame e) {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (μ : ι → Measure ℂ) [∀ i, IsFiniteMeasure (μ i)] (j : ℕ) :
    frameCoef e (∑ i ∈ s, c i • μ i) j = ∑ i ∈ s, (c i : ℝ) * frameCoef e (μ i) j := by
  unfold frameCoef
  rw [integral_finsetSum_measure fun i _ => (he.integrable (μ i) j).smul_measure_nnreal]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_smul_nnreal_measure, NNReal.smul_def,
    smul_eq_mul]

/-- On `Ω_μ ∩ Ω_ν`: `(h, μ + ν) = (h, μ) + (h, ν)`. -/
theorem pairing_add_of_mem (he : IsGFFFrame e) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ω : Coord} (hμω : ω ∈ pairingSet e μ) (hνω : ω ∈ pairingSet e ν) :
    pairing e (μ + ν) ω = pairing e μ ω + pairing e ν ω := by
  refine pairing_eq_of_tendsto (((tendsto_pairing_of_mem hμω).add
    (tendsto_pairing_of_mem hνω)).congr fun n => ?_)
  rw [← psum_frameCoef, ← psum_frameCoef, ← psum_frameCoef]
  unfold psum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [frameCoef_add he]; ring

/-- On `Ω_μ`: `(h, c μ) = c (h, μ)`. -/
theorem pairing_smul_of_mem (c : ℝ≥0∞) {ω : Coord} (hω : ω ∈ pairingSet e μ) :
    pairing e (c • μ) ω = c.toReal * pairing e μ ω := by
  refine pairing_eq_of_tendsto (((tendsto_pairing_of_mem hω).const_mul c.toReal).congr
    fun n => ?_)
  rw [← psum_frameCoef, ← psum_frameCoef]
  unfold psum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [frameCoef_smul]; ring

/-- On `⋂_i Ω_{μ_i}`: `(h, ∑ c_i μ_i) = ∑ c_i (h, μ_i)` for `c_i ≥ 0`. -/
theorem pairing_finsetSum_of_mem (he : IsGFFFrame e) {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (μ : ι → Measure ℂ) [∀ i, IsFiniteMeasure (μ i)] {ω : Coord}
    (hω : ∀ i ∈ s, ω ∈ pairingSet e (μ i)) :
    pairing e (∑ i ∈ s, c i • μ i) ω = ∑ i ∈ s, (c i : ℝ) * pairing e (μ i) ω := by
  refine pairing_eq_of_tendsto ((tendsto_psum_finsetSum s (fun i => (c i : ℝ)) μ hω).congr
    fun n => ?_)
  rw [← psum_frameCoef]
  unfold psum
  exact Finset.sum_congr rfl fun j _ => by rw [frameCoef_finsetSum he]

/-- **Lemma `lem:field`(b)**, a.s. linearity: `(h, μ + ν) = (h, μ) + (h, ν)` a.s. -/
theorem ae_pairing_add (he : IsGFFFrame e) (hμ : IsRegular μ) (hν : IsRegular ν) :
    ∀ᵐ ω ∂stdP, pairing e (μ + ν) ω = pairing e μ ω + pairing e ν ω := by
  have := hμ.1
  have := hν.1
  filter_upwards [ae_mem_pairingSet he hμ, ae_mem_pairingSet he hν] with ω h1 h2
  exact pairing_add_of_mem he h1 h2

/-- **Lemma `lem:field`(b)**, a.s. homogeneity: `(h, c μ) = c (h, μ)` a.s. -/
theorem ae_pairing_smul (he : IsGFFFrame e) (hμ : IsRegular μ) (c : ℝ≥0∞) :
    ∀ᵐ ω ∂stdP, pairing e (c • μ) ω = c.toReal * pairing e μ ω := by
  filter_upwards [ae_mem_pairingSet he hμ] with ω hω
  exact pairing_smul_of_mem c hω

/-- **Lemma `lem:field`(b)**, a.s. linearity for finite positive combinations. -/
theorem ae_pairing_finsetSum (he : IsGFFFrame e) {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (μ : ι → Measure ℂ) (hμ : ∀ i, IsRegular (μ i)) :
    ∀ᵐ ω ∂stdP, pairing e (∑ i ∈ s, c i • μ i) ω = ∑ i ∈ s, (c i : ℝ) * pairing e (μ i) ω := by
  have : ∀ i, IsFiniteMeasure (μ i) := fun i => (hμ i).1
  filter_upwards [ae_forall_mem_pairingSet he s μ fun i _ => hμ i] with ω hω
  exact pairing_finsetSum_of_mem he s c μ hω

/-! ## Joint Gaussianity -/

/-- **Lemma `lem:field`(b)**: the pairings with regular measures form a Gaussian process. -/
theorem isGaussianProcess_pairing (he : IsGFFFrame e) :
    IsGaussianProcess (fun μ : {μ : Measure ℂ // IsRegular μ} => pairing e μ.1) stdP where
  hasGaussianLaw I := by
    refine LQGDimension.ExistAsm.hasGaussianLaw_pi_of_forall_hasLaw
      (Y := fun (i : I) => pairing e i.1.1)
      (fun i => (measurable_pairing e _).aemeasurable) fun c => ?_
    exact ⟨_, hasLaw_sum_pairing he Finset.univ c (fun i : I => i.1.1) fun i _ => i.1.2⟩

end GaussianLQG
