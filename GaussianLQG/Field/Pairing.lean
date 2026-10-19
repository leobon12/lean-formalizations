import GaussianLQG.Field.Pairing.Basic
import GaussianLQG.Field.Pairing.Linear
import GaussianLQG.Field.Pairing.Quasi
import GaussianLQG.Field.Pairing.Circle
import GaussianLQG.Field.Pairing.Segments

/-!
# The coordinate pairing (blueprint Lemma `lem:field`)

Let `e` be a GFF frame (`IsGFFFrame e`), `ℙ = stdP` the standard Gaussian product measure on
`ℝ^ℕ`, and `(h, μ)(ω) = pairing e μ ω = lim_n ∑_{j<n} ω_j ∫ e_j dμ`.

* (a) `pairingSet e μ` (the convergence set `Ω_μ`) is measurable, has full measure for regular
  `μ`, and `Ω_μ + v = Ω_μ`, with `(h, μ)(ω + v) = (h, μ)(ω) + ∫ f_v dμ` on `Ω_μ`
  (`lemField_a`); the partial sums converge a.s. and in `L²` (`ae_tendsto_pairing`,
  `tendsto_integral_sq_sub_pairing`).
* (b) `((h, μ))_{μ regular}` is a centered Gaussian process with covariance `ℰ`, a.s. linear for
  finite positive combinations (`lemField_b`; `hasLaw_pairing`, `isGaussianProcess_pairing`,
  `covariance_pairing`, `hasLaw_sum_pairing`, `ae_pairing_finsetSum`).
* (c) `ℙ` is invariant under `ω ↦ -ω`, which maps `(h, μ)` to `-(h, μ)` on `Ω_μ`; the law of
  `ω + v` is `exp(∑ v_j ω_j - ½ ∑ v_j²) · ℙ`, mutually absolutely continuous with `ℙ`
  (`lemField_c`; `stdP_map_neg`, `pairing_neg`, `stdP_map_shiftBy`).

The module also re-exports the circle energies (`Field/Pairing/Circle.lean`) and the regularity
of the segment pairings `H(s,t)` (blueprint Lemma `lem:H-continuity`,
`Field/Pairing/Segments.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

variable {e : ℕ → ℂ → ℝ} {μ ν : Measure ℂ}

/-- **Lemma `lem:field`(a)**: for regular `μ`, the convergence set `Ω_μ` of the coordinate
series is measurable, has probability one and is invariant under finitely supported shifts, and
`(h, μ)(ω + v) = (h, μ)(ω) + ∫ f_v dμ` for `ω ∈ Ω_μ`; the series converges in `L²`. -/
theorem lemField_a (he : IsGFFFrame e) (hμ : IsRegular μ) :
    MeasurableSet (pairingSet e μ) ∧ (∀ᵐ ω ∂stdP, ω ∈ pairingSet e μ) ∧
      (∀ (ω : Coord) (v : ℕ →₀ ℝ), shiftBy ω v ∈ pairingSet e μ ↔ ω ∈ pairingSet e μ) ∧
      (∀ ω ∈ pairingSet e μ, ∀ v : ℕ →₀ ℝ,
        pairing e μ (shiftBy ω v) = pairing e μ ω + ∫ z, frameFun e v z ∂μ) ∧
      Tendsto (fun n => ∫ ω, (pairing e μ ω - ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) ^ 2
        ∂stdP) atTop (𝓝 0) := by
  have := hμ.1
  exact ⟨measurableSet_pairingSet e μ, ae_mem_pairingSet he hμ,
    fun _ v => shiftBy_mem_pairingSet_iff v, fun _ hω v => pairing_shiftBy he hω v,
    tendsto_integral_sq_sub_pairing he hμ⟩

/-- **Lemma `lem:field`(b)**: `(h, μ) ∼ N(0, ℰ(μ, μ))`, the pairings with regular measures form a
Gaussian process with covariance `ℰ`, and they are a.s. linear for finite positive
combinations. -/
theorem lemField_b (he : IsGFFFrame e) :
    (∀ μ, IsRegular μ → HasLaw (pairing e μ) (gaussianReal 0 (energy μ μ).toNNReal) stdP) ∧
      IsGaussianProcess (fun μ : {μ : Measure ℂ // IsRegular μ} => pairing e μ.1) stdP ∧
      (∀ μ ν, IsRegular μ → IsRegular ν → cov[pairing e μ, pairing e ν; stdP] = energy μ ν) ∧
      (∀ {ι : Type} (s : Finset ι) (c : ι → ℝ≥0) (μ : ι → Measure ℂ), (∀ i, IsRegular (μ i)) →
        ∀ᵐ ω ∂stdP, pairing e (∑ i ∈ s, c i • μ i) ω = ∑ i ∈ s, (c i : ℝ) * pairing e (μ i) ω) :=
  ⟨fun _ hμ => hasLaw_pairing he hμ, isGaussianProcess_pairing he,
    fun _ _ hμ hν => covariance_pairing he hμ hν,
    fun s c μ hμ => ae_pairing_finsetSum he s c μ hμ⟩

/-- **Lemma `lem:field`(c)**: `ℙ` is invariant under `ω ↦ -ω`, which maps `(h, μ)` to `-(h, μ)` on
`Ω_μ`; for finitely supported `v` the law of `ω + v` has density `exp(∑ v_j ω_j - ½ ∑ v_j²)` with
respect to `ℙ`, and is mutually absolutely continuous with `ℙ`. -/
theorem lemField_c :
    stdP.map (fun ω : Coord => -ω) = stdP ∧
      (∀ ω ∈ pairingSet e μ, pairing e μ (-ω) = -pairing e μ ω) ∧
      ∀ v : ℕ →₀ ℝ, stdP.map (fun ω => shiftBy ω v) =
          stdP.withDensity (fun ω => ENNReal.ofReal (Real.exp
            (∑ j ∈ v.support, v j * ω j - (∑ j ∈ v.support, v j ^ 2) / 2))) ∧
        stdP.map (fun ω => shiftBy ω v) ≪ stdP ∧ stdP ≪ stdP.map (fun ω => shiftBy ω v) :=
  ⟨stdP_map_neg, fun _ hω => pairing_neg hω,
    fun v => ⟨stdP_map_shiftBy v, map_shiftBy_absolutelyContinuous v,
      absolutelyContinuous_map_shiftBy v⟩⟩

end GaussianLQG
