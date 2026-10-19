import GaussianLQG.Field.Frame
import GaussianLQG.Field.Realization
import GaussianLQG.Energy.Measures
import LQGMetric.Field.MeasurableAvg

/-!
# The unconditional coordinate realization (blueprint Proposition `prop:realization`)

`exists_coordRealization`: there are a GFF frame `e` (blueprint Definition `def:frame`), a
measurable field `h₀ : ℝ^ℕ → 𝒟'(ℂ)` that is a whole-plane GFF normalized by `h_1(0) = 0` under
`stdP`, and a measurable, full-measure, shift-invariant set `Ω_W` with

* (b) `h₀(ω + v) = h₀(ω) + f_v` for `ω ∈ Ω_W` and finitely supported `v`;
* (c) for every regular `μ`, a.s. `(h₀, μ) = lim_n ∑_{j<n} ω_j ∫ e_j dμ`.

It combines the white-noise frame of Appendix B (`exists_nice_hilbertBasis`,
`isGFFFrame_of_nice`) with the realization theorem `exists_realization`.

Two consequences used to instantiate `Setup`:
* `pairing_ae_eq_measPairing`: the coordinate pairing `pairing e μ` (the limit of the partial sums)
  agrees a.s. with the mollified pairing `(h₀, μ)`;
* `measPairing_circleMeasure`: `(g, σ_{z,r}) = g_r(z)` (`LQGMetric.circleAvg`) for every
  distribution `g`, since both are limits of the same mollified circle averages.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

open LQGMetric

/-- **Coordinate realization of the normalized whole-plane GFF** (blueprint Proposition
`prop:realization`), unconditionally: the frame is the white-noise frame of Appendix B. -/
theorem exists_coordRealization :
    ∃ (e : ℕ → ℂ → ℝ) (he : IsGFFFrame e) (h₀ : Coord → DistC) (ΩW : Set Coord),
      Measurable h₀ ∧ IsNormalizedWPGFF h₀ stdP ∧ MeasurableSet ΩW ∧ stdP ΩWᶜ = 0 ∧
      (∀ ω ∈ ΩW, ∀ v, shiftBy ω v ∈ ΩW) ∧
      (∀ ω ∈ ΩW, ∀ v, h₀ (shiftBy ω v) = addFun (h₀ ω) (frameFunC e he.1 v)) ∧
      ∀ μ, IsRegular μ → ∀ᵐ ω ∂stdP,
        Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop
          (𝓝 (measPairing (h₀ ω) μ)) := by
  obtain ⟨b, hb⟩ := exists_nice_hilbertBasis
  have he := isGFFFrame_of_nice b hb
  exact ⟨_, he, exists_realization b hb he.1 he⟩

/-- Where the partial sums of the frame series converge to `(h₀, μ)`, the coordinate pairing
`pairing e μ` (their `limUnder`) equals `(h₀, μ)`. -/
theorem pairing_ae_eq_measPairing {e : ℕ → ℂ → ℝ} {h₀ : Coord → DistC} {μ : Measure ℂ}
    (hμ : ∀ᵐ ω ∂stdP, Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, e j z ∂μ) atTop
      (𝓝 (measPairing (h₀ ω) μ))) :
    pairing e μ =ᵐ[stdP] fun ω => measPairing (h₀ ω) μ :=
  hμ.mono fun _ hω => hω.limUnder_eq

/-- **`(g, σ_{z,r}) = g_r(z)`** (blueprint Lemma `lem:pairing`, last claim, which holds by
definition): the pairing with the uniform measure on `∂B_r(z)` is `LQGMetric`'s circle average,
for every distribution `g`. -/
theorem measPairing_circleMeasure (g : DistC) (z : ℂ) (r : ℝ) :
    measPairing g (circleMeasure z r) = circleAvg g r z := by
  unfold measPairing circleAvg
  congr 1
  funext n
  exact integral_circleMeasure z r
    ((map_continuous g).comp (continuous_bumpTest n)).aestronglyMeasurable

end GaussianLQG
