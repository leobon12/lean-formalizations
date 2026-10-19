import GaussianLQG.Probability.GaussianLp.Projection

/-!
# The Gaussian `L^p` inequality

Blueprint Proposition `prop:gaussian-Lp` (source (3.2)). Let `1 ≤ p < ∞` and let
`F : ℝ^ℕ → ℝ` be measurable with `E|F|^p < ∞` under the product Gaussian measure `P = stdP`.
Suppose that there are a measurable set `𝒢` with `P(𝒢) = 1` and constants `L_j` such that for
every `ω ∈ 𝒢`

  `|F(ω + v) - F(ω + v')| ≤ ∑_j L_j |v_j - v'_j|` for all finitely supported `v, v'` (H)

(the points `ω + v` need not lie in `𝒢`). Then

* (a) for each `j`, `∂_j F(ω) = d/dt|_{t=0} F(ω + t δ_j)` exists for `P`-a.e. `ω`
  (`GaussianLQG.ae_differentiableAt_coord`; `∂_j F` is a.e. strongly measurable,
  `GaussianLQG.aestronglyMeasurable_coordDeriv`);
* (b) `‖F - E F‖_p ≤ c_p ‖(∑_j |∂_j F|²)^{1/2}‖_p` with `c_p = (π/2) ‖N‖_p`,
  `N ∼ 𝒩(0, 1)` (`GaussianLQG.gaussian_Lp_inequality`).

Conventions. `∂_j F` is `GaussianLQG.coordDeriv F j`, with the junk value `0` where the derivative
does not exist (as in the blueprint). The right side of (b) is written with lower integrals:
`G = (∫⁻ (∑'_j ofReal ((∂_j F)²))^{p/2})^{1/p} ∈ [0, ∞]`, where the `[0, ∞]`-valued series
`∑'_j ofReal ((∂_j F)²)` is `∞` exactly at the points where `∑_j (∂_j F)²` diverges. Hence
non-summability on a set of positive measure makes the right side `∞` (never a junk `0`), and
otherwise `G` is the usual `‖(∑_j |∂_j F|²)^{1/2}‖_p`.

Proof (blueprint). For each `n`, the projection `F_n(x) = ∫ F(x, y) dP(y)` onto the first `n`
coordinates is Lipschitz and satisfies `E|F_n - E F|^p ≤ (π/2)^p E|N|^p E Γ^p` by the
finite-dimensional Maurey–Pisier inequality (`GaussianLp/FiniteDim.lean`), Minkowski and Jensen
(`GaussianLp/Projection.lean`). Since `F_n(ω₀, …, ω_{n-1}) = E[F | ω₀, …, ω_{n-1}]`, Lévy's upward
theorem gives `F_n → F` a.s. (`GaussianLp/Split.lean`), and Fatou's lemma concludes. No `L^p`
martingale convergence theorem is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open GaussLp

/-- **The Gaussian `L^p` inequality** (blueprint Proposition `prop:gaussian-Lp` (b); source (3.2)).
Let `1 ≤ p < ∞` and let `F : ℝ^ℕ → ℝ` be measurable and in `L^p(P)`. Suppose that on a measurable
set `𝒢` of full measure, `|F(ω + v) - F(ω + v')| ≤ ∑_j L_j |v_j - v'_j|` for all finitely
supported `v, v'`. Then
`‖F - E F‖_p ≤ c_p (E (∑_j |∂_j F|²)^{p/2})^{1/p}`, `c_p = (π/2) (E|N|^p)^{1/p}`,
where the square function is summed in `[0, ∞]`. -/
theorem gaussian_Lp_inequality {F : Coord → ℝ} (hF : Measurable F) {𝒢 : Set Coord}
    (h𝒢 : MeasurableSet 𝒢) (h𝒢c : stdP 𝒢ᶜ = 0) {L : ℕ → ℝ}
    (hH : ∀ ω ∈ 𝒢, ∀ v v' : ℕ →₀ ℝ,
      |F (shiftBy ω v) - F (shiftBy ω v')| ≤ ∑ j ∈ v.support ∪ v'.support, L j * |v j - v' j|)
    {p : ℝ} (hp : 1 ≤ p) (hFp : MemLp F (ENNReal.ofReal p) stdP) :
    eLpNorm (fun ω => F ω - ∫ ω', F ω' ∂stdP) (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)) *
        (∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2) ∂stdP) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hH' : ShiftLipschitzOn F 𝒢 L := hH
  have hL : ∀ i, 0 ≤ L i := hH'.nonneg (nonempty_of_measure_compl_eq_zero h𝒢c)
  have hFi : Integrable F stdP := hFp.integrable (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp)
  set EF := ∫ ω', F ω' ∂stdP with hEF
  set C := ENNReal.ofReal (Real.pi / 2) ^ p * (∫⁻ t, ‖t‖ₑ ^ p ∂gaussianReal 0 1) *
    ∫⁻ ω, gradPow F p ω ∂stdP with hC
  -- the projections and their bounds
  have hcont : ∀ n, Continuous (projF F n) := fun n =>
    (lipschitzWith_projF hF hFi h𝒢 h𝒢c hH' hL n).continuous
  have hmeasn : ∀ n, Measurable fun ω => ‖projF F n (headN n ω) - EF‖ₑ ^ p := fun n =>
    ((((hcont n).measurable.comp (measurable_headN n)).sub_const EF).enorm).pow_const p
  have hbound : ∀ n, ∫⁻ ω, ‖projF F n (headN n ω) - EF‖ₑ ^ p ∂stdP ≤ C := by
    intro n
    rw [(measurePreserving_headN n).lintegral_comp
      ((((hcont n).measurable.sub_const EF).enorm).pow_const p)]
    exact lintegral_projF_sub_le hF hFi h𝒢 h𝒢c hH' hL n hp
  -- Lévy's upward theorem: `F_n(ω₀, …, ω_{n-1}) → F(ω)` a.s.
  have hlim : ∀ᵐ ω ∂stdP, Tendsto (fun n => projF F n (headN n ω)) atTop (𝓝 (F ω)) :=
    tendsto_ae_integral_joinN hF hFi fun n => (hcont n).measurable
  -- Fatou's lemma
  have hfatou : ∫⁻ ω, ‖F ω - EF‖ₑ ^ p ∂stdP ≤ C := by
    calc ∫⁻ ω, ‖F ω - EF‖ₑ ^ p ∂stdP
        = ∫⁻ ω, liminf (fun n => ‖projF F n (headN n ω) - EF‖ₑ ^ p) atTop ∂stdP := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with ω hω
          have ht : Tendsto (fun n => ‖projF F n (headN n ω) - EF‖ₑ ^ p) atTop
              (𝓝 (‖F ω - EF‖ₑ ^ p)) :=
            ((ENNReal.continuous_rpow_const.tendsto _).comp
              ((continuous_enorm.tendsto _).comp (hω.sub_const EF)))
          exact ht.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ‖projF F n (headN n ω) - EF‖ₑ ^ p ∂stdP) atTop :=
          lintegral_liminf_le' fun n => (hmeasn n).aemeasurable
      _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hbound)
  -- taking `p`-th roots
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  change _ ≤ ENNReal.ofReal (gaussLpConst p) * (∫⁻ ω, gradPow F p ω ∂stdP) ^ (1 / p)
  rw [ofReal_gaussLpConst hp0]
  exact rpow_inv_le_of_le hp0 hfatou

end GaussianLQG
