import QuantumZipper.Proofs.Zipper.FibreGaussMaxSetup
import QuantumZipper.Proofs.Zipper.FibreGaussMaxLaw
import QuantumZipper.Proofs.Zipper.FibreGaussMaxChain
import LQGDimension.Gaussian.Concentration

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FIBRE-GAUSSMAX (3): the finite Gaussian maxima, `FibreGaussMaxStmt κ p` for `p > 0`

For a finite set `F` of tip parameters, add the reference parameter `(0,0)` (whose circle is
`fc(0,1)`, so its coordinate vanishes) and the intermediate parameters `(h.1, g.2)`. The tip
coordinates `X(ν i) - X(fc(0,1))` form a finite centred Gaussian vector, realised as `⟪v i, x⟫`
under a standard Gaussian (`fgmLaw_gram`). Then

* increments: `‖v g - v h‖² ≤ 4 A ‖P g - P h‖^{1/36}` with `A = fgmA κ C` (`fgm_hv`);
* expected maximum (Dudley chaining, Hölder form, `fgmChain_bound`; Adler–Taylor, *Random Fields
  and Geometry*, Thm 1.3.3; Talagrand, *Upper and Lower Bounds for Stochastic Processes*, §2.2):
  `E max ≤ K_ch · 2√A · 2^{1/72}`;
* concentration (Maurey–Pisier form of Borell–TIS, `MaxConc.lintegral_exp_max_le`;
  Pisier 1986, *Probabilistic methods in the geometry of Banach spaces*, Thm 2.2; Adler–Taylor
  Thm 2.1.1): `E e^{t(M - EM)} ≤ e^{π² t² σ²/8}` with `σ² ≤ 4A`;

so `E[(max e^{√κ X(ν i)})^p] ≤ exp(fgmE κ p · (1 + A))` (`fgm_core`), and `A ≤ fgmD κ (1 + C)`
(`fgmA_le`) gives the `K_ε e^{ε C²}` bound for every `ε > 0` (in fact `e^{O(C)}`).
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal RealInnerProductSpace Real

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont KolmD RegSample LQGDimension

/-- Exponential moment of a finite Gaussian maximum from a bound on its expectation. -/
theorem fgm_gauss_exp_le {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (v : ι → E)
    {t σ B : ℝ} (ht : 0 ≤ t) (hσ : ∀ i ∈ F, ‖v i‖ ≤ σ) (hB : vecExpectedMax F v 0 ≤ B) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * ⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i)) ∂stdGaussian E ≤
      ENNReal.ofReal (Real.exp (t * B + π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  have h := MaxConc.lintegral_exp_max_le F v 0 hσ t
  set EM := vecExpectedMax F v 0
  have e : ∀ x : E, ENNReal.ofReal (Real.exp (t * ⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i)) =
      ENNReal.ofReal (Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i) - EM))) *
        ENNReal.ofReal (Real.exp (t * EM)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) *
        ENNReal.ofReal (Real.exp (t * EM)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (t * EM + π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_comm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))

end RegUnif
end QuantumZipper
