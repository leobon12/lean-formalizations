import QuantumZipper.Proofs.Thm18.G3Zc2Two
import QuantumZipper.Proofs.Thm18.G3ZcChain
import QuantumZipper.Proofs.Thm18.G3ZcTwoSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: G0 at two separated points for one free field

`twoPoint_free`: for admissible local maps `ψ₁`, `ψ₂` of G0 and `0 < γ < 2` there is `K > 0` such
that for every real `x₂` with `|x₂| > K` there is, on one probability space, a free field `W` and
radii such that the joint law of the normalized canonical zooms of `W` at `0` through `ψ₁` and at
`x₂` through `ψ₂` converges (per pair of test functionals) to the product of two `0`-quantum
wedge laws.

Proof: the joint coupling at the two points (`exists_twoCouplings`), the G0 chain at each point
(`g0Model_of'`, `g0Setup_of'`), and the separation clause of `G3TwoPointFixedStmt`: the dyadic data
of the second zoom are, a.s., increments of `W` between measures carried by
`x₂ + Ψ₂(closedBall 0 ρ₂)`, which lies outside `{‖y‖ ≤ M₁ρ₁} ⊇ Ψ₁(closedBall 0 ρ₁)` once
`|x₂| > M₁ρ₁ + M₂ρ₂` (bi-Lipschitz bounds), hence a.s. coordinates of `Ξ₁` (`FarPair`, the domain
Markov property). Sheffield, arXiv:1012.4797, p. 71 (independent zooms at two points). Own
assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm D3Plus

/-- Two maps agreeing near `0` give the same `coordChange` at circles carried near `0`. -/
theorem coordChange_swap {ψ Ψ : ℂ → ℂ} {R₀ R : ℝ} (heq : EqOn Ψ ψ (ball (0 : ℂ) R₀))
    (hRR : R < R₀) {d : ℂ} {t : ℝ} (hdt : foldedCircle d t (closedBall (0 : ℂ) R ∩ Hbar)ᶜ = 0)
    (x : FieldSample) (Q : ℝ) :
    coordChange x ψ Q (foldedCircle d t) = coordChange x Ψ Q (foldedCircle d t) := by
  have hsub : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) R₀ := closedBall_subset_ball hRR
  have hae : ∀ᵐ z ∂foldedCircle d t, z ∈ ball (0 : ℂ) R₀ :=
    (ae_mem_of_compl_null_g3cv hdt).mono fun z hz => hsub hz.1
  have hmap : (foldedCircle d t).map ψ = (foldedCircle d t).map Ψ :=
    Measure.map_congr (hae.mono fun z hz => (heq hz).symm)
  have hder : (fun z => Real.log ‖deriv ψ z‖) =ᵐ[foldedCircle d t]
      fun z => Real.log ‖deriv Ψ z‖ := hae.mono fun z hz => by
    show Real.log ‖deriv ψ z‖ = Real.log ‖deriv Ψ z‖
    rw [(Filter.EventuallyEq.deriv_eq (eventually_of_mem (isOpen_ball.mem_nhds hz) heq))]
  simp only [coordChange, hmap, integral_congr_ae hder]

/-- A bi-Lipschitz map fixing `0` maps `closedBall 0 ρ` into `closedBall 0 (Mρ)`. -/
theorem norm_le_of_pullData {Ψ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ} (hD : PullData Ψ 0 r₀ ρ r₁ m M)
    (h0 : Ψ 0 = 0) {w : ℂ} (hw : w ∈ closedBall ((0 : ℝ) : ℂ) ρ) : ‖Ψ w‖ ≤ M * ρ := by
  have h0m : (0 : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := by simpa using hD.hρ.le
  have := (hD.bl.2.2 w hw 0 h0m).2
  rw [h0, sub_zero, sub_zero] at this
  have hw' : ‖w‖ ≤ ρ := by simpa using hw
  exact this.trans (mul_le_mul_of_nonneg_left hw' hD.bl.2.1.le)

end G3Cv
end QuantumZipper
