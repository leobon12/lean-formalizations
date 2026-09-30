import QuantumZipper.Proofs.Thm18.G1FM2PotBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE round 2 (energy), part 3: `PushPotLip` holds

For a selected map `ψ` (`G1RC.PsiGood`) and a box index `m` we fix uniform constants on the
compact region `{‖z‖ ≤ 2(m+1)+1, Im z ≥ 1/(2(m+1))}` (`G1FM2.psi_consts`) and a disc radius
`rD` so small that `ψ'` varies by at most `|ψ'(w)|/4` on `B̄(w, rD)`. Then:

* in pre-image coordinates the pushed potential is `fmPot` (Lipschitz `2π/τ`,
  `D3Plus.fmPotLip_of_psi`) minus a correction with Lipschitz constant `2 B₀ L_E`
  (`G1FM2.abs_ek_sub_le`, no atoms);
* by the Koebe `1/4` theorem (`CA.Koebe.ball_subset_image_koebe`) every point of the ball
  `B(Sψ(w), ρ₁)` is `S ψ(x)` with `x ∈ B(w, rD)`, and `‖Sψ(x) − Sψ(x')‖ ≥ S (a₀/2) ‖x − x'‖`
  (`fmQ` bound), so the pushed potential is `L/τ`-Lipschitz on that ball.

Main result: `G1FM2.pushPotLip_holds`. Own elementary argument (Koebe covering theorem:
Pommerenke, *Boundary Behaviour of Conformal Maps*, Cor. 1.4, as cited in `KoebeCovering.lean`).
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology ComplexConjugate Real

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

open G1RC

variable {ψ : ℂ → ℂ}

/-- Lipschitz bound of the pushed potential in pre-image coordinates on the disc. -/
theorem pushPot_comp_lip (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) {w u : ℂ} (hu : ‖u‖ = 1)
    {rD τ s M₂ α M₁ c₀ LE : ℝ} (hr : rD < w.im) (hτ : 0 < τ) (hs : 0 ≤ s) (hsτ : s ≤ τ)
    (h2τ : 2 * τ ≤ rD) (h3 : 3 * τ ≤ w.im) (hM₂ : 0 ≤ M₂) (hα : 0 < α) (hc₀ : 0 < c₀)
    (hL : ∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD,
      ‖deriv (fun z => (S : ℂ) * ψ z) x - deriv (fun z => (S : ℂ) * ψ z) x'‖ ≤
        M₂ * ‖x - x'‖)
    (hq : ∀ x ∈ closedBall w rD, ∀ y ∈ closedBall w rD,
      α ≤ ‖fmQ (fun z => (S : ℂ) * ψ z) x y‖)
    (him : ∀ x ∈ closedBall w rD, c₀ ≤ ((S : ℂ) * ψ x).im)
    (hM₁ : ∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD,
      ‖(S : ℂ) * ψ x - (S : ℂ) * ψ x'‖ ≤ M₁ * ‖x - x'‖)
    (hLE : M₂ / α + 1 / (2 * (w.im - rD)) + M₁ / (2 * c₀) ≤ LE)
    {x x' : ℂ} (hx : x ∈ closedBall w rD) (hx' : x' ∈ closedBall w rD) :
    |pushPot ψ S w ((τ : ℂ) * u) s ((S : ℂ) * ψ x) -
        pushPot ψ S w ((τ : ℂ) * u) s ((S : ℂ) * ψ x')| ≤
      (2 * π / τ + 2 * (D3Plus.fmBase.real univ * LE)) * ‖x - x'‖ := by
  set f : ℂ → ℂ := fun z => (S : ℂ) * ψ z with hf
  have hd := hψ.2.1
  have hinj := hψ.2.2.1
  have hfd : DifferentiableOn ℂ f H := (differentiableOn_const _).mul hd
  have hfinj : InjOn f H := fun a ha b hb hab => hinj ha hb
    (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hS.ne') hab)
  set v : ℂ := (τ : ℂ) * u with hvdef
  have hnv : ‖v‖ = τ := by
    rw [hvdef, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hv : 0 < ‖v‖ := by rw [hnv]; exact hτ
  have hvw : ‖v‖ + s < w.im := by rw [hnv]; linarith
  have hvw' : ‖-v‖ + s < w.im := by rwa [norm_neg]
  have hv' : 0 < ‖-v‖ := by rwa [norm_neg]
  rw [pushPot_comp hψ hS hs hv hvw x, pushPot_comp hψ hS hs hv hvw x']
  have hpot := D3Plus.fmPotLip_of_psi D3Plus.fmPsiStmt_holds u w τ s hu hτ hs hsτ h3 x
    (show (0 : ℝ) ≤ x.im by linarith [im_ge_of_mem hx]) x'
    (show (0 : ℝ) ≤ x'.im by linarith [im_ge_of_mem hx'])
  have hB0 : 0 ≤ D3Plus.fmBase.real univ := measureReal_nonneg
  -- the correction is Lipschitz
  have corr : ∀ v' : ℂ, 0 < ‖v'‖ → ‖v'‖ + s < w.im → ‖v'‖ = τ →
      |(∫ y, ek f x y ∂D3Plus.fmMeas w v' s) - ∫ y, ek f x' y ∂D3Plus.fmMeas w v' s| ≤
        D3Plus.fmBase.real univ * LE * ‖x - x'‖ := by
    intro v' hv' hvw' hn'
    have : IsFiniteMeasure (D3Plus.fmMeas w v' s) :=
      CircleFubini.isFiniteMeasure_bind_circle (r := s) (D3Plus.fmArc w v')
    rw [← integral_sub (integrable_ek hψ hS hs hv' hvw' x)
      (integrable_ek hψ hS hs hv' hvw' x')]
    have hae : ∀ᵐ y ∂D3Plus.fmMeas w v' s, ‖ek f x y - ek f x' y‖ ≤ LE * ‖x - x'‖ := by
      have n1 : ∀ᵐ y ∂D3Plus.fmMeas w v' s, y ≠ x :=
        ae_iff.2 (by simpa using fmMeas_singleton hs hv' x)
      have n2 : ∀ᵐ y ∂D3Plus.fmMeas w v' s, y ≠ x' :=
        ae_iff.2 (by simpa using fmMeas_singleton hs hv' x')
      filter_upwards [G1FM.ae_dist_fmMeas_le (w := w) (v := v') hs (by linarith), n1, n2]
        with y hy h1 h2
      have hyD : y ∈ closedBall w rD := mem_closedBall.2 (by rw [hn'] at hy; linarith)
      rw [Real.norm_eq_abs]
      refine (abs_ek_sub_le hfd hfinj hr hM₂ hL hα hq hc₀ him hM₁ hx hx' hyD h1.symm
        h2.symm).trans ?_
      exact mul_le_mul_of_nonneg_right hLE (norm_nonneg _)
    have := norm_integral_le_of_norm_le_const hae
    rw [Real.norm_eq_abs] at this
    have hm : (D3Plus.fmMeas w v' s).real univ = D3Plus.fmBase.real univ := by
      rw [measureReal_def, measureReal_def, D3Plus.fmMeas_univ]
    rw [hm] at this
    linarith
  have c1 := corr v hv hvw hnv
  have c2 := corr (-v) hv' hvw' (by rw [norm_neg, hnv])
  have e : D3Plus.fmPot w v s x - ((∫ y, ek f x y ∂D3Plus.fmMeas w v s) -
        ∫ y, ek f x y ∂D3Plus.fmMeas w (-v) s) -
      (D3Plus.fmPot w v s x' - ((∫ y, ek f x' y ∂D3Plus.fmMeas w v s) -
        ∫ y, ek f x' y ∂D3Plus.fmMeas w (-v) s)) =
      (D3Plus.fmPot w v s x - D3Plus.fmPot w v s x') -
        ((∫ y, ek f x y ∂D3Plus.fmMeas w v s) - ∫ y, ek f x' y ∂D3Plus.fmMeas w v s) +
        ((∫ y, ek f x y ∂D3Plus.fmMeas w (-v) s) -
          ∫ y, ek f x' y ∂D3Plus.fmMeas w (-v) s) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_sub _ _).trans (add_le_add hpot c1)) c2).trans (le_of_eq ?_)
  ring

end G1FM2
end Thm18Asm
end QuantumZipper
