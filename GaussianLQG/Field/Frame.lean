import GaussianLQG.Field.Frame.Kappa
import GaussianLQG.Field.Frame.Nice

/-!
# The white-noise GFF frame (blueprint Appendix B, `prop:frame-exists`)

For a Hilbert basis `(b_j)` of the white-noise space `L²(ℝ × ℂ)` consisting of nice vectors, the
normalized frame functions `e_j = frameFunN (b_j)` form a GFF frame (`isGFFFrame_of_nice`):
each `e_j` is continuous and bounded (`Field/FrameFun`), and for regular `μ, ν`

`∑_j (∫ e_j dμ)(∫ e_j dν) = ∑_j ⟪κ_μ, b_j⟫⟪b_j, κ_ν⟫ = ⟪κ_μ, κ_ν⟫ = energy μ ν`

by `integral_frameFunN_eq_inner` (Fubini), Parseval (`HilbertBasis.hasSum_inner_mul_inner`) and
`inner_kappaL2` (heat kernels, Chapman–Kolmogorov, Frullani). A nice Hilbert basis exists
(`exists_nice_hilbertBasis`, Gram–Schmidt), so a GFF frame exists (`exists_isGFFFrame`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace GaussianLQG

open WNFrame

/-- **The white-noise frame.** If `b` is a Hilbert basis of `L²(ℝ × ℂ)` made of nice vectors,
then `j ↦ frameFunN (b j)` is a GFF frame. -/
theorem isGFFFrame_of_nice (b : HilbertBasis ℕ ℝ WNSpace) (hb : ∀ j, IsNiceWN (b j)) :
    IsGFFFrame (fun j => frameFunN (b j)) := by
  refine ⟨fun j => continuous_frameFunN (hb j), fun j => exists_bound_frameFunN (hb j), ?_⟩
  intro μ ν hμ hν
  have h := b.hasSum_inner_mul_inner (kappaL2 μ hμ) (kappaL2 ν hν)
  rw [inner_kappaL2 hμ hν] at h
  have e : (fun j => (∫ z, frameFunN (b j) z ∂μ) * ∫ z, frameFunN (b j) z ∂ν) =
      fun j => ⟪kappaL2 μ hμ, b j⟫ * ⟪b j, kappaL2 ν hν⟫ := by
    funext j
    rw [integral_frameFunN_eq_inner (hb j) hμ, integral_frameFunN_eq_inner (hb j) hν,
      real_inner_comm (kappaL2 ν hν) (b j)]
  show HasSum (fun j => (∫ z, frameFunN (b j) z ∂μ) * ∫ z, frameFunN (b j) z ∂ν) (energy μ ν)
  rw [e]
  exact h

/-- **Existence of a GFF frame** (blueprint `prop:frame-exists` with a nice basis). -/
theorem exists_isGFFFrame : ∃ e : ℕ → ℂ → ℝ, IsGFFFrame e := by
  obtain ⟨b, hb⟩ := exists_nice_hilbertBasis
  exact ⟨_, isGFFFrame_of_nice b hb⟩

end GaussianLQG
