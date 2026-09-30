import QuantumZipper.Proofs.Thm11.LyapunovAlgebra
import QuantumZipper.Proofs.Thm11.NonSwallowingLyap

/-!
# THM11-AD3: the FD-8 function `g` and the quadratic variation of `𝔥`

The blueprint `THM11_BLUEPRINT.md` §9 AD-2/AD-3 routes the addendum through the estimate
`E[C_0 − C_{τ−}] ≤ 2‖g‖` (`C` the quadratic variation of `𝔥`, `g` the FD-8 function of
`LyapunovAlgebra.lean`). This file proves the differential identity behind it: dividing the
ODE `gFun_ode` of FD-8 by `sin²θ` gives

`(κ/2) g''(θ) + (κ−4) cot θ · g'(θ) = −4`,

i.e. the generator `L` of the forward centered flow applied to the *bounded* function
`θ ↦ g(θ)` equals `−4 (sin θ)²/r²`, the negative of the quadratic-variation density
`4 (Im z)²/‖z‖⁴` of `𝔥`. (The density itself is the generator of the unbounded `Φ²`; see
`dynkinGen_fzPhi_sq` in `AddendumEnergy.lean`.) Consequently
`−g(arg Z̃_t) − ∫₀ᵗ 4 (Im Z̃_s)²/‖Z̃_s‖⁴ ds` is the driftless (local) martingale associated with
the quadratic variation of `𝔥`, and it is *bounded* whenever `g` is.

**Not yet formalized here** (chain-rule bookkeeping on the product state, see the report):
the `dynkinGen (fzDrift c) (fzNoise κ)` version of `genL_neg_gFun_arg` for
`fun y : ℂ × ℝ => -gFun κ (Complex.arg y.1)`, which is the form the martingale machinery
(`FrozenMart.martingale_localDynkin_stopped`) consumes. The boundedness of `g` for `κ < 8`
(the κ > 4 part of FD-8) is also not yet formalized: `LyapunovAlgebra.abs_gFun_le` covers
`κ ≤ 4`.

Source: own elementary computation from `gFun_ode` (FD-8, `LyapunovAlgebra.lean`); no departure
from the blueprint.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped Topology ENNReal NNReal

namespace QuantumZipper

open Thm11Lyap

/-- **FD-8 in the form used by AD-2/AD-3.** With `θ = arg z ∈ (0,π)`,
`(κ/2) g''(θ) + (κ−4) cot θ · g'(θ) = −4`: the divided form of `gFun_ode`, i.e. the statement
that the generator of `θ ↦ g(θ)` is `−4 (sin θ)²/‖z‖²`, the negative of the quadratic-variation
density of `𝔥`. -/
theorem gPrime_ode_div {κ : ℝ} (hκ : κ ≠ 0) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    κ / 2 * deriv (gPrime κ) θ + (κ - 4) * (cos θ / sin θ) * gPrime κ θ = -4 := by
  have hs := Thm11Lyap.sin_pos_of_mem_Ioo h
  have hode := gFun_ode hκ h
  have hs2 : sin θ ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
  field_simp at hode ⊢
  linarith [hode]

end QuantumZipper
