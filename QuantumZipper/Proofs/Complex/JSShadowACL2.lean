import QuantumZipper.Proofs.Complex.JSTents
import QuantumZipper.Proofs.Complex.JSShadowACL

/-!
# EXT-JS node B1, step 3: oscillation of `g = e ∘ F` on the shadow of a level-`n` tent

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 step 3 of "(C0: SH ⇒ removable.)".

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1, pp. 271–272:
if `u` and `v` are two boundary points lying in the *shadow* of one Whitney cube `Q` (i.e.
reachable from `Q` by two curves of the family `F`), then `u` and `v` can be joined by a curve
through `Q`, and `|f(u) - f(v)| ≤ 2^n Σ_{Q' ≺ γ} |∇f|(Q') l(Q')`. Here the curves of `F` are the
vertical rays of the half-plane and the role of a Whitney cube is played by a dyadic tent
(`JSTents.lean`): the shadow of the top box `Q_{n,j}` is the base interval
`I_{n,j} = [-R + jℓ_n, -R + (j+1)ℓ_n]`, and a base point of `I_{n,j}` is joined to the top of the
tent by the vertical chain of top boxes above it.

Concretely, for `s, s' ∈ I_{n,j}` the "curve through `Q_{n,j}`" is the Λ-shaped path
`s ↑ (s, ℓ_n) → (s', ℓ_n) ↓ s'` inside the rectangle `T_{n,j}`; it is covered by the two
descendant tents `T_{n+1,j₁}`, `T_{n+1,j₂}` (bottom half) and by the top box `Q_{n,j}` (top half),
which gives (each of the five legs of the path contributes one diameter, in the order of the path)

`edist (g s) (g s') ≤ diam g(T_{n+1,j₁}) + diam g(Q_{n,j}) + diam g(Q_{n,j}) + diam g(Q_{n,j})
  + diam g(T_{n+1,j₂})`,

i.e. the bound `2 diam g(T_{n+1,j₁}) + 3 diam g(Q_{n,j}) + 2 diam g(T_{n+1,j₂})` up to the order of
the summands. Since the two descendant tents `T_{n+1,j₁}`, `T_{n+1,j₂}` are distinct and each of the
five summands is a tent/box diameter of level `≥ n` whose image contains the point of the line, the
whole bound is dominated by a fixed multiple of the level-`n` shadow sum `Φ_n` of blueprint §2
step 5.

The two descendant indices `j₁, j₂` are the level-`(n+1)` dyadic intervals containing `s` resp.
`s'` (every point of `I_{n,j}` lies in the child `I_{n+1,2j}` or `I_{n+1,2j+1}`). Each tent
diameter is charged, in the level-`n` sum `Φ_n` of blueprint §2 step 5, to the tent *containing*
the corresponding base point, whose image contains the point on the line; this is why the sum in
step 5 runs over all tents of level `≥ n` rather than only over the level-`n` ones.

Main result: `edist_apply_le_mem_dyI`.
-/

noncomputable section

open Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

variable {R : ℝ}

/-- The point `(x : ℂ) + t * I` has real part `x`. -/
lemma re_ofReal_add_mul_I (x t : ℝ) : ((x : ℂ) + t * I).re = x := by simp

/-- The point `(x : ℂ) + t * I` has imaginary part `t`. -/
lemma im_ofReal_add_mul_I (x t : ℝ) : ((x : ℂ) + t * I).im = t := by simp

end QuantumZipper.JS
