import QuantumZipper.Proofs.Thm18.LWFarDefs2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LW-FAR, re-plan (D57): the nodes of Lawler–Werness §4 as published

Task LW-FAR re-plan (plan `handoff/LW-FAR.md` §5). The pocket simplification of §1–§4 of the plan
(`FjordDeepStmt`, `FjordStmt`, `PocketProdStmt`, `DeepPocketCoverStmt'`) is withdrawn: at general
stopping times the future curve may have to traverse a pocket (the horseshoe of the LWF-6′
prover), so these statements are false. The remaining route is G. Lawler, B. Werness,
*Multi-point Green's functions for SLE and an estimate of Beffara*, Ann. Probab. 41 (2013)
1513–1555, §4 and Appendix A as published (`literature/1011.3551.pdf`), specialized to `θ = 1`,
`δ = ε`, `0 < κ < 4` (simple curves). Every statement below cites the lemma it formalizes.

Notation (LW §2.1 p. 6, §4.2 p. 25): for `x ∈ H_t = H \ K_t`,
* `inradT W t x = Δ_t(x) = inrad_{H_t}(x)`;
* `sideDist W t x false/true = Δ_{H_t,1}(x; γ(t), ∞)`, `Δ_{H_t,2}(…)`: the infimum of the `s`
  such that a curve from `x` inside `B(x, s) ∩ H_t` ends on `∂₁H_t = Z_t⁻¹(−∞, 0)`
  (resp. `∂₂H_t = Z_t⁻¹(0, ∞)`), where `Z_t = fwdMap W t` (D49); prime ends are encoded by the
  limit of `Z_t` along the curve;
* `farDist = Δ*_t(x) = max(Δ_{t,1}, Δ_{t,2})`;
* `IsSepFamily W L z w I`: the four properties of LW's `I_t` (p. 26, Appendix A p. 37) for the
  line `𝓘 = L`; `sepFam` is the family when it is unique (LW Appendix A);
* `renewal W I z w k = τ_k` (LW p. 28), `hatTime` = `τ̂_k`.

Standing setting (LW p. 23, (15)): `LWSetting L z w`: `Im z, Im w ≥ 1`, `L` a straight line with
`dist(z, L), dist(w, L) ≥ 1`, meeting `ℝ`, and `z`, `w` in different components of `H \ L`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The deterministic setting in which the LW §4 lemmas hold: a continuous driver with `W 0 = 0`
whose trace is a simple chord generating the hulls (a.s. the case for SLE_κ, `κ ≤ 4`). -/
structure GoodChord (W : ℝ → ℝ) : Prop where
  cont : Continuous W
  zero : W 0 = 0
  simple : IsSimpleChord (trace W)
  hull : ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t

end LWFar
end Thm18Asm
end QuantumZipper
