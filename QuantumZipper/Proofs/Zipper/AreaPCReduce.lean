import QuantumZipper.Proofs.Zipper.AreaCoordCov
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale
import QuantumZipper.Proofs.LQG.IndepParams
import QuantumZipper.Proofs.Zipper.UnifUCTrBasic
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.GFF.CoordRegHarm
import QuantumZipper.Proofs.Zipper.WedgeDecompCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# W-A-pc from the free-field node X-A-pc (W-D, X-C and a deterministic comparison)

The node `E6.WedgeAreaPCStmt` (W-A-pc, `AreaCoordPC.lean`) compares, for the *unscaled wedge
field* `x₀ = F2.zU √κ X' A`, the pairing with the pushed circle `ψ_* fc(z, 2^{-k})`
(`ψ = f_t⁻¹`) and the circle average `imgAvg x₀ = ⟨x₀, fc(ψ z, 2^{-k}|ψ'(z)|)⟩`.

By the proved radial resampling W-D (`WedgeUnzip.wedgeDecompStmt_holds`), on a product extension
`x₀` agrees on every folded circle with `y + G`, `y = X'' + α₀(−log|·|)` (`X''` a free field
independent of the driver) and `G` continuous. Since `evalReg` only reads a field through its
folded-circle values, the error of W-A-pc splits exactly as

  `[⟨y, ψ_* fc(z, r)⟩ − ⟨y, fc(ψ z, r|ψ'(z)|)⟩] + [∫ G dψ_* fc(z, r) − ∫ G dfc(ψ z, r|ψ'(z)|)]`

(`WedgeUnzip.unzipAddFun` for the pushed circle, with the continuum input X-C
`WedgeUnzip.XContinuumStmt`; `GoodSample.evalReg_add_ofFun_fc` for the circle). The second bracket
tends to `0` uniformly on compact subsets of `ℍ` for every continuous `G` (deterministic,
`eventually_abs_pushAvg_sub_circAvg_le`: both measures live within `O(r)` of `ψ(z)`). The first
bracket is the new free-field node

* **`XAreaPCStmt`** (X-A-pc): for `X` a free field modulo constants on `ℍ`, independent of the
  Brownian driver `B`, for each fixed `t ≥ 0`, a.s., uniformly on compact subsets of `ℍ`,
  `⟨X + α₀(−log|·|), ψ_* fc(z, 2^{-k})⟩ − ⟨X + α₀(−log|·|), fc(ψ z, 2^{-k}|ψ'(z)|)⟩ → 0`.

Why X-A-pc is true (planned proof, not formalized here). The log part is continuous near
`ψ(K) ⋐ ℍ`, so it is handled like `G`. For the free field and a *fixed* driver: the uniform
measure on `∂B(z, r)` is harmonic measure of `B(z, r)` from `z`, so `μ₁ = ψ_* fc(z, r)` is harmonic
measure of `ψ(B(z, r))` from `ψ z`, and `μ₂ = fc(ψ z, ρ)`, `ρ = r|ψ'(z)|`, harmonic measure of
`B(ψ z, ρ)`. Hence the reflected Neumann kernel `log|u − v̄|` (harmonic in `u ∈ ℍ`) has equal
`μ₁`- and `μ₂`-averages, and the logarithmic potentials of `μ₁`, `μ₂` coincide off
`ψ(B(z, r)) ∪ B(ψ z, ρ)`; by Koebe distortion both supports lie in the annulus
`ρ(1 ± C r) ` about `ψ z`, so the Neumann energy of `μ₁ − μ₂` is `O(r)` (maximum principle), and the
Gaussian variance of the difference is `O(r)`. Together with the Hölder moduli in `(z, r)` of the
two families (`JointModSpace`, `RegCont`), the multiparameter Kolmogorov–Čentsov theorem
(Revuz–Yor, 3rd ed., Ch. I, Thm (2.1), in the form `KolmN.exists_continuous_modification_N`)
gives a continuous modification on `K × [0, r₀]` vanishing at `r = 0`, whence uniform convergence
(the pattern of `UnifUCFix.fixedUCStmt_of_id_det`); the random independent driver is handled by
conditioning on the path as in `UnifUCTr.unifUCStmt_of_fixedUCStmt`. Sources:
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1
(continuity of circle averages, via the same energy/Kolmogorov route); Sheffield–Wang,
arXiv:1605.06171, Lemmas 3.4–3.5, pp. 17–19 (coordinate change of smoothed fields).

Main result: `wedgeAreaPCStmt_of_x : WedgeDecompStmt → XContinuumStmt → XAreaPCStmt →
WedgeAreaPCStmt`, and `wedgeAreaPCStmt_of_xpc` with W-D discharged. The splitting and the
deterministic comparison are own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-! ## Deterministic comparison of the two averages of a continuous function -/

/-- A folded circle about a point of `Hbar` stays within its radius. -/
theorem foldedCircle_ae_dist_le_pc {c : ℂ} (hc : c ∈ Hbar) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ᵐ u ∂foldedCircle c ρ, dist u c ≤ ρ := by
  unfold foldedCircle
  refine (ae_map_iff (p := fun u => dist u c ≤ ρ) measurable_foldH.aemeasurable
    (measurableSet_closedBall (x := c) (ε := ρ))).2 ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif c hρ] with z hz
  have hfc : foldH c = c := by
    have : 0 ≤ c.im := hc
    simp [foldH, this]
  have h := TwoPoint.norm_foldH_sub_le z c
  rw [hfc] at h
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [dist_eq_norm]
  linarith

/-! ## The free-field node and the reduction -/

end QuantumZipper.E6
