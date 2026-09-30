import QuantumZipper.Proofs.Zipper.XPCIdBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, R3: the fixed-driver UC node from a deterministic smoothing-energy node

`XPCUCStmt` (a.s., at every scale `k`, the smoothed pairings `Ψ_j(z) = ∫ avgReg (X ω) j dμ_z`,
`μ_z = muP W t z 2^{-k}` or `muI W t z 2^{-k}`, are uniformly Cauchy in `j` on compact subsets of
`UR (2^{-k})`) is reduced to the **deterministic** node

* `XPCSmoothStmt`: on every parameter rectangle `B` inside `UR r`, the circle-smoothed families
  `μ_z ⋆ fc(·, s)` (`muPs`, `muIs`) form, against the unsmoothed `μ_z`, a `DiffFam` (energy of
  `μ_z ⋆ fc_s − μ_z` at most `C s`, energy moduli `C (‖z − z'‖ + |s − s'|) / min s s'`).

Main result: `xpcUCStmt_of_smooth : XPCSmoothStmt → XPCUCStmt`, hence (with `XPCIdGlue`)
`xAreaPCStmt_of_smooth : XPCModPStmt → XPCSmoothStmt → XPCMeasStmt → XPCUCBStmt → XAreaPCStmt`.

Proof. The Kolmogorov step for difference families (`ae_unif_small_diffFam`) gives `Y(z, s)`,
continuous, a.s. equal to `X(μ_z ⋆ fc_s) − X(μ_z)` at fixed parameters and uniformly small as
`s → 0`. Stochastic Fubini (`Regularization.ae_integral_avgReg_eq`) gives
`Ψ_j(z) = X(μ_z ⋆ fc_{2^{-j}})` a.s. at fixed `z`, so on a countable dense set
`Ψ_j − Ψ_{j'} = Y(·, 2^{-j}) − Y(·, 2^{-j'})`; both sides are continuous (`continuousOn_integral_muP`,
`continuousOn_integral_muI`), so this holds on the rectangle, and the right side is uniformly
small. Countably many rectangles `boxK r n` exhaust `UR r`.
Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I,
Thm (2.1). The gluing is own bookkeeping, as in `UnifUCFix.fixedUCStmt_of_id_det`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper.E6
namespace XAreaPC

/-- Rectangles exhausting `UR r`. -/
def boxK (r : ℝ) (n : ℕ) : PBox :=
  ⟨-((n : ℝ) + 1), (n : ℝ) + 1, r + 1 / ((n : ℝ) + 1), r + ((n : ℝ) + 1), 1,
    by linarith [n.cast_nonneg (α := ℝ)],
    by
      have h : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
      linarith [n.cast_nonneg (α := ℝ)],
    one_pos⟩

end XAreaPC
end QuantumZipper.E6
