import QuantumZipper.Proofs.Zipper.XFlowUCFix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-ENERGY: the three moduli of `FlowEnergyStmt` and their assembly

`FlowEnergyStmt` (`XFlowUCFix.lean`) asks for a Hölder bound, uniform on `flowBox m × [0,1]`,
for the energy of `μ_{p,ρ} − μ_{p',ρ'}`. By the triangle inequality for the Neumann energy
(`RegUnif.kernelCov2_self_triangle`) through `μ_{p,ρ'}` and `μ_{(u',s',d,r),ρ'}` it follows from

* `FlowE1Stmt`: the radius modulus (D33 E1, `RegUnif.energyRadStmt_holds`) with constants uniform
  over the circles of the box;
* `FlowE2Stmt`: the time modulus (D33 E2, `RegUnif.energyParStmt_holds`) likewise;
* `FlowE3Stmt`: the circle modulus in `(d, r)` at fixed `(u, s, ρ)`;

and the admissibility node `FlowAdmStmt` (needed for the triangle inequality). The assembly
`flowEnergyStmt_of` is own elementary bookkeeping (as `RegUnif.energyUS_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif

/-- **Radius modulus, uniform over the box.** -/
def FlowE1Stmt : Prop :=
  ∀ m : ℕ, ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ p ∈ flowBox m, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W p ρ, flowMu W p ρ') (flowMu W p ρ, flowMu W p ρ')| ≤
        C * |ρ - ρ'| ^ a

/-- **Time modulus, uniform over the box** (same circle `(d, r)`). -/
def FlowE2Stmt : Prop :=
  ∀ m : ℕ, ∀ W : ℝ → ℝ, ∀ a CH : ℝ, HolderDrv W (2 * (m : ℝ) + 2) a CH →
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ ∀ p ∈ flowBox m, ∀ p' ∈ flowBox m, p.2.2 = p'.2.2 →
      ∀ ρ ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ) (flowMu W p ρ, flowMu W p' ρ)| ≤
        C * dist p p' ^ b

/-- **Circle modulus, uniform over the box** (same times `(u, s)`). -/
def FlowE3Stmt : Prop :=
  ∀ m : ℕ, ∀ W : ℝ → ℝ, ∀ a CH : ℝ, HolderDrv W (2 * (m : ℝ) + 2) a CH →
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ ∀ p ∈ flowBox m, ∀ p' ∈ flowBox m, p.1 = p'.1 →
      p.2.1 = p'.2.1 → ∀ ρ ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ) (flowMu W p ρ, flowMu W p' ρ)| ≤
        C * dist p p' ^ b

end F1
end QuantumZipper
