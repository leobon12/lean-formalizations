import QuantumZipper.Proofs.Thm18.G1FMAsm
import QuantumZipper.Proofs.Thm18.G1FMBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE (3): assembly — the node reduced to a 5-parameter variance node

`G1FMPushVarStmt` (stated here) is the 5-parameter analogue, for the pushed free field
`V(d, r, S) = X((S ψ)_* fc(d, r))`, of the variance node `D3Plus.N2ZFirstModeVarStmt`: in the
rescaled block coordinates `2^n (Re w, Im w, τ, s, S)` the real and imaginary parts of the first
mode agree a.s. with continuous centred Gaussian processes with variance `≤ c` and increment
variance `≤ c ‖q − q'‖` (`G1FM.FM5VarHyp`). Then

* `g1FMPush_of_var : G1FMPushVarStmt → G1FMPushStmt` (dyadic chaining + Borel–Cantelli,
  `G1FM.fm5_bound_of_var`, Hu–Miller–Peres, Ann. Probab. 38 (2010), proof of Prop. 2.1);
* `g1RestFirstMode_of_pushVar : G1FMPushVarStmt → G1RestFirstModeStmt`;
* `g1RegRepRestStmt_of_pushVar : G1FMPushVarStmt → G1RegRepRestStmt`.

What `G1FMPushVarStmt` needs (as in the proved FMVar chain for `ψ = id`, `S = 1`): stochastic
Fubini for the arc measures (`FMReprStmt`), admissibility, and the Neumann energies of the pushed
first-mode pairs `≤ c` and of their increments `≤ c (‖Δw‖ + |Δτ| + |Δs| + |ΔS|)/τ`; the pulled-back
kernel is `-log|z - z'|` plus a smooth function on compacts of `H` (`ψ` injective holomorphic).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Node G1-FM-PUSHVAR**: 5-parameter Gaussian variance bounds for the first mode of the pushed
free field (scale `S` as fifth parameter). -/
def G1FMPushVarStmt : Prop :=
  ∀ ψ : ℂ → ℂ, G1RC.PsiGood ψ →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ V : ℂ × ℝ × ℝ → Ω → ℝ, (∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0 ×ˢ Ioi 0)) →
      (∀ (d : ℂ) (r S : ℝ), 0 < r → r < d.im → 0 < S → (fun ω => V (d, r, S) ω) =ᵐ[P]
        fun ω => X ω ((foldedCircle d r).map fun z => (S : ℂ) * ψ z)) →
      G1FM.FM5VarHyp P fun ω S p => V (p.1, p.2, S) ω

/-- **G1-FM-PUSH from the variance node.** -/
theorem g1FMPush_of_var (h : G1FMPushVarStmt) : G1FMPushStmt :=
  fun ψ hψ _ _ P _ X hX V hVc hVm => G1FM.fm5_bound_of_var (h ψ hψ P X hX V hVc hVm)

/-- **G1-REST-FIRSTMODE from the variance node.** -/
theorem g1RestFirstMode_of_pushVar (h : G1FMPushVarStmt) : G1RestFirstModeStmt :=
  g1RestFirstMode_of_push (g1FMPush_of_var h)

end Thm18Asm
end QuantumZipper
