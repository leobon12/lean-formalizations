import QuantumZipper.Proofs.Thm18.G1FMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE round 2 (energy): the pushed first-mode potential (interface)

`pushPot ψ S w v s` is the Neumann potential of the pushed first-mode pair
`(pfmMeas ψ S w v s, pfmMeas ψ S w (−v) s)`. `PushPotLip ψ` collects, uniformly on the
parameter boxes of `G1FMEnergyStmt`, the local bounds of `ψ` on a disc `B̄(w, rD)` and the
Lipschitz bound `L/τ` of the pushed potential on a ball of fixed radius `ρ₁ S` around `S ψ(w)`
(proved in `G1FM2Pot.lean`; used in `G1FM2Energy.lean`). Interface between the two halves of
task G1FM2 (own bookkeeping).
-/

noncomputable section

open MeasureTheory Metric Set

namespace QuantumZipper
namespace Thm18Asm

/-- Neumann potential of the pushed first-mode pair. -/
def pushPot (ψ : ℂ → ℂ) (S : ℝ) (w v : ℂ) (s : ℝ) (p : ℂ) : ℝ :=
  (∫ y, neumannH p y ∂pfmMeas ψ S w v s) - ∫ y, neumannH p y ∂pfmMeas ψ S w (-v) s

/-- Uniform local bounds and the Lipschitz bound of the pushed first-mode potential. -/
def PushPotLip (ψ : ℂ → ℂ) : Prop :=
  ∀ m : ℕ, ∃ M₀ M₁ rD L ρ₁ τ₁ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 < rD ∧ 0 ≤ L ∧ 0 < ρ₁ ∧ 0 < τ₁ ∧
    2 * τ₁ ≤ rD ∧ ∀ w : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → 1 / ((m : ℝ) + 1) ≤ w.im →
      rD < w.im ∧ (∀ x ∈ closedBall w rD, ‖ψ x‖ ≤ M₀) ∧
      (∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD, ‖ψ x - ψ x'‖ ≤ M₁ * ‖x - x'‖) ∧
      ∀ u : ℂ, ‖u‖ = 1 → ∀ S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1),
        ∀ τ s : ℝ, 0 < τ → τ ≤ τ₁ → 0 ≤ s → s ≤ τ →
          ∀ p ∈ ball ((S : ℂ) * ψ w) ρ₁, ∀ p' ∈ ball ((S : ℂ) * ψ w) ρ₁,
            |pushPot ψ S w ((τ : ℂ) * u) s p - pushPot ψ S w ((τ : ℂ) * u) s p'| ≤
              L / τ * ‖p - p'‖

end Thm18Asm
end QuantumZipper
