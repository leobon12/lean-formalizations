import QuantumZipper.Proofs.Zipper.GenUCKolm
import QuantumZipper.Proofs.Zipper.UnifRC3Mix
import QuantumZipper.Proofs.Zipper.UnifUCFixBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GENERIC-UC: the energy hypothesis of `GenFam` from separate moduli

`genFam_of_moduli`: on a bounded parameter set `S`, the joint Hölder bound of `GenFam` follows
from admissibility, constant mass and two separate moduli — the radius modulus (the XFLOW E1
`FlowE1Stmt`, D33 `energyRadStmt_holds`) and the parameter modulus at a fixed radius (the XFLOW
E2/E3 `FlowE2Stmt`, `FlowE3Stmt`, D33 `energyParStmt_holds`) — by the triangle inequality for
the Neumann energy (`RegUnif.kernelCov2_self_triangle`) through `μ p ρ'` and the exponent
bookkeeping `RegUnif.rpow_le_of_le_both`. This is the generic form of `F1.flowEnergyStmt_of`
(XFlowEnergyAsm); own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuantumZipper
namespace GenUC

open RegUnif

/-- **`GenFam` from the radius modulus and the parameter modulus.** -/
theorem genFam_of_moduli {n : ℕ} {S : Set (Fin n → ℝ)} {μ : (Fin n → ℝ) → ℝ → Measure ℂ}
    {M : ℝ≥0∞} (hadm : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, IsAdmissibleH (μ p ρ))
    (hmass : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, μ p ρ univ = M)
    {D₀ : ℝ} (hdiam : ∀ p ∈ S, ∀ p' ∈ S, dist p p' ≤ D₀)
    {C₁ a₁ : ℝ} (hC₁ : 0 ≤ C₁) (ha₁ : 0 < a₁)
    (hE1 : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (μ p ρ, μ p ρ') (μ p ρ, μ p ρ')| ≤ C₁ * |ρ - ρ'| ^ a₁)
    {C₂ b₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : 0 < b₂)
    (hE2 : ∀ p ∈ S, ∀ p' ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (μ p ρ, μ p' ρ) (μ p ρ, μ p' ρ)| ≤ C₂ * dist p p' ^ b₂) :
    ∃ K c : ℝ, GenFam S μ M K c := by
  set c := min a₁ b₂ with hc
  have hc0 : 0 < c := lt_min ha₁ hb₂
  have hca : c ≤ a₁ := min_le_left _ _
  have hcb : c ≤ b₂ := min_le_right _ _
  set L : ℝ := max D₀ 1 with hL
  have hL0 : 0 ≤ L := le_trans zero_le_one (le_max_right _ _)
  refine ⟨2 * (C₁ * (1 + (L + 1) ^ a₁)) + 2 * (C₂ * (1 + (L + 1) ^ b₂)), c,
    ⟨hadm, hmass, by positivity, hc0, fun p hp p' hp' ρ hρ ρ' hρ' => ?_⟩⟩
  have hA1 := hadm p hp ρ hρ
  have hA2 := hadm p hp ρ' hρ'
  have hA4 := hadm p' hp' ρ' hρ'
  have hm1 := hmass p hp ρ hρ
  have hm2 := hmass p hp ρ' hρ'
  have hm4 := hmass p' hp' ρ' hρ'
  rw [abs_of_nonneg (kernelCov2_self_nonneg hA1 hA4 (hm1.trans hm4.symm))]
  have t1 := kernelCov2_self_triangle hA1 hA2 hA4 (hm1.trans hm2.symm) (hm2.trans hm4.symm)
  have e1 := (le_abs_self _).trans (hE1 p hp ρ hρ ρ' hρ')
  have e2 := (le_abs_self _).trans (hE2 p hp p' hp' ρ' hρ')
  set Δ := dist p p' + |ρ - ρ'| with hΔ
  have hρL : |ρ - ρ'| ≤ L := by
    have : |ρ - ρ'| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2, hρ'.1, hρ'.2]
    exact this.trans (le_max_right _ _)
  have hdL : dist p p' ≤ L := (hdiam p hp p' hp').trans (le_max_left _ _)
  have f1 := rpow_le_of_le_both (abs_nonneg _)
    (show |ρ - ρ'| ≤ Δ by linarith [dist_nonneg (x := p) (y := p')]) hρL hc0 hca
  have f2 := rpow_le_of_le_both dist_nonneg
    (show dist p p' ≤ Δ by linarith [abs_nonneg (ρ - ρ')]) hdL hc0 hcb
  have g1 := mul_le_mul_of_nonneg_left f1 hC₁
  have g2 := mul_le_mul_of_nonneg_left f2 hC₂
  nlinarith

end GenUC
end QuantumZipper
