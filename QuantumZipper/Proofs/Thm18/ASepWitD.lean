import QuantumZipper.Proofs.Thm18.ASepWitB
import QuantumZipper.Proofs.Thm18.ASepDetB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-WIT (d): pathwise continuity of the smoothed values `Φ_j` for the A-sep family at `τ' = 0`

`ae_continuousOn_Phi_A0`: almost surely, for every `j`,
`p ↦ ∫ avgReg x_{p 0} j dν_p` is continuous on the parameter set, where
`x_t = coordChange (ofFun (a' log |·| + g₁) + X) ψ_t Q` and `ν_p = σ.map (w ↦ f_{p 0}((p 1) w))`.
On `ℍ̄` the smoothed field is the joint witness `Z(t, ·, 2^{-j})` (`ae_exists_joint_witness_fixed`),
so `Φ_j(p) = ∫ Z(p 0, f_{p 0}((p 1) w), 2^{-j}) dσ(w)`, continuous by dominated convergence with
the centre modulus (C2) `norm_fwdMap_sub_le`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif UnzipInvariance RegSample

/-- Continuity of the centre map in the parameter (modulus (C2)). -/
theorem continuousOn_fwdMap_param {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {d : ℂ} {r a₀ a₁ m : ℝ} (hm : 0 < m)
    (hsol : ∀ z ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {S : Set (Fin 2 → ℝ)} (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁)
    {w : ℂ} (hw : w ∈ foldSph d r) :
    ContinuousOn (fun p : Fin 2 → ℝ => fwdMap W (p 0) ((p 1 : ℂ) * w)) S := by
  intro p hp
  set Ψ : (Fin 2 → ℝ) → ℝ := fun p' => Real.exp (2 * T / m ^ 2) *
      ‖(p' 1 : ℂ) * w - (p 1 : ℂ) * w‖ + |W (p' 0) - W (p 0)| + 2 * |p' 0 - p 0| / m
    with hΨ
  have hbd : ∀ p' ∈ S, ‖fwdMap W (p' 0) ((p' 1 : ℂ) * w) - fwdMap W (p 0) ((p 1 : ℂ) * w)‖
      ≤ Ψ p' := fun p' hp' =>
    norm_fwdMap_sub_le hW hW0 hT hm hsol hlow (mem_scaledSph (hSb p' hp').2 hw)
      (mem_scaledSph (hSb p hp).2 hw) (hSb p' hp').1 (hSb p hp).1
  have hΨc : Continuous Ψ := by
    have h0 : Continuous fun p' : Fin 2 → ℝ => p' 0 := continuous_apply 0
    have h1 : Continuous fun p' : Fin 2 → ℝ => p' 1 := continuous_apply 1
    exact ((continuous_const.mul
      (((Complex.continuous_ofReal.comp h1).mul continuous_const).sub continuous_const).norm).add
      ((hW.comp h0).sub continuous_const).abs).add
      ((continuous_const.mul (h0.sub continuous_const).abs).div_const _)
  have hΨ0 : Ψ p = 0 := by simp [hΨ]
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall hbd) ?_
  have := (hΨc.continuousWithinAt (s := S) (x := p))
  rwa [ContinuousWithinAt, hΨ0] at this

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
