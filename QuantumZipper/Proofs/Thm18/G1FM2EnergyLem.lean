import QuantumZipper.Proofs.Thm18.G1FM2PotDef
import QuantumZipper.Proofs.Thm18.G1FMAdm
import QuantumZipper.Proofs.Thm18.G1FMVarClamp
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarEnergy
import QuantumZipper.Proofs.Zipper.Cor15Markov2Energy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1FM2-ENERGY (1): tools for the energies of the pushed first-mode pairs

* `G1FM2.abs_integral_fmMeas_sub_le_on`: the synchronous coupling bound
  `D3Plus.abs_integral_fmMeas_sub_le` for a function that is Lipschitz only on a set containing
  both supports (McShane extension `LipschitzOnWith.extend_real`);
* `G1FM2.kernelCov2_sub_le`: `𝓔(a − b) ≤ 2 𝓔(a) + 2 𝓔(b)` for balanced admissible pairs
  (parallelogram law, from `𝓔(a + b) ≥ 0`, `Cor15Group.kernelCov2_self_nonneg_adm`).

Own elementary arguments.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

/-- McShane extension of a function Lipschitz on a set. -/
theorem exists_lip_ext {F : ℂ → ℝ} {D : Set ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x ∈ D, ∀ x' ∈ D, |F x - F x'| ≤ K * ‖x - x'‖) :
    ∃ G : ℂ → ℝ, Measurable G ∧ (∀ x x', |G x - G x'| ≤ K * ‖x - x'‖) ∧ EqOn F G D := by
  have hl : LipschitzOnWith (Real.toNNReal K) F D :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK]; exact hF x hx y hy
  obtain ⟨G, hG, hEq⟩ := hl.extend_real
  refine ⟨G, hG.continuous.measurable, fun x x' => ?_, hEq⟩
  have := hG.dist_le_mul x x'
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK] at this

/-- **Coupling bound for a function Lipschitz on a set containing both supports.** -/
theorem abs_integral_fmMeas_sub_le_on {F : ℂ → ℝ} {D : Set ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x ∈ D, ∀ x' ∈ D, |F x - F x'| ≤ K * ‖x - x'‖) {w v w' v' : ℂ} {s s' : ℝ}
    (hs : 0 ≤ s) (hs' : 0 ≤ s') (hv : ‖v‖ ≤ w.im) (hv' : ‖v'‖ ≤ w'.im)
    (hD : closedBall w (‖v‖ + s) ⊆ D) (hD' : closedBall w' (‖v'‖ + s') ⊆ D) :
    |∫ x, F x ∂D3Plus.fmMeas w v s - ∫ x, F x ∂D3Plus.fmMeas w' v' s'| ≤
      D3Plus.fmBase.real univ * (K * (‖w - w'‖ + ‖v - v'‖ + |s - s'|)) := by
  obtain ⟨G, hGm, hG, hEq⟩ := exists_lip_ext hK hF
  have e : ∀ (w₀ v₀ : ℂ) (s₀ : ℝ), 0 ≤ s₀ → ‖v₀‖ ≤ w₀.im → closedBall w₀ (‖v₀‖ + s₀) ⊆ D →
      ∫ x, F x ∂D3Plus.fmMeas w₀ v₀ s₀ = ∫ x, G x ∂D3Plus.fmMeas w₀ v₀ s₀ :=
    fun w₀ v₀ s₀ h0 h1 h2 => integral_congr_ae (by
      filter_upwards [G1FM.ae_dist_fmMeas_le h0 h1] with x hx
      exact hEq (h2 (mem_closedBall.2 hx)))
  rw [e w v s hs hv hD, e w' v' s' hs' hv' hD']
  exact D3Plus.abs_integral_fmMeas_sub_le hGm hK (fun x _ x' _ => hG x x') w v w' v' hs hs'

/-- Potentials of admissible measures are integrable against admissible measures. -/
theorem integrable_pot {A M : Measure ℂ} (hM : IsAdmissibleH M) (hA : IsAdmissibleH A) :
    Integrable (fun x => ∫ y, neumannH x y ∂A) M := by
  have := hA.1
  exact (integrable_neumannH_prod hM hA).integral_prod_left

theorem pot_add {A B : Measure ℂ} (hA : IsAdmissibleH A) (hB : IsAdmissibleH B) (x : ℂ) :
    ∫ y, neumannH x y ∂(A + B) = (∫ y, neumannH x y ∂A) + ∫ y, neumannH x y ∂B := by
  have := hA.1
  have := hB.1
  exact integral_add_measure (D3Plus.integrable_neumannH_right_adm hA x)
    (D3Plus.integrable_neumannH_right_adm hB x)

theorem integral_pot2 {M X Y : Measure ℂ} (hM : IsAdmissibleH M) (hX : IsAdmissibleH X)
    (hY : IsAdmissibleH Y) :
    ∫ x, ((∫ y, neumannH x y ∂X) - ∫ y, neumannH x y ∂Y) ∂M =
      (∫ x, (∫ y, neumannH x y ∂X) ∂M) - ∫ x, (∫ y, neumannH x y ∂Y) ∂M :=
  integral_sub (integrable_pot hM hX) (integrable_pot hM hY)

theorem integral_pot4 {M X₁ X₂ Y₁ Y₂ : Measure ℂ} (hM : IsAdmissibleH M)
    (hX₁ : IsAdmissibleH X₁) (hX₂ : IsAdmissibleH X₂) (hY₁ : IsAdmissibleH Y₁)
    (hY₂ : IsAdmissibleH Y₂) :
    ∫ x, ((∫ y, neumannH x y ∂X₁) + (∫ y, neumannH x y ∂X₂) -
      ((∫ y, neumannH x y ∂Y₁) + ∫ y, neumannH x y ∂Y₂)) ∂M =
      (∫ x, (∫ y, neumannH x y ∂X₁) ∂M) + (∫ x, (∫ y, neumannH x y ∂X₂) ∂M) -
        ((∫ x, (∫ y, neumannH x y ∂Y₁) ∂M) + ∫ x, (∫ y, neumannH x y ∂Y₂) ∂M) := by
  have i1 := integrable_pot hM hX₁
  have i2 := integrable_pot hM hX₂
  have i3 := integrable_pot hM hY₁
  have i4 := integrable_pot hM hY₂
  have e := integral_sub (i1.add i2) (i3.add i4)
  simp only [Pi.add_apply] at e
  rw [e, integral_add i1 i2, integral_add i3 i4]

theorem integral_pot4_add {M M' X₁ X₂ Y₁ Y₂ : Measure ℂ} (hM : IsAdmissibleH M)
    (hM' : IsAdmissibleH M') (hX₁ : IsAdmissibleH X₁) (hX₂ : IsAdmissibleH X₂)
    (hY₁ : IsAdmissibleH Y₁) (hY₂ : IsAdmissibleH Y₂) :
    ∫ x, ((∫ y, neumannH x y ∂X₁) + (∫ y, neumannH x y ∂X₂) -
      ((∫ y, neumannH x y ∂Y₁) + ∫ y, neumannH x y ∂Y₂)) ∂(M + M') =
      ((∫ x, (∫ y, neumannH x y ∂X₁) ∂M) + (∫ x, (∫ y, neumannH x y ∂X₂) ∂M) -
        ((∫ x, (∫ y, neumannH x y ∂Y₁) ∂M) + ∫ x, (∫ y, neumannH x y ∂Y₂) ∂M)) +
      ((∫ x, (∫ y, neumannH x y ∂X₁) ∂M') + (∫ x, (∫ y, neumannH x y ∂X₂) ∂M') -
        ((∫ x, (∫ y, neumannH x y ∂Y₁) ∂M') + ∫ x, (∫ y, neumannH x y ∂Y₂) ∂M')) := by
  have e := integral_add_measure (((integrable_pot hM hX₁).add (integrable_pot hM hX₂)).sub
      ((integrable_pot hM hY₁).add (integrable_pot hM hY₂)))
    (((integrable_pot hM' hX₁).add (integrable_pot hM' hX₂)).sub
      ((integrable_pot hM' hY₁).add (integrable_pot hM' hY₂)))
  simp only [Pi.add_apply, Pi.sub_apply] at e
  rw [e, integral_pot4 hM hX₁ hX₂ hY₁ hY₂, integral_pot4 hM' hX₁ hX₂ hY₁ hY₂]

/-- **Parallelogram bound.** `𝓔((A, B) − (C, D)) ≤ 2 𝓔(A, B) + 2 𝓔(C, D)`. -/
theorem kernelCov2_sub_le {A B C D : Measure ℂ} (hA : IsAdmissibleH A) (hB : IsAdmissibleH B)
    (hC : IsAdmissibleH C) (hD : IsAdmissibleH D) (hAB : A univ = B univ)
    (hCD : C univ = D univ) :
    kernelCov2 neumannH (A + D, B + C) (A + D, B + C) ≤
      2 * kernelCov2 neumannH (A, B) (A, B) + 2 * kernelCov2 neumannH (C, D) (C, D) := by
  have hnn := Cor15Group.kernelCov2_self_nonneg_adm (isAdmissibleH_add hA hC)
    (isAdmissibleH_add hB hD) (by simp only [Measure.add_apply, hAB, hCD])
  rw [D3Plus.kernelCov2_self_eq_pot (isAdmissibleH_add hA hD) (isAdmissibleH_add hB hC)]
  rw [D3Plus.kernelCov2_self_eq_pot (isAdmissibleH_add hA hC) (isAdmissibleH_add hB hD)] at hnn
  rw [D3Plus.kernelCov2_self_eq_pot hA hB, D3Plus.kernelCov2_self_eq_pot hC hD,
    integral_pot2 hA hA hB, integral_pot2 hB hA hB, integral_pot2 hC hC hD,
    integral_pot2 hD hC hD]
  simp only [pot_add hA hD, pot_add hB hC, pot_add hA hC, pot_add hB hD] at hnn ⊢
  rw [integral_pot4_add hA hD hA hD hB hC, integral_pot4_add hB hC hA hD hB hC]
  rw [integral_pot4_add hA hC hA hC hB hD, integral_pot4_add hB hD hA hC hB hD] at hnn
  linarith

end G1FM2
end Thm18Asm
end QuantumZipper
