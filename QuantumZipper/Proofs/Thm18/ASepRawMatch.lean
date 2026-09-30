import QuantumZipper.Proofs.Thm18.ASepRaw0
import QuantumZipper.Proofs.Thm18.ASepModA
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Thm18.ASepRawDet
import QuantumZipper.Proofs.Thm18.ASepDetA
import QuantumZipper.Proofs.RS.GenerationBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: the deterministic term of the raw identity is the engine limit `detLimA0`

`detLimA0 W a' g₁ Q d r p = ∫ Gdet dν_p` (ASepDetA.lean, the `ρ → 0` limit of the deterministic
part, `ν_p = σ.map (w ↦ f_τ(a w))`) equals the deterministic term of the raw identity
`ASep.ae_raw_A0`: `∫ (a' log|v| + g₁ v) dfc(a d, a r) + Q ∫ log ‖R'(ψ w)‖ dσ(w)`
(`detLimA0_eq_raw`), because `f_τ⁻¹(f_τ(a w)) = a w` off the hull (`RS.fwdMapInv_fwdMap`) and
`log ‖R'(ψ w)‖ = log ‖(f_τ⁻¹)'(f_τ(a w))‖` (`ASep.log_deriv_revMap_revDrv_psi`). With
`ae_raw_A0` this is the raw identity input `hraw` of `ASep.GenInputsDep` in the form
`x_p(ν_p) = X(μ p 0) + detLim p`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- **The engine limit equals the raw deterministic term.** -/
theorem detLimA0_eq_raw {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (a' : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {d : ℂ} {r : ℝ} {p : Fin 2 → ℝ}
    (hτ : 0 ≤ p 0) (ha : 0 < p 1)
    (hmeas : AEMeasurable (fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) (foldedCircle d r))
    (hgd : ∀ᵐ w ∂foldedCircle d r, 0 < w.im ∧
      w ∈ revMap (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 '' H ∧
      (p 1 : ℂ) * w ∉ fwdHull W (p 0))
    (hint1 : Integrable (fun w => a' * Real.log ‖(p 1 : ℂ) * w‖ + g₁ ((p 1 : ℂ) * w))
      (foldedCircle d r))
    (hI2 : Integrable (fun w => Real.log ‖deriv (revMap (backDrv W (p 0) 0 (p 1)).2
      (backDrv W (p 0) 0 (p 1)).1) (revMapInv (backDrv W (p 0) 0 (p 1)).2
        (backDrv W (p 0) 0 (p 1)).1 w)‖) (foldedCircle d r)) :
    detLimA0 W a' g₁ Q d r p =
      (∫ v, (a' * Real.log ‖v‖ + g₁ v) ∂foldedCircle ((p 1 : ℂ) * d) (p 1 * r)) +
        Q * ∫ w, Real.log ‖deriv (revMap (backDrv W (p 0) 0 (p 1)).2
          (backDrv W (p 0) 0 (p 1)).1) (revMapInv (backDrv W (p 0) 0 (p 1)).2
            (backDrv W (p 0) 0 (p 1)).1 w)‖ ∂foldedCircle d r := by
  set τ := p 0
  set a := p 1
  set σ := foldedCircle d r
  set f : ℂ → ℂ := fun w => fwdMap W τ ((a : ℂ) * w) with hf
  have haH : ∀ w : ℂ, 0 < w.im → (a : ℂ) * w ∈ H := fun w hw => by
    show 0 < ((a : ℂ) * w).im
    simpa using mul_pos ha hw
  -- a measurable version of `Gdet` on `ℍ`
  set V := B2.vrev W τ
  have hV : Continuous V := B2.continuous_vrev hW τ
  set G' : ℂ → ℝ := fun v => a' * Real.log ‖revMap V τ v‖ + g₁ (revMap V τ v) +
    Q * Real.log ‖deriv (revMap V τ) v‖ with hG'
  have hG'm : Measurable G' := by
    have hR := TwoPoint.measurable_revMap hV hτ
    exact ((measurable_const.mul (Real.measurable_log.comp hR.norm)).add
      (hg₁.measurable.comp hR)).add
      (measurable_const.mul (Real.measurable_log.comp (measurable_deriv _ ).norm))
  have hGG : ∀ v ∈ H, Gdet W a' g₁ Q τ v = G' v := fun v hv => by
    have hev : fwdMapInv W τ =ᶠ[𝓝 v] revMap V τ :=
      Filter.eventually_of_mem (isOpen_H_asep.mem_nhds hv) fun z hz =>
        B2.fwdMapInv_eq_revMap_vrev hW hW0 hτ hz
    simp only [Gdet, hG', hev.deriv_eq, B2.fwdMapInv_eq_revMap_vrev hW hW0 hτ hv]
    rfl
  have hfH : ∀ᵐ w ∂σ, f w ∈ H := hgd.mono fun w hw =>
    FwdHolo.mapsTo_fwdMap hW hτ ⟨haH w hw.1, hw.2.2⟩
  have hmapH : ∀ᵐ v ∂σ.map f, v ∈ H :=
    (ae_map_iff hmeas isOpen_H_asep.measurableSet).2 hfH
  unfold detLimA0
  rw [integral_congr_ae (hmapH.mono fun v hv => hGG v hv),
    integral_map hmeas hG'm.aestronglyMeasurable]
  -- pointwise identity along `σ`
  have hpt : ∀ᵐ w ∂σ, G' (f w) = (a' * Real.log ‖(a : ℂ) * w‖ + g₁ ((a : ℂ) * w)) +
      Q * Real.log ‖deriv (revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1)
        (revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w)‖ := by
    filter_upwards [hgd, hfH] with w hw hfw
    rw [← hGG _ hfw]
    have hinv : fwdMapInv W τ (f w) = (a : ℂ) * w :=
      RS.fwdMapInv_fwdMap hW hW0 hτ ⟨haH w hw.1, hw.2.2⟩
    have hinv' : fwdMapInv W τ (fwdMap W τ ((a : ℂ) * w)) = (a : ℂ) * w := hinv
    simp only [Gdet, hf, hinv', log_deriv_revMap_revDrv_psi hW hW0 hτ ha hw.2.1 hw.1]
  rw [integral_congr_ae hpt, integral_add hint1 (hI2.const_mul Q), integral_const_mul]
  congr 1
  rw [← foldedCircle_map_mul ha, integral_map (measurable_const_mul _).aemeasurable]
  exact ((measurable_const.mul (Real.measurable_log.comp measurable_norm)).add
    hg₁.measurable).aestronglyMeasurable

end ASep
end QuantumZipper
