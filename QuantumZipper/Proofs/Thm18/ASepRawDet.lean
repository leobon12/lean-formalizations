import QuantumZipper.Proofs.Thm18.ASepRaw0
import QuantumZipper.Proofs.Thm18.ASepHopf
import QuantumZipper.Proofs.Thm18.G4WeldRem
import QuantumZipper.Proofs.Zipper.B2Defs
import QuantumZipper.Proofs.Loewner.ReverseHolo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (raw side at `τ' = 0`): the deterministic term in forward coordinates

For `R = revMap (revDrv W τ a)` (the rescaled time reversal, `= backDrv W τ 0 a`):

* `revMap_revDrv_eq_fwdMapInv`: `R(y) = f_τ⁻¹(a y) / a` on `ℍ` (Loewner scaling
  `Thm18Asm.revMap_revDrv` and `f_τ⁻¹ = revMap (vrev W τ) τ`, `B2.fwdMapInv_eq_revMap_vrev`);
* `deriv_revMap_revDrv`: `R'(y) = (f_τ⁻¹)'(a y)` on `ℍ`;
* `log_deriv_revMap_revDrv_psi`: at `y = ψ(w)`, `w ∈ R(ℍ)`,
  `log ‖R'(ψ w)‖ = log ‖(f_τ⁻¹)'(f_τ(a w))‖`.

So the deterministic term `Q ∫ log ‖R'(ψ w)‖ dσ` of the raw identity (`ASep.unzippedField_raw0`)
is `Q ∫ log ‖(f_τ⁻¹)'‖ dν_p`, `ν_p = σ.map (w ↦ f_τ(a w))`: the log-derivative part of the
engine's limit `detLim` (the `ρ → 0` limit of `Dfun`). Own elementary bookkeeping (chain rule).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

theorem revMap_revDrv_eq_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ a : ℝ}
    (hτ : 0 ≤ τ) (ha : 0 < a) {y : ℂ} (hy : y ∈ H) :
    revMap (revDrv W τ a).2 (revDrv W τ a).1 y = fwdMapInv W τ ((a : ℂ) * y) / a := by
  have hay : (a : ℂ) * y ∈ H := by
    show 0 < ((a : ℂ) * y).im
    have : 0 < y.im := hy
    simpa using mul_pos ha this
  rw [revMap_revDrv hW hτ ha hy, B2.fwdMapInv_eq_revMap_vrev hW hW0 hτ hay]

theorem deriv_revMap_revDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ a : ℝ}
    (hτ : 0 ≤ τ) (ha : 0 < a) {y : ℂ} (hy : y ∈ H) :
    deriv (revMap (revDrv W τ a).2 (revDrv W τ a).1) y = deriv (fwdMapInv W τ) ((a : ℂ) * y) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hev : revMap (revDrv W τ a).2 (revDrv W τ a).1 =ᶠ[𝓝 y]
      fun y => fwdMapInv W τ ((a : ℂ) * y) / a :=
    Filter.eventually_of_mem (isOpen_H_asep.mem_nhds hy) fun z hz =>
      revMap_revDrv_eq_fwdMapInv hW hW0 hτ ha hz
  have hay : (a : ℂ) * y ∈ H := by
    show 0 < ((a : ℂ) * y).im
    have : 0 < y.im := hy
    simpa using mul_pos ha this
  -- differentiability of `f_τ⁻¹` at `a y`
  have hV := B2.continuous_vrev hW τ
  have hd : DifferentiableAt ℂ (fwdMapInv W τ) ((a : ℂ) * y) := by
    have hev2 : fwdMapInv W τ =ᶠ[𝓝 ((a : ℂ) * y)] revMap (B2.vrev W τ) τ :=
      Filter.eventually_of_mem (isOpen_H_asep.mem_nhds hay) fun z hz =>
        B2.fwdMapInv_eq_revMap_vrev hW hW0 hτ hz
    exact ((hasDerivAt_revMap _ hV hτ hay).differentiableAt).congr_of_eventuallyEq
      hev2
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun y => fwdMapInv W τ ((a : ℂ) * y))
      (deriv (fwdMapInv W τ) ((a : ℂ) * y) * (a : ℂ)) y := by
    have h2 : HasDerivAt (fun y : ℂ => (a : ℂ) * y) (a : ℂ) y := by
      simpa using (hasDerivAt_id y).const_mul (a : ℂ)
    exact hd.hasDerivAt.comp y h2
  rw [(h1.div_const (a : ℂ)).deriv, mul_div_cancel_right₀ _ haC]

/-- **The deterministic term in forward coordinates.** -/
theorem log_deriv_revMap_revDrv_psi {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ a : ℝ}
    (hτ : 0 ≤ τ) (ha : 0 < a) {w : ℂ}
    (hw : w ∈ revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 '' H) (hwH : 0 < w.im) :
    Real.log ‖deriv (revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1)
        (revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w)‖ =
      Real.log ‖deriv (fwdMapInv W τ) (fwdMap W τ ((a : ℂ) * w))‖ := by
  have e := mul_revMapInv_revDrv0_eq hW hW0 hτ ha hw hwH
  rw [backDrv_zero] at e hw ⊢
  obtain ⟨z, hz, rfl⟩ := hw
  have hT : 0 ≤ (revDrv W τ a).1 := by simp only [revDrv]; positivity
  have hψ : revMapInv (revDrv W τ a).2 (revDrv W τ a).1
      (revMap (revDrv W τ a).2 (revDrv W τ a).1 z) = z :=
    Cor15Group.revMapInv_revMap (by simp only [revDrv]; fun_prop) hT hz
  rw [hψ] at e ⊢
  rw [deriv_revMap_revDrv hW hW0 hτ ha hz, e]

end ASep
end QuantumZipper
