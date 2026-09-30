import QuantumZipper.Proofs.Thm18.G4SepUCRaw
import QuantumZipper.Proofs.Thm18.G1PkgTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (raw side at `τ' = 0`): the raw value of `U_τ` at the pushed circle

At `τ' = 0` the raw-value identity `G4Core.unzippedField_backDrv_raw` (G4SepUCRaw.lean) reads the
field at time `0`, where the unzipping map is the identity on `ℍ` (`G1Pkg.fwdMapInv_zero_time`,
`W 0 = 0`). Hence, for `σ` carried by `R(ℍ) ⊆ ℍ`,

`U_τ(σ.map (a ψ)) = evalReg y (σ.map (a ·)) + Q ∫ log ‖R'(ψ w)‖ dσ(w)`

(`unzippedField_raw0`): the raw side of the A-sep conjunct 2 is the regularized value of the
original field at the scaled circle plus a deterministic term. This is the raw identity input
(`hraw`) of the engine `ASep.GenInputsDep` up to circle exactness of `y` at `σ.map (a ·)`.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

theorem isOpen_H_asep : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

/-- At time `0` the unzipped field is the regularized field on measures carried by `ℍ`. -/
theorem unzippedField_zero_eq (γ : ℝ) (y : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ H) :
    unzippedField γ (y, W) 0 μ = evalReg y μ := by
  have hid : ∀ z ∈ H, fwdMapInv W 0 z = z := fun z hz => by
    rw [G1Pkg.fwdMapInv_zero_time hW hz, hW0, Complex.ofReal_zero, add_zero]
  have hmap : μ.map (fwdMapInv W 0) = μ := by
    rw [Measure.map_congr (g := id) (hμ.mono fun z hz => hid z hz), Measure.map_id]
  have hder : ∀ z ∈ H, Real.log ‖deriv (fwdMapInv W 0) z‖ = 0 := fun z hz => by
    have hev : fwdMapInv W 0 =ᶠ[𝓝 z] id :=
      Filter.eventually_of_mem (isOpen_H_asep.mem_nhds hz) fun w hw => hid w hw
    rw [hev.deriv_eq, deriv_id, norm_one, Real.log_one]
  show evalReg y (μ.map (fwdMapInv W 0)) +
      Qc γ * ∫ z, Real.log ‖deriv (fwdMapInv W 0) z‖ ∂μ = evalReg y μ
  rw [hmap, integral_congr_ae (hμ.mono fun z hz => hder z hz), integral_zero, mul_zero,
    add_zero]

/-- **Raw value at `τ' = 0`.** -/
theorem unzippedField_raw0 (γ : ℝ) (y : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {τ a : ℝ} (hτ : 0 ≤ τ) (ha : 0 < a) {σ : Measure ℂ}
    (hσH : ∀ᵐ w ∂σ, w ∈ H)
    (hsupp : σ (revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 '' H)ᶜ = 0)
    (hI2 : Integrable (fun w => Real.log ‖deriv (revMap (backDrv W τ 0 a).2
      (backDrv W τ 0 a).1) (revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w)‖) σ) :
    unzippedField γ (y, W) τ
        (σ.map fun w => (a : ℂ) * revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w) =
      evalReg y (σ.map fun w => (a : ℂ) * w) +
        Qc γ * ∫ w, Real.log ‖deriv (revMap (backDrv W τ 0 a).2 (backDrv W τ 0 a).1)
          (revMapInv (backDrv W τ 0 a).2 (backDrv W τ 0 a).1 w)‖ ∂σ := by
  have haH : ∀ w ∈ H, (a : ℂ) * w ∈ H := fun w hw => by
    show 0 < ((a : ℂ) * w).im
    have : 0 < w.im := hw
    simpa using mul_pos ha this
  have hid : ∀ z ∈ H, fwdMapInv W 0 z = z := fun z hz => by
    rw [G1Pkg.fwdMapInv_zero_time hW hz, hW0, Complex.ofReal_zero, add_zero]
  have hder : ∀ z ∈ H, Real.log ‖deriv (fwdMapInv W 0) z‖ = 0 := fun z hz => by
    have hev : fwdMapInv W 0 =ᶠ[𝓝 z] id :=
      Filter.eventually_of_mem (isOpen_H_asep.mem_nhds hz) fun w hw => hid w hw
    rw [hev.deriv_eq, deriv_id, norm_one, Real.log_one]
  have hI1 : Integrable (fun w => Real.log ‖deriv (fwdMapInv W 0) ((a : ℂ) * w)‖) σ :=
    (integrable_zero ℂ ℝ σ).congr (hσH.mono fun w hw => (hder _ (haH w hw)).symm)
  rw [unzippedField_backDrv_raw γ y hW hW0 le_rfl hτ ha hsupp hI1 hI2]
  congr 1
  have hm : Measurable fun w : ℂ => (a : ℂ) * w := measurable_const_mul _
  refine unzippedField_zero_eq γ y hW hW0 ?_
  exact (ae_map_iff hm.aemeasurable isOpen_H_asep.measurableSet).2
    (hσH.mono fun w hw => haH w hw)

end ASep
end QuantumZipper
