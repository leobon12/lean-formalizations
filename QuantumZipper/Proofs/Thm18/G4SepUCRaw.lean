import QuantumZipper.Proofs.Thm18.G4ASepLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G4 A-sep exactness via GENERIC-UC (2/n): the raw side (step (d))

For `ψ = revMapInv (backDrv W τ τ' a)`, `R = revMap (backDrv W τ τ' a)` and a finite measure `σ`
carried by `R(ℍ)` (`BackSupportI`), the raw value of the unzipped field at the pushed measure
`σ.map (a ψ)` is the raw value of the *earlier* unzipped field at the scaled measure
`σ.map (a ·)` plus a deterministic term:

`U_τ(σ.map (a ψ)) = U_{τ'}(σ.map (a ·)) + Q ∫ log ‖R'(ψ w)‖ dσ(w)`.

Proof: the flow identity `f_τ⁻¹(a z) = f_{τ'}⁻¹(a R(z))` (`fwdMapInv_mul_backDrv`, the
Loewner semigroup property) gives `(σ.map (a ψ)).map f_τ⁻¹ = (σ.map (a ·)).map f_{τ'}⁻¹`, and the
chain rule `log_deriv_fwdMapInv_backDrv_eq` splits the log-derivative term. Own elementary
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- `f_s⁻¹` is a.e.-measurable for every measure carried by `ℍ`. -/
theorem aemeasurable_fwdMapInv_of_ae_H {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ H) : AEMeasurable (fwdMapInv W s) μ := by
  refine (TwoPoint.measurable_revMap (RegCont.continuous_vRev hW s) hs).aemeasurable.congr ?_
  filter_upwards [hμ] with u hu
  exact (UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 hs hu).symm

theorem measurable_log_norm_deriv (f : ℂ → ℂ) :
    Measurable fun z => Real.log ‖deriv f z‖ :=
  Real.measurable_log.comp (measurable_deriv f).norm

/-- **Raw identity.** -/
theorem unzippedField_backDrv_raw (γ : ℝ) (y : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (ha : 0 < a) {σ : Measure ℂ}
    (hsupp : σ (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 '' H)ᶜ = 0)
    (hI1 : Integrable (fun w => Real.log ‖deriv (fwdMapInv W τ') ((a : ℂ) * w)‖) σ)
    (hI2 : Integrable (fun w => Real.log ‖deriv (revMap (backDrv W τ τ' a).2
      (backDrv W τ τ' a).1) (revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w)‖) σ) :
    unzippedField γ (y, W) τ
        (σ.map fun w => (a : ℂ) * revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w) =
      unzippedField γ (y, W) τ' (σ.map fun w => (a : ℂ) * w) +
        Qc γ * ∫ w, Real.log ‖deriv (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1)
          (revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w)‖ ∂σ := by
  set V := (backDrv W τ τ' a).2 with hV
  set T := (backDrv W τ τ' a).1 with hT
  have hVc : Continuous V := continuous_backDrv hW τ τ' a
  have hT0 : 0 ≤ T := backDrv_fst_nonneg W hττ a
  have hτ : 0 ≤ τ := hτ'.trans hττ
  set ψ := revMapInv V T with hψ
  set g : ℂ → ℂ := fun w => (a : ℂ) * ψ w with hg
  set m : ℂ → ℂ := fun w => (a : ℂ) * w with hm
  have hgm : Measurable g := (Cor15Group.measurable_revMapInv hVc hT0).const_mul _
  have hmm : Measurable m := measurable_const_mul _
  have hRH : ∀ᵐ w ∂σ, w ∈ revMap V T '' H := by
    rw [ae_iff]; simpa [compl_def] using hsupp
  have hψH : ∀ᵐ w ∂σ, ψ w ∈ H ∧ revMap V T (ψ w) = w := by
    filter_upwards [hRH] with w hw
    exact Cor15Group.revMapInv_mem_H hVc hT0 hw
  have hgH : ∀ᵐ z ∂σ.map g, z ∈ H := by
    refine (ae_map_iff hgm.aemeasurable isOpen_H.measurableSet).2 ?_
    filter_upwards [hψH] with w hw
    exact rezip_mul_mem_H ha hw.1
  -- `σ` itself is carried by `ℍ` (`R` maps `ℍ` into `ℍ`)
  have hσH : ∀ᵐ w ∂σ, w ∈ H := by
    filter_upwards [hψH] with w hw
    rw [← hw.2]; exact TwoPoint.im_revMap_pos hVc hw.1 hT0
  have hmH : ∀ᵐ z ∂σ.map m, z ∈ H := by
    refine (ae_map_iff hmm.aemeasurable isOpen_H.measurableSet).2 ?_
    filter_upwards [hσH] with w hw
    exact rezip_mul_mem_H ha hw
  have hf1 := aemeasurable_fwdMapInv_of_ae_H hW hW0 hτ hgH
  have hf2 := aemeasurable_fwdMapInv_of_ae_H hW hW0 hτ' hmH
  have hmap : (σ.map g).map (fwdMapInv W τ) = (σ.map m).map (fwdMapInv W τ') := by
    rw [AEMeasurable.map_map_of_aemeasurable hf1 hgm.aemeasurable,
      AEMeasurable.map_map_of_aemeasurable hf2 hmm.aemeasurable]
    refine Measure.map_congr ?_
    filter_upwards [hψH] with w hw
    have h := fwdMapInv_mul_backDrv hW hW0 hτ' hττ ha hw.1
    simp only [Function.comp, hg, hm]
    rw [h, ← hV, ← hT, hw.2]
  have hint1 : ∫ z, Real.log ‖deriv (fwdMapInv W τ) z‖ ∂(σ.map g) =
      ∫ w, Real.log ‖deriv (fwdMapInv W τ) (g w)‖ ∂σ :=
    integral_map hgm.aemeasurable (measurable_log_norm_deriv _).aestronglyMeasurable
  have hint2 : ∫ z, Real.log ‖deriv (fwdMapInv W τ') z‖ ∂(σ.map m) =
      ∫ w, Real.log ‖deriv (fwdMapInv W τ') (m w)‖ ∂σ :=
    integral_map hmm.aemeasurable (measurable_log_norm_deriv _).aestronglyMeasurable
  have hsplit : ∫ w, Real.log ‖deriv (fwdMapInv W τ) (g w)‖ ∂σ =
      ∫ w, Real.log ‖deriv (fwdMapInv W τ') (m w)‖ ∂σ +
        ∫ w, Real.log ‖deriv (revMap V T) (ψ w)‖ ∂σ := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae ?_
    filter_upwards [hRH] with w hw
    exact log_deriv_fwdMapInv_backDrv_eq hW hW0 hτ' hττ ha hw
  show evalReg y ((σ.map g).map (fwdMapInv W τ)) +
      Qc γ * ∫ z, Real.log ‖deriv (fwdMapInv W τ) z‖ ∂(σ.map g) =
    (evalReg y ((σ.map m).map (fwdMapInv W τ')) +
      Qc γ * ∫ z, Real.log ‖deriv (fwdMapInv W τ') z‖ ∂(σ.map m)) +
      Qc γ * ∫ w, Real.log ‖deriv (revMap V T) (ψ w)‖ ∂σ
  rw [hmap, hint1, hint2, hsplit]
  ring

end G4Core
end Thm18Asm
end QuantumZipper
