import QuantumZipper.Proofs.Thm18.G4ASepDefs
import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.Thm18.G4ReadFix
import QuantumZipper.Proofs.Zipper.Cor15RezipRegDist
import QuantumZipper.Proofs.Zipper.UnzipFullSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core A-sep (task G4C-ASEP): the log-integrability conjuncts

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1); decision
D57 (`handoff/G4-CORE.md` §6).

With `R = revMap (backDrv W τ τ' a)`, `ψ = R⁻¹` and `w ∈ R(ℍ)`, `z = ψ w`:

* `ψ'(w) = R'(z)⁻¹` (inverse function theorem, `Cor15Group.hasStrictDerivAt_revMapInv`), so
  `log ‖ψ'(w)‖ = − log ‖R'(ψ w)‖`;
* `(f_τ⁻¹)'(a z) = (f_{τ'}⁻¹)'(a w) · R'(z)` (`deriv_fwdMapInv_mul_backDrv`, flow composition and
  Brownian scaling), so `log ‖(f_τ⁻¹)'(a ψ w)‖ = log ‖(f_{τ'}⁻¹)'(a w)‖ + log ‖R'(ψ w)‖`;
* `w ↦ log ‖(f_{τ'}⁻¹)'(a w)‖` is integrable on every folded circle, by the Koebe bound for the
  injective holomorphic map `f_{τ'}⁻¹(a ·)` on `ℍ` (`G1.integrable_log_norm_deriv_foldedCircle_of_injOn`;
  Koebe distortion, Pommerenke, *Boundary Behaviour of Conformal Maps*, Cor. 1.4).

Hence both integrability conjuncts of `DriverPushExactI` follow from the single deterministic
node `BackLogSepStmt` (integrability of `log ‖R' ∘ ψ‖` on separated circles), and
`G4DriverPushSepAllStmt` follows from `BackLogSepStmt` and the exactness node
`G4DriverPushSepExactStmt` (`g4DriverPushSepAllStmt_of_log_exact`).
**Own elementary argument** (chain rule and inverse function theorem).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- `log ‖(f_t⁻¹)'(a ·)‖` is integrable on every folded circle (Koebe). -/
theorem integrable_log_deriv_fwdMapInv_mul {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun w => Real.log ‖deriv (fwdMapInv W t) ((a : ℂ) * w)‖) (foldedCircle d r) := by
  set V : ℝ → ℝ := fun s => W (t - s) - W t with hVdef
  have hV : Continuous V := by fun_prop
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set φ : ℂ → ℂ := fun z => revMap V t ((a : ℂ) * z) with hφdef
  have hmaps : MapsTo (fun z : ℂ => (a : ℂ) * z) H H := fun z hz => rezip_mul_mem_H ha hz
  have hφd : DifferentiableOn ℂ φ H :=
    (differentiableOn_revMap V hV ht).comp (differentiableOn_id.const_mul (a : ℂ)) hmaps
  have hφi : InjOn φ H := fun z hz z' hz' h =>
    mul_left_cancel₀ ha0 (injOn_revMap V hV ht (hmaps hz) (hmaps hz') h)
  have hI := G1.integrable_log_norm_deriv_foldedCircle_of_injOn hφd hφi d hr
  refine (hI.sub (integrable_const (Real.log a))).congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
  have haz := rezip_mul_mem_H ha hz
  have hloc : fwdMapInv W t =ᶠ[𝓝 ((a : ℂ) * z)] revMap V t :=
    Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds haz) fun v hv =>
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hv
  have hRd : HasDerivAt (revMap V t) (deriv (revMap V t) ((a : ℂ) * z)) ((a : ℂ) * z) :=
    ((differentiableOn_revMap V hV ht) _ haz).differentiableAt (isOpen_H.mem_nhds haz)
      |>.hasDerivAt
  have hmul : HasDerivAt (fun u : ℂ => (a : ℂ) * u) (a : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (a : ℂ)
  have hφ' : deriv φ z = deriv (revMap V t) ((a : ℂ) * z) * (a : ℂ) :=
    (hRd.comp z hmul).deriv
  have hne : deriv (revMap V t) ((a : ℂ) * z) ≠ 0 := deriv_revMap_ne_zero V hV ht haz
  show Real.log ‖deriv φ z‖ - Real.log a = Real.log ‖deriv (fwdMapInv W t) ((a : ℂ) * z)‖
  rw [hloc.deriv_eq, hφ', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    Real.log_mul (norm_ne_zero_iff.2 hne) ha.ne']
  ring

/-- `log ‖ψ'(w)‖ = − log ‖R'(ψ w)‖` on `R(ℍ)`. -/
theorem log_deriv_revMapInv_eq {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T) {w : ℂ}
    (hw : w ∈ revMap V T '' H) :
    Real.log ‖deriv (revMapInv V T) w‖ = -Real.log ‖deriv (revMap V T) (revMapInv V T w)‖ := by
  obtain ⟨hzH, hRz⟩ := Cor15Group.revMapInv_mem_H hV hT hw
  have hs := Cor15Group.hasStrictDerivAt_revMapInv hV hT hzH
  rw [hRz] at hs
  rw [hs.hasDerivAt.deriv, norm_inv, Real.log_inv]

/-- `log ‖(f_τ⁻¹)'(a ψ w)‖ = log ‖(f_{τ'}⁻¹)'(a w)‖ + log ‖R'(ψ w)‖` on `R(ℍ)`. -/
theorem log_deriv_fwdMapInv_backDrv_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (ha : 0 < a) {w : ℂ}
    (hw : w ∈ revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 '' H) :
    Real.log ‖deriv (fwdMapInv W τ)
        ((a : ℂ) * revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w)‖ =
      Real.log ‖deriv (fwdMapInv W τ') ((a : ℂ) * w)‖ +
        Real.log ‖deriv (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1)
          (revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w)‖ := by
  obtain ⟨hzH, hRz⟩ := Cor15Group.revMapInv_mem_H (continuous_backDrv hW τ τ' a)
    (backDrv_fst_nonneg W hττ a) hw
  obtain ⟨hd, hne1, hne2⟩ := deriv_fwdMapInv_mul_backDrv hW hW0 hτ' hττ ha hzH
  rw [hd, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hne1) (norm_ne_zero_iff.2 hne2), hRz]

/-- **The two integrability conjuncts** of `DriverPushExactI` at a measure carried by `R(ℍ)`,
from integrability of `log ‖R' ∘ ψ‖` and of `log ‖(f_{τ'}⁻¹)'(a ·)‖`. -/
theorem integrable_logs_backDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (ha : 0 < a) {σ : Measure ℂ}
    (hsup : σ (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 '' H)ᶜ = 0)
    (hL : Integrable (fun w => Real.log ‖deriv (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1)
      (revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w)‖) σ)
    (hA : Integrable (fun w => Real.log ‖deriv (fwdMapInv W τ') ((a : ℂ) * w)‖) σ) :
    Integrable (fun w => Real.log ‖deriv (fwdMapInv W τ)
      ((a : ℂ) * revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w)‖) σ ∧
    Integrable (fun w => Real.log ‖deriv
      (revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1) w‖) σ := by
  have hae : ∀ᵐ w ∂σ, w ∈ revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 '' H := by
    rw [ae_iff]; exact hsup
  refine ⟨(hA.add hL).congr ?_, hL.neg.congr ?_⟩
  · filter_upwards [hae] with w hw
    exact (log_deriv_fwdMapInv_backDrv_eq hW hW0 hτ' hττ ha hw).symm
  · filter_upwards [hae] with w hw
    exact (log_deriv_revMapInv_eq (continuous_backDrv hW τ τ' a)
      (backDrv_fst_nonneg W hττ a) hw).symm

/-- The data at one separated circle, for a deterministic configuration. -/
theorem driverPushExactI_of_log {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} (hL : BackLogSepStmt)
    (hc : Continuous c.2) (hW0 : c.2 0 = 0) {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ)
    (ha : 0 < a) {i : ℕ} (hsup : BackSupportI c τ τ' a i) (hsep : BackSepI c τ τ' a i)
    (h1 : evalReg (rescale (unzippedField γ c τ) (Qc γ) a)
        ((fcI i).map (revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1)) =
      rescale (unzippedField γ c τ) (Qc γ) a
        ((fcI i).map (revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1)))
    (h2 : evalReg (unzippedField γ c τ)
        ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1 w) =
      unzippedField γ c τ
        ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ τ' a).2
          (backDrv c.2 τ τ' a).1 w)) :
    DriverPushExactI γ c τ τ' a i := by
  have hp0 : (backDrv c.2 τ τ' a).2 0 = 0 := by simp [backDrv]
  have hLi : Integrable (fun w => Real.log ‖deriv (revMap (backDrv c.2 τ τ' a).2
      (backDrv c.2 τ τ' a).1) (revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1 w)‖)
      (fcI i) :=
    hL (backDrv c.2 τ τ' a).2 (continuous_backDrv hc τ τ' a) hp0
      (backDrv c.2 τ τ' a).1 (backDrv_fst_nonneg _ hττ a)
      (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      (UnzipFull.fullIndex_radius_pos i) hsup hsep
  have hA : Integrable (fun w => Real.log ‖deriv (fwdMapInv c.2 τ') ((a : ℂ) * w)‖) (fcI i) :=
    integrable_log_deriv_fwdMapInv_mul hc hW0 hτ' ha _ (UnzipFull.fullIndex_radius_pos i)
  exact ⟨h1, h2, integrable_logs_backDrv hc hW0 hτ' hττ ha hsup hLi hA⟩

end G4Core
end Thm18Asm
end QuantumZipper
