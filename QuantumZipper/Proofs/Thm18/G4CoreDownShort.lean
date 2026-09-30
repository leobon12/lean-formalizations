import QuantumZipper.Proofs.Thm18.G4RezipNodes
import QuantumZipper.Proofs.Thm18.G4GroupMixCross
import QuantumZipper.Proofs.Thm18.G4WeldRound

/-!
# Theorem 1.8, node G4: the rezip identity of the core `G4DownShortCoreStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2), case
`t < 0 < s`, `s < −t` (the paper gives no proof). Let `c = (x, W)`, `τ' ≤ τ` two capacity
times, `a > 0`, `U_τ = x ∘ f_τ⁻¹ + Q log|(f_τ⁻¹)'|` the field unzipped by `τ` (`f_τ⁻¹ =
fwdMapInv W τ`), and `p = backDrv W τ τ' a` the `a`-rescaled time reversal of `W` on `[τ', τ]`,
with reverse flow `R = revMap p.2 p.1` and inverse `g = revMapInv p.2 p.1`.

* `fwdMapInv_mul_backDrv` (Loewner flow composition over `[τ', τ]` plus Brownian scaling):
  `f_τ⁻¹(a z) = f_{τ'}⁻¹(a R z)` on `ℍ`. Sources: Lawler, *Conformally Invariant Processes in
  the Plane*, §4.1 (scaling, `LoewnerAlgebra.revMap_scale`) and the flow property of the
  Loewner equation (`RegCont.fwdMapInv_add`, built on `TwoPoint.revMap_concat_eq`).
* `rezipShort_fc_apply` (deterministic, at one measure `σ`): re-zipping `U_τ(a·) + Q log a`
  along `p` gives, at `σ`, the value of `U_{τ'}(a·) + Q log a`, once `σ` is carried by `R(ℍ)`,
  the three intermediate fields are regular at the pushed measures, and the two
  log-derivative terms whose sum is `log|(f_{τ'}⁻¹)'(a·)|` are `σ`-integrable.
* `regEq_rezipShort_cfg`: the `RegEq` conjunct of `DownShortCoreData` from `DownShortPushReg`.
* `g4DownShortCoreStmt_of`: `G4DownShortCoreStmt` from the welding node
  `G4DownShortWeldStmt` (first three conjuncts), the regularity node `G4DownShortPushRegStmt`
  and `G4UnzipGoodStmt`.

**Own elementary argument** (change of variables and the chain rule, as in `G4RezipDet`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

theorem continuous_backDrv {W : ℝ → ℝ} (hW : Continuous W) (τ τ' a : ℝ) :
    Continuous (backDrv W τ τ' a).2 := by
  show Continuous fun u => (W (τ - a ^ 2 * u) - W τ) / a
  fun_prop

theorem backDrv_fst_nonneg (W : ℝ → ℝ) {τ τ' : ℝ} (h : τ' ≤ τ) (a : ℝ) :
    0 ≤ (backDrv W τ τ' a).1 :=
  div_nonneg (sub_nonneg.2 h) (sq_nonneg a)

/-- **Flow composition over `[τ', τ]` with scaling**: `f_τ⁻¹(a z) = f_{τ'}⁻¹(a R z)`, `R` the
reverse flow of `backDrv W τ τ' a`. -/
theorem fwdMapInv_mul_backDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ τ' a : ℝ}
    (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (ha : 0 < a) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv W τ ((a : ℂ) * z) =
      fwdMapInv W τ' ((a : ℂ) * revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 z) := by
  have haz := rezip_mul_mem_H ha hz
  have key := RegCont.fwdMapInv_add hW hW0 hτ' (sub_nonneg.2 hττ) haz
  rw [show τ' + (τ - τ') = τ by ring] at key
  rw [key]
  congr 1
  have hVc : Continuous fun r => W (τ - r) - W τ := by fun_prop
  have hsc := LoewnerAlgebra.revMap_scale (fun r => W (τ - r) - W τ) hVc ha
    (backDrv_fst_nonneg W hττ a) hz
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have e : a ^ 2 * (backDrv W τ τ' a).1 = τ - τ' := by
    simp only [backDrv]; field_simp
  rw [e] at hsc
  have hsc' : revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 z =
      revMap (fun r => W (τ - r) - W τ) (τ - τ') ((a : ℂ) * z) / (a : ℂ) := hsc
  rw [hsc']
  field_simp

/-- Derivative identity behind `fwdMapInv_mul_backDrv`:
`(f_τ⁻¹)'(a z) = (f_{τ'}⁻¹)'(a R z) · R'(z)` on `ℍ`, with both factors nonzero. -/
theorem deriv_fwdMapInv_mul_backDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ : τ' ≤ τ) (ha : 0 < a) {z : ℂ} (hz : z ∈ H) :
    deriv (fwdMapInv W τ) ((a : ℂ) * z) =
        deriv (fwdMapInv W τ') ((a : ℂ) * revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 z) *
          deriv (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1) z ∧
      deriv (fwdMapInv W τ') ((a : ℂ) * revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 z) ≠ 0 ∧
      deriv (revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1) z ≠ 0 := by
  set R := revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 with hRdef
  have hpc := continuous_backDrv hW τ τ' a
  have hp1 := backDrv_fst_nonneg W hττ a
  have hτ : 0 ≤ τ := hτ'.trans hττ
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  -- the unzipping maps agree with reverse flows near points of `ℍ`
  have hloc : ∀ {t : ℝ}, 0 ≤ t → ∀ {w : ℂ}, w ∈ H →
      fwdMapInv W t =ᶠ[𝓝 w] revMap (fun r => W (t - r) - W t) t := fun ht w hw =>
    Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hw) fun v hv =>
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hv
  have hdiff : ∀ {t : ℝ}, 0 ≤ t → ∀ {w : ℂ}, w ∈ H → DifferentiableAt ℂ (fwdMapInv W t) w :=
    fun ht w hw =>
      (((differentiableOn_revMap _ (by fun_prop) ht) _ hw).differentiableAt
        (isOpen_H.mem_nhds hw)).congr_of_eventuallyEq (hloc ht hw)
  have hRz : R z ∈ H := TwoPoint.im_revMap_pos hpc hz hp1
  have haz := rezip_mul_mem_H ha hz
  have haRz := rezip_mul_mem_H ha hRz
  have hRd : HasDerivAt R (deriv R z) z :=
    ((differentiableOn_revMap _ hpc hp1) _ hz).differentiableAt (isOpen_H.mem_nhds hz)
      |>.hasDerivAt
  have hmul : ∀ w : ℂ, HasDerivAt (fun u : ℂ => (a : ℂ) * u) (a : ℂ) w := fun w => by
    simpa using (hasDerivAt_id w).const_mul (a : ℂ)
  have h1 : HasDerivAt (fun u => fwdMapInv W τ ((a : ℂ) * u))
      (deriv (fwdMapInv W τ) ((a : ℂ) * z) * (a : ℂ)) z :=
    (hdiff hτ haz).hasDerivAt.comp z (hmul z)
  have h2 : HasDerivAt (fun u => fwdMapInv W τ' ((a : ℂ) * R u))
      (deriv (fwdMapInv W τ') ((a : ℂ) * R z) * ((a : ℂ) * deriv R z)) z := by
    have hc := (hdiff hτ' haRz).hasDerivAt.comp z (hRd.const_mul (a : ℂ))
    exact hc
  have heq : (fun u => fwdMapInv W τ ((a : ℂ) * u)) =ᶠ[𝓝 z]
      fun u => fwdMapInv W τ' ((a : ℂ) * R u) :=
    Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) fun u hu =>
      fwdMapInv_mul_backDrv hW hW0 hτ' hττ ha hu
  have hd := h1.deriv.symm.trans ((heq.deriv_eq).trans h2.deriv)
  have hne1 : deriv (fwdMapInv W τ') ((a : ℂ) * R z) ≠ 0 := by
    rw [(hloc hτ' haRz).deriv_eq]
    exact deriv_revMap_ne_zero _ (by fun_prop) hτ' haRz
  have hne2 : deriv R z ≠ 0 := deriv_revMap_ne_zero _ hpc hp1 hz
  refine ⟨?_, hne1, hne2⟩
  have : deriv (fwdMapInv W τ) ((a : ℂ) * z) * (a : ℂ) =
      (deriv (fwdMapInv W τ') ((a : ℂ) * R z) * deriv R z) * (a : ℂ) := by
    rw [hd]; ring
  exact mul_right_cancel₀ ha0 this

/-! ## The configuration-level reduction -/

/-- The re-zipping driver of `Z_s ∘ Z_{−ℓ}`: `backDrv W τ_ℓ τ_{ℓ−s} a_ℓ`. -/
abbrev dsDrv (γ s ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ × (ℝ → ℝ) :=
  backDrv c.2 (unzipTime γ ℓ c) (unzipTime γ (ℓ - s) c) (unzipScale γ ℓ c)

end Thm18Asm
end QuantumZipper
