import QuantumZipper.Proofs.GFF.CoordRegRC2
import QuantumZipper.Proofs.Zipper.UnzipInvariance

/-!
# RC2 and RC3 (circles) for `fwdMapInv W t`

`fwdMapInv W t = revMap (W^{rev,t}) t` on `ℍ` (`fwdMapInv_eq_revMap_timeRev`), and folded
circles of positive radius do not charge `ℝ` (`TwoPoint.foldedCircle_ae_mem_H`). Hence the two
coordinate changes agree at every folded circle of positive radius (`coordChange_fc_congr`), which
is all that `IsRegularWith` and `evalReg` read. The results of `CoordRegRC2` transfer.

Source: none — **own elementary proof** (a transfer of `CoordRegRC2` along `EqOn` on `ℍ`, whose
only mathematical input is the project's identification `fwdMapInv_eq_revMap_timeRev`, EXT_RS
P3(e)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace CoordReg

open RegSample

/-- Two maps agreeing on `ℍ` give the same coordinate change at any measure not charging `ℍᶜ`. -/
theorem coordChange_congr_of_eqOn_H (x : FieldSample) {f g : ℂ → ℂ} (hfg : EqOn f g H) (Q : ℝ)
    {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ H) :
    coordChange x f Q μ = coordChange x g Q μ := by
  have hmap : μ.map f = μ.map g := Measure.map_congr (hμ.mono fun z hz => hfg hz)
  have hder : ∀ z ∈ H, deriv f z = deriv g z := fun z hz =>
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hfg)
  unfold coordChange
  rw [hmap]
  congr 2
  exact integral_congr_ae (hμ.mono fun z hz => by simp only [hder z hz])

theorem coordChange_fc_congr (x : FieldSample) {f g : ℂ → ℂ} (hfg : EqOn f g H) (Q : ℝ) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    coordChange x f Q (foldedCircle c r) = coordChange x g Q (foldedCircle c r) :=
  coordChange_congr_of_eqOn_H x hfg Q (TwoPoint.foldedCircle_ae_mem_H c hr)

theorem avgReg_coordChange_congr (x : FieldSample) {f g : ℂ → ℂ} (hfg : EqOn f g H) (Q : ℝ)
    (k : ℕ) (z : ℂ) :
    avgReg (coordChange x f Q) k z = avgReg (coordChange x g Q) k z := by
  have h : ∀ c : ℂ, coordChange x f Q (foldedCircle c (radius k)) =
      coordChange x g Q (foldedCircle c (radius k)) := fun c =>
    coordChange_fc_congr x hfg Q c (radius_pos k)
  unfold avgReg
  simp only [h]

theorem isRegularWith_coordChange_congr (x : FieldSample) {f g : ℂ → ℂ} (hfg : EqOn f g H)
    (Q : ℝ) {F : ℂ × ℝ → ℝ} :
    IsRegularWith (coordChange x f Q) F ↔ IsRegularWith (coordChange x g Q) F := by
  have h : ∀ (c : ℂ) (k : ℕ), coordChange x f Q (foldedCircle c (radius k)) =
      coordChange x g Q (foldedCircle c (radius k)) := fun c k =>
    coordChange_fc_congr x hfg Q c (radius_pos k)
  unfold IsRegularWith
  simp only [h]

theorem evalReg_coordChange_congr (x : FieldSample) {f g : ℂ → ℂ} (hfg : EqOn f g H) (Q : ℝ)
    (μ : Measure ℂ) :
    evalReg (coordChange x f Q) μ = evalReg (coordChange x g Q) μ := by
  unfold evalReg
  simp only [avgReg_coordChange_congr x hfg Q]

variable {W : ℝ → ℝ} {t : ℝ}

theorem eqOn_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    EqOn (fwdMapInv W t) (revMap (fun s => W (t - s) - W t) t) H := fun _ hw =>
  UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end CoordReg
end QuantumZipper
