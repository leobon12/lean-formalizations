import QuantumZipper.Proofs.Thm18.RT6MOTrans2
import QuantumZipper.Proofs.Thm18.RTBeurMass
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Thm18.RT5FarGeo
import QuantumZipper.Proofs.Thm18.R18RTZipMain
import QuantumZipper.Proofs.Thm18.R18RTMask
import QuantumZipper.Proofs.GFF.CircleMeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D87, node N2 proved: at `Z^A_{−ℓ} c₀`, zipping up reads only the pieces

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, p. 26: zipping up re-welds the
two pieces cut out by the curve; the reverse map pulls circles off the new curve back to sets off
the old curve (FarPull, proved at `c₁ = Z^A_{−ℓ} c₀` by RT5: `rt5FarPullStmt_holds`), and the
field of the pieces agrees with the field off the curve (`regEqOff_offConfig`). The regularized
congruence of RT5 (`rt5_zipLenUpA_fld_congr`) is made exact here: the raw circle coordinates of
the rescaled zipped fields are regularized values of the unrescaled ones at scaled circles, which
stay off the scaled curve (`circleOff_scaleRT`), so they agree (`rt6_evalReg_foldedCircle_congr`).
The bookkeeping is an own elementary argument.

Main result: **`zipOffExactUnzAStmt_holds`** (N2 of RT6MOTrans.lean) from X1 and A-sep.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

theorem rt6_foldH_im_nonneg (w : ℂ) : 0 ≤ (foldH w).im := by
  unfold foldH
  split_ifs with h
  · exact h
  · simp only [Complex.conj_im]; linarith [not_le.1 h]

/-- Regularized values at a folded circle off `K` only see the fields off `K`. -/
theorem rt6_evalReg_foldedCircle_congr {K : Set ℂ} {x y : FieldSample} (h : RegEqOff K x y)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hc : CircleOff K z r) :
    evalReg x (foldedCircle z r) = evalReg y (foldedCircle z r) := by
  set K' : Set ℂ := K ∩ {p | 0 ≤ p.im} with hK'
  have h' : RegEqOff K' x y := by
    intro k w hw
    refine h k w ?_
    obtain ⟨δ, hδ, hK⟩ := hw
    exact ⟨δ, hδ, fun v hv hvK => hK v hv ⟨hvK, rt6_foldH_im_nonneg v⟩⟩
  obtain ⟨δ₀, hδ₀, hm⟩ := RTBeur.margin_of_circleOff hc
  refine evalReg_congr_of_regEqOff_far h' hδ₀ ?_
  set S : Set ℂ := {w | 0 ≤ w.im ∧ ∀ p ∈ K', δ₀ ≤ dist w p} with hS
  have hSe : S = {w : ℂ | 0 ≤ w.im} ∩ ⋂ p ∈ K', {w : ℂ | δ₀ ≤ dist w p} := by
    ext w; simp [hS]
  have hSc : IsClosed S := by
    rw [hSe]
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_biInter fun p _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  change ∀ᵐ w ∂((circleUnif z r).map foldH), w ∈ S
  refine (ae_map_iff measurable_foldH.aemeasurable hSc.measurableSet).2 ?_
  filter_upwards [CircleMV.ae_circleUnif z r] with v hv
  show 0 ≤ (foldH v).im ∧ ∀ p ∈ K', δ₀ ≤ dist (foldH v) p
  refine ⟨rt6_foldH_im_nonneg v, fun p hp => ?_⟩
  by_contra hlt
  have hv' : dist (foldH v) z = r ∨ dist (foldH v) (starRingEnd ℂ z) = r := by
    rw [abs_of_pos hr] at hv
    unfold foldH
    split_ifs with hi
    · left; rw [dist_eq_norm]; exact hv
    · right
      rw [← Complex.dist_conj_conj]; simp only [Complex.conj_conj]; rw [dist_eq_norm]
      exact hv
  exact hm (foldH v) hv' p hp.2 (by rw [dist_comm]; exact not_le.1 hlt) hp.1

/-- **Deterministic exact congruence of the zip-up** (masked coordinates and driver): if the pieces
of `c` have the welding driver and area of `c`, the zip scale is positive and FarPull holds at `c`,
then zipping up the pieces and zipping up `c` have the same masked coordinates and driver. -/
theorem rt6_πd_zipLenUpOA_offConfig {γ ℓ : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0)
    (hp : lenWeldDriverO γ (offConfig γ c).fld ℓ = lenWeldDriver γ c.fld ℓ)
    (ha : (offConfig γ c).area = c.area) (hfar : Rt5FarPull γ ℓ c) :
    πd (offData (zipLenUpOA γ ℓ (offConfig γ c)).toPair) =
      πd (offData (zipLenUpA γ ℓ c).toPair) := by
  classical
  obtain ⟨hD, -⟩ := rt6_zipLenUpOA_offConfig_drv_area hp ha
  obtain ⟨hpos, hgeo⟩ := hfar
  have hreg := regEqOff_offConfig γ hc hc0
  set p := lenWeldDriver γ c.fld ℓ with hpdef
  set a := areaScale (zipWeldUpA γ p.1 p.2 c).area with hadef
  set K := curveOf (zipLenUpA γ ℓ c).drv with hKdef
  have e1 : (zipLenUpOA γ ℓ (offConfig γ c)).fld =
      rescale (coordChange (offConfig γ c).fld (revMapInv p.2 p.1) (Qc γ)) (Qc γ) a := by
    simp only [zipLenUpOA, canonAConfig, zipWeldUpA, zipWeldUp, AreaConfig.toPair, hp, ha, hadef]
  have e2 : (zipLenUpA γ ℓ c).fld =
      rescale (coordChange c.fld (revMapInv p.2 p.1) (Qc γ)) (Qc γ) a := rfl
  have h1 : RegEqOff {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K}
      (coordChange (offConfig γ c).fld (revMapInv p.2 p.1) (Qc γ))
      (coordChange c.fld (revMapInv p.2 p.1) (Qc γ)) :=
    regEqOff_coordChange_of_pull (Qc γ) fun d k hck => by
      obtain ⟨δ, hδ, hν⟩ := hgeo d k hck
      exact evalReg_congr_of_regEqOff_far hreg hδ hν
  refine Prod.ext (funext fun i => ?_) ?_
  · have hcur : curveOf (zipLenUpOA γ ℓ (offConfig γ c)).drv = curveOf (zipLenUpA γ ℓ c).drv := by
      rw [hD]
    simp only [πd, offData, lawDataOff]
    by_cases hi : CircleOff (curveOf (zipLenUpA γ ℓ c).toPair.2) (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2
    · have hi' : CircleOff (curveOf (zipLenUpOA γ ℓ (offConfig γ c)).toPair.2)
          (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 := by
        show CircleOff (curveOf (zipLenUpOA γ ℓ (offConfig γ c)).drv) _ _
        rw [hcur]; exact hi
      rw [if_pos hi', if_pos hi]
      have hr := UnzipFull.fullIndex_radius_pos i
      show (zipLenUpOA γ ℓ (offConfig γ c)).fld _ = (zipLenUpA γ ℓ c).fld _
      rw [e1, e2]
      unfold rescale coordChange
      congr 1
      rw [foldedCircle_map_mul hpos]
      exact rt6_evalReg_foldedCircle_congr h1 (mul_pos hpos hr) (circleOff_scaleRT hpos hi)
    · have hi' : ¬ CircleOff (curveOf (zipLenUpOA γ ℓ (offConfig γ c)).toPair.2)
          (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 := by
        show ¬ CircleOff (curveOf (zipLenUpOA γ ℓ (offConfig γ c)).drv) _ _
        rw [hcur]; exact hi
      rw [if_neg hi', if_neg hi]
  · simp only [πd, offData, AreaConfig.toPair]
    rw [hD]

end R18
end QuantumZipper
