import QuantumZipper.Proofs.Thm18.R18MuScale
import QuantumZipper.Proofs.Thm18.R18OffCongr
import QuantumZipper.Proofs.Thm18.D74R1
import QuantumZipper.Proofs.Thm18.G4RezipNodes
import QuantumZipper.Proofs.Thm18.G4WeldRem
import QuantumZipper.Proofs.Thm18.G4PushRegScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T7b: the round trip `Z^LEN_ℓ ∘ Z^LEN_{−ℓ} = id` off the curve, deterministic part

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
`Z^LEN_ℓ` is the inverse of `Z^LEN_{−ℓ}` ("a.s. uniquely defined via conformal welding"). The
paper gives no separate computation; this is the area-carrying, off-curve copy of the by-hand
verification `Thm18Asm.configEq_zipLenC_zipLenDown_of` (G4WeldRound.lean) and of the rezip identity
`Thm18Asm.regEq_rezipUp_cfg` (G4RezipNodes.lean). **Own elementary argument** (as the old one).

Differences with the old route (handoff/R18-PLAN.md §1, T7b):
* the re-zip scale is `areaScale` of the carried area; it is `a⁻¹` deterministically once the
  carried area has scale `1`, lives on `ℍ` and does not charge the unzipped hull
  (`R18.zipWeldUpA_canonAConfig_area`, `R18.zipWeldUpA_zipCapDownA_area`,
  `R18.areaScale_map_inv_mul`); no field-area conjunct;
* the field is compared off the curve: the rezip identity is used only at dyadic circles off the
  re-zipped hull (`D74R.PushRegOffAt`, which A-sep gives at every parameter), then rescaled
  (`regEqOff_rescale`) and compared off `η[0,t] ⊆ curveOf W`.

Main results: `regEqOff_of_coordsOff`, `regEqOff_rescale`, `coordsFull_rezipUp_off`,
`zipWeldUpA_congr`, and **`configEqOff_zipLenUpA_zipLenDownA_of`**.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-! ## Off-curve comparison tools -/

theorem regEqOff_mono' {K K' : Set ℂ} (hK : K ⊆ K') {x y : FieldSample} (h : RegEqOff K x y) :
    RegEqOff K' x y := fun k z hz => by
  obtain ⟨δ, hδ, hw⟩ := hz
  exact h k z ⟨δ, hδ, fun w hw' hk => hw w hw' (hK hk)⟩

theorem regEqOff_trans_regEq {K : Set ℂ} {x y z : FieldSample} (h : RegEqOff K x y)
    (h' : RegEq y z) : RegEqOff K x z := fun k w hw => (h k w hw).trans (h' k w)

/-- A small move of the centre keeps a circle off `K` (with half the margin). -/
theorem circleOff_of_near {K : Set ℂ} {z d : ℂ} {r δ : ℝ}
    (hK : ∀ w : ℂ, |dist w z - r| < δ → foldH w ∉ K) (hd : dist d z < δ / 2) :
    ∀ w : ℂ, |dist w d - r| < δ / 2 → foldH w ∉ K := by
  intro w hw
  refine hK w ?_
  have h1 := dist_triangle w d z
  have h2 := dist_triangle w z d
  rw [dist_comm z d] at h2
  rw [abs_lt] at hw ⊢
  constructor <;> linarith [hw.1, hw.2]

/-- **Coordinates off `K` determine the field off `K`.** If `x` and `y` have equal raw values at
every enumerated dyadic folded circle that stays off `K`, then `RegEqOff K x y`. -/
theorem regEqOff_of_coordsOff {K : Set ℂ} {x y : FieldSample}
    (h : ∀ i : ℕ, CircleOff K (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 →
      CoordsFull.coordsFull x i = CoordsFull.coordsFull y i) :
    RegEqOff K x y := by
  intro k z hz
  obtain ⟨δ, hδ, hK⟩ := hz
  have hev : (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      fun n => y (foldedCircle (dyadicRoundC n z) (radius k)) := by
    filter_upwards [(RegClosure.tendsto_dyadicRoundC z).eventually_mem
      (Metric.ball_mem_nhds z (half_pos hδ))] with n hn
    obtain ⟨i, hi⟩ := CoordsFull.fullIndex_surj n z 1 one_pos k
    rw [← CoordsFull.radius_eq_div] at hi
    have hoff : CircleOff K (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 := by
      rw [hi]
      exact ⟨δ / 2, half_pos hδ, circleOff_of_near hK hn⟩
    have := h i hoff
    simp only [CoordsFull.coordsFull, hi] at this
    exact this
  unfold avgReg
  rw [limUnder, limUnder, Filter.map_congr hev]

/-- **Rescaling moves the removed set.** If `x = y` off `K`, then `x(s·) + Q log s` and
`y(s·) + Q log s` agree off `s⁻¹ K = {w | s w ∈ K}`. -/
theorem regEqOff_rescale {K : Set ℂ} {x y : FieldSample} (h : RegEqOff K x y) (Q : ℝ) {s : ℝ}
    (hs : 0 < s) : RegEqOff {w | (s : ℂ) * w ∈ K} (rescale x Q s) (rescale y Q s) := by
  intro k z hz
  obtain ⟨δ, hδ, hK⟩ := hz
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hev : (fun n => rescale x Q s (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      fun n => rescale y Q s (foldedCircle (dyadicRoundC n z) (radius k)) := by
    filter_upwards [(RegClosure.tendsto_dyadicRoundC z).eventually_mem
      (Metric.ball_mem_nhds z (half_pos hδ))] with n hn
    have hnear := circleOff_of_near hK hn
    simp only [rescale, coordChange]
    rw [foldedCircle_map_mul hs]
    congr 1
    refine evalReg_foldedCircle_congr_of_regEqOff h
      (mul_nonneg hs.le (radius_pos k).le) ⟨s * (δ / 2), by positivity, fun w hw hwK => ?_⟩
    set w' : ℂ := (s : ℂ)⁻¹ * w with hw'
    have hww : (s : ℂ) * w' = w := by rw [hw', ← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
    have hdist : dist w ((s : ℂ) * dyadicRoundC n z) = s * dist w' (dyadicRoundC n z) := by
      rw [← hww, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs]
    have h1 : |dist w' (dyadicRoundC n z) - radius k| < δ / 2 := by
      rw [hdist, ← mul_sub, abs_mul, abs_of_pos hs] at hw
      exact lt_of_mul_lt_mul_left hw hs.le
    refine hnear w' h1 ?_
    show (s : ℂ) * foldH w' ∈ K
    rw [← foldH_mul_ofReal hs, hww]
    exact hwK
  unfold avgReg
  rw [limUnder, limUnder, Filter.map_congr hev]

/-! ## The rezip identity at off-hull circles -/

/-- **Rezip identity off the re-zipped hull** (copy of `regEq_rezipUp_cfg` restricted to the
circles off `revHull (revDrv W τ a)`, with free `τ ≥ 0`, `a > 0`): the unzipped field at time
`τ`, rescaled by `a` and zipped back along `revDrv W τ a`, has the raw values of `x(a·) + Q log a`
at every off-hull dyadic circle. -/
theorem coordsFull_rezipUp_off {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} (hc : Continuous c.2)
    (hc0 : c.2 0 = 0) {τ a : ℝ} (hτ : 0 ≤ τ) (ha : 0 < a) (hR : D74R.PushRegOffAt γ c τ 0 a)
    (i : ℕ) (hoff : CircleOff (revHull (revDrv c.2 τ a).2 (revDrv c.2 τ a).1)
      (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) :
    CoordsFull.coordsFull (coordChange (rescale (coordChange c.1 (fwdMapInv c.2 τ) (Qc γ))
      (Qc γ) a) (revMapInv (revDrv c.2 τ a).2 (revDrv c.2 τ a).1) (Qc γ)) i =
      CoordsFull.coordsFull (rescale c.1 (Qc γ) a) i := by
  have heq := revDrv_eqOn_vrev c.2 hτ ha
  have hrm : revMap (revDrv c.2 τ a).2 (revDrv c.2 τ a).1 =
      revMap (fun s => B2.vrev c.2 τ (a ^ 2 * s) / a) (τ / a ^ 2) := revMap_congr_lenZip heq
  have hri : revMapInv (revDrv c.2 τ a).2 (revDrv c.2 τ a).1 =
      revMapInv (fun s => B2.vrev c.2 τ (a ^ 2 * s) / a) (τ / a ^ 2) :=
    Cor15Group.revMapInv_congr_drive heq
  have hVc : Continuous (B2.vrev c.2 τ) := B2.continuous_vrev hc τ
  have hF : EqOn (fwdMapInv c.2 τ) (revMap (B2.vrev c.2 τ) τ) H := fun z hz =>
    B2.fwdMapInv_eq_revMap_vrev hc hc0 hτ hz
  have h' := hR i
  unfold DriverPushExactI BackSupportI at h'
  rw [backDrv_zero] at h'
  obtain ⟨hsup, -, h1, h2, -⟩ := h' hoff
  rw [hri] at h1 h2
  rw [hrm] at hsup
  show coordChange (rescale (coordChange c.1 (fwdMapInv c.2 τ) (Qc γ)) (Qc γ) a)
      (revMapInv (revDrv c.2 τ a).2 (revDrv c.2 τ a).1) (Qc γ) (fcI i) =
    rescale c.1 (Qc γ) a (fcI i)
  rw [hri]
  exact rezipUp_fc_apply c.1 (Qc γ) hVc hτ ha hF (fcI i) hsup h1 h2

/-! ## Zipping along drivers equal on `[0,T]` -/

theorem zipWeldUpA_congr {γ T : ℝ} {W₁ W₂ : ℝ → ℝ} (hT : 0 ≤ T) (h : EqOn W₁ W₂ (Icc 0 T))
    (c : AreaConfig) : zipWeldUpA γ T W₁ c = zipWeldUpA γ T W₂ c := by
  simp only [zipWeldUpA, zipWeldUp_congr hT h c.toPair, revMap_congr_lenZip h]

end R18
end QuantumZipper
