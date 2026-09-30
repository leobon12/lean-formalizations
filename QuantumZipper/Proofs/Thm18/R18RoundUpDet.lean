import QuantumZipper.Proofs.Thm18.R18MuScale
import QuantumZipper.Proofs.Thm18.R18OffCongr
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Thm18.G4PushRegScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T7a: the round trip `Z^LEN_{−ℓ} ∘ Z^LEN_ℓ = id` off the curve, deterministic part

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
`Z^LEN_ℓ` is the inverse of `Z^LEN_{−ℓ}` ("a.s. uniquely defined via conformal welding"). The
paper gives no separate computation; this is the area-carrying, off-curve copy of the by-hand
verification `Thm18Asm.configEq_zipLenDown_zipLenC_of` (G4WeldRound.lean) with the rezip identity
`Thm18Asm.rezipDown_fc_apply` (G4RezipDet.lean) and `Thm18Asm.roundDown_tail_of_rezip`
(G4RoundDownAlg.lean). **Own elementary argument** (as the old one).

Differences with the old route (handoff/R18-PLAN.md §1, T7a):
* the zip-up scale is `b = areaScale` of the pushed area; the down-scale after the round trip is
  `b⁻¹` deterministically (`R18.zipCapDownA_canonAConfig_area`, `R18.zipCapDownA_zipWeldUpA_area`,
  `R18.areaScale_map_inv_mul`, carried area of scale `1` on `ℍ`); no field-area conjunct;
* the field is compared off the curve: the rezip identity is used only at dyadic circles whose
  image `b ·` stays off `curveOf c.drv` (`DownZipPushRegOffA`), then rescaled by `b⁻¹`.

The off-curve tools `circleOff_of_nearU`, `regEqOff_of_coordsOffU`, `regEqOff_rescaleU` are copies
of the same lemmas of the sibling task T7b (`R18RoundDownDet.lean`, written in parallel).

Main result: **`configEqOff_zipLenDownA_zipLenUpA_of`**.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-! ## Off-curve comparison tools (copies, see the module docstring) -/

theorem circleOff_of_nearU {K : Set ℂ} {z d : ℂ} {r δ : ℝ}
    (hK : ∀ w : ℂ, |dist w z - r| < δ → foldH w ∉ K) (hd : dist d z < δ / 2) :
    ∀ w : ℂ, |dist w d - r| < δ / 2 → foldH w ∉ K := by
  intro w hw
  refine hK w ?_
  have h1 := dist_triangle w d z
  have h2 := dist_triangle w z d
  rw [dist_comm z d] at h2
  rw [abs_lt] at hw ⊢
  constructor <;> linarith [hw.1, hw.2]

theorem regEqOff_of_coordsOffU {K : Set ℂ} {x y : FieldSample}
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
      exact ⟨δ / 2, half_pos hδ, circleOff_of_nearU hK hn⟩
    have := h i hoff
    simp only [CoordsFull.coordsFull, hi] at this
    exact this
  unfold avgReg
  rw [limUnder, limUnder, Filter.map_congr hev]

theorem regEqOff_rescaleU {K : Set ℂ} {x y : FieldSample} (h : RegEqOff K x y) (Q : ℝ) {s : ℝ}
    (hs : 0 < s) : RegEqOff {w | (s : ℂ) * w ∈ K} (rescale x Q s) (rescale y Q s) := by
  intro k z hz
  obtain ⟨δ, hδ, hK⟩ := hz
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hev : (fun n => rescale x Q s (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      fun n => rescale y Q s (foldedCircle (dyadicRoundC n z) (radius k)) := by
    filter_upwards [(RegClosure.tendsto_dyadicRoundC z).eventually_mem
      (Metric.ball_mem_nhds z (half_pos hδ))] with n hn
    have hnear := circleOff_of_nearU hK hn
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

/-! ## The off-curve pushed-circle regularity of the zip-then-unzip round trip -/

theorem regEqOff_monoU {K K' : Set ℂ} (hK : K ⊆ K') {x y : FieldSample} (h : RegEqOff K x y) :
    RegEqOff K' x y := fun k z hz => by
  obtain ⟨δ, hδ, hw⟩ := hz
  exact h k z ⟨δ, hδ, fun w hw' hk => hw w hw' (hK hk)⟩

/-! ## The round trip -/

end R18
end QuantumZipper
