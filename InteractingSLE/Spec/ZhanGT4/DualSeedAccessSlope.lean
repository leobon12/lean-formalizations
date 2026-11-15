/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessMap

/-!
# Divided differences along the opposite image flow

Packet PROVE-ZHAN-GT4-A22. The derivative equation for a divided difference
holds at coincident fixed coordinates as well as distinct ones. These are the
unrenormalized numerators of (D13)--(D15) in the opposite time direction.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)

/-- The real space derivative of an alive hydrodynamic image map is its
complex derivative's real part. -/
theorem hasDerivAt_frzImg_real {U b : ℝ → ℝ} (hU : Continuous U)
    {v H t : ℝ} {q : ℝ → ℂ} (hq : IsForwardSol U (v : ℂ) H q)
    (ht : b t ∈ Icc (0 : ℝ) H) :
    HasDerivAt (fun x => frzImg U b x t) (frzImgD U b v t) v := by
  have hH : 0 ≤ H := ht.1.trans ht.2
  obtain ⟨δ, hδ, hlow, hv⟩ := exists_aliveDisc_self hq hH
  have hd := hasDerivAt_fwdMap_aliveDisc hU hq hδ hlow hv ht
  have hr := (hd.differentiableAt.hasDerivAt.add_const ((U (b t) : ℝ) : ℂ)).real_of_complex
  simpa only [frzImg, frzImgD, Complex.add_re, Complex.ofReal_re] using hr

namespace OwnData

variable {W U b : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ}
    (h : OwnData W A φ T b U)
include h

/-- The image-map divided difference has positive value, also on the diagonal.
Both coordinates need only be alive in the image chart. -/
theorem dslope_frzImg_pos {u v : ℝ} {q r : ℝ → ℂ}
    (hq : IsForwardSol U (u : ℂ) (b T) q)
    (hr : IsForwardSol U (v : ℂ) (b T) r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    0 < dslope (fun x => frzImg U b x t) u v := by
  have hbt := h.mapsTo_clock ht
  have hH : 0 ≤ b T := (h.mapsTo_clock ⟨h.pos.le, le_rfl⟩).1
  rcases lt_trichotomy u v with huv | rfl | hvu
  · have ho := QuantumZipper.F1.isForwardSol_lt_of_lt hH huv hq hr (b t) hbt
    rw [dslope_of_ne _ huv.ne', slope_def_field]
    apply div_pos _ (sub_pos.2 huv)
    simp only [frzImg, fwdMap_eq_of_isForwardSol h.contW' hr hbt,
      fwdMap_eq_of_isForwardSol h.contW' hq hbt]
    linarith only [ho]
  · rw [dslope_same, (hasDerivAt_frzImg_real h.contW' hq hbt).deriv]
    exact (deriv_fwdMap_real h.contW' hq hbt).2
  · have ho := QuantumZipper.F1.isForwardSol_lt_of_lt hH hvu hr hq (b t) hbt
    rw [dslope_of_ne _ hvu.ne, slope_def_field]
    apply div_pos_of_neg_of_neg _ (sub_neg.2 hvu)
    simp only [frzImg, fwdMap_eq_of_isForwardSol h.contW' hr hbt,
      fwdMap_eq_of_isForwardSol h.contW' hq hbt]
    linarith only [ho]

/-- Opposite-time evolution of a divided difference, including coincident
seed accesses. No division by their initial gap remains in the rate. -/
theorem hasDerivWithinAt_dslope_frzImg {u v : ℝ} {q r : ℝ → ℂ}
    (hq : IsForwardSol U (u : ℂ) (b T) q)
    (hr : IsForwardSol U (v : ℂ) (b T) r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun y => dslope (fun x => frzImg U b x y) u v)
      (-2 * frzA W U b φ 1 t ^ 2 * dslope (fun x => frzImg U b x t) u v /
        ((frzImg U b u t - frzA W U b φ 0 t) *
          (frzImg U b v t - frzA W U b φ 0 t))) (Icc 0 T) t := by
  rcases eq_or_ne v u with rfl | hne
  · have he (y : ℝ) (hy : y ∈ Icc (0 : ℝ) T) :
        frzImgD U b v y = dslope (fun x => frzImg U b x y) v v := by
      rw [dslope_same, (hasDerivAt_frzImg_real h.contW' hq (h.mapsTo_clock hy)).deriv]
    have hd := (h.hasDerivWithinAt_frzImgD hq ht).congr (fun y hy => (he y hy).symm) (he t ht).symm
    simpa only [he t ht, pow_two] using hd
  · have hd := ((h.hasDerivWithinAt_frzImg hr ht).sub
        (h.hasDerivWithinAt_frzImg hq ht)).div_const (v - u)
    have he (y : ℝ) : (frzImg U b v y - frzImg U b u y) / (v - u) =
        dslope (fun x => frzImg U b x y) u v := by
      rw [dslope_of_ne _ hne, slope_def_field]
    have hd' := hd.congr (fun y _ => (he y).symm) (he t).symm
    refine hd'.congr_deriv ?_
    rw [dslope_of_ne _ hne, slope_def_field]
    have hq0 := h.frzImg_sub_ne_zero hq ht
    have hr0 := h.frzImg_sub_ne_zero hr ht
    field_simp [hq0, hr0, sub_ne_zero.2 hne]
    ring

end OwnData
end InteractingSLE.ZhanGT4
