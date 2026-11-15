/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonHigh

/-!
# Finite chart operations preserve the inherited normalization

The actual lifts in `Chart.id`, `Chart.recenter`, and `Chart.loewner` have
zero limit at imaginary infinity. No branch correction is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H fwdMapInv logDerivFwd)

namespace InteractingSLE.Theorem14.WalkIntCanon

theorem isNormalized_id : IsNormalized Chart.id := by
  refine ⟨Chart.isConformal_id, WalkNorm.hasDerivLift_id, ⟨0, ?_⟩, ?_⟩
  · intro z _
    change ‖z - z‖ ≤ 0
    simp
  · exact tendsto_const_nhds

theorem IsNormalized.recenter {c : Chart} (h : IsNormalized c) (a : ℝ) :
    IsNormalized (c.recenter a) := by
  have haH : MapsTo (fun z : ℂ => z + a) H H := by
    intro z hz
    simpa only [QuantumZipper.H, mem_ofPred_eq, add_im, ofReal_im, add_zero] using hz
  have hhigh : Tendsto (fun z : ℂ => z + a) highHalfPlane highHalfPlane :=
    tendsto_highHalfPlane_of_bound haH (M := |a|) fun z _ => by simp
  obtain ⟨M, hM⟩ := h.inverse_bound
  refine ⟨h.conformal.recenter a, WalkNorm.HasDerivLift.recenter h.derivLift a,
    ⟨M + |a|, ?_⟩, h.lift_limit.comp hhigh⟩
  intro z hz
  change ‖c.2.1 (z + a) - z‖ ≤ M + |a|
  calc
    _ ≤ ‖c.2.1 (z + a) - (z + a)‖ + ‖(z + a) - z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ M + |a| := by simpa using add_le_add_right (hM _ (haH hz)) |a|

theorem IsNormalized.loewner {c : Chart} (h : IsNormalized c)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsNormalized (c.loewner W t) := by
  have hFH : MapsTo (fwdMapInv W t) H H := fun z hz =>
    QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hz
  obtain ⟨N, hN⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ht
  have hhigh : Tendsto (fwdMapInv W t) highHalfPlane highHalfPlane :=
    tendsto_highHalfPlane_of_bound hFH hN
  have hlog : Tendsto (fun z => logDerivFwd W t (fwdMapInv W t z))
      highHalfPlane (𝓝 0) :=
    (tendsto_canonicalLog_of_im_atTop (isHPHull_fwdHull hW ht)
      (isMapOut_fwdMap hW hW0 ht)
      (Sec7.ReverseArc.isCanonicalDerivLog_logDerivFwd hW hW0 ht)
      tendsto_im_highHalfPlane).comp hhigh
  have him : Tendsto (fun z => (logDerivFwd W t (fwdMapInv W t z)).im)
      highHalfPlane (𝓝 0) := by
    simpa only [Function.comp_def, zero_im] using
      continuous_im.continuousAt.tendsto.comp hlog
  obtain ⟨M, hM⟩ := h.inverse_bound
  refine ⟨h.conformal.loewner hW hW0 ht,
    WalkNorm.HasDerivLift.loewner h.conformal h.derivLift hW hW0 ht,
    ⟨M + N, ?_⟩, ?_⟩
  · intro z hz
    change ‖c.2.1 (fwdMapInv W t z) - z‖ ≤ M + N
    exact (norm_sub_le_norm_sub_add_norm_sub _ (fwdMapInv W t z) _).trans
      (add_le_add (hM _ (hFH hz)) (hN _ hz))
  · have hsum := him.add (h.lift_limit.comp hhigh)
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_mem_highHalfPlane] with z hz
    change (logDerivFwd W t (fwdMapInv W t z)).im +
      c.2.2 (c.2.1 (fwdMapInv W t z)) =
      (logDerivFwd W t (c.1 (c.2.1 (fwdMapInv W t z)))).im +
        c.2.2 (c.2.1 (fwdMapInv W t z))
    rw [h.conformal.2.2 _ (hFH hz)]

end InteractingSLE.Theorem14.WalkIntCanon
