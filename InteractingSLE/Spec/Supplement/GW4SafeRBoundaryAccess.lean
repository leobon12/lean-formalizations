/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryInputs

/-!
# GW4: inverse boundary access from the actual relative hulls

Every finite relative hull of a good frame is the filling of a continuous
prefix of its existing driven curve. The landed Carathéodory extension theorem
therefore supplies the inverse extension for every version of that hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Rel Sec7.PocketTraversal Sec7.PocketStopSide

/-- A version's inverse has continuous boundary values whenever its finite
hull is one of the actual relative hulls of the good frame. -/
theorem Frame.exists_inverse_extension_of_hullAt {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {R : ℝ → ℝ}
    (hR : Continuous R) (hR0 : R 0 = 0) {q t : ℝ≥0}
    (he : fwdHull R q = F.hullAt w t) :
    ∃ Fb : ℂ → ℂ, EqOn Fb (fwdMapInv R q) H ∧ ContinuousOn Fb Hbar := by
  have hb : Bornology.IsBounded (F.hullAt w t) :=
    he ▸ (isHPHull_fwdHull hR q.coe_nonneg).2.1
  have ht := Frame.lt_exit_of_isBounded hF hw hb
  obtain ⟨T, htT, hloc⟩ := Frame.exists_isLoc_gt hF hw ht
  let t' := max t (F.ent w)
  have hA : F.hullAt w t = F.hullAt w t' := by
    rcases le_total t (F.ent w) with h | h
    · rw [Frame.hullAt_eq_empty_of_le hF hw h,
        Frame.hullAt_eq_empty_of_le hF hw (max_le h le_rfl)]
    · change F.hullAt w t = F.hullAt w (max t (F.ent w))
      rw [max_eq_left h]
  have ht'T : t' < T := max_lt htT hloc.2.1
  obtain ⟨v, hv, heq⟩ := Frame.exists_ent_add_clockOf_eq
    (T := T) (w := w) (le_max_right t (F.ent w)) ht'T
  have hfill : fwdHull R q = fillH (F.curve w T '' Icc 0 v) := by
    rw [Frame.fillH_curve hF hloc hv, heq]
    exact he.trans hA
  obtain ⟨Fb, hFb, hFbc, -⟩ := exists_inverse_extension_of_filling hR hR0
    ((Frame.isDrivenCurve_curve hF hloc).continuousOn.mono Icc_subset_Ici_self) hfill
  exact ⟨Fb, hFb, hFbc⟩

/-- The original path-rule version assumptions supply inverse boundary
extensions at all live relative times on one full-measure event. -/
theorem ae_inverse_extension_of_relVersion {Ω : Type*} [MeasurableSpace Ω]
    {F : Frame} (hF : F.IsOk) {ν : Measure Ω} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V) :
    ∀ᵐ ω ∂ν, ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ Fb : ℂ → ℂ, EqOn Fb (fwdMapInv (fun r => R r.toNNReal ω) q) H ∧
        ContinuousOn Fb Hbar := by
  filter_upwards [hGTae, hver.1.1.2.2.2.2] with ω hω hHull q hq
  obtain ⟨t, ht⟩ := hHull q hq
  exact Frame.exists_inverse_extension_of_hullAt hF (hGT ω hω)
    ((hver.1.1.2.1 ω).comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hver.1.1.2.2.1 ω) ht

end InteractingSLE.Theorem14.GW4Fix
