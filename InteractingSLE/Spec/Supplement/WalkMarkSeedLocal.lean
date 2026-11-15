/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFreshRecordMain

/-! # Both seed heights at an untouched exterior point -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkMarkSeed

open Exist Exist.Staged Exist.StagedLaw Restart
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- A continuous increasing local chart that reads the boundary word away
from the finite marked sets preserves both one-sided heights. -/
theorem seed_limits_of_local_transport {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (β : BoundaryWord)
    {m : ℝ → ℝ} {U : Set ℝ} {w : ℝ} (hU : U ∈ 𝓝 w) (hm : StrictMonoOn m U)
    (hc : ContinuousAt m w)
    (hO : ∀ x ∈ U, x ∉ jumps → m x ∉ β.jumps → β.fn (m x) = b x) :
    leftLim β.fn (m w) = leftLim b w ∧ rightLim β.fn (m w) = rightLim b w := by
  have hw : w ∈ U := mem_of_mem_nhds hU
  have hUe : ∀ᶠ x in 𝓝 w, x ∈ U := hU
  have hUL : ∀ᶠ x in 𝓝[<] w, x ∈ U := hUe.filter_mono nhdsWithin_le_nhds
  have hUR : ∀ᶠ x in 𝓝[>] w, x ∈ U := hUe.filter_mono nhdsWithin_le_nhds
  have hmL : Tendsto m (𝓝[<] w) (𝓝[<] (m w)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hUL, self_mem_nhdsWithin] with x hx hlt
    exact hm hx hw hlt
  have hmR : Tendsto m (𝓝[>] w) (𝓝[>] (m w)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hUR, self_mem_nhdsWithin] with x hx hgt
    exact hm hw hx hgt
  have avoidL (J : Finset ℝ) (a : ℝ) : ∀ᶠ x in 𝓝[<] a, x ∉ J :=
    (GW1W.eventually_notMem_of_finite J.finite_toSet a).filter_mono
      (nhdsWithin_mono a fun x (hx : x < a) => ne_of_lt hx)
  have avoidR (J : Finset ℝ) (a : ℝ) : ∀ᶠ x in 𝓝[>] a, x ∉ J :=
    (GW1W.eventually_notMem_of_finite J.finite_toSet a).filter_mono
      (nhdsWithin_mono a fun x (hx : a < x) => ne_of_gt hx)
  constructor
  · obtain ⟨lo, hlo, hβ⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim
      β.isPiecewiseConstantBoundaryData (m w)
    obtain ⟨lo', hlo', hb'⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim hb w
    have hβe : ∀ᶠ z in 𝓝[<] (m w), β.fn z = leftLim β.fn (m w) := by
      filter_upwards [Ioo_mem_nhdsLT hlo] with z hz using hβ z hz
    have hbe : ∀ᶠ x in 𝓝[<] w, b x = leftLim b w := by
      filter_upwards [Ioo_mem_nhdsLT hlo'] with x hx using hb' x hx
    have he : ∀ᶠ _x in 𝓝[<] w, leftLim β.fn (m w) = leftLim b w := by
      filter_upwards [hUL, hmL.eventually hβe, hbe, avoidL jumps w,
        hmL.eventually (avoidL β.jumps (m w))] with x hx hβx hbx hxJ hmxJ
      exact hβx.symm.trans ((hO x hx hxJ hmxJ).trans hbx)
    exact eventually_const.1 he
  · obtain ⟨hi, hhi, hβ⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim
      β.isPiecewiseConstantBoundaryData (m w)
    obtain ⟨hi', hhi', hb'⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb w
    have hβe : ∀ᶠ z in 𝓝[>] (m w), β.fn z = rightLim β.fn (m w) := by
      filter_upwards [Ioo_mem_nhdsGT hhi] with z hz using hβ z hz
    have hbe : ∀ᶠ x in 𝓝[>] w, b x = rightLim b w := by
      filter_upwards [Ioo_mem_nhdsGT hhi'] with x hx using hb' x hx
    have he : ∀ᶠ _x in 𝓝[>] w, rightLim β.fn (m w) = rightLim b w := by
      filter_upwards [hUR, hmR.eventually hβe, hbe, avoidR jumps w,
        hmR.eventually (avoidR β.jumps (m w))] with x hx hβx hbx hxJ hmxJ
      exact hβx.symm.trans ((hO x hx hxJ hmxJ).trans hbx)
    exact eventually_const.1 he

/-- Recentering the word at a point strictly beyond either old record
reads both original one-sided heights at that point. -/
theorem seed_limits_shift_of_gInv {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : GW2aConn.GInv b jumps β s) {w : ℝ} (hw : stRecR s < w ∨ w < stRecL s) :
    leftLim (BoundaryWord.shiftW (rProf (stChart s) w) β).fn 0 = leftLim b w ∧
      rightLim (BoundaryWord.shiftW (rProf (stChart s) w) β).fn 0 = rightLim b w := by
  have he : (BoundaryWord.shiftW (rProf (stChart s) w) β).fn =
      fun y => β.fn (y + rProf (stChart s) w) := funext (BoundaryWord.fn_shiftW _ _)
  rw [he, leftLim_comp_add, rightLim_comp_add, zero_add]
  rcases hw with hw | hw
  · exact seed_limits_of_local_transport hb β (Ioi_mem_nhds hw) hI.2.1.1.1
      (hI.2.1.1.2.1.continuousAt (Ioi_mem_nhds hw)) hI.2.2.2.1
  · exact seed_limits_of_local_transport hb β (Iio_mem_nhds hw)
      (GW2aConn.strictMonoOn_of_lProf hI.2.2.1.1.1)
      ((GW2aConn.continuousOn_rProf_of_lProf hI.2.2.1.1.2.1).continuousAt (Iio_mem_nhds hw))
      hI.2.2.2.2.1

theorem admissible_shift_of_gInv {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {s : ExplState}
    (hI : GW2aConn.GInv b jumps β s) {w : ℝ} (hw : stRecR s < w ∨ w < stRecL s)
    (ha : ExplState.IsAdmissibleSeed κ (leftLim b w) (rightLim b w) θ) :
    ExplState.IsAdmissibleSeed κ (leftLim (BoundaryWord.shiftW (rProf (stChart s) w) β).fn 0)
      (rightLim (BoundaryWord.shiftW (rProf (stChart s) w) β).fn 0) θ := by
  obtain ⟨hL, hR⟩ := seed_limits_shift_of_gInv hb hI hw
  rwa [hL, hR]

end InteractingSLE.Theorem14.WalkMarkSeed
