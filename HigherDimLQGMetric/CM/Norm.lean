import HigherDimLQGMetric.CM.Direction
import HigherDimLQGMetric.Sphere.Conv

/-! The additive normalization of a Cameron–Martin shift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The mean-zero pairings do not see the additive normalization. -/
theorem pair0Rd_shiftNorm (g : DistRd d) (F : C(Rd d, ℝ)) :
    pair0Rd (shiftNorm g F) = pair0Rd (addFun g F) := by
  funext φ
  exact addConst_apply_testRd0 (addFun g F) _ φ

/-- A shifted distribution with a convergent sphere average has zero unit-sphere average. -/
theorem sphereAvg_shiftNorm_zero (hd : 1 ≤ d) {g : DistRd d} (hg : g ∈ convSet d)
    (hzero : sphereAvg g 1 0 = 0) (F : C(Rd d, ℝ)) :
    sphereAvg (shiftNorm g F) 1 0 = 0 := by
  have hlim : Tendsto (sphereAvgSeq g 1 0) atTop (𝓝 (sphereAvg g 1 0)) :=
    tendsto_sphereAvgSeq_sphereAvg hg
  have hlimF : Tendsto (sphereAvgSeq (addFun g F) 1 0) atTop
      (𝓝 (sphereAvg g 1 0 + ∫ u, F u ∂(unitSphereProb d))) := by
    convert (tendsto_sphereAvgSeq_addFun_iff g F 1 0 (sphereAvg g 1 0)).2 hlim using 2;
      simp
  rw [shiftNorm, sphereAvg_addConst_of_tendsto hd hlimF,
    sphereAvg_addFun_of_tendsto hlim, hzero]
  simp

theorem shiftNorm_mem_convSet (hd : 1 ≤ d) {g : DistRd d} (hg : g ∈ convSet d)
    (F : C(Rd d, ℝ)) : shiftNorm g F ∈ convSet d := by
  obtain ⟨a, ha⟩ := hg
  have hb := (tendsto_sphereAvgSeq_addFun_iff g F 1 0 a).2 ha
  refine ⟨a + (∫ u, F u ∂(unitSphereProb d)) -
    (∫ u, F u ∂(unitSphereProb d)), ?_⟩
  have hc := hb.add_const (-(∫ u, F u ∂(unitSphereProb d)))
  have he : sphereAvgSeq (shiftNorm g F) 1 0 =
      fun n => sphereAvgSeq (addFun g F) 1 0 n - ∫ u, F u ∂(unitSphereProb d) := by
    funext n
    simp only [shiftNorm, sphereAvgSeq_addConst hd, sub_eq_add_neg]
  rw [he]
  simpa only [zero_add, one_smul, sub_eq_add_neg] using hc

/-- Reconstruct the sphere-normalized representative from its mean-zero pairings. -/
def cmNormRetract (d : ℕ) (g : DistRd d) : DistRd d :=
  addConst (recenter (bumpTest 0 (0 : Rd d)) g)
    (-sphereAvg (recenter (bumpTest 0 (0 : Rd d)) g) 1 0)

theorem measurable_cmNormRetract_sigma0 :
    Measurable[sigma0 d] (cmNormRetract d) := by
  have hK : Measurable (fun g : DistRd d => addConst g (-sphereAvg g 1 0)) :=
    Measurable.addConst measurable_id (measurable_sphereAvg_left 1 0).neg
  exact hK.comp (measurable_recenter_sigma0 integral_bumpTest_zero)

theorem cmNormRetract_eq_self (hd : 1 ≤ d) {g : DistRd d} (hg : g ∈ convSet d)
    (hn : sphereAvg g 1 0 = 0) : cmNormRetract d g = g := by
  unfold cmNormRetract recenter
  rw [sphereAvg_addConst_of_mem_convSet hd hg, addConst_addConst, hn]
  simp only [zero_add, neg_neg, neg_add_cancel, addConst_zero]

/-- Every measurable event of a normalized field is a mean-zero-pairing event on the
convergence set. -/
theorem exists_pair0_event_of_normalized (hd : 1 ≤ d) (A : Set (DistRd d))
    (hA : MeasurableSet A) :
    ∃ A0 : Set (TestRd0 d → ℝ), MeasurableSet A0 ∧
      ∀ g : DistRd d, g ∈ convSet d → sphereAvg g 1 0 = 0 →
        (g ∈ A ↔ pair0Rd g ∈ A0) := by
  have hS : MeasurableSet[sigma0 d] ((cmNormRetract d) ⁻¹' A) :=
    hA.preimage measurable_cmNormRetract_sigma0
  obtain ⟨A0, hA0, he⟩ := hS
  refine ⟨A0, hA0, fun g hg hn => ?_⟩
  have hmem : g ∈ (cmNormRetract d) ⁻¹' A ↔ pair0Rd g ∈ A0 := by
    change g ∈ cmNormRetract d ⁻¹' A ↔ g ∈ ev0 ⁻¹' A0
    rw [he]
  simpa only [Set.mem_preimage, cmNormRetract_eq_self hd hg hn] using hmem

end HigherDimLQGMetric
