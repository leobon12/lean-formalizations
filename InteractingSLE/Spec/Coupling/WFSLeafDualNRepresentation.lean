/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDualNRiesz

/-! # Extension of bounded L² representatives to L¹ -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.WFS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Integration against an essentially bounded function is continuous on L¹. -/
def boundedL1Pairing {h : Ω → ℝ} (hm : AEStronglyMeasurable h P)
    {K : ℝ} (hb : ∀ᵐ x ∂P, ‖h x‖ ≤ K) : Lp ℝ 1 P →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, h x * f x ∂P
      map_add' := fun f g => by
        calc
          (∫ x, h x * (f + g) x ∂P) = ∫ x, h x * f x + h x * g x ∂P := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with x hx
            rw [hx, Pi.add_apply, mul_add]
          _ = _ := integral_add ((L1.integrable_coeFn f).bdd_mul hm hb)
            ((L1.integrable_coeFn g).bdd_mul hm hb)
      map_smul' := fun c f => by
        change (∫ x, h x * (c • f) x ∂P) = c * (∫ x, h x * f x ∂P)
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
        ring }
    K (fun f => by
      change ‖∫ x, h x * f x ∂P‖ ≤ K * ‖f‖
      rw [L1.norm_eq_integral_norm, ← integral_const_mul]
      apply norm_integral_le_of_norm_le ((L1.integrable_coeFn f).norm.const_mul K)
      filter_upwards [hb] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Real L¹–L∞ duality for a probability measure, including the a.e. norm bound. -/
theorem exists_bounded_l1_representative (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 1 P →L[ℝ] ℝ) :
    ∃ h : Ω → ℝ, AEStronglyMeasurable h P ∧ (∀ᵐ x ∂P, ‖h x‖ ≤ ‖L‖) ∧
      ∀ (f : Ω → ℝ) (hf : Integrable f P), (∫ x, h x * f x ∂P) = L (hf.toL1 f) := by
  obtain ⟨h, hr, hb⟩ := exists_bounded_l2_representative P L
  let T := boundedL1Pairing (Lp.aestronglyMeasurable h) hb
  have he : ∀ f : Lp ℝ 1 P, T f = L f := by
    apply Lp.induction ENNReal.one_ne_top (fun f => T f = L f)
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst]
      let f := indicatorConstLp 2 hs hμs.ne c
      have hf : l2ToL1 P f = indicatorConstLp 1 hs hμs.ne c := by
        apply Lp.ext
        exact (coeFn_l2ToL1 P f).trans
          (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)
      rw [← hf]
      change (∫ x, h x * (l2ToL1 P f) x ∂P) = L (l2ToL1 P f)
      calc
        (∫ x, h x * (l2ToL1 P f) x ∂P) = ∫ x, h x * f x ∂P := by
          apply integral_congr_ae
          filter_upwards [coeFn_l2ToL1 P f] with x hx
          rw [hx]
        _ = _ := hr f
    · intro f g _ _ _ hf hg
      rw [map_add, map_add, hf, hg]
    · exact isClosed_eq T.continuous L.continuous
  refine ⟨h, Lp.aestronglyMeasurable h, hb, fun f hf => ?_⟩
  rw [← he (hf.toL1 f)]
  change (∫ x, h x * f x ∂P) = ∫ x, h x * hf.toL1 f x ∂P
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1] with x hx
  rw [hx]

end InteractingSLE.WFS
