import HigherDimLQGMetric.ShellDec.Functional
import HigherDimLQGMetric.ShellDec.Sigma
import HigherDimLQGMetric.B3.Interfaces
import LQGMetric.Prob.CondIndepAEDet

/-!
# Recentred shell decoupling for restrictions of distributions

This module transfers G3's functional estimate for mean-zero pairings to the
restriction sigma algebra used by B3. The transfer uses the a.s. convergence
of mollified spherical averages and the standard-Borel representative theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private theorem fieldSigmaRd_le_fieldSigmaOn {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (g : Ω → DistRd d) (U : Opens (Rd d)) :
    fieldSigmaRd g U ≤ fieldSigmaOn g U := by
  have hm : Measurable[fieldSigmaOn g U] (fun ω => restrictTo U (g ω)) := by
    apply (@measurable_distOn_iff d U Ω (fieldSigmaOn g U)
      (fun ω => restrictTo U (g ω))).mpr
    intro φ
    let ψ : {θ : TestRd d // tsupport (θ : Rd d → ℝ) ⊆ U} :=
      ⟨testIncl U φ, by simpa only [coe_testIncl] using φ.tsupport_subset⟩
    have hsrc : Measurable[fieldSigmaOn g U]
        (fun ω (ψ : {θ : TestRd d // tsupport (θ : Rd d → ℝ) ⊆ U}) => g ω ψ.1) :=
      Measurable.of_comap_le le_rfl
    have hp : Measurable[fieldSigmaOn g U] (fun ω => g ω ψ.1) :=
      (measurable_pi_apply ψ).comp hsrc
    simpa only [restrictTo_apply, ψ] using hp
  exact hm.comap_le

private theorem shellOpen_coe_eq_ann {d : ℕ} (z : Rd d) (a b : ℝ) :
    (shellOpen z a b : Set (Rd d)) = ann z a b := by
  rw [ann_eq_ball_diff]
  rfl

private theorem sphere_subset_shellOpen {d : ℕ} (z : Rd d) {a b r : ℝ}
    (ha : a < 1) (hb : 1 < b) (hr : 0 < r) :
    Metric.sphere z r ⊆ (shellOpen z (a * r) (b * r) : Set (Rd d)) := by
  rw [shellOpen_coe_eq_ann]
  intro x hx
  have hxr : ‖x - z‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  change a * r < ‖x - z‖ ∧ ‖x - z‖ < b * r
  rw [hxr]
  exact ⟨(mul_lt_mul_of_pos_right ha hr).trans_eq (one_mul r),
    (one_mul r).symm.trans_lt (mul_lt_mul_of_pos_right hb hr)⟩

/-- Every event of the recentred shell restriction is, modulo a null set,
determined by mean-zero pairings of the original field on the shell. -/
theorem shellBridge_aeDeterminedSigma {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {a b r : ℝ} (ha : a < 1) (hb : 1 < b) (hr : 0 < r) :
    LQGMetric.AEDeterminedSigma
      (fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) r z))
        (shellOpen z (a * r) (b * r)))
      (fieldSigma0 h (ann z (a * r) (b * r))) P := by
  intro E hE
  let U := shellOpen z (a * r) (b * r)
  have hE' : MeasurableSet[fieldSigmaOn
      (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) (ann z (a * r) (b * r))] E := by
    have hle := fieldSigmaRd_le_fieldSigmaOn
      (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) U
    rw [show (U : Set (Rd d)) = ann z (a * r) (b * r) from shellOpen_coe_eq_ann z _ _] at hle
    exact hle E hE
  exact aeEventIn_of_recentred hd hh (isOpen_ann z _ _) hr
    (by simpa only [shellOpen_coe_eq_ann] using sphere_subset_shellOpen z ha hb hr) hE'

/-- B3's shell functional estimate, deduced from G3's mean-zero pairing estimate. -/
theorem shellDecouplingFun_rd : ShellDecouplingFun := by
  intro d hd a b q ha ha1 hb hq hq1
  obtain ⟨K, hK, hbound⟩ := shellDecouplingFun (Nat.le_trans (by omega : 1 ≤ 2) hd)
    a b q ha ha1 hb hq hq1
  refine ⟨K, hK, ?_⟩
  intro Ω mΩ P hProb h hh z r hr hdec I F hFm hFrange
  apply hbound P h hh z r hr hdec I F _ hFrange
  intro i
  have hdet := shellBridge_aeDeterminedSigma hd hh z ha1 hb (hr i)
  have hdetF : LQGMetric.AEDeterminedSigma
      (MeasurableSpace.comap (F i) inferInstance)
      (fieldSigma0 h (ann z (a * r i) (b * r i))) P := by
    intro E hE
    exact hdet E ((hFm i).comap_le E hE)
  exact LQGMetric.exists_ae_eq_measurable_of_aeDeterminedSigma hdetF

end HigherDimLQGMetric
