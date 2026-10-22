import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGMetric.CM.Norm
import HigherDimLQGMetric.Sec8b.CountHolder

/-!
# Radius-ten pin and compactly supported Cameron–Martin shifts (packet Q8b)

The deterministic identity below is the pin-transfer step of NA2 R12.  It is
stated on the natural sphere-average convergence set, then applied almost surely
under the normalized LGF law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem q8b_zero_on_sphere_ten (F : C(Rd d, ℝ))
    (hsupp : tsupport F ⊆ ball (0 : Rd d) 4) :
    ∀ᵐ u ∂(unitSphereProb d), F (0 + (10 : ℝ) • u) = 0 := by
  filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hball := hsupp hmem
  simp only [zero_add, mem_ball, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 10), hu, mul_one] at hball
  norm_num at hball

theorem q8b_pin_addFun_of_tendsto (g : DistRd d)
    (F : C(Rd d, ℝ)) (hsupp : tsupport F ⊆ ball (0 : Rd d) 4)
    {a : ℝ} (ha : Tendsto (sphereAvgSeq g 10 0) atTop (𝓝 a)) :
    pin 10 (addFun g F) = addFun (pin 10 g) F := by
  have hzero : (∫ u, F (0 + (10 : ℝ) • u) ∂(unitSphereProb d)) = 0 :=
    integral_eq_zero_of_ae (q8b_zero_on_sphere_ten F hsupp)
  unfold pin
  rw [sphereAvg_addFun_of_tendsto ha F, hzero, add_zero, addFun_addConst]

theorem q8b_pin_shiftNorm_of_tendsto (hd : 1 ≤ d) (g : DistRd d)
    (F : C(Rd d, ℝ)) (hsupp : tsupport F ⊆ ball (0 : Rd d) 4)
    {a : ℝ} (ha : Tendsto (sphereAvgSeq g 10 0) atTop (𝓝 a)) :
    pin 10 (shiftNorm g F) = addFun (pin 10 g) F := by
  rw [shiftNorm, pin_addConst_of_tendsto hd
    ((tendsto_sphereAvgSeq_addFun_iff g F 10 0 a).2 ha)
    (-(∫ u, F u ∂(unitSphereProb d)))]
  exact q8b_pin_addFun_of_tendsto g F hsupp ha

theorem q8b_pin_shiftNorm_ae (hd : 2 ≤ d) (F : C(Rd d, ℝ))
    (hsupp : tsupport F ⊆ ball (0 : Rd d) 4) :
    ∀ᵐ g ∂(normLGFLaw d),
      pin 10 (shiftNorm g F) = addFun (pin 10 g) F := by
  have hh := (normLGFLaw_spec_holds d hd).2.1
  filter_upwards [hh.1.ae_exists_tendsto_sphereAvgSeq hd (r := 10) (by norm_num) 0] with g hg
  obtain ⟨a, ha⟩ := hg
  exact q8b_pin_shiftNorm_of_tendsto (by omega) g F hsupp ha

theorem q8b_pin_shiftNorm_finite_ae (hd : 2 ≤ d) {ι : Type*}
    (S : Finset ι) (F : ι → C(Rd d, ℝ))
    (hsupp : ∀ i, tsupport (F i) ⊆ ball (0 : Rd d) 4) :
    ∀ᵐ g ∂(normLGFLaw d),
      ∀ i ∈ S, pin 10 (shiftNorm g (F i)) = addFun (pin 10 g) (F i) := by
  classical
  rw [Filter.eventually_all_finset]
  intro i hi
  exact q8b_pin_shiftNorm_ae hd (F i) (hsupp i)

open Classical in
theorem q8b_card_filter_iff {ι : Type*} (S : Finset ι)
    (P Q : ι → Prop) (hPQ : ∀ i ∈ S, P i ↔ Q i) :
    ((S.filter P).card : ℝ) = ((S.filter Q).card : ℝ) := by
  classical
  apply congrArg (fun t : Finset ι => (t.card : ℝ))
  apply Finset.filter_congr
  intro i hi
  exact hPQ i hi

end HigherDimLQGContinuity
