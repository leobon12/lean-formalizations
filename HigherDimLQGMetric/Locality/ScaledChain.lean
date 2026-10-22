import HigherDimLQGMetric.Locality.FieldLaw
import HigherDimLQGMetric.Locality.FromInside

/-! Identification of the normalized metric in the marked law with the
Borel chain metric used by the locality interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_chainInf_smul {d : ℕ} (D : ContMetric d)
    (hD : D.IsLength) (c : ℝ) (hc : 0 < c)
    {U : Set (Rd d)} (hU : IsOpen U) (u v : Rd d) :
    (D.smul c hc).chainInf U u v =
      ENNReal.ofReal c * D.chainInf U u v := by
  rw [← (D.smul c hc).internal_eq_chainInf
      (ContMetric.isLength_smul hc hD) hU u v,
    ContMetric.internal_smul hc,
    D.internal_eq_chainInf hD hU]

theorem l7a_metricLift_original {d : ℕ} (D : ContMetric d) :
    l7a_metricLift D.1 = D := by
  exact Subtype.ext (l7a_metricLift_val D.2)

theorem l7a_normalizedMarked_chain_original
    {d : ℕ} (ξ : ℝ) (g : DistRd d) (D : ContMetric d)
    (ρ : ℝ) (z₀ : Rd d) (F : C(Rd d, ℝ))
    (hD : D.IsLength) (U : TopologicalSpace.Opens (Rd d))
    (u v : Rd d) :
    (l7a_normalizedMarkedMetric ξ
      ((pairJ ⊤ g, (sphereAvg g ρ z₀, F)), D.1)).chainInf U u v =
      l7b_chainFam ξ (fun _ : Unit => g) (fun _ => D) ρ z₀ () U u v := by
  dsimp [l7a_normalizedMarkedMetric, l7b_chainFam, l7b_scale]
  rw [l7a_metricLift_original]
  simpa only [mul_neg, neg_mul] using
    l7a_chainInf_smul D hD _ (Real.exp_pos _) U.isOpen u v

end HigherDimLQGMetric
