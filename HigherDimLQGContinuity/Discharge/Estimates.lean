import HigherDimLQGContinuity.Discharge.Uniform
import HigherDimLQGContinuity.Crude.Ratio
import HigherDimLQGContinuity.MomentsW2.Main
import HigherDimLQGContinuity.ConvTransfer.UpperFinal
import HigherDimLQGContinuity.ConvTransfer.LowerFinal
import HigherDimLQGContinuity.Lemma21.A3
import HigherDimLQGContinuity.Concentration.Main
import HigherDimLQGContinuity.MarginalEuclid.Main
import HigherDimLQGContinuity.Windows.Basic
import HigherDimLQGContinuity.Rotation.Law
import HigherDimLQGContinuity.Frame.Exists
import HigherDimLQGMetric.Frozen.SubcriticalNonempty

/-!
# Discharge of Lemma 2.1 (`UniformEstimates`, I1) and Lemma 5.1 (`MarginalEuclidStmt`, I17) (orchestrator)

The Appendix A chain: CRUDE (A1), W1 (A2), W2 (A3), the uniform DGZ interfaces (U0–U5, `Discharge/Uniform.lean`), the
convolution transfer C1/C2 (A4), Proposition A.3 and the pin step (L4, with L1, L2) give `UniformEstimates d ξbar s` for
every subcritical `ξbar` and `s ∈ [1, 10]`. With the frame (N3), the rotation law (N2), the parameter rate (PARX) and the
concentration (N4), Lemma 5.1 (N5) follows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd IsLFPPKernel)

/-- **I12** (`WNInvCrossShape`, W2), from A3's `wnInvCross` with CRUDE (A1) and U5's interfaces. -/
theorem wnInvCross_holds {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : WNInvCrossShape d κ :=
  wnInvCross hd hκ (crudeLower hd hκ) (uNondeg hd hκ) (uQuantComp hd hκ)

/-- **I13** (C1), from A4's `convUpperMoment`. -/
theorem convUpperMoment_holds {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ConvUpperMomentShape d κ :=
  convUpperMoment hd hκ (wnUpperMoment_holds hd hκ) (uHolderTight hd hκ) (uNondeg hd hκ) (uQuantComp hd hκ)

/-- **I14** (C2), from A4's `convInvCross`. -/
theorem convInvCross_holds {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ConvInvCrossShape d κ :=
  convInvCross hd hκ (wnInvCross_holds hd hκ) (uHolderTight hd hκ) (uNondeg hd hκ) (uQuantComp hd hκ)

/-- **Lemma 2.1 (I1)**: the uniform estimates for every subcritical `ξbar` and every pin `s ∈ [1, 10]`. -/
theorem uniformEstimates_holds {d : ℕ} (hd : 3 ≤ d) {ξbar s : ℝ} (hbar : ξbar ∈ subcritSet d) (hs1 : 1 ≤ s)
    (hs10 : s ≤ 10) : UniformEstimates d ξbar s := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  exact lemma21_of hd hκ (convUpperMoment_holds (by omega) hκ) (convInvCross_holds (by omega) hκ) hbar hs1 hs10

/-- **I20** (`ConcentrationStmt`), from N4's `concentration_of` at a subcritical parameter and the frame of N3. -/
theorem concentration_holds {d : ℕ} (hd : 3 ≤ d) : ConcentrationStmt d := by
  obtain ⟨ξ₀, hξ₀, hsub⟩ := subcritical_nonempty d (by omega)
  have hmem : ξ₀ / 2 ∈ subcritSet d := ⟨half_pos hξ₀, hsub _ ⟨half_pos hξ₀, half_lt_self hξ₀⟩⟩
  exact concentration_of hd hmem.1 hmem.2 (uniformEstimates_holds hd hmem le_rfl (by norm_num))
    (Classical.choice (exists_pairingFrame hd))

/-- **Lemma 5.1 (I17)** (`MarginalEuclidStmt`), from N5's `marginalEuclid_of`. -/
theorem marginalEuclid_holds {d : ℕ} (hd : 3 ≤ d) : MarginalEuclidStmt d :=
  marginalEuclid_of hd (phiRate_holds (by omega)) (strongRotLaw_holds hd) (concentration_holds hd)

end HigherDimLQGContinuity
