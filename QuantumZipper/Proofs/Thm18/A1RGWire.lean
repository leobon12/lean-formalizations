import QuantumZipper.Proofs.Thm18.A1RGArc
import QuantumZipper.Proofs.Thm18.Wire18

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RG (wiring): the A1b input without the all-times growth node

The only consumer of `G1A1b2SideTendstoStmt` is `g1ZA1bSideExactArcStmt_of_sideRTX`
(G1A1bMain.lean), which reads SideRTX at the single time `t = lenTimeArc γ ℓ c₀` (and only on the
event `unzipScaleArc > 0`). At that time the growth of the witness is proved by the open-arc E6
transfer (`A1RG.ae_arcGrowth`, A1RGArc.lean). The cut-off argument of
`g1A1b2SideTendstoStmt_of_cut` (A1RNodes.lean, decision D90) is repeated verbatim at that time:

* `A1RG.ae_sideRTXArc : A1RFarStmt → (SideRTX at lenTimeArc, a.s.)`;
* `A1RG.g1ZA1bSideExactArcStmt_of_far : A1RFarStmt → G1ZA1bSideExactArcStmt`;
* `theorem1_8PaperMO_of_leaves6`: `theorem1_8PaperMO` from the leaves of
  `theorem1_8PaperMO_of_leaves` minus `A1RGrowthStmt` (body copied from Wire18.lean, only the
  `hA1b` line changed).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

namespace A1RG

/-- The arc growth in the near-`ℝ` form of `A1RGrowthStmt`. -/
theorem ae_arcGrowthNear {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, 0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) → ∀ F : ℂ × ℝ → ℝ,
      IsRegularWith (coordChange (Y ω) (fwdMapInv (drive (γ ^ 2) B ω)
        (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))) (Qc γ)) F →
      ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ z ∈ Hbar, ‖z‖ ≤ Rr →
        z.im ≤ Real.sqrt ρ → |F (z, ρ)| ≤ C * (1 + |Real.log ρ|) := by
  filter_upwards [ae_arcGrowth hS hIn hℓ] with ω h ha F hF Rr
  obtain ⟨C, hC, hb⟩ := h ha F hF (max Rr 1)
  exact ⟨C, hC, fun ρ hρ hρ1 z hz hzR _ =>
    hb z hz (hzR.trans (le_max_left _ _)) ρ hρ (hρ1.le.trans (le_max_right _ _))⟩

end A1RG

end R18
end QuantumZipper
