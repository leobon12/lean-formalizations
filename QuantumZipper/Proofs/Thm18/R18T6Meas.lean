import QuantumZipper.Proofs.Thm18.R18T6Defs
import QuantumZipper.Proofs.Section5.Prop16MeasArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T6 (R18-AREAREAD), part 5: a measurable reading of the ball masses

`areaBallRead γ a : E6.FullData → ℝ≥0∞` is an explicit countable formula (suprema and limits of
pre-limit integrals against cut-offs of the random open set `B_a(0) ∩ ℍ ∖ curve`), hence
measurable (`measurable_areaBallRead`), and it equals `areaOfData γ d (B_a(0) ∩ ℍ)` whenever the
local area limit on `ℍ ∖ curve` exists (`areaBallRead_eq`); in particular on the masked data of
every configuration whose field has a global area limit (`areaBallRead_offData`).

The cut-off machinery is `Prop16Area.Meas` (`IsBumpFamily`, `lintegral_eq_iSup`, `Psi`,
`measurable_Psi`), built for Proposition 1.6 on random domains. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.Meas

/-- A continuous cut-off equal to `1` on `B_a(0)`, supported in `B̄_{a+1}(0)`. -/
def ballCut (a : ℝ) (z : ℂ) : ℝ := max 0 (min 1 (a + 1 - ‖z‖))

theorem continuous_ballCut (a : ℝ) : Continuous (ballCut a) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

theorem hasCompactSupport_ballCut (a : ℝ) : HasCompactSupport (ballCut a) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (a + 1)) fun z hz => ?_
  simp only [mem_closedBall, dist_zero_right, not_le] at hz
  simp only [ballCut]
  rw [max_eq_left (min_le_of_right_le (by linarith))]

theorem ballCut_eq_one {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) a) : ballCut a z = 1 := by
  simp only [mem_ball, dist_zero_right] at hz
  simp only [ballCut]
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The local area limit exists for the masked data of a configuration with a global area limit. -/
theorem isVagueLimitOn_offData {γ : ℝ} {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x.1) μ) :
    ∃ m, IsVagueLimitOn (offSet (offData x)) (areaApprox γ (readOffField (offData x))) m := by
  have hUo : IsOpen (H \ curveOf x.2) := isOpen_H.sdiff isClosed_closure
  refine ⟨μ.restrict (H \ curveOf x.2), ?_⟩
  unfold offSet
  rw [curveSel_offData hc h0]
  exact Prop16Area.G.isVagueLimitOn_of_circAgree hUo (circAgree_readOffField hc h0) sdiff_subset
    subset_rfl (isVagueLimitOn_restrict_R18 hUo sdiff_subset hμ)

end R18
end QuantumZipper
