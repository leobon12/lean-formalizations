import QuantumZipper.Proofs.Thm18.R18G3TSplit
import QuantumZipper.Proofs.Thm18.R18G3TJointAbs
import QuantumZipper.Proofs.Thm18.G3G2Scale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T-J: weighted joint mixing of the profiled scheme from its two nodes

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71: conditionally on the field outside the
two half-discs (and the Palm length), each zoomed-in figure has conditional law close to the
wedge law (conditional Proposition 5.5, here the mixing body `G3FixMixBody` of the profiled
scheme, given by `G3TProfMixTransferStmt`), and the two figures are conditionally independent by
the GFF Markov property (`condIndepCE_g3p`). Hence the weighted joint zoom probability
factorizes (`g3TProfJointMix_weighted`, the second conjunct of `G3TProfJointMixStmt`).

Steps (own bookkeeping, AGENT_GUIDE cost rule):
1. on the margin event, the region zoom `g3pU` and the full zoom `g3pUf` agree on a cylinder
   unless the zoomed area of a small half-ball is `< 1` (`zoomLaw_mem_lawCyl_iff`,
   `fcAgree_restrictField_circIn`, `bad_subset_geo_union_area`), which has small probability by
   `G3TProfAreaStmt`;
2. the mixing body transfers to the region zooms, and `abs_integral_inter_sub_le`
   (`R18G3TJointAbs.lean`) gives the weighted product formula for the region zooms;
3. back to the full zooms (`abs_integral_indicator_sub_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Symmetric difference of intersections. -/
theorem real_inter_symmDiff_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (a a' b b' : Set Ω) :
    P.real ((a ∩ b) ∆ (a' ∩ b')) ≤ P.real (a ∆ a') + P.real (b ∆ b') := by
  refine (measureReal_mono ?_).trans (measureReal_union_le (a ∆ a') (b ∆ b'))
  intro p hp
  simp only [mem_symmDiff, mem_inter_iff, mem_union] at hp ⊢
  tauto

/-- Replacing an event inside `P.real (· ∩ G)`. -/
theorem abs_real_inter_sub_le_of_symmDiff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A A' G : Set Ω} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hG : MeasurableSet G) : |P.real (A ∩ G) - P.real (A' ∩ G)| ≤ P.real (A ∆ A') := by
  refine (abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hG).nullMeasurableSet
    (hA'.inter hG).nullMeasurableSet).trans (measureReal_mono ?_)
  rw [← inter_symmDiff_distrib_right]
  exact inter_subset_left

end R18
end QuantumZipper
