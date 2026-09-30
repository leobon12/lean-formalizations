import QuantumZipper.Proofs.Thm18.G3ZqFFix
import QuantumZipper.Proofs.Zipper.D3PlusN2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE-B: monotonicity of the local scale and of the dyadic good event in the radius

* `scaleParamOn_halfDisc_mono`: if the local area measure on `halfDisc r'` is a genuine vague
  limit and its scale `s` lies in `(0, r)` with `r ≤ r'`, then the local area measure on
  `halfDisc r` is also a genuine limit (the restriction, `D3Plus.isVagueLimitOn_restrict`) and
  the local scale computed on `halfDisc r` is the same `s` (`D3Plus.scaleParamOn_halfDisc_restrict`).
* `not_dyadBad_mono`: the dyadic form used by the zoom machinery — off the bad dyadic set at
  radius `r'`, with the scale times `R + 1` below `r`, the dyadic data at radius `r` is off the
  bad dyadic set at radius `r`.

Locality of the quantum area measure: Sheffield, arXiv:1012.4797, §5 (the zoom at a point only
reads the field near the point; used in the proof of Prop. 5.5, p. 65). Own elementary assembly
(AGENT_GUIDE cost rule) from the existing restriction/uniqueness lemmas.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open D3Plus G3Cv S5.FieldLaw.Raw

/-- The local scale on the smaller half-disc equals the one on the larger half-disc, once the
latter is positive and below the smaller radius. -/
theorem scaleParamOn_halfDisc_mono {γ r r' : ℝ} {y : FieldSample} (hr : 0 < r) (hrr : r ≤ r')
    {μ : Measure ℂ} (hμ : IsVagueLimitOn (halfDisc r') (areaApprox γ y) μ)
    (hpos : 0 < scaleParamOn γ y (halfDisc r')) (hs : scaleParamOn γ y (halfDisc r') < r) :
    (∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m) ∧
      scaleParamOn γ y (halfDisc r) = scaleParamOn γ y (halfDisc r') := by
  have _hr := hr
  have hsub : halfDisc r ⊆ halfDisc r' :=
    inter_subset_inter_left _ (Metric.ball_subset_ball hrr)
  exact ⟨⟨_, isVagueLimitOn_restrict (isOpen_halfDisc r) hsub hμ⟩,
    scaleParamOn_halfDisc_restrict hrr hpos hs⟩

/-- Off the bad dyadic set at radius `r'`, with the scale times `R + 1` below `r ≤ r'`, the
dyadic data at radius `r` is off the bad dyadic set at radius `r`. -/
theorem not_dyadBad_mono {γ r r' : ℝ} {R : ℕ} {y : FieldSample} (hr : 0 < r) (hrr : r ≤ r')
    (hg : ∃ m, IsVagueLimitOn (halfDisc r') (areaApprox γ y) m)
    (hb : dyadData r' y ∉ dyadBad γ r' (R + 1))
    (hsr : scaleParamOn γ y (halfDisc r') * ((R : ℝ) + 1) < r) :
    (∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m) ∧ dyadData r y ∉ dyadBad γ r (R + 1) := by
  obtain ⟨m, hm⟩ := hg
  have hag' := agreeNear_dyadField r' y
  have hgood : dyadData r' y ∈
      Prop16Area.Meas.goodSet γ (dyadField r') (fun _ => halfDisc r') :=
    (exists_isVagueLimitOn_halfDisc_iff hag').1 ⟨m, hm⟩
  have hs' := scaleParamOn_halfDisc_congr (γ := γ) hag'
  have hc : 0 < scaleParamOn γ y (halfDisc r') := by
    simp only [dyadBad, mem_ofPred_eq, not_not] at hb
    rw [dyadScale_eq hgood, ← hs'] at hb
    exact hb.1
  have hR : (1 : ℝ) ≤ (R : ℝ) + 1 := by
    linarith [(R.cast_nonneg : (0 : ℝ) ≤ R)]
  have hlt : scaleParamOn γ y (halfDisc r') < r :=
    lt_of_le_of_lt (le_mul_of_one_le_right hc.le hR) hsr
  obtain ⟨hex, heq⟩ := scaleParamOn_halfDisc_mono hr hrr hm hc hlt
  refine ⟨hex, ?_⟩
  have hag := agreeNear_dyadField r y
  have hgood2 : dyadData r y ∈
      Prop16Area.Meas.goodSet γ (dyadField r) (fun _ => halfDisc r) :=
    (exists_isVagueLimitOn_halfDisc_iff hag).1 hex
  have hs2 := scaleParamOn_halfDisc_congr (γ := γ) hag
  simp only [dyadBad, mem_ofPred_eq, not_not]
  rw [dyadScale_eq hgood2, ← hs2, heq]
  push_cast
  exact ⟨hc, hsr⟩

end ZqC
end Thm18Asm
end QuantumZipper
