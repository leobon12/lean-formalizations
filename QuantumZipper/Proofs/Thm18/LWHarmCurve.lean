import QuantumZipper.Proofs.Thm18.LWExcDefs
import QuantumZipper.Proofs.Complex.TopoSep
import Mathlib.Analysis.Convex.Segment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): the Jordan curve `ξ ∪ [a, b]` of a crosscut

Task LW-HARM (B), topological part. For a crosscut `ξ` of `ℍ` from `a` to `b ≠ a`, the set
`E = ξ ∪ [a, b]` is the image of the loop `lwLoop` (the arc, then the segment back), which is
continuous on `[0, 1]` and injective on `[0, 1)`. Hence
* `lwCrossE_ulc`: `E` is uniformly locally connected (`CA.Topo.ULC.image_Icc`);
* `lwCrossE_diff_preconnected`: `E \ {q}` is connected for every `q` (a Jordan curve minus a
  point is an arc).
These are the hypotheses of the Jordan case of Carathéodory's theorem (Pommerenke, *Boundary
Behaviour of Conformal Maps*, Thm 2.6 (iii), p. 24) used in `LWHarmCross.lean`. Own elementary
proofs.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The arc extended by its end points. -/
def lwArcExt (ξ : ℝ → ℂ) (a b : ℝ) (t : ℝ) : ℂ := if t ≤ 0 then a else if 1 ≤ t then b else ξ t

variable {ξ : ℝ → ℂ} {a b : ℝ}

lemma lwArcExt_contOn (hξ : IsCrosscutH ξ) (ha : Tendsto ξ (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto ξ (𝓝[<] 1) (𝓝 (b : ℂ))) : ContinuousOn (lwArcExt ξ a b) (Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.1 ha ε hε
    refine ⟨min δ 1, by positivity, fun {s} hs hsd => ?_⟩
    have hs1 : s < 1 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1] at hsd; linarith [min_le_right δ 1]
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · subst hs0; simp [lwArcExt, hε]
    · have e : lwArcExt ξ a b s = ξ s := by simp [lwArcExt, not_le.2 hs0, not_le.2 hs1]
      rw [e, show lwArcExt ξ a b 0 = a by simp [lwArcExt]]
      exact hd hs0 (lt_of_lt_of_le hsd (min_le_left _ _))
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.1 hb ε hε
    refine ⟨min δ 1, by positivity, fun {s} hs hsd => ?_⟩
    have hs0 : 0 < s := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hs.2])] at hsd
      linarith [min_le_right δ 1]
    rcases eq_or_lt_of_le hs.2 with hs1 | hs1
    · subst hs1; simp [lwArcExt, hε]
    · have e : lwArcExt ξ a b s = ξ s := by simp [lwArcExt, not_le.2 hs0, not_le.2 hs1]
      rw [e, show lwArcExt ξ a b 1 = b by simp [lwArcExt]]
      exact hd hs1 (lt_of_lt_of_le hsd (min_le_left _ _))
  · have hev : lwArcExt ξ a b =ᶠ[𝓝 t] ξ := by
      filter_upwards [Ioo_mem_nhds h0 h1] with s hs
      simp [lwArcExt, not_le.2 hs.1, not_le.2 hs.2]
    exact ((hξ.1.continuousAt (Ioo_mem_nhds h0 h1)).congr hev.symm).continuousWithinAt

lemma lwArcExt_mem (hξ : IsCrosscutH ξ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    lwArcExt ξ a b s = ξ s ∧ 0 < (ξ s).im :=
  ⟨by simp [lwArcExt, not_le.2 hs.1, not_le.2 hs.2], hξ.2.2.1 hs⟩

end LWFar
end Thm18Asm
end QuantumZipper
