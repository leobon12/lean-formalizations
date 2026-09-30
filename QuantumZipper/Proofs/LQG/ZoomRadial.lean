import QuantumZipper.Proofs.LQG.ZoomRadialBasic

/-!
# The radial process at a zoom is the wedge radial process (TASKS.md R6 / D3-RAD)

This file reduces R6's `abs_prob_zoomRadial_sub_le` to its two probabilistic ingredients, on a
single probability space carrying `b, b'` (so that the wedge path `wA α Q b b'` and the
Williams decomposition L14 both make sense):

* `prob_trunc_Vpath_le_add` / `prob_trunc_Rw_le_add`: the truncated zoom radial path
  `trunc S (Vpath …)` (the integrand on the left of R6) and the truncated *re-centred wedge
  path* `trunc S (Rw …)` differ only on `{Tc < S}`. These are steps (1)–(3) of the blueprint
  D3 sketch: the window `[−S, 0]` is compared at nonnegative times of the drifted path, and
  the only loss is the event that the radial process hits `0` before time `S`
  (`ZoomRadialBasic.trunc_Rw_eq`, the mirror of `WedgeTranslation.translation_good`).

Remaining for the full R6 statement (see the report):

* `P {trunc S (Rw …) ∈ E} = P {trunc S (wA …) ∈ E}` — the pushforward of
  `WedgeTranslation.wedge_translation` (B4(c) from L14): the re-centred wedge path has the law
  of the wedge path. Formalizing it needs `AEMeasurable (fun ω => Rw α Q b b' c ω) P`
  (coordinate measurability of the re-centred wedge path at the random time `hitTime`), the
  same plumbing as `WedgeTrans.translation_good`'s `hZpm`.
* `P {ω | Tc α Q c b ω < S} ≤ P' {ω | ∃ u ∈ Icc 0 S, c ≤ A (-u) ω}` — the Williams
  comparison: `{Tc < S} ⊆ {∃ u ∈ Icc 0 S, c ≤ Zp u}` (as `Zp (Tc) = Xc 0 = c`) and
  `P.map Zp = P.map Yh` (`WilliamsDriftDecomposition`, i.e. L14), with `Yh u = A (-u)`;
  this needs the a.e.-continuity reduction of the uncountable quantifier to rationals.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α Q c S : ℝ}
  {b b' : ℝ≥0 → Ω → ℝ} {E : Set (ℝ → ℝ)}

/-- The truncated zoom radial path equals the truncated re-centred wedge path at every `ω` with
`S ≤ Tc ω` (`ZoomRadialBasic.trunc_Rw_eq`). Hence, on `{S ≤ Tc}`, the events
`trunc S (Vpath …) ∈ E` and `trunc S (Rw …) ∈ E` coincide. -/
theorem trunc_Vpath_eq_trunc_Rw {ω : Ω} (h : S ≤ Tc α Q c b ω) :
    trunc S (Vpath α Q c b ω) = trunc S (Rw α Q b b' c ω) := by
  rw [trunc_Rw_eq h]
  rfl

/-- The truncated zoom radial path lies in `E` exactly when the truncated re-centred wedge path
does, on `{S ≤ Tc}`. -/
theorem trunc_Vpath_mem_iff_of_le_Tc {ω : Ω} (h : S ≤ Tc α Q c b ω) :
    trunc S (Vpath α Q c b ω) ∈ E ↔ trunc S (Rw α Q b b' c ω) ∈ E := by
  rw [trunc_Vpath_eq_trunc_Rw (α := α) (Q := Q) (c := c) (S := S) (b := b) (b' := b') h]

/-- **D3 steps (1)–(3), first half.** The truncated zoom radial path lies in `E` only if either
the truncated re-centred wedge path does, or `Tc < S`. -/
theorem prob_trunc_Vpath_le_add :
    P {ω | trunc S (Vpath α Q c b ω) ∈ E} ≤
      P {ω | trunc S (Rw α Q b b' c ω) ∈ E} + P {ω | Tc α Q c b ω < S} := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_cases h : S ≤ Tc α Q c b ω
  · exact Or.inl ((trunc_Vpath_mem_iff_of_le_Tc (α := α) (Q := Q) (c := c) (S := S)
      (b := b) (b' := b') (E := E) h).1 hω)
  · exact Or.inr (not_le.1 h)

/-- **D3 steps (1)–(3), second half.** Conversely, the truncated re-centred wedge path lies in
`E` only if either the truncated zoom radial path does, or `Tc < S`. -/
theorem prob_trunc_Rw_le_add :
    P {ω | trunc S (Rw α Q b b' c ω) ∈ E} ≤
      P {ω | trunc S (Vpath α Q c b ω) ∈ E} + P {ω | Tc α Q c b ω < S} := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_cases h : S ≤ Tc α Q c b ω
  · exact Or.inl ((trunc_Vpath_mem_iff_of_le_Tc (α := α) (Q := Q) (c := c) (S := S)
      (b := b) (b' := b') (E := E) h).2 hω)
  · exact Or.inr (not_le.1 h)

end ZoomRadial
end QuantumZipper
