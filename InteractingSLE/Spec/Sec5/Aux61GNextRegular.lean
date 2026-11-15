/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextRefSeed

/-! # Reference boundary values away from the seed -/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GNext
open Aux61Fib (FibData)
open PiecewiseConstantBoundaryData

/-- Every reference force mark is either the seed or an actual listed
jump candidate; there are no additional nonzero exceptional points. -/
theorem forceJumpSet_flowLine_subset (b : ℝ → ℝ) (J : Finset ℝ) :
    forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0) ⊆ insert 0 (J : Set ℝ) := by
  rintro z (hz | ⟨i, hi⟩ | ⟨i, hi⟩)
  · exact Or.inl hz
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · left
      exact hi.symm
    · right
      have hm := ((jumpSet b J).filter (· < 0)).orderEmbOfFin_mem rfl (Fin.rev i)
      have hj : ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) ∈ J :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).1
      rw [← hi]
      change ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) - 0 ∈ J
      simpa only [sub_zero] using hj
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · left
      exact hi.symm
    · right
      have hm := ((jumpSet b J).filter (0 < ·)).orderEmbOfFin_mem rfl i
      have hj : ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl i ∈ J :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 hm).1).1
      rw [← hi]
      change ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl i - 0 ∈ J
      simpa only [sub_zero] using hj

/-- Off the seed and the listed reference jumps, `refMean0` has exactly
the prescribed reference boundary height. -/
theorem tendsto_refMean0_regular (d : FibData) {a : ℝ} (ha0 : a ≠ 0) (haJ : a ∉ d.JR) :
    Tendsto (Aux61GlueK.refMean0 d) (𝓝[H] (a : ℂ)) (𝓝 (d.bR a)) := by
  have ha : a ∉ forceJumpSet (flowLineXL d.bR d.JR 0) (flowLineXR d.bR d.JR 0) := by
    intro hm
    rcases forceJumpSet_flowLine_subset d.bR d.JR hm with h | h
    · exact ha0 h
    · exact haJ h
  have hb := (Aux61GlueK.refMean0_ext d).2.2 a (by simpa only [sub_zero] using ha)
  simpa only [sub_zero, Sec4.forceBoundaryData_flowLine d.κ_pos d.bR_pc ha0 haJ] using hb

/-- Physical height and inherited phase limits identify the charted
comparison mean with the reference boundary data at a regular point. -/
theorem tendsto_charted_mean_sub_refMean0 (d : FibData) {a : ℝ}
    (ha0 : a ≠ 0) (haJ : a ∉ d.JR)
    {u lift : ℂ → ℝ} {inv : ℂ → ℂ} {height phase offset k : ℝ}
    (hphysical_height : Tendsto (u ∘ inv) (𝓝[H] (a : ℂ)) (𝓝 height))
    (hinherited_phase : Tendsto (lift ∘ inv) (𝓝[H] (a : ℂ)) (𝓝 phase))
    (hreference_height : d.bR a = height + offset + k * phase) :
    Tendsto (fun z => u (inv z) + offset + k * lift (inv z) - Aux61GlueK.refMean0 d z)
      (𝓝[H] (a : ℂ)) (𝓝 0) := by
  have ht := ((hphysical_height.add_const offset).add (hinherited_phase.const_mul k)).sub
    (tendsto_refMean0_regular d ha0 haJ)
  rw [hreference_height, sub_self] at ht
  exact ht

end InteractingSLE.Sec5.Aux61GNext
