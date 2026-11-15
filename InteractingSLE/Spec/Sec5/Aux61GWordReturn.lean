/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondThetaImg

/-! # The actual returned counterflow word and its regular boundary germs

Read the force positions from the stopped counterflow history. The existing
return theorem gives a bounded harmonic extension of this explicit word,
so its regular boundary heights require no assumed physical mean limit.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61GWord
open WangWu GlueCond LawUnique Cond44Ref Sec7.StripSysField

/-- The return of the actual counterflow force word at the retained stop. -/
def returnedCfData (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (s : ℝ≥0) (y : HistorySpace 0 0) : ℝ → ℝ :=
  returnData (cfOffset κ) (cfCoeff κ)
    (forceBoundaryData (16 / κ) (cfRhoL κ b J) (cfRhoR κ b J)
      (cfPosL κ b J (Sec4.regPath (cfStop s y)) s)
      (cfPosR κ b J (Sec4.regPath (cfStop s y)) s))

/-- The finite exceptional coordinates of the returned counterflow word. -/
def returnedCfJumps (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (s : ℝ≥0) (y : HistorySpace 0 0) : Finset ℝ :=
  returnExcept (forceJumpFinset
    (cfPosL κ b J (Sec4.regPath (cfStop s y)) s)
    (cfPosR κ b J (Sec4.regPath (cfStop s y)) s))

/-- The counterflow-only mean, read in its own chart, extends the actual
returned word. This is valid for every stopped history. -/
theorem isBoundedHarmonicExtension_returnedCf (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (s : ℝ≥0) (y : HistorySpace 0 0) :
    IsBoundedHarmonicExtension (returnedCfData κ b J s y)
      (returnedCfJumps κ b J s y)
      (GlueImg.retMean κ (cfU κ b J s (cfStop s y))) := by
  have hv := isBoundedHarmonicExtension_cfU κ b J s (cfStop s y)
  rw [← coe_forceJumpFinset] at hv
  exact GlueImg.isBoundedHarmonicExtension_retMean hv

/-- At a regular returned coordinate the reference height is the value of
the explicit returned force word, with no further harmonic limit premise. -/
theorem tendsto_returnedCfMean (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (s : ℝ≥0) (y : HistorySpace 0 0) {ξ : ℝ}
    (hξ : ξ ∉ returnedCfJumps κ b J s y) :
    Tendsto (GlueImg.retMean κ (cfU κ b J s (cfStop s y)))
      (𝓝[H] (ξ : ℂ)) (𝓝 (returnedCfData κ b J s y ξ)) :=
  (isBoundedHarmonicExtension_returnedCf κ b J s y).2.2 ξ hξ

/-- Zero is retained as an exceptional returned coordinate. Seed cancellation
uses the own-line argument rather than a regular-boundary limit here. -/
theorem ne_zero_of_notMem_returnedCfJumps (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ)
    (s : ℝ≥0) (y : HistorySpace 0 0) {ξ : ℝ}
    (hξ : ξ ∉ returnedCfJumps κ b J s y) : ξ ≠ 0 :=
  ne_zero_of_notMem_returnExcept hξ

end InteractingSLE.Sec5.Aux61GWord
