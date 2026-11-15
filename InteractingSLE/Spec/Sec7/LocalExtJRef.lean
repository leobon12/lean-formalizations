/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHRef
import InteractingSLE.Spec.Sec7.StripSysBorel

/-!
# Aux. lemma 54: Theorem 2.2 on a standard Borel space, and the reference without named inputs

Packet PROVE-LOCEXT-J. PROVE-LOCEXT-H reduced Aux. lemma 54 for stopped seed couplings
(`StoppedSeedExtensionStatement`) to four named inputs, one of them Theorem 2.2's existence on a standard Borel space
for the two-seed words (`Coupling.Thm22StdBorelStatement`). That input is a consequence of landed results:

* **`thm22StdBorelStatement_of_ordered`**: for every ordered force word, Theorem 2.2's evolution
  (`exists_isIntegratedSLEEvolution_assembled`) read through the dyadic code of Theorem 2.2's uniqueness proof is an
  evolution on the standard Borel code space (PROVE-STRIPSYS3's `StripSysBorel.isIntegratedSLEEvolution_code`); lifted
  to any universe by `ULift`;
* **`stdTwoSeedReferenceStatement`**: a standard reference exists for every admissible seed pair (no named input);
* **`stoppedSeedExtensionStatement_of_lawPreLoc`**: Aux. lemma 54 from (U), (K-pre) and (Loc) alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Coupling Sec7.StripSysBorel Sec2.Assembly

/-- **Theorem 2.2 (existence) on a standard Borel space**, for every ordered force word (in every universe). -/
theorem thm22StdBorelStatement_of_ordered {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) :
    Thm22StdBorelStatement.{u} κ xL xR ρL ρR := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled (ρL := ρL) (ρR := ρR) hκ hF
  obtain ⟨μ, hμ, 𝓗, hE'⟩ := isIntegratedSLEEvolution_code hκ hE
  set P₀ : Measure (ULift.{u} (XCode nL nR)) := μ.map ULift.up with hP₀
  have hP₀p : IsProbabilityMeasure P₀ := inferInstance
  have hmap : P₀.map ULift.down = μ := by
    rw [hP₀, Measure.map_map measurable_down measurable_up]
    exact Measure.map_id
  exact ⟨ULift.{u} (XCode nL nR), inferInstance, inferInstance, P₀, hP₀p, _, _, _, _, _, _,
    IsIntegratedSLEEvolution.comap measurable_down hmap hE'⟩

/-- **A standard reference exists** for every admissible seed pair (`StdTwoSeedReferenceStatement`, no named input). -/
theorem stdTwoSeedReferenceStatement {κ : ℝ} (hκ : 0 < κ) : StdTwoSeedReferenceStatement.{u} κ :=
  stdTwoSeedReferenceStatement_of_thm22StdBorel hκ fun _ _ _ _ =>
    thm22StdBorelStatement_of_ordered hκ isOrderedForceWord_twoSeed'

/-- **Aux. lemma 54 for stopped seed couplings** from (U), (K-pre) and (Loc) only. -/
theorem stoppedSeedExtensionStatement_of_lawPreLoc {κ : ℝ} (hκ : 0 < κ) (hU : StoppedTwoSeedLawStatement.{u} κ)
    (hPre : ExtPreStopStatement.{u} κ) (hLoc : ExtLocalityStatement.{u} κ) : StoppedSeedExtensionStatement.{u} κ :=
  stoppedSeedExtensionStatement_of_inputs hκ (stdTwoSeedReferenceStatement hκ) hU hPre hLoc

end LocalExt

end InteractingSLE
