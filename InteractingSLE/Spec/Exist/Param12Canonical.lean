/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12CanonicalExist

/-!
# The measurable set of canonical coupling laws; Theorem 1.2 with a map measurable in the word

Packet PROVE-PARAM12C. Assembly:

* **`borelCanonicalCouplingStatement`**: PROVE-PARAM12B's named input `BorelCanonicalCouplingStatement` holds, with the
  canonical space `XCode × 𝒟'(ℍ)`, the read-out `canonF` of field and killed driving code, and the measurable set of
  canonical coupling laws `{(θ, π) | CanonCond κ θ π}` (`measurableSet_canonCond`): every ordered word has one
  (`exists_canonCond`), and each is realized by an optional hull coupling of the word
  (`CanonCond.exists_isOptionalHullCoupling`);
* **`couplingLawKernelStatement_of_thm12_thm13`**: Theorem 1.1's coupling law is a Borel kernel in the word, from
  the frozen Theorems 1.2–1.3 (named inputs in their frozen anchor types);
* **`theorem12ParamStatement_of_thm12_thm13`**: Theorem 1.2 with a determination map jointly measurable in the word
  (ruling R44), from the frozen Theorems 1.2–1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Staged LQGMetric

instance instStandardBorelSpaceCanon {nL nR : ℕ} :
    StandardBorelSpace (XCode nL nR × DistOn upperHalfPlaneOpens) := StandardBorelSpace.prod

/-- **`BorelCanonicalCouplingStatement` holds** (PROVE-PARAM12B's remaining input). -/
theorem borelCanonicalCouplingStatement : BorelCanonicalCouplingStatement.{u} := by
  intro κ hκ nL nR
  refine ⟨XCode nL nR × DistOn upperHalfPlaneOpens, inferInstance, inferInstance, ⟨(0, 0)⟩, canonF,
    measurable_canonF, {r : WordData nL nR × ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens) |
      CanonCond κ r.1 (r.2 : Measure (XCode nL nR × DistOn upperHalfPlaneOpens))}, measurableSet_canonCond κ,
    fun xL xR ρL ρR hF => ⟨?_, fun π hπ => CanonCond.exists_isOptionalHullCoupling.{u} hκ hπ⟩⟩
  obtain ⟨π, hπ⟩ := exists_canonCond (ρL := ρL) (ρR := ρR) hκ hF
  exact ⟨π, hπ⟩

/-- **Theorem 1.1's coupling law is a Borel kernel in the word**, from the frozen Theorems 1.2–1.3. -/
theorem couplingLawKernelStatement_of_thm12_thm13 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) : CouplingLawKernelStatement.{u} :=
  couplingLawKernelStatement_of_borelCanonical h12 h13 borelCanonicalCouplingStatement

/-- **Theorem 1.2 with a determination map jointly measurable in the word** (`Theorem12ParamStatement`, ruling R44),
from the frozen Theorems 1.2–1.3. -/
theorem theorem12ParamStatement_of_thm12_thm13 (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) : Theorem12ParamStatement.{u} :=
  theorem12ParamStatement_of_borelCanonical h12 h13 borelCanonicalCouplingStatement

end Param12

end Exist

end InteractingSLE
