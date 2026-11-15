/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12Limit
import InteractingSLE.Spec.Exist.Param12LimitGiry

/-!
# Theorem 1.1's coupling law as a kernel in the word, from a measurable set of canonical laws

Packet PROVE-PARAM12B. This file states the remaining input of `Param12Limit` with laws as the descriptions.
`ProbabilityMeasure Ωc` is standard Borel (`Param12LimitGiry`), so a measurable set of (word data, law) pairs on a
canonical space `Ωc` is a Borel set of descriptions, read out by a measurable map `F : Ωc → (field, killed driver
code)`.

* **`BorelCanonicalCouplingStatement`** (named input): for `κ > 0` and numbers of marks, a nonempty standard Borel
  space `Ωc`, a measurable read-out `F` and a measurable set `C` of pairs (word data, law on `Ωc`) such that every
  ordered word has a law in `C`, and every law `π` of an ordered word `w` in `C` is realized by an optional hull
  coupling of `w` whose joint law of field and killed driver code is `π.map F`.
* **`couplingLawKernelStatement_of_borelCanonical`**: with Theorems 1.2–1.3 it gives `CouplingLawKernelStatement`.

The intended instance: `Ωc` = (driver code `XCode nL nR`) × (field `𝒟'(ℍ)`), `F` = (field, lifetime and killed driver
code), and `C` the laws under which the canonical processes satisfy countably many Borel conditions: the code lies in
the canonical solution codes of the word (`Param12FamilyRel.measurableSet_paramCRel`), the driving Brownian increments
are independent of the canonical filtration, the field marginal is the field law of the word, and the sampled and
projection-independence constraints of Theorem 1.1's compactness step hold at a Borel family of stops. See the handoff.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly LQGMetric Staged

/-- The law kernel `(w, π) ↦ π.map F` on pairs (word data, probability law on `Ωc`). -/
def lawMapKernel {Θ Ωc X : Type*} [MeasurableSpace Θ] [MeasurableSpace Ωc] [MeasurableSpace X] {F : Ωc → X}
    (hF : Measurable F) : Kernel (Θ × ProbabilityMeasure Ωc) X where
  toFun p := (p.2 : Measure Ωc).map F
  measurable' := (Measure.measurable_map F hF).comp (measurable_subtype_coe.comp measurable_snd)

theorem lawMapKernel_apply {Θ Ωc X : Type*} [MeasurableSpace Θ] [MeasurableSpace Ωc] [MeasurableSpace X]
    {F : Ωc → X} (hF : Measurable F) (p : Θ × ProbabilityMeasure Ωc) :
    lawMapKernel hF p = (p.2 : Measure Ωc).map F := rfl

/-- The section measure `(w, π) ↦ π {x | (w, x) ∈ S}` of a jointly measurable set is measurable on
(parameter, law): the Borel conditions "the law is carried by the section at the word" are measurable. -/
theorem measurable_measure_section {Θ Ωc : Type*} [MeasurableSpace Θ] [MeasurableSpace Ωc] {S : Set (Θ × Ωc)}
    (hS : MeasurableSet S) :
    Measurable fun p : Θ × ProbabilityMeasure Ωc => (p.2 : Measure Ωc) {x | (p.1, x) ∈ S} := by
  let κ : Kernel (Θ × ProbabilityMeasure Ωc) Ωc := ⟨fun p => (p.2 : Measure Ωc), measurable_subtype_coe.comp measurable_snd⟩
  have : IsMarkovKernel κ := ⟨fun p => (p.2 : ProbabilityMeasure Ωc).prop⟩
  have ht : MeasurableSet {q : (Θ × ProbabilityMeasure Ωc) × Ωc | (q.1.1, q.2) ∈ S} :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd hS
  exact Kernel.measurable_kernel_prodMk_left (κ := κ) ht

/-- "The law is carried by the section of `S` at the word" is a measurable condition on (word, law). -/
theorem measurableSet_ae_mem_section {Θ Ωc : Type*} [MeasurableSpace Θ] [MeasurableSpace Ωc] {S : Set (Θ × Ωc)}
    (hS : MeasurableSet S) :
    MeasurableSet {p : Θ × ProbabilityMeasure Ωc | (p.2 : Measure Ωc) {x | (p.1, x) ∉ S} = 0} :=
  measurable_measure_section hS.compl (measurableSet_singleton 0)

/-- **Named input: a measurable set of canonical coupling laws.** For `κ > 0` and numbers of marks: a nonempty
standard Borel space `Ωc`, a measurable read-out `F : Ωc → 𝒟'(ℍ) × DCode`, and a measurable set `C` of pairs (word
data, law on `Ωc`) such that every ordered word `w` has a law in `C`, and every law `π` with `(w, π) ∈ C` is realized
by an optional hull coupling of `w` (at universe `u`) whose joint law of field and killed driver code is `π.map F`. -/
def BorelCanonicalCouplingStatement : Prop :=
  ∀ (κ : ℝ) (_ : 0 < κ) (nL nR : ℕ),
    ∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (_ : StandardBorelSpace Ωc) (_ : Nonempty Ωc)
      (F : Ωc → DistOn upperHalfPlaneOpens × DCode) (_ : Measurable F)
      (C : Set (WordData nL nR × ProbabilityMeasure Ωc)), MeasurableSet C ∧
      ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
        (∃ π, ((((xL, xR), (ρL, ρR)) : WordData nL nR), π) ∈ C) ∧
          ∀ π, ((((xL, xR), (ρL, ρR)) : WordData nL nR), π) ∈ C →
            ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
              (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
              (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
              (h : Ω → DistOn upperHalfPlaneOpens),
              IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧
                P.map (fieldCode h W ζ) = (π : Measure Ωc).map F

/-- Canonical laws are Borel descriptions (`ProbabilityMeasure Ωc` is standard Borel). -/
theorem borelDescription_of_borelCanonical (hC : BorelCanonicalCouplingStatement.{u}) :
    BorelCouplingDescriptionStatement.{u} := by
  intro κ hκ nL nR
  obtain ⟨Ωc, mΩc, hΩc, hne, F, hF, C, hCm, hdesc⟩ := hC κ hκ nL nR
  exact ⟨ProbabilityMeasure Ωc, inferInstance, inferInstance, C, lawMapKernel hF, hCm, fun xL xR ρL ρR hw =>
    ⟨(hdesc xL xR ρL ρR hw).1, fun π hπ => (hdesc xL xR ρL ρR hw).2 π hπ⟩⟩

/-- **Theorem 1.1's coupling law is a Borel kernel in the word**, from Theorems 1.2–1.3 and a measurable set of
canonical coupling laws. -/
theorem couplingLawKernelStatement_of_borelCanonical (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hC : BorelCanonicalCouplingStatement.{u}) :
    CouplingLawKernelStatement.{u} :=
  couplingLawKernelStatement_of_borelDescription h12 h13 (borelDescription_of_borelCanonical hC)

/-- **Theorem 1.2 with a determination map jointly measurable in the word** (`Theorem12ParamStatement`, ruling R44),
from Theorems 1.2–1.3 and a measurable set of canonical coupling laws (through PROVE-PARAM12's
`theorem12ParamStatement_of_couplingLawKernel`). -/
theorem theorem12ParamStatement_of_borelCanonical (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hC : BorelCanonicalCouplingStatement.{u}) :
    Theorem12ParamStatement.{u} :=
  theorem12ParamStatement_of_couplingLawKernel h12 h13 (couplingLawKernelStatement_of_borelCanonical h12 h13 hC)

end Param12

end Exist

end InteractingSLE
