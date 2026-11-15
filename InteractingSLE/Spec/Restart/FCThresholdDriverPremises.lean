/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCPlumbAssembly2Inputs
import InteractingSLE.Spec.Restart.Lemma75Data
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Coupling.WholeField9Entr
import InteractingSLE.Spec.Sec7.ReverseArcAux70

/-!
# Premises of the first-contact threshold assembly

Lemma 7.5 follows directly from word-parametric determination. Aux. 56 is
unconditional. Lemma 7.7 follows from Lemma 7.6 and Lemma 7.5; canonical driver
codes follow from Theorems 1.2 and 1.3. All theorem inputs are explicit below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb

open Exist.Staged

universe u

/-- Word-parametric determination gives the jointly measurable universal flow-line
map of Lemma 7.5 at the same probability-space universe. -/
theorem lemma75DataStatement_of_param (h12p : Theorem12ParamStatement.{u}) :
    Lemma75DataStatement.{u} := by
  intro κ hκ _hκ4 x θ
  let T : BoundaryWord × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ) :=
    fun q => flowTrace h12p hκ θ ((q.1, x), q.2)
  have hTm : Measurable T :=
    (measurable_flowTrace h12p hκ θ).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  refine ⟨fun q => ((T q).1, fun t => (x : ℂ) + (T q).2 t),
    (measurable_fst.comp hTm).prodMk (measurable_pi_iff.2 fun t =>
      measurable_const.add ((measurable_pi_apply t).comp (measurable_snd.comp hTm))), ?_⟩
  intro c Ω _ P _ h _hh η ζ hη
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hC, hgen⟩ := hη
  have he : h' = fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  subst he
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps x
  have hdet := (h12p κ hκ _ _).choose_spec.2 _ _ _ _ hF hC
  filter_upwards [hdet, hgen] with ω hdetω hgenω
  dsimp only [T]
  rw [flowTrace_mk]
  refine ⟨hdetω.1, fun t ht => ?_⟩
  have heval := hdetω.2 _ hgenω t
  rw [min_eq_left ht, ENNReal.toNNReal_coe] at heval
  change (x : ℂ) +
    ((h12p κ hκ _ _).choose
      (((flowLineXL c.fn c.jumps x, flowLineXR c.fn c.jumps x),
        (flowLineRhoL κ c.fn c.jumps x θ, flowLineRhoR κ c.fn c.jumps x θ)),
          Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω))).2 t = η ω t
  rw [heval]
  ring

/-- The L75 premise can be replaced by the same-universe Theorems 1.2 and 1.3. -/
theorem lemma75Statement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : Theorem15.Lemma75Statement.{u} :=
  lemma75Statement_of_lemma75DataStatement
    (lemma75DataStatement_of_param (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))

/-- Aux. 56 at the entrance times is a landed unconditional theorem. -/
theorem firstContact_retainedRangeEntranceStatement : RetainedRangeEntranceStatement.{u} :=
  WholeField.retainedRangeEntranceStatement

/-- Lemma 7.7's remaining input is Lemma 7.6 once determination is available. -/
theorem lemma77Statement_of_thm12_thm13_lemma76 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h76 : Sec7.Lemma76Statement.{u}) :
    Supp10.Lemma77Statement.{u} :=
  Sec7.lemma77Statement_of_lemma76_of_lemma75 h76 (lemma75Statement_of_thm12_thm13 h12 h13)
    firstContact_retainedRangeEntranceStatement

/-- Canonical driver codes need only the Type-level Theorems 1.2 and 1.3. -/
theorem firstContact_canonicalDriverCodeStatement_of_thm12_thm13
    (h12 : Exist.Theorem12Statement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    CanonicalDriverCodeStatement :=
  canonicalDriverCodeStatement_of_param
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13

/-- The original threshold assembly with all four auxiliary premises accounted for.
The threshold-input statement and Lemma 7.6 are still explicit hypotheses. -/
theorem firstContactCanonCondDetStatement_of_thresholdInputs_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u}) (hInputs : FirstContactThresholdDriverInputsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_thresholdInputs (lemma75Statement_of_thm12_thm13 h12 h13)
    (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) firstContact_retainedRangeEntranceStatement
    (firstContact_canonicalDriverCodeStatement_of_thm12_thm13 h12₀ h13₀) hInputs

end InteractingSLE.Restart.FCPlumb
