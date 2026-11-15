/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovRefl
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRoute
import InteractingSLE.Spec.Wire.T12Asm3Inputs

/-!
# The late seed-interval landings, PROVED (the counterflow's no-return from Aux. lemma 7)

Packet PROVE-COLLAR-COVER (third round). PROVE-R5-FRESHTIP's non-circular no-return argument
(`R5Fresh.ae_noReturn_r7_of_aux7`) at the late pockets: the counterflow of every word of the tops' physical context
has barrier seeds — its boundary data satisfy `b ≤ −λ + πχ/2` on `ℝ₋` and `b ≥ λ − πχ/2` on `ℝ₊` off the jumps
(`PhysCtx.hWordleft`/`hWordright` at the angles `∓π/2`, the same bounds as `R7Leaves.r7_cf_bounds` on the R.7 tests) —
so `CfNoReturn.Route.ae_trace_ne_zero_of_centered` applies with Aux. lemma 7 at `16/(16/κ)`, supplied by the proved
clearance Part A (`T12Asm3.partA`); the word's curve is a generating trace of its driver (`PhysCtx.hWordηtr`).

* **`noReturn_of_physCtx`**: every word's counterflow does not return to `0` at a positive time;
* **`colCovSeedInput_holds`**: the tops' `ColCovSeedInput`, PROVED;
* **`sideCollarInputExc_of_source`**: the tops' collar input `T12Asm3.SideCollarInputExc` from SIDE-COLLAR2's source
  input `ColCovSourceInput` alone (with `colCovReflInput_holds`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` or
`CounterflowNoReturnStatement`; Aux. lemma 7 enters only through clearance Part A (proved from the A.1 laws).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open QuantumZipper (chiC)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current

/-- **The counterflow of every word of the tops' physical context does not return to its start** (barrier seeds;
Aux. lemma 7 from clearance Part A). -/
theorem noReturn_of_physCtx {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow) :
    ∀ᵐ ω ∂(Relay.words T12Asm2.cond44Holds baseWord hWordb index).measure, ∀ t : ℝ, 0 < t →
      (Relay.words T12Asm2.cond44Holds baseWord hWordb index).curve ω t ≠ 0 := by
  have hS := hC.wordT index
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have haux7 : Sec4.Aux7Statement.{0} (16 / (16 / index.kappa)) :=
    Sec5.aux7Statement_sixteen_div_of_partA_of_clearance T12Asm3.partA hκ hκ4
  have hpi : 0 ≤ π / 2 := by positivity
  have hL : ∀ x : ℝ, x < 0 → x ∉ (Relay.words T12Asm2.cond44Holds baseWord hWordb index).jumps →
      (Relay.words T12Asm2.cond44Holds baseWord hWordb index).boundary x ≤
        -sleLambda (16 / index.kappa) + π / 2 * chiC (16 / index.kappa) := by
    intro x hx hxJ
    have h := hC.hWordleft index (-(π / 2)) ⟨le_rfl, by linarith⟩ x hx hxJ
    linarith
  have hR : ∀ x : ℝ, 0 < x → x ∉ (Relay.words T12Asm2.cond44Holds baseWord hWordb index).jumps →
      sleLambda (16 / index.kappa) - π / 2 * chiC (16 / index.kappa) ≤
        (Relay.words T12Asm2.cond44Holds baseWord hWordb index).boundary x := by
    intro x hx hxJ
    have h := hC.hWordright index (π / 2) ⟨by linarith, le_rfl⟩ x hx hxJ
    linarith
  have h := CfNoReturn.Route.ae_trace_ne_zero_of_centered hκ hκ4 haux7 hS.boundaryData hL hR hS.gff hS.counterflow
  filter_upwards [h, hC.hWordηtr index] with ω hω htr t ht
  have hne := hω _ htr t.toNNReal (Real.toNNReal_pos.2 ht)
  simpa only [Real.coe_toNNReal _ ht.le] using hne

/-- **The tops' seed-interval landing input, PROVED.** -/
theorem colCovSeedInput_holds : ColCovSeedInput :=
  colCovSeedInput_of_noReturn fun _ _ _ _ _ _ hC index => noReturn_of_physCtx hC index

/-- **The tops' collar input from SIDE-COLLAR2's source input alone.** -/
theorem sideCollarInputExc_of_source (hSrc : ColCovSourceInput) : T12Asm3.SideCollarInputExc :=
  sideCollarInputExc_of_colCov hSrc colCovSeedInput_holds colCovReflInput_holds

end InteractingSLE.Sec7.ColCov
