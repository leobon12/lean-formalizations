/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoAngHist
import InteractingSLE.Spec.Wire.Thm12NowPocket

/-!
# Theorems 1.2–1.3's leaf `hWordT` for strip objects carrying the two-angle experiments

Packet PROVE-TWOANGLE. The expanded wiring `Wire.theorem12Statement_wordSafe_expanded` (PROVE-WORDSAFE) takes, for each
both-low index `i`, strip objects `x = word i` (`Wire.Now.StripObjects`) and the leaf

`hWordT : ∀ i, IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime
  x.experiment`.

Here: for strip objects whose field is a GFF with piecewise-constant data, whose driver is a centred counterflow of the
field with infinite lifetime, and whose data have the strip heights (exactly the wiring's binders `hWordleft`,
`hWordright`), replacing the experiment family by the R48-safe family `TwoAngle.twoAngleFam` gives strip objects
satisfying `hWordT` (**`isTwoAngleStripSystem_withTwoAngle`**), with experiment drivers regular at every sample.
A supplier of the word objects therefore builds them with `experiment := twoAngleFam …` (`withTwoAngle`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only
named input is `Theorem12ParamCond44Statement` (`h44`, R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoAngle

open QuantumZipper (chiC)
open Exist.Staged (IsRegularDriver)
open Prop513Schedule (Driver)
open Sec7.AdmCode (Theorem12ParamCond44Statement)

/-- `16/κ ∈ (0, 4)` for a both-low index (`κ > 4`). -/
theorem sixteen_div_kappa_pos (i : Wire.Current.BothLow) : 0 < 16 / i.kappa :=
  div_pos (by norm_num) (by linarith [i.kappa_gt_four])

theorem sixteen_div_kappa_lt_four (i : Wire.Current.BothLow) : 16 / i.kappa < 4 := by
  have hk := i.kappa_gt_four
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- The strip objects `x` with the experiment family replaced by `Es`. -/
abbrev withExperiment {Ω : Type} [MeasurableSpace Ω] (x : Wire.Now.StripObjects Ω)
    (Es : ExplSpec → ℕ → Ω → Driver) : Wire.Now.StripObjects Ω :=
  { x with experiment := Es }

/-- A boundary word of piecewise-constant data (chosen). -/
def wordOf {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) : Restart.BoundaryWord :=
  (Restart.BoundaryWord.exists_fn_eq hb).choose

theorem wordOf_jumps {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) : (wordOf hb).jumps = J :=
  (Restart.BoundaryWord.exists_fn_eq hb).choose_spec.1

theorem wordOf_fn {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    ∀ y ∉ J, (wordOf hb).fn y = b y :=
  (Restart.BoundaryWord.exists_fn_eq hb).choose_spec.2

/-- **The strip objects with the two-angle experiments**: `x` with `experiment := twoAngleFam` of its field (built from
`h44`, R74). -/
abbrev withTwoAngle (h44 : Theorem12ParamCond44Statement.{0}) (i : Wire.Current.BothLow) {Ω : Type} [MeasurableSpace Ω]
    (x : Wire.Now.StripObjects Ω) (hb : IsPiecewiseConstantBoundaryData x.boundary x.jumps) :
    Wire.Now.StripObjects Ω :=
  withExperiment x (twoAngleFam h44 (sixteen_div_kappa_pos i) (sixteen_div_kappa_lt_four i) (wordOf hb) x.field)

/-- **The leaf `hWordT` for the strip objects with the two-angle experiments** (R48-safe): if the field of `x` is a GFF
with piecewise-constant data `x.boundary` (jumps `x.jumps`) having the strip heights at every angle of `[−π/2, π/2]`
(the wiring's `hWordleft`, `hWordright`), and `x.driver` is a centred counterflow of the field with lifetime
`x.lifetime` infinite almost surely, then `withTwoAngle h44 i x hb` is a two-angle strip system, and its experiment
drivers are regular at every sample. -/
theorem isTwoAngleStripSystem_withTwoAngle (h44 : Theorem12ParamCond44Statement.{0}) (i : Wire.Current.BothLow)
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (x : Wire.Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hb : IsPiecewiseConstantBoundaryData x.boundary x.jumps)
    (hh : IsGFFWithBoundaryData x.measure x.field x.boundary x.jumps)
    (hcf : IsCenteredCounterflowDriver (16 / i.kappa) x.measure x.field x.driver x.lifetime)
    (hζ : ∀ᵐ ω ∂x.measure, x.lifetime ω = ⊤)
    (hleft : ∀ a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa)) :
    let x' := withTwoAngle h44 i x hb
    Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x'.boundary x'.jumps x'.measure x'.field x'.driver x'.lifetime
      x'.experiment ∧ ∀ spec k ω, IsRegularDriver (x'.experiment spec k ω) := by
  have hκ := sixteen_div_kappa_pos i
  have hκ4 := sixteen_div_kappa_lt_four i
  refine ⟨⟨hκ, hκ4, hb, hh, hcf, hζ, fun θ hθ => ?_, fun {θ₀ θ} hθ₀ hθ t₀ => ?_⟩,
    twoAngleFam_regular h44 hκ hκ4 (wordOf hb) x.field⟩
  · change IsStagedHistory (16 / i.kappa) x.boundary x.jumps x.measure x.field (Sec7.R7Aux131.constSpec θ)
      (twoAngleFam h44 hκ hκ4 (wordOf hb) x.field (Sec7.R7Aux131.constSpec θ))
    rw [twoAngleFam_constSpec]
    obtain ⟨hL, hR⟩ := Sec7.R7Aux131.heights_const hκ hκ4 hleft hright hθ
    exact Sec7.StripSafe.isStagedHistory_constFam h44 hκ hκ4 hb (wordOf_jumps hb) (wordOf_fn hb) hh hL hR
  · change IsStagedHistory (16 / i.kappa) x.boundary x.jumps x.measure x.field (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (twoAngleFam h44 hκ hκ4 (wordOf hb) x.field (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ))
    rw [twoAngleFam_twoAngleSpec]
    exact isStagedHistory_twoFam_strip h44 hκ hκ4 hb hleft hright hh (wordOf_jumps hb) (wordOf_fn hb) hθ₀ hθ

end InteractingSLE.Sec5.TwoAngle
