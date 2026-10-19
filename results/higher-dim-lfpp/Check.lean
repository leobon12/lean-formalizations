import HigherDimLFPP.Frozen.MainTheorem
import HigherDimLFPP.Frozen.DimensionComparison
import HigherDimLFPP.Frozen.KappaTwo
import HigherDimLFPP.Frozen.BandVecNormSq
import HigherDimLFPP.Frozen.FieldExists
import HigherDimLFPP.Frozen.LQGDimensionAsymptotics
import HigherDimLFPP.Frozen.GFFCircleAverage
import Mathlib.Util.AssertNoSorry

/-! A small-parameter limit for higher-dimensional LFPP: the exact statements of the seven frozen
theorems (Theorem 1.1 of the source paper for every `d ≥ 2`, the dimension comparison (1.8),
`κ₂ = a*/log 16`, the variance normalization, non-vacuity, and the two `d = 2` corollaries), the
twenty frozen definitions, the main proof ingredients (the existence of the exponent with the
percolation duality repair, and the upper and lower comparisons), absence of `sorry` and axioms,
then an axiom audit of every declaration in the included `HigherDimLFPP`, `LQGMetric`,
`LQGDimension`, `QuantumZipper` and `GaussianLQG` modules. The result guide documents the
correspondence with the paper. -/

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ## Theorem 1.1: its type, restated verbatim from `HigherDimLFPP/Frozen/MainTheorem.lean` -/

#check HigherDimLFPP.theorem11

namespace HigherDimLFPP

example : ∀ d : ℕ, 2 ≤ d →
    (∀ n : ℕ, A n d ≠ ⊥ ∧ A n d ≠ ⊤) ∧
    (∀ n r : ℕ, A (n + r) d ≤ A n d + A r d) ∧
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) ∧
    0 < kappa d ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∃ lam : ℝ, IsLFPPExponent H P ζ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) →
        Tendsto (fun ζ => lam ζ / ζ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa d)) :=
  theorem11

/-! ## The six further frozen theorems, restated verbatim from `HigherDimLFPP/Frozen/` -/

-- (1.8), `DimensionComparison.lean`
example : ∀ d : ℕ, 2 ≤ d →
    ((d : ℝ) - 1) ^ (2 / 3 : ℝ) * kappa 2 ≤ kappa d ∧ kappa d ≤ ((d : ℝ) - 1) * kappa 2 :=
  dimension_comparison

-- `κ₂ = a*/log 16`, `KappaTwo.lean`
example : kappa 2 = LQGDimension.aStar / Real.log 16 :=
  kappa_two_eq

-- variance normalization of (1.1), `BandVecNormSq.lean`
example : ∀ d : ℕ, 1 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ a b : ℝ, 0 < a → a < b → ∀ z : Rd d,
      MemLp (bandKernel κ a b z) 2 volume ∧ ‖bandVec κ a b z‖ ^ 2 = Real.log (b / a) :=
  bandVec_norm_sq

-- non-vacuity, `FieldExists.lean`
example : ∀ d : ℕ, 1 ≤ d →
    (∃ κ : Rd d → ℝ, IsLFPPKernel κ) ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℝ → Rd d → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsWhiteNoise P W ∧
          ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε) :=
  field_exists

-- d = 2, LQG dimension, `LQGDimensionAsymptotics.lean`
example : Tendsto (fun γ : ℝ => (LQGMetric.dGamma γ - 2) / γ ^ (4 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (2 ^ (-1 / 3 : ℝ) * kappa 2)) :=
  lqg_dimension_asymptotics

-- d = 2, circle-average LFPP of the whole-plane GFF, `GFFCircleAverage.lean`
example : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage h P →
      (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, ∃ lam : ℝ, LQGDimension.IsLFPPExponent h P ξ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, LQGDimension.IsLFPPExponent h P ξ (lam ξ)) →
        Tendsto (fun ξ => lam ξ / ξ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa 2)) :=
  gff_circle_average_lfpp

/-! ## The hypotheses of Theorem 1.1 can be met: an exponent exists for an actual field -/

example (d : ℕ) (hd : 2 ≤ d) :
    ∃ (κ : Rd d → ℝ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℝ → Rd d → Ω → ℝ), IsLFPPKernel κ ∧ IsProbabilityMeasure P ∧ IsWhiteNoise P W ∧
      (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) ∧
      ∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∃ lam : ℝ, IsLFPPExponent H P ζ lam := by
  obtain ⟨⟨κ, hκ⟩, hfield⟩ := field_exists d (by omega)
  obtain ⟨Ω, _, P, W, H, hP, hW, hH⟩ := hfield κ hκ
  exact ⟨κ, Ω, inferInstance, P, W, H, hκ, hP, hW, hH,
    ((theorem11 d hd).2.2.2.2 κ hκ Ω P W hW H hH).1⟩

end HigherDimLFPP

assert_no_sorry HigherDimLFPP.theorem11
assert_no_sorry HigherDimLFPP.dimension_comparison
assert_no_sorry HigherDimLFPP.kappa_two_eq
assert_no_sorry HigherDimLFPP.bandVec_norm_sq
assert_no_sorry HigherDimLFPP.field_exists
assert_no_sorry HigherDimLFPP.lqg_dimension_asymptotics
assert_no_sorry HigherDimLFPP.gff_circle_average_lfpp
#print axioms HigherDimLFPP.theorem11
#print axioms HigherDimLFPP.dimension_comparison
#print axioms HigherDimLFPP.kappa_two_eq
#print axioms HigherDimLFPP.bandVec_norm_sq
#print axioms HigherDimLFPP.field_exists
#print axioms HigherDimLFPP.lqg_dimension_asymptotics
#print axioms HigherDimLFPP.gff_circle_average_lfpp

/-! ## The twenty frozen definitions -/

#print HigherDimLFPP.Rd
#print HigherDimLFPP.Vg
#print HigherDimLFPP.energy
#print HigherDimLFPP.gCov
#print HigherDimLFPP.Ag
#print HigherDimLFPP.A
#print HigherDimLFPP.kappa
#print HigherDimLFPP.IsLFPPKernel
#print HigherDimLFPP.scaleKernel
#print HigherDimLFPP.WN
#print HigherDimLFPP.IsWhiteNoise
#print HigherDimLFPP.bandKernel
#print HigherDimLFPP.bandVec
#print HigherDimLFPP.IsBandVersion
#print HigherDimLFPP.cube
#print HigherDimLFPP.e₁
#print HigherDimLFPP.IsAdmissiblePath
#print HigherDimLFPP.lfppLength
#print HigherDimLFPP.lfppDistance
#print HigherDimLFPP.IsLFPPExponent

/-! ## The parts of the proof of Theorem 1.1 -/

-- the Gaussian part: finiteness, subadditivity, the limit `κ_d`, and `κ_d > 0` (§2)
#check HigherDimLFPP.theorem11_variational
-- the existence of `λ_d(ζ)` for every `ζ > 0`, chosen before the realization (DGZ Prop. 1.1, App. A.1)
#check HigherDimLFPP.exponent_exists
#check HigherDimLFPP.prop31
#check HigherDimLFPP.lemma33
-- the d-dimensional percolation duality that DGZ use without proof, replaced by proved statements
#print HigherDimLFPP.Perc.PoincareMod2
#print HigherDimLFPP.Perc.ExtBoundaryConn
#print HigherDimLFPP.Perc.SurgeryLemma
#print HigherDimLFPP.Perc.EnclosureBound
#check HigherDimLFPP.Perc.poincareMod2
#check HigherDimLFPP.Perc.extBoundaryConn
#check HigherDimLFPP.Perc.surgeryLemma
#check HigherDimLFPP.Perc.peierlsD
#check HigherDimLFPP.Perc.diameterBound
#check HigherDimLFPP.Perc.enclosureBound
-- the upper comparison (§4, (4.25)) with Lemma 4.3, and the lower comparison (§5, (5.29)) with Lemma 5.3
#check HigherDimLFPP.Upper.goodRecordMeanBound_all
#check HigherDimLFPP.Upper.upperComparison_limsup
#check HigherDimLFPP.Lower.lemma53Holds_holds
#check HigherDimLFPP.Lower.lowerComparison_liminf
-- the assembly
#check HigherDimLFPP.theorem11_of_inputs

assert_no_sorry HigherDimLFPP.theorem11_variational
assert_no_sorry HigherDimLFPP.exponent_exists
assert_no_sorry HigherDimLFPP.prop31
assert_no_sorry HigherDimLFPP.lemma33
assert_no_sorry HigherDimLFPP.Perc.poincareMod2
assert_no_sorry HigherDimLFPP.Perc.extBoundaryConn
assert_no_sorry HigherDimLFPP.Perc.surgeryLemma
assert_no_sorry HigherDimLFPP.Perc.peierlsD
assert_no_sorry HigherDimLFPP.Perc.diameterBound
assert_no_sorry HigherDimLFPP.Perc.enclosureBound
assert_no_sorry HigherDimLFPP.Upper.goodRecordMeanBound_all
assert_no_sorry HigherDimLFPP.Upper.upperComparison_limsup
assert_no_sorry HigherDimLFPP.Lower.lemma53Holds_holds
assert_no_sorry HigherDimLFPP.Lower.lowerComparison_liminf
#print axioms HigherDimLFPP.theorem11_variational
#print axioms HigherDimLFPP.exponent_exists
#print axioms HigherDimLFPP.prop31
#print axioms HigherDimLFPP.lemma33
#print axioms HigherDimLFPP.Perc.poincareMod2
#print axioms HigherDimLFPP.Perc.extBoundaryConn
#print axioms HigherDimLFPP.Perc.surgeryLemma
#print axioms HigherDimLFPP.Perc.peierlsD
#print axioms HigherDimLFPP.Perc.diameterBound
#print axioms HigherDimLFPP.Perc.enclosureBound
#print axioms HigherDimLFPP.Upper.goodRecordMeanBound_all
#print axioms HigherDimLFPP.Upper.upperComparison_limsup
#print axioms HigherDimLFPP.Lower.lemma53Holds_holds
#print axioms HigherDimLFPP.Lower.lowerComparison_liminf

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := moduleNames[idx.toNat]!
    if (`HigherDimLFPP).isPrefixOf m || (`LQGMetric).isPrefixOf m || (`LQGDimension).isPrefixOf m ||
        (`QuantumZipper).isPrefixOf m || (`GaussianLQG).isPrefixOf m then
      roots := roots.push n
  if roots.isEmpty then throwError "No included declarations found"
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing declaration {n}"
    match ci with
    | .axiomInfo _ =>
      axioms := axioms.insert n
      unless allowed.contains n do
        throwError "Disallowed axiom reachable from included declarations: {n}"
    | _ => pure ()
    pending := pending ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      pending := pending ++ v.getUsedConstants
  logInfo m!"HIGHER_DIM_LFPP_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
