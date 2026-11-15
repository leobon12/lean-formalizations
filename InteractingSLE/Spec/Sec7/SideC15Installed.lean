/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15RefinedMean
import InteractingSLE.Spec.Sec7.SideC14Context

/-!
# The actual word context installs the R90a refined native initial means

PROVE-SIDE-COLLAR2. Use the two-angle strip's own field transports and
its actual normalized installer. All branch refinements, native-word
identifications and original-flow formulas are produced in the proof.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx

open Current LocalSets Sec7 Sec7.SideC15 Sec7.Aux119Heights Sec7.PocketCoord
  Sec7.StripWall Sec7.PocketWordIn

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual normalized installed side on every positive source-branch
piece has a native initial mean. Only an existing counterflow mean
version is needed; its original mean is constructed by inverse transport.
The installer uses offset `2πχ(1-k)` on the fibre labelled `k`. -/
theorem installedFrameSide_exists_refined_initialMean
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hHarm : EqOn x.harmonic (counterflowObjects hS.counterflow).mean H)
    (j : SideTest Ω) (hj : j.Ready (wordSafeObjects i x hS))
    (hvR : IsWallVersion x.measure (x.experiment (StripSys.alphaSpec
      (rs136Theta1 (16 / i.kappa) i.leftWeight))) 1 x.rightWall)
    (hvL : IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt j.seed)
      (rs136Theta2 (16 / i.kappa) i.rightWeight))) (StripSys.rt j.seed) (x.leftWall j.seed))
    (hleft : ∀ᵐ ω ∂x.measure, ω ∈ j.event →
      changePocket (x.rightWall ω) (x.leftWall j.seed ω) (StripSys.rt j.seed) ⊆ leftSideOf (range (x.rightWall ω))) :
    let d := wordSafeObjects i x hS
    ∃ n : Ω → ℤ, Measurable[(j.target i d).walls] n ∧
      (∀ᵐ ω ∂x.measure, ω ∈ j.event → 0 < x.measure (branchEvent j.event n (n ω))) ∧
      ∀ k : ℤ, 0 < x.measure (branchEvent j.event n k) →
        let j' := j.refineBranch n k
        j'.Ready d ∧ ∀ g : Ω → DistOn upperHalfPlaneOpens,
          IsLocalSetMean (j'.capacityReference i d 0) (j'.target i d).zeroField x.measure g →
          ∃ G : Ω → DistOn upperHalfPlaneOpens,
            IsLocalSetMean (j'.capacityReference i d 0) (j'.target i d).zeroField x.measure G ∧
            ∀ᵐ ω ∂x.measure, ω ∈ j'.event → ∀ z ∈ (j'.target i d).domain ω,
              harmRep (G ω) (H \ j'.capacityReference i d 0 ω) z + (j'.target i d).harmonic z +
                chiC (j'.target i d).kappa * ((j'.target i d).baseChart ω).2.2 z =
              j'.initialWordExtension i d ω (((j'.target i d).baseChart ω).1 z) -
                (installedFrameSide i x hS side idx (fun _ => sourceFrameOffset (16 / i.kappa) 0 k) j').offset := by
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, _, hu₁⟩ := counterflowObjects_spec hS.counterflow
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω) := by
    simpa only [d, wordSafeObjects, hd] using hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω) := by
    simpa only [d, wordSafeObjects, hd, zero_mul] using hTr
  exact j.exists_refined_initialMeanFormula_native_of_ready cond44 hS hcumL hcumR
    hu₀ hvR hvL hj hleft hT' hTr' hu₁.1 hHarm

end InteractingSLE.Wire.T12Ctx
