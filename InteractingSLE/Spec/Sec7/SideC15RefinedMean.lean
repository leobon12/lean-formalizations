/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Frame
import InteractingSLE.Spec.Sec7.SideC15Inverse
import InteractingSLE.Spec.Sec7.SideC15Refine

/-!
# R90a normalized initial means on the ready branch partition

PROVE-SIDE-COLLAR2. The native source formula applies to every version
of the actual original exterior mean. Transport the proved source formula through the actual physical field
relations and use the exact native-word normalization.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.Current.SideTest

open LocalSets WholeField WangWu Sec7.SideC15 Sec7 Sec7.SideC14 Sec7.SideC13 Sec7.SideC12 Sec7.Aux119Heights
  Sec7.PocketCoord Sec7.PocketWordPerQ Sec7.StripWall Sec7.StripSideHeightProb

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual source strip produces normalized native initial means on
all positive branch fibres. Any existing counterflow mean supplies the
original mean by inverse physical transport; there is no original-mean,
branch-constancy, native-word or flow-formula hypothesis. -/
theorem exists_refined_initialMeanFormula_native_of_ready
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} [IsProbabilityMeasure d.measure]
    {b : ℝ → ℝ} {jumps : Finset ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) b jumps d.measure d.field W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps →
      sleLambda (16 / i.kappa) ≤ b y + a * chiC (16 / i.kappa))
    (hu₀ : IsBoundedHarmonicExtension b jumps d.originalMean)
    (hvR : IsWallVersion d.measure (E (StripSys.alphaSpec
      (rs136Theta1 (16 / i.kappa) i.leftWeight))) 1 d.rightWall)
    (hvL : IsWallVersion d.measure (E (StripSys.betaSpec (StripSys.rt j.seed)
      (rs136Theta2 (16 / i.kappa) i.rightWeight))) (StripSys.rt j.seed) (d.leftWall j.seed))
    (hj : j.Ready d)
    (hleft : ∀ᵐ ω ∂d.measure, ω ∈ j.event →
      changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) ⊆ leftSideOf (range (d.rightWall ω)))
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω))
    (hu₁ : InnerProductSpace.HarmonicOnNhd d.coupledMean H)
    (hHarm : EqOn d.harmonic d.coupledMean H) :
    ∃ n : Ω → ℤ, Measurable[(j.target i d).walls] n ∧
      (∀ᵐ ω ∂d.measure, ω ∈ j.event → 0 < d.measure (branchEvent j.event n (n ω))) ∧
      ∀ k : ℤ, 0 < d.measure (branchEvent j.event n k) →
        (j.refineBranch n k).Ready d ∧
        ∀ g : Ω → DistOn upperHalfPlaneOpens,
          IsLocalSetMean ((j.refineBranch n k).capacityReference i d 0)
            ((j.refineBranch n k).target i d).zeroField d.measure g →
          ∃ G : Ω → DistOn upperHalfPlaneOpens,
            IsLocalSetMean ((j.refineBranch n k).capacityReference i d 0)
              ((j.refineBranch n k).target i d).zeroField d.measure G ∧
            ∀ᵐ ω ∂d.measure, ω ∈ (j.refineBranch n k).event →
              ∀ z ∈ ((j.refineBranch n k).target i d).domain ω,
                harmRep (G ω) (H \ (j.refineBranch n k).capacityReference i d 0 ω) z +
                  ((j.refineBranch n k).target i d).harmonic z +
                  chiC ((j.refineBranch n k).target i d).kappa *
                    (((j.refineBranch n k).target i d).baseChart ω).2.2 z =
                  (j.refineBranch n k).initialWordExtension i d ω
                    ((((j.refineBranch n k).target i d).baseChart ω).1 z) - sourceFrameOffset (16 / i.kappa) 0 k := by
  obtain ⟨n, hn, hPieces, _⟩ := j.exists_ready_branch_refinement i hj
    hvR.continuous hvL.continuous hvL.zero 0
  refine ⟨n, hn, ae_mem_positive_branchEvent d.measure j.event n, ?_⟩
  intro k hk
  obtain ⟨hReady, hbranch⟩ := hPieces k hk
  refine ⟨hReady, ?_⟩
  intro g hg
  let j' := j.refineBranch n k
  have hg' := hg
  rw [target_zeroField] at hg'
  have hG₀ := localSetMean_inversePhysicalMean
    (j'.original_filling_regular (i := i) hReady 0) hT hTr hu₀.1 hu₁ hg'
  have hleft' : ∀ᵐ ω ∂d.measure, ω ∈ j'.event →
      changePocket (d.rightWall ω) (d.leftWall j'.seed ω) (StripSys.rt j'.seed) ⊆
        leftSideOf (range (d.rightWall ω)) :=
    hleft.mono fun _ h hω => h hω.1
  let G₀ := fun ω => inversePhysicalMean (-(π * chiC (16 / i.kappa))) (chiC i.kappa) 0
    d.originalMean d.coupledMean (g ω)
  let G := fun ω => physicalMean (-(π * chiC (16 / i.kappa))) (chiC i.kappa) 0
    d.originalMean d.coupledMean (G₀ ω)
  have hMean := j'.initialMeanFormula_native_of_ready h44 hS hcumL hcumR hu₀ hvR hvL
    hReady hleft' hG₀ k (fun ω hω => (hbranch ω hω).1) hT hTr hu₁ hHarm
  refine ⟨G, hMean.1, ?_⟩
  simpa only [target_event] using hMean.2

end InteractingSLE.Wire.Current.SideTest
