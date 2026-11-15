/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Native
import InteractingSLE.Spec.Sec7.SideC14ChangePocket

/-!
# The original filled-pocket formula with the actual native word

PROVE-SIDE-COLLAR2. Apply the proved general selected-pocket strip
identity to the actual ready chart. The native finite-word extension
is now produced, so there is no assumed initial-flow formula or word
matching in this theorem. The identity holds for all mean versions.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.Current.SideTest

open LocalSets WholeField Sec7 Sec7.SideC14 Sec7.SideC13 Sec7.SideC12 Sec7.Aux119Heights
  Sec7.PocketCoord Sec7.PocketWordPerQ Sec7.StripWall Sec7.StripSideHeightProb

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Every original filled-pocket mean has the actual native flow word,
with every valid source branch. No native-word or flow identity is an input. -/
theorem ae_initialFlowMean_native_of_ready
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
    {gC : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (fun ω => H \ selectedChangePocket j.event d.rightWall (d.leftWall j.seed)
      (StripSys.rt j.seed) ω) (centredField d.field d.originalMean) d.measure gC) :
    ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) →
        gC ω φ = ∫ z, v z * φ z) → ∀ n : ℤ,
      Lemma71N.IsPocketBranch (d.leftWall j.seed ω) (d.rightWall ω)
        (conjugateFlowChart ((j.target i d).baseChart ω)) n →
      ∀ z ∈ changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed),
        v z + d.originalMean z = j.canonicalInitialFlowMean i d ω
          (conjugateFlowMap ((j.target i d).baseChart ω) z) - chiC (16 / i.kappa) *
            (conjugateFlowLift ((j.target i d).baseChart ω) z + 2 * π * n) := by
  have hκ : 0 < 16 / i.kappa := div_pos (by norm_num) (lt_trans (by norm_num) i.kappa_gt_four)
  have hκ4 : 16 / i.kappa < 4 := (div_lt_iff₀ (lt_trans (by norm_num) i.kappa_gt_four)).2 (by linarith [i.kappa_gt_four])
  have hAeq : counterflowA (16 / i.kappa) - 2 = i.kappa / 2 - 4 := by
    unfold counterflowA
    have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
    rw [hd]
    ring
  have hθ := rs136_mem_Ioo hκ hκ4
    (show i.leftWeight ∈ Ioo (-2) (counterflowA (16 / i.kappa) - 2) from
      ⟨i.left_gt, hAeq ▸ i.left_lt⟩)
    (show i.rightWeight ∈ Ioo (-2) (counterflowA (16 / i.kappa) - 2) from
      ⟨i.right_gt, hAeq ▸ i.right_lt⟩)
  have hA : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)] j.event :=
    hj.2.2.2.2.2.2.2.1
  have hF := fun ω hω => j.isFlowChart_conjugate_of_ready (i := i) hj hvR.continuous hvL.continuous
    (by rwa [target_event]) (ω := ω)
  have hSource := ae_eqOn_selectedChangePocket_twoAngleStrip h44 hS hcumL hcumR
    (Ioo_subset_Icc_self hθ.1) (Ioo_subset_Icc_self hθ.2) hj.1 hu₀ hvL hvR hA
    (fun ω hω => (hF ω hω).config) hgC
  filter_upwards [hSource, hleft] with ω hSourceω hleftω hω v hv hrep n hn
  simp only [← conjugateFlowChart_fwd, ← conjugateFlowChart_lift]
  have hDcf := j.isDomainChart_baseChart (i := i) hj hvR.continuous hvL.continuous
    (ω := ω) (by rwa [target_event])
  rw [target_domain] at hDcf
  have hD := SideC13.isDomainChart_conjugate_pocket hDcf
  obtain ⟨ℓ, hℓ, hlift⟩ := hD.2.2
  exact hSourceω hω v hv hrep
    (SideAnc.jordanUnif (PocketJordan.openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) (j.chart ω))
    (conjugateFlowChart ((j.target i d).baseChart ω)) ℓ n (j.canonicalInitialFlowMean i d ω) (hF ω hω)
    (hleftω hω) hℓ (fun z hz => hlift hz) hn
    (j.canonicalInitialFlowMean_source_extension (i := i) hj hvR.continuous hvL.continuous (by rwa [target_event]))

end InteractingSLE.Wire.Current.SideTest
