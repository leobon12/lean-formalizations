import InteractingSLE.Spec.Sec7.R5OutSourceAmbient
import InteractingSLE.Spec.Sec7.R5OLawWire

/-! # The permitted shared lift and initial-height data for outer R.5 -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec7.R5Out
open LocalSets WholeField PocketTraversal Lemma71C PocketStop PocketStopSide PocketStopField PocketUnionPt
  PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketCoupling PocketAdapt R5Phase R5Wall PhaseSel
open PocketWordPerQ R5Ref
variable {Ω : Type*}

/-- Shared inputs only: a coherent branch, its lattice phase, the two
lift words and the initial wall heights. All geometric covers and increment
laws are proved separately. The finite set includes the current attachments. -/
def TwoSeedOuterLiftHeightInputOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ →
    ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ),
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω);
      ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧
        (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
          ∃ m : ℤ, δ q ω = m * phaseStep κ) ∧
        R7AmbientLiftWord κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7OuterLiftWord κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
          (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u (X q) ∧
        (∀ ω ∈ A, outerExc R L r η ψ q ω ⊆ X q ω)

/-- Shared inputs only: a coherent branch, its lattice phase, the two
lift words and the initial wall heights. All geometric covers and increment
laws are proved separately. The finite set includes the current attachments. -/
def TwoSeedOuterLiftHeightInputInfOn (κ rL rR : ℝ) [MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[wallsSigma P R L] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
    @IsPointMeasurableInf Ω (wallsSigma P R L) R L r G ψ →
    ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∃ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → Set ℂ),
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω);
      ∀ q : ℝ≥0, (∀ ω, (X q ω).Finite) ∧
        (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
          ∃ m : ℤ, δ q ω = m * phaseStep κ) ∧
        R7AmbientLiftWordInf κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7OuterLiftWordInf κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) ρL' ρR' P A R L r η ψ
          (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a W' ζ' VL VR (δ q) (X q) q ∧
        R7InitialHeights κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
          (fun ω => cfPocket (R ω) (L ω) r) (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u (X q) ∧
        (∀ ω ∈ A, outerExcInf R L r η ψ q ω ⊆ X q ω)

end InteractingSLE.Sec7.R5Out
