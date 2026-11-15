import InteractingSLE.Spec.Sec7.R5OutAmbientGeom

/-! # The exposed-wall source geometry from the outer configurations (R98) -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec7.R5Out
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase R5Ref MartChar.RealFlow
open Theorem14.SB.FinRel (freeNear)
open Wire.Current.SideTest (rationalOriginalTime)
variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart}

/-- The exposed-wall incident geometry, in the ambient half-disc form of R98. -/
theorem r7OuterAmbientGeometry [MeasurableSpace Ω] {P : Measure Ω}
    {α : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL' xR' ρL' ρR' (fun t => W' t ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : ∀ ω ∈ A, xL ω 0 = 0) (hxR : ∀ ω ∈ A, xR ω 0 = 0)
    {X : Ω → Set ℂ} {q : ℝ≥0} (hX : ∀ ω ∈ A, R5Wall.outerExc R L r η ψ q ω ⊆ X ω) :
    R7OuterAmbientGeometry P A R L r η ψ xL xR c W' ζ' VL VR X q := by
  filter_upwards [hpath] with ω hp hω hq ξ _ hExc hS
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h := (hcfg ω hω).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζ ω hω) hV fun _ => rfl
  exact exists_ambient_outer_cover hω (hcfg ω hω)
    (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hζ ω hω)
    (fun i t => hL i t) (fun j t => hR j t) (hxL ω hω) (hxR ω hω) hq ξ
    (fun h => hExc (Or.inl h)) (fun h => hExc (Or.inr (hX ω hω h))) hS

/-- The exposed-wall incident geometry, in the ambient half-disc form of R98. -/
theorem r7OuterAmbientGeometryInf [MeasurableSpace Ω] {P : Measure Ω}
    {α : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL' xR' ρL' ρR' (fun t => W' t ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : ∀ ω ∈ A, xL ω 0 = 0) (hxR : ∀ ω ∈ A, xR ω 0 = 0)
    {X : Ω → Set ℂ} {q : ℝ≥0} (hX : ∀ ω ∈ A, R5Wall.outerExcInf R L r η ψ q ω ⊆ X ω) :
    R7OuterAmbientGeometryInf P A R L r η ψ xL xR c W' ζ' VL VR X q := by
  filter_upwards [hpath] with ω hp hω hq ξ _ hExc hS
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h := (hcfg ω hω).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζ ω hω) hV fun _ => rfl
  exact exists_ambient_outer_coverInf hω (hcfg ω hω)
    (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hζ ω hω)
    (fun i t => hL i t) (fun j t => hR j t) (hxL ω hω) (hxR ω hω) hq ξ
    (fun h => hExc (Or.inl h)) (fun h => hExc (Or.inr (hX ω hω h))) hS

end InteractingSLE.Sec7.R5Out
