/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutAmbient

/-!
# The source outer hull cover from the common lift word

All reference selection, incident collars and ambient accesses are proved;
the remaining per-collar lift input is the same R7AmbientLiftWord used for
the extremal tests.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar fwdMap fwdHull chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω} {c : Ω → Chart}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- The hull cover from the permitted lift word for a bounded outer pocket. -/
theorem r7AmbientCoverHull_of_liftWord [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {α : ℝ}
    {xL₀ : Fin mL → ℝ} {xR₀ : Fin mR → ℝ} {ρL₀ : Fin mL → ℝ} {ρR₀ : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤)
    (hLW : R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAll R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ'
      VL VR δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q := by
  filter_upwards [ae_exists_ambient_cover hpath hcfg hψ hc hdom heq hζ q, hLW] with ω hgeo hlw hω hq ξ hξ hXω hCω
  obtain ⟨i, x, ε, x', hM, hv, hcol, hz, hland, hev, hjump, hcur, hold⟩ :=
    hgeo hω hq ξ (fun h => hXω (Or.inl h)) hCω
  obtain ⟨d, hd, hword⟩ :=
    hlw hω hq ξ hξ (fun h => hXω (Or.inr h)) hCω i x ε x' hM hv hcol hz.2 hjump hcur hold
  exact ⟨i, x, ε, x', d, _, hM, hcol.1, hcol.2.1, hcol.2.2.1, hz, hland, hev, hjump, hcur, hd, hword⟩

/-- The hull cover from the permitted lift word for a seed-opening outer pocket. -/
theorem r7AmbientCoverHull_of_liftWordInf [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {α : ℝ}
    {xL₀ : Fin mL → ℝ} {xR₀ : Fin mR → ℝ} {ρL₀ : Fin mL → ℝ} {ρR₀ : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤)
    (hLW : R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAllInf R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ'
      VL VR δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q := by
  filter_upwards [ae_exists_ambient_coverInf hpath hcfg hψ hc hdom heq hζ q, hLW] with ω hgeo hlw hω hq ξ hξ hXω hCω
  obtain ⟨i, x, ε, x', hM, hv, hcol, hz, hland, hev, hjump, hcur, hold⟩ :=
    hgeo hω hq ξ (fun h => hXω (Or.inl h)) hCω
  obtain ⟨d, hd, hword⟩ :=
    hlw hω hq ξ hξ (fun h => hXω (Or.inr h)) hCω i x ε x' hM hv hcol hz.2 hjump hcur hold
  exact ⟨i, x, ε, x', d, _, hM, hcol.1, hcol.2.1, hcol.2.2.1, hz, hland, hev, hjump, hcur, hd, hword⟩

end InteractingSLE.Sec7.R5Out
