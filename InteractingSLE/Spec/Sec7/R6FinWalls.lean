/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6RelInner

/-!
# R.6's walls: the outer and inner walls' data on an R.7 configuration

PROVE-R6-CERT2. The walls–hull laws used by R.6 (`R6Cert.isLocalSet_activeCompl_outer`, `_cf`,
`R6Cert.ae_r6Germ_outer_cf`) take, for each wall, continuity and start at `0` at every sample, measurability at
fixed times, almost sure determination by the centred field and entrance-history locality. This file packages them
(`IsWallData`) and proves them for the outer walls `R`, `L` (versions of `α_R`, `α_L`) and for the inner walls
`innerRight k r_L R M_R`, `innerLeft k r_R L M_L` (`M_R`, `M_L` versions of the certified frontiers), as in
`OuterPhNext.r7OuterPhaseSideRemaining_of_cont_shared`. It also proves that a pocket nested in a bounded pocket is
bounded (`rightLo_pos_of_cfPocket_subset`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Fin

open WholeField R7Outer R7Leaves R6Nest R6Rel PocketCoord PocketJordan PocketMarks Lemma71I

section Walls

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The walls' data of the walls–hull laws** for one wall `R` and the centred field `h₀`. -/
structure IsWallData (P : Measure Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens) (R : Ω → ℝ≥0 → ℂ) : Prop where
  cont : ∀ ω, Continuous (R ω)
  zero : ∀ ω, R ω 0 = 0
  meas : ∀ t, Measurable fun ω => R ω t
  det : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧ (fun ω => R ω t) =ᵐ[P] fun ω => f (h₀ ω)
  loc : Sec6.IsEntranceHistoryLocal R h₀ P

variable [IsProbabilityMeasure P] {k rL rR c c' : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- The walls' data of a version of a Borel flow line of infinite lifetime of the R.7 field. -/
theorem isWallData_of_flowLine (hk4 : 4 < k) {θ : ℝ}
    (hgff : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    {α : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ P h α ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {Φ : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ} (hΦ : Measurable Φ)
    (hαΦ : ∀ ω, α ω = Φ (h ω)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ) u₀)
    {R : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => R ω t) (hRα : ∀ᵐ ω ∂P, R ω = α ω) :
    IsWallData P (centredField h u₀) R := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  exact ⟨hRc, hR0, hRm, fun t => hdet_of_borel hΦ hαΦ hRα u₀ t,
    isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hfl hζ hu₀ hRc hR0 hRm hRα⟩

/-- **The outer right wall's data** (a version of `α_R`). -/
theorem isWallData_R (hk4 : 4 < k) (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ) u₀)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : R7Leaves.IsR7Versions P W' αR αL R L η) :
    IsWallData P (centredField h u₀) R := by
  obtain ⟨ΦαR, _, _, _, hΦαR, -, -, -, hΦ⟩ := hcfg.borel
  exact isWallData_of_flowLine hk4 hcfg.gff hcfg.flow_αR (hcfg.regular.mono fun ω hω => hω.2.2.2.2.1) hΦαR
    (fun ω => (hΦ ω).1) hu₀ hV.R_cont hV.R_zero hV.R_meas hV.R_ae

/-- **The outer left wall's data** (a version of `α_L`). -/
theorem isWallData_L (hk4 : 4 < k) (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ) u₀)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : R7Leaves.IsR7Versions P W' αR αL R L η) :
    IsWallData P (centredField h u₀) L := by
  obtain ⟨_, _, _, ΦαL, -, -, -, hΦαL, hΦ⟩ := hcfg.borel
  exact isWallData_of_flowLine hk4 hcfg.gff hcfg.flow_αL (hcfg.regular.mono fun ω hω => hω.2.2.2.2.2.2.2) hΦαL
    (fun ω => (hΦ ω).2.2.2) hu₀ hV.L_cont hV.L_zero hV.L_meas hV.L_ae

/-- **The inner right wall's data** (`α_R` or the version `M_R` of the certified frontier `β_R`). -/
theorem isWallData_innerRight (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ) u₀)
    {R L MR : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : R7Leaves.IsR7Versions P W' αR αL R L η)
    (hMR : IsFrontierVersion P βR MR) :
    IsWallData P (centredField h u₀) (innerRight k rL R MR) := by
  by_cases hd : k / 2 - 4 < rL
  · simp only [innerRight, hd, ↓reduceIte]
    obtain ⟨_, ΦβR, _, _, -, hΦβR, -, -, hΦ⟩ := hcfg.borel
    exact isWallData_of_flowLine hk4 hcfg.gff hcfg.flow_βR (hcfg.regular.mono fun ω hω => hω.2.2.2.2.2.1) hΦβR
      (fun ω => (hΦ ω).2.1) hu₀ hMR.1 hMR.2.1 hMR.2.2.1 hMR.2.2.2
  · simp only [innerRight, hd, ↓reduceIte]
    exact isWallData_R hk4 hcfg hu₀ hV

/-- **The inner left wall's data** (`α_L` or the version `M_L` of the certified frontier `β_L`). -/
theorem isWallData_innerLeft (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ) u₀)
    {R L ML : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : R7Leaves.IsR7Versions P W' αR αL R L η)
    (hML : IsFrontierVersion P βL ML) :
    IsWallData P (centredField h u₀) (innerLeft k rR L ML) := by
  by_cases hd : k / 2 - 4 < rR
  · simp only [innerLeft, hd, ↓reduceIte]
    obtain ⟨_, _, ΦβL, _, -, -, hΦβL, -, hΦ⟩ := hcfg.borel
    exact isWallData_of_flowLine hk4 hcfg.gff hcfg.flow_βL (hcfg.regular.mono fun ω hω => hω.2.2.2.2.2.2.1) hΦβL
      (fun ω => (hΦ ω).2.2.1) hu₀ hML.1 hML.2.1 hML.2.2.1 hML.2.2.2
  · simp only [innerLeft, hd, ↓reduceIte]
    exact isWallData_L hk4 hcfg hu₀ hV

end Walls

/-! ### Nested pockets of a bounded pocket are bounded -/

section Nest

variable {R L R' L' : ℝ≥0 → ℂ} {r r' : ℝ≥0}

/-- A change pocket whose counterflow-chart pocket lies in a bounded one (`0 < rightLo`) is bounded. -/
theorem rightLo_pos_of_cfPocket_subset (h : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r)
    (h' : IsChangeConfigInc R' L' r') (hsub : cfPocket R' L' r' ⊆ cfPocket R L r) : 0 < rightLo R' L' r' := by
  refine h'.rightLo_pos fun h0 => zero_notMem_closure_of_rightLo_pos h hpos (closure_mono ?_ h0)
  intro z hz
  have hm : negInv z ∈ cfPocket R L r := hsub ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := hm
  rw [← WangWu.negInv_negInv z, ← hwz, WangWu.negInv_negInv]
  exact hw

end Nest

end InteractingSLE.Sec7.R6Fin
