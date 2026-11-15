/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TnChart
import InteractingSLE.Spec.Sec7.R6TwoFace

/-!
# The boundary adapters for the two kinds of outer pocket

PROVE-R6-TWO. Interior visits give interior capacity tips in a right
neighbourhood. The actual outer charts therefore have strict seed
signs and the boundary models required by the local face theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Tn

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField
open HOuter PocketWordAssembly PocketSeedOpen R6Safe R6Two
open PocketStopMarked.Outer

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- The boundary model of an actual bounded outer current chart. -/
theorem outer_boundaryChart
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (htip : capTrace (travAll R L r η ψ ω) q ∈ H) :
    ∃ _M : BoundaryChart (cfPocket (R ω) (L ω) r)
      (closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)})
      (currentChart A R L r η ψ n q ω) (leftSeed (travAll R L r η ψ) q ω)
      (rightSeed (travAll R L r η ψ) q ω),
      leftSeed (travAll R L r η ψ) q ω < 0 ∧ 0 < rightSeed (travAll R L r η ψ) q ω := by
  exact boundaryChart (n := n) (fun ω hω => (hcfg ω hω).erase.isOpen)
    (fun ω hω => ((hcfg ω hω).toPocket (hψ ω hω)).subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1)
    (isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos (hcfg ω hω).conf (hcfg ω hω).bounded))
    (hcfg ω hω).conf.cfPt_openPt_notMem (hψ ω hω) hω ((hcfg ω hω).props (hψ ω hω)).1 hq0 hq htip

/-- The boundary model of an actual outer chart opening at the flow seed. -/
theorem outer_boundaryChartInf
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (htip : capTrace (travAllInf R L r η ψ ω) q ∈ H) :
    ∃ _M : BoundaryChart (cfPocket (R ω) (L ω) r) (closure (cfPocket (R ω) (L ω) r))
      (currentChartInf A R L r η ψ n q ω) (leftSeed (travAllInf R L r η ψ) q ω)
      (rightSeed (travAllInf R L r η ψ) q ω),
      leftSeed (travAllInf R L r η ψ) q ω < 0 ∧ 0 < rightSeed (travAllInf R L r η ψ) q ω := by
  exact boundaryChartInf (n := n) (fun ω hω => (hcfg ω hω).erase.isOpen)
    (fun ω hω => ((hcfg ω hω).toPocketInf (hψ ω hω)).subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) (hψ ω hω) hω ((hcfg ω hω).props (hψ ω hω)).1 hq0 hq htip

/-- Strictly later capacity tips remain interior after a bounded outer
pocket visit; includes the nonnegative visit capacity. -/
theorem tips_after_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {V : Set ℂ} {x₀ y₀ : ℂ}
    {τ σ T : ℝ} {φ : ℂ → ℂ} (hP : IsOuterPocket W η V x₀ y₀ τ σ φ)
    (hT0 : 0 ≤ T) (htip : η T ∈ V) :
    0 ≤ PocketStopMarked.relCap η V τ σ φ T ∧
    ∃ ε > 0, ∀ q' : ℝ≥0, PocketStopMarked.relCap η V τ σ φ T < q' →
      (q' : ℝ) < PocketStopMarked.relCap η V τ σ φ T + ε →
      capTrace (PocketStopMarked.trav η V τ σ φ) q' ∈ H := by
  have hv := hP.erase.mem_visitSet hT0 htip
  have hI : T ∈ Ico τ σ := ⟨hv.1.1.le, hv.1.2⟩
  have hc0 : 0 ≤ PocketStopMarked.relCap η V τ σ φ T :=
    hP.driven.capClock_nonneg (PocketStopMarked.Outer.relTime_nonneg hP hI)
  have hc := PocketStopMarked.Outer.relCap_lt_capLife hP hI
  have hlive : ((PocketStopMarked.relCap η V τ σ φ T).toNNReal : ℝ≥0∞) <
      capLife (PocketStopMarked.trav η V τ σ φ) := by
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0] using hc
  have htH : capTrace (PocketStopMarked.trav η V τ σ φ) (PocketStopMarked.relCap η V τ σ φ T).toNNReal ∈ H := by
    rw [capTrace_relCap_outer_of_visit hP hv]
    exact hP.jordan.2.2.2.1.2.mapsTo htip
  obtain ⟨ε, hε, hεtip⟩ := exists_right_capTrace_mem_H hP.driven hlive htH
  refine ⟨hc0, ε, hε, fun q' hlo hhi => hεtip q' ?_ ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]; exact hlo
  · rwa [Real.coe_toNNReal _ hc0]

/-- The same interior-tip persistence for an outer pocket opening at the seed. -/
theorem tips_after_visitInf {W : ℝ → ℝ} {η : ℝ → ℂ} {V : Set ℂ} {y₀ : ℂ}
    {τ T : ℝ} {φ : ℂ → ℂ} (hP : IsOuterPocketInf W η V y₀ τ φ)
    (hT0 : 0 ≤ T) (htip : η T ∈ V) :
    0 ≤ PocketStopMarked.relCapInf η V τ φ T ∧
    ∃ ε > 0, ∀ q' : ℝ≥0, PocketStopMarked.relCapInf η V τ φ T < q' →
      (q' : ℝ) < PocketStopMarked.relCapInf η V τ φ T + ε →
      capTrace (PocketStopMarked.travInf η V τ φ) q' ∈ H := by
  have hv := hP.erase.mem_visitSet hT0 htip
  have hc0 : 0 ≤ PocketStopMarked.relCapInf η V τ φ T :=
    hP.driven.capClock_nonneg (PocketStopMarked.Outer.relTimeInf_nonneg hP hv.1.le)
  have hc := PocketStopMarked.Outer.relCapInf_lt_capLife hP hv.1.le
  have hlive : ((PocketStopMarked.relCapInf η V τ φ T).toNNReal : ℝ≥0∞) <
      capLife (PocketStopMarked.travInf η V τ φ) := by
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0] using hc
  have htH : capTrace (PocketStopMarked.travInf η V τ φ) (PocketStopMarked.relCapInf η V τ φ T).toNNReal ∈ H := by
    rw [capTrace_relCapInf_outer_of_visit hP hv]
    exact hP.jordan.2.2.2.1.2.mapsTo htip
  obtain ⟨ε, hε, hεtip⟩ := exists_right_capTrace_mem_H hP.driven hlive htH
  refine ⟨hc0, ε, hε, fun q' hlo hhi => hεtip q' ?_ ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]; exact hlo
  · rwa [Real.coe_toNNReal _ hc0]

end InteractingSLE.Sec7.R6Tn
