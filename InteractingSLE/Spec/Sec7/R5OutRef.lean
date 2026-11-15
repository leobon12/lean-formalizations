/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutVisit

/-!
# Component clause 3 for the source outer reference family

The source rational original-time charts and pair events of R5Ref are reused
unchanged. Their domains contain the current component and lie in the old
reference complement. No equality with that entire complement is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open PocketTraversal PocketAdapt PocketStop PocketStopSide PocketStopMarked
  PocketCoupling PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen
  PocketStopWallsFin Lemma71C R5Phase R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {A : Set Ω}

/-- The zero original-time reference has zero relative capacity in an outer pocket. -/
theorem visitCap_zero {ω : Ω}
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) : visitCap R L r η ψ ω 0 = 0 := by
  have hP := hcfg.toPocket hψ
  exact relCap_eq_zero_of_le hP hP.erase.nonneg

/-- The zero reference also has zero relative capacity for a seed-opening outer pocket. -/
theorem visitCapInf_zero {ω : Ω}
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) : visitCapInf R L r η ψ ω 0 = 0 := by
  have hP := hcfg.toPocketInf hψ
  exact relCapInf_eq_zero_of_le hP hP.erase.nonneg

/-- Source reference events satisfy the component domain clause for bounded outer pockets. -/
theorem refEvent_spec
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (F : ℕ → Ω → Set ℂ) (q : ℝ≥0) :
    ∀ i, ∀ ω ∈ refEvent A R L r W η ψ F q i,
      ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (refChart c R L r η ψ i ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChart c R L r η ψ i ω).dom ∧
      ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0 ω := by
  rintro i ω ⟨hω, hq, hv, hpq, hF⟩
  have hγ := ((hcfg ω hω).props (hψ ω hω)).1
  have hp : ((visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
      capLife (travAll R L r η ψ ω) :=
    lt_of_le_of_lt (by exact_mod_cast hpq) hq
  refine ⟨hω, hq, isConformal_relChart_of_driven (c := c) hγ hp (hc ω hω),
    relChart_dom_antitone (hc ω hω) hγ hq hpq, ?_⟩
  rw [H_diff_liveExt_zero hω hγ, hF]
  rcases hv with hv | hz
  · exact (visit_chart_subset hω (hcfg ω hω) (hψ ω hω) (hc ω hω)
      (hdom ω hω) (heq ω hω) (rationalOriginalTime i).coe_nonneg hv).2.2
  · have hp0 : (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal = 0 := by
      rw [hz, NNReal.coe_zero, visitCap_zero (hcfg ω hω) (hψ ω hω), Real.toNNReal_zero]
    rw [refChart, hp0, relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hdom ω hω, hz, NNReal.coe_zero,
      QuantumZipper.RS.fwdHull_zero_eq_empty (hcfg ω hω).continuous_W, sdiff_empty]
    exact fun z hz => ⟨hz, PocketJordan.image_negInv_subset_H
      (hcfg ω hω).conf.changePocket_subset_H hz⟩

/-- Source reference events satisfy the component domain clause for seed-opening outer pockets. -/
theorem refEventInf_spec
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (F : ℕ → Ω → Set ℂ) (q : ℝ≥0) :
    ∀ i, ∀ ω ∈ refEventInf A R L r W η ψ F q i,
      ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      (refChartInf c R L r η ψ i ω).IsConformal ∧
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChartInf c R L r η ψ i ω).dom ∧
      ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆
        H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0 ω := by
  rintro i ω ⟨hω, hq, hv, hpq, hF⟩
  have hγ := ((hcfg ω hω).props (hψ ω hω)).1
  have hp : ((visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
      capLife (travAllInf R L r η ψ ω) :=
    lt_of_le_of_lt (by exact_mod_cast hpq) hq
  refine ⟨hω, hq, isConformal_relChart_of_driven (c := c) hγ hp (hc ω hω),
    relChart_dom_antitone (hc ω hω) hγ hq hpq, ?_⟩
  rw [H_diff_liveExt_zero hω hγ, hF]
  rcases hv with hv | hz
  · exact (visit_chart_subsetInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω)
      (hdom ω hω) (heq ω hω) (rationalOriginalTime i).coe_nonneg hv).2.2
  · have hp0 : (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal = 0 := by
      rw [hz, NNReal.coe_zero, visitCapInf_zero (hcfg ω hω) (hψ ω hω), Real.toNNReal_zero]
    rw [refChartInf, hp0, relChart_zero_dom (c := c) (γ := travAllInf R L r η ψ) hγ, hdom ω hω, hz, NNReal.coe_zero,
      QuantumZipper.RS.fwdHull_zero_eq_empty (hcfg ω hω).continuous_W, sdiff_empty]
    exact fun z hz => ⟨hz, PocketJordan.image_negInv_subset_H
      (hcfg ω hω).conf.changePocket_subset_H hz⟩

end InteractingSLE.Sec7.R5Out
