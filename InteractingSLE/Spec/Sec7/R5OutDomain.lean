/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutStop
import InteractingSLE.Spec.Sec7.R5RefFamily
import InteractingSLE.Spec.Sec7.HOuterGeo
import InteractingSLE.Spec.Sec7.R5EnlCollar

/-!
# The domain obligation in transferring R.5 to outer pockets

PROVE-R5-OUTER. The outer active face lies inside the ambient pocket domain.
The extremal reference-family wrapper needs equality with that entire domain.
The lemmas below expose the missing reverse inclusion without assuming it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open PocketTraversal PocketAdapt Lemma71C PocketCoupling PocketStopSide PocketUnionPt
  PocketStopField PocketStop R5Phase PocketMarks PocketCoord PocketJordan
  PocketWordAssembly PocketSeedOpen

variable {Ω : Type*}

/-- The actual relative chart is a chart of the relative hull complement, for any pocket shape. -/
theorem current_dom_eq_relHull {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hγ : IsDrivenCurve (γ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω)
    (heq : EqOn (c ω).1 (ψ ω) (C ω)) (hCH : C ω ⊆ H)
    (hψ : IsConformalBijection (ψ ω) (C ω) H) :
    ((relChart c γ q ω).dom : Set ℂ) = H \ HOuter.relHull (C ω) (ψ ω) (γ ω) q := by
  rw [← activeDom_eq_relChart_dom hω hq hγ hc,
    activeDom_eq_inter (C := C) (ψ := ψ)
      (F := fun ω => HOuter.relHull (C ω) (ψ ω) (γ ω) q) hω hq hc hdom heq hψ.2.injOn
      (HOuter.image_inter_H_diff_relHull hCH hψ (γ ω) q),
    HOuter.H_diff_relHull hCH, ← inter_assoc, inter_self]

/-- Outer current charts give the needed inclusion, rather than the extremal domain identity. -/
theorem current_dom_subset_ambient {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart}
    {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (W ω) (R5Ref.leftStop R L r η ψ q ω)) := by
  have hP := hcfg.toPocket hψ
  rw [current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ)
      hω hq (hcfg.props hψ).1 hc hdom heq hP.subset_H hψ.2.2.2.1,
    HOuter.H_diff_relHull hP.subset_H]
  exact fun z hz => ⟨hz.1, HOuter.relDomain_subset_domain_ambTime0 hcfg.erase hcfg.trace
    hcfg.continuous_W hcfg.W_zero hP.subset_H
    (hcfg.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)).isBounded
    hP.jordan (hcfg.props hψ).1 q.coe_nonneg
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) hz⟩

/-- The same domain inclusion for an outer pocket opening at the seed. -/
theorem current_dom_subset_ambientInf {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart}
    {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (W ω) (R5Ref.leftStopInf R L r η ψ q ω)) := by
  have hP := hcfg.toPocketInf hψ
  rw [current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ)
      hω hq (hcfg.props hψ).1 hc hdom heq hP.subset_H hψ.2.2.2.1,
    HOuter.H_diff_relHull hP.subset_H]
  exact fun z hz => ⟨hz.1, HOuter.relDomain_subset_domain_ambTime0Inf hcfg.erase hcfg.trace
    hP.subset_H hP.jordan (hcfg.props hψ).1 q.coe_nonneg
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) hz⟩

/-- Clause 3 forces every selected reference chart to uniformize the whole reference complement. -/
theorem reference_dom_of_r5ClausesOn [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {C : Ω → Set ℂ}
    {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ} {X : Ω → Set ℂ}
    {liftB : ℕ → Ω → ℂ → ℝ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart} {q : ℝ≥0}
    (hcl : R5Enl.R5ClausesOn κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {i : ℕ} {ω : Ω} (hM : ω ∈ M i) :
    ((old i ω).dom : Set ℂ) = C ω ∩ (H \ F i ω) := by
  obtain ⟨hω, -, -, -, hOld⟩ := hcl.2.2.1 i ω hM
  exact hOld.trans (H_diff_liveExt_zero hω (hγ ω hω))

/-- A point in the ambient pocket domain outside the chosen face obstructs
the reference-chart identity. -/
theorem not_reference_dom_eq_of_bulge {old : Chart} {C F : Set ℂ} {z : ℂ}
    (hz : z ∈ C ∩ (H \ F)) (hface : z ∉ (old.dom : Set ℂ)) :
    (old.dom : Set ℂ) ≠ C ∩ (H \ F) := by
  intro h
  exact hface (h.symm ▸ hz)

end InteractingSLE.Sec7.R5Out
