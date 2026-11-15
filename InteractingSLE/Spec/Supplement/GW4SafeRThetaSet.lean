/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocGeom
import InteractingSLE.Spec.Supplement.GW4CLocSafe
import InteractingSLE.Spec.Supplement.GW4SafeREtaPhysical

/-! # GW4: the transported union is exactly the relative hull -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets GW4Traverse GW4Rel Sec5.GlueCond

/-- The reverse inclusion to the landed union containment. Every relative
hull point comes from the counterflow part of the actual retained union. -/
theorem chartSet_eq_relHullFam {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    {S : Set ℂ} (hSC : Disjoint S C) {y : LawUnique.HistorySpace 0 0}
    (hy : y ∈ Sec5.CfRegQ.goodCfSet) {w : ℝ≥0 → ℝ}
    (hw : Sec5.Prop411Q.cfDrv y = fun s : ℝ => w s.toNNReal) (t : ℝ≥0) :
    chartSet c (relClosureH (S ∪ cfHullQ t y)) = relHullFam c C w t := by
  refine (chartSet_subset_relHullFam hch hCo hCH hSC hy hw t).antisymm ?_
  rintro v ⟨z, ⟨hzK, hzD⟩, rfl⟩
  have hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  rw [mem_chartSet_iff hc (relMapC_mem_H hch hzD)]
  have hzC : WangWu.negInv z ∈ C := hzD
  have hCan : c.2.1 (WangWu.negInv (relMapC c z)) = WangWu.negInv z := by
    change c.2.1 (WangWu.negInv (WangWu.negInv (c.1 (WangWu.negInv z)))) = _
    rw [WangWu.negInv_negInv, hch.2.2.2.1.1 hzC]
  change c.2.1 (WangWu.negInv (relMapC c z)) ∈ _
  rw [hCan]
  have hzCf : WangWu.negInv z ∈ cfHullQ t y := by
    rw [cfHullQ_eq_of_mem_goodCfSet hy t, hw]
    exact ⟨z, hzK, rfl⟩
  exact ⟨hCH hzC, subset_closure ⟨Or.inr hzCf, hCH hzC⟩⟩

end InteractingSLE.Theorem14.GW4Fix.CLoc

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets CLoc GW4Rel GW4Traverse MartChar Sec5.GlueCond Sec5.Cond44Ref

/-- At the actual live clock the retained union and the physical safe
hull are the same set, almost surely under the conditioned measure. -/
theorem ae_chartSet_eq_safeHull {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {F : Frame} (hF : F.IsOk) {Wd W Rv : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {V ζ : Ω → ℝ≥0∞} (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTae : ∀ᵐ ω ∂Q, ω ∈ GT) (hVW : ∀ᵐ ω ∂Q, ∀ r, Wd r ω = W r ω)
    (hζ : ∀ᵐ ω ∂Q, ζ ω = ⊤) (hver : IsGW4RelVersionR Q Wd F.c F.C Rv V)
    {A S : Ω → Set ℂ} (t : ℝ≥0)
    (hA : ∀ᵐ ω ∂Q, A ω = relClosureH (S ω ∪ cfHullQ t (cfHistory W ζ ω)))
    (hS : ∀ᵐ ω ∂Q, Disjoint (S ω) F.C) :
    ∀ᵐ ω ∂Q, lineClock F Wd GT V t ω < V ω →
      chartSet F.c (A ω) = safeHull F Wd GT Rv V t ω := by
  filter_upwards [hGTae, hVW, hζ, hA, hS, hver.1.1.2.2.2.2]
    with ω hω hWω hζω hAω hSω hHull hLive
  have hw := hGT ω hω
  have hCo := Frame.isOpen_C hF hw
  have hCH := CLoc.subset_H_of_mem_betweenComponents hF.2.1
  have hWe : (fun r => W r ω) = fun r => Wd r ω := funext fun r => (hWω r).symm
  have hcW : Continuous (fun r => W r ω) := hWe ▸ hw.1
  have hy : cfHistory W ζ ω ∈ Sec5.CfRegQ.goodCfSet := by
    refine Sec5.CfRegQ.cfHistory_mem_goodCfSet hζω hcW ?_
      (η := trc fun r => Wd r ω) ?_
    · rw [← hWω 0]; exact hw.2.1
    · rw [hWe]; exact hw.2.2.1
  have hDrv : Sec5.Prop411Q.cfDrv (cfHistory W ζ ω) =
      fun s : ℝ => W s.toNNReal ω := by
    rw [Sec5.CfRegQ.cfDrv_eq_hDrv, hDrv_cfHistory hζω hcW]
  have hSet : chartSet F.c (A ω) = F.hullAt (fun r => Wd r ω) t := by
    rw [hAω, chartSet_eq_relHullFam hF.2.2.2.1 hCo hCH hSω hy
      (w := fun r => W r ω) hDrv]
    rw [Frame.hullAt, hWe]
  rw [hSet, safeHull, ite_eq_left hLive]
  change F.hullAt (fun r => Wd r ω) t = H ∩
    QuantumZipper.fwdHull (wpath Rv ω) (lineClock F Wd GT V t ω).toNNReal
  rw [component_fwdHull_eq_hullAt hF hGT hω (hver.1.1.2.1 ω)
      (hver.1.1.2.2.1 ω) hHull hLive]
  apply (inter_eq_right.2 ?_).symm
  intro v hv
  obtain ⟨z, hz, rfl⟩ := hv
  exact relMapC_mem_H hF.2.2.2.1 hz.2

end InteractingSLE.Theorem14.GW4Fix
