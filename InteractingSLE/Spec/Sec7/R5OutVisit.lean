/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutDomain
import InteractingSLE.Spec.Sec7.SideVisClock

/-!
# Source original-time references in outer pockets

The existing rational visit references are retained. At an interior visit,
the left erasure stop equals the original time. Consequently their relative
charts lie in the ambient reference complement, as required by R88.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open Sec6 PocketTraversal PocketAdapt PocketStopWallsFin PocketUnionPt Lemma71C
  PocketStop PocketStopMarked PocketStopMarked.Outer PocketStopSide PocketCoupling PocketCoord PocketJordan
  PocketWordAssembly PocketSeedOpen R5Phase

section Clock

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ t : ℝ} {ψ : ℂ → ℂ}

/-- An actual interior visit is the left end of its erasure fibre. -/
theorem pocketFibreLeft_clock_of_visit (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    (ht : t ∈ visitSet η C τ σ) :
    pocketFibreLeft η C τ σ (pocketClock η C τ σ t) = t := by
  have hv : pocketClock η C τ σ t ∈ Ico 0 (pocketClock η C τ σ σ) :=
    ⟨hP.erase.clock_nonneg ht.1.1.le, hP.erase.clock_lt_clock_σ ⟨ht.1.1.le, ht.1.2⟩⟩
  have hright := hP.erase.fibre_clock_of_mem ht
  have hle := fibreLeft_le_fibreRight hP.erase.continuous_clock hP.erase.lt.le
    (show pocketClock η C τ σ t ∈ Icc (pocketClock η C τ σ τ) (pocketClock η C τ σ σ) by
      rw [R7StopIn.IsErasurePocket.clock_τ]; exact ⟨hv.1, hv.2.le⟩)
  change pocketFibreLeft η C τ σ (pocketClock η C τ σ t) ≤
    pocketFibre η C τ σ (pocketClock η C τ σ t) at hle
  rw [hright] at hle
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  exact HOuter.notMem_of_mem_Ioc_fibre' hP.erase hv ⟨hlt, hright.ge⟩ ht.2

/-- The optional left stop of a visit capacity is the original visit time. -/
theorem ambTime0_relCap_of_visit (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    (ht : t ∈ visitSet η C τ σ) :
    ambTime0 η C τ σ ψ (relCap η C τ σ ψ t) = t := by
  change pocketFibreLeft η C τ σ (clockOf (pocketClock η C τ σ σ)
    (capInv (trav η C τ σ ψ) (capClock (trav η C τ σ ψ) (relTime η C τ σ t)))) = t
  rw [hP.driven.capInv_eq (relTime_nonneg hP ⟨ht.1.1.le, ht.1.2⟩),
    clockOf_relTime hP ⟨ht.1.1.le, ht.1.2⟩, pocketFibreLeft_clock_of_visit hP ht]

/-- The same left-fibre identity at a seed-opening visit. -/
theorem pocketFibreLeftInf_clock_of_visit (hP : IsOuterPocketInf W η C y₀ τ ψ)
    (ht : t ∈ visitSetInf η C τ) :
    pocketFibreLeftInf η C τ (pocketClockInf η C τ t) = t := by
  have hv : pocketClockInf η C τ t ∈ Ico 0 (clockEnd η C τ) :=
    ⟨hP.erase.clock_nonneg ht.1.le, hP.erase.clock_lt_clockEnd ht.1.le⟩
  have hright := hP.erase.fibre_clock_of_mem ht
  have hle := (HOuter.pocketFibreLeftInf_props hP.erase hv).2.2
  rw [hright] at hle
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  exact HOuter.notMem_of_mem_Ioc_fibreInf' hP.erase hv ⟨hlt, hright.ge⟩ ht.2

/-- The optional left stop of a seed-opening visit capacity is the visit time. -/
theorem ambTime0Inf_relCapInf_of_visit (hP : IsOuterPocketInf W η C y₀ τ ψ)
    (ht : t ∈ visitSetInf η C τ) :
    ambTime0Inf η C τ ψ (relCapInf η C τ ψ t) = t := by
  change pocketFibreLeftInf η C τ (clockOf (clockEnd η C τ)
    (capInv (travInf η C τ ψ) (capClock (travInf η C τ ψ) (relTimeInf η C τ t)))) = t
  rw [hP.driven.capInv_eq (relTimeInf_nonneg hP ht.1.le),
    clockOf_relTimeInf hP ht.1.le, pocketFibreLeftInf_clock_of_visit hP ht]

end Clock

section Visit

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {A : Set Ω} {ω : Ω}

/-- At an original interior visit the reference chart is live and lies in the ambient reference complement. -/
theorem visit_chart_subset (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {s : ℝ} (hs : 0 ≤ s) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) :
    ((visitCap R L r η ψ ω s).toNNReal : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom : Set ℂ) ⊆
        cfPocket (R ω) (L ω) r ∩ (H \ QuantumZipper.fwdHull (W ω) s) := by
  have hP := hcfg.toPocket hψ
  have hvisit' : s ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := ⟨hP.erase.mem_Ioo s hs hvisit, hvisit⟩
  have hp := SideVis.erasure_relCap_pos_lt_of_visit hP.erase hP.driven hvisit'
  have hpos : 0 < visitCap R L r η ψ ω s := hp.1
  have hlive : ((visitCap R L r η ψ ω s).toNNReal : ℝ≥0∞) <
      capLife (travAll R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hpos.le]
    exact hp.2
  have hT : R5Ref.leftStop R L r η ψ (visitCap R L r η ψ ω s).toNNReal ω = s := by
    change ambTime0 _ _ _ _ _ ((visitCap R L r η ψ ω s).toNNReal : ℝ) = s
    rw [Real.coe_toNNReal _ hpos.le]
    exact ambTime0_relCap_of_visit hP hvisit'
  refine ⟨hlive, isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hP.driven hlive hc, ?_⟩
  have hsub := current_dom_subset_ambient hω hcfg hψ hc hdom heq hlive
  rwa [hT] at hsub

/-- At an original interior visit the reference chart is live and lies in the ambient reference complement. -/
theorem visit_chart_subsetInf (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {s : ℝ} (hs : 0 ≤ s) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) :
    ((visitCapInf R L r η ψ ω s).toNNReal : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom : Set ℂ) ⊆
        cfPocket (R ω) (L ω) r ∩ (H \ QuantumZipper.fwdHull (W ω) s) := by
  have hP := hcfg.toPocketInf hψ
  have hvisit' : s ∈ visitSetInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) := ⟨hP.erase.mem_Ioi s hs hvisit, hvisit⟩
  have hp := SideVis.erasureInf_relCap_pos_lt_of_visit hP.erase hP.driven hvisit'
  have hpos : 0 < visitCapInf R L r η ψ ω s := hp.1
  have hlive : ((visitCapInf R L r η ψ ω s).toNNReal : ℝ≥0∞) <
      capLife (travAllInf R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hpos.le]
    exact hp.2
  have hT : R5Ref.leftStopInf R L r η ψ (visitCapInf R L r η ψ ω s).toNNReal ω = s := by
    change ambTime0Inf _ _ _ _ ((visitCapInf R L r η ψ ω s).toNNReal : ℝ) = s
    rw [Real.coe_toNNReal _ hpos.le]
    exact ambTime0Inf_relCapInf_of_visit hP hvisit'
  refine ⟨hlive, isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hP.driven hlive hc, ?_⟩
  have hsub := current_dom_subset_ambientInf hω hcfg hψ hc hdom heq hlive
  rwa [hT] at hsub

end Visit

end InteractingSLE.Sec7.R5Out
