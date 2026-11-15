/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5PhaseR7
import InteractingSLE.Spec.Sec7.PocketSideInSyncClock
import InteractingSLE.Spec.Sec7.PocketSideInActVisit
import InteractingSLE.Spec.Sec7.SideC5Relative
import InteractingSLE.Spec.Sec7.PocketStopSideCloseGeometry

/-!
# Lemma R.5's reference charts at original visits of a change pocket (clause 3 of `R5Clauses`)

Packet PROVE-R5-PHASE. Proof of Lemma R.5 (spec p. 475): "In the `s` chart …" — the old reference at an original
time `s` at which the counterflow visits the pocket is read in the pocket's own relative chart at the relative
capacity `Q(s)` reached at `s`. This file proves, for the two-seed tests of a walls' event, the pathwise reference-chart
clause of `R5Clauses` for these visit references:

* `visitCap`, `visitCapInf` (defs): the relative capacity reached at an original time;
* **`visitCap_spec`**, **`visitCapInf_spec`**: at an original visit it is positive and live, and the relative chart
  there has domain `C ∩ (ℍ ∖ K_s)` (`K_s` the counterflow's hull at `s`);
* **`reference_chart_at_visit`**, **`reference_chart_at_visitInf`**: the reference chart is conformal, contains the
  current domain at every later live capacity `q ≥ Q(s)`, and has domain `ℍ ∖ liveExt A γ C K_s 0` (the reference
  complement), on the event that the regularized hull at `s` is the hull of the driver.

These are the R.7 analogues of the late `SideTest.isDomainChart_capacityReference_at_visit` and
`current_dom_subset_reference_at_visit`. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Phase

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked Sec6

variable {Ω : Type*}

/-- The relative capacity reached at the original time `t` (bounded change pocket). -/
def visitCap (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t

/-- The relative capacity reached at the original time `t` (pocket opening at the flow seed). -/
def visitCapInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (ω : Ω) (t : ℝ) : ℝ :=
  relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t

/-- The complement of a reference at relative level `0` on a test. -/
theorem H_diff_liveExt_zero {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ} {ω : Ω} (hω : ω ∈ A)
    (hγ : IsDrivenCurve (γ ω)) : H \ liveExt A γ C F 0 ω = C ω ∩ (H \ F ω) := by
  rw [liveExt_of_live ⟨hω, PocketPhaseMeans.capLife_pos hγ⟩]
  ext z
  simp only [extHullSet, Set.mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff]
  constructor
  · rintro ⟨hz, hn⟩
    by_cases hzC : z ∈ C ω
    · exact ⟨hzC, hz, fun hF => hn ⟨hz, Or.inr hF⟩⟩
    · exact absurd ⟨hz, Or.inl hzC⟩ hn
  · rintro ⟨hzC, hz, hF⟩
    exact ⟨hz, fun h => h.2.elim (fun h' => h' hzC) hF⟩

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- **At an original visit the relative capacity is positive and live, and the relative chart there has the
original-time domain** (bounded change pocket). -/
theorem visitCap_spec {A : Set Ω} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordan (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : η ω t ∈ cfPocket (R ω) (L ω) r) :
    0 < visitCap R L r η ψ ω t ∧
      ((visitCap R L r η ψ ω t).toNNReal : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω t).toNNReal ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (W ω) t) := by
  unfold visitCap
  have hP := hcfg.conf.isReversePocket_of_counterflow
    (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
    hcfg.trace hcfg.continuous_W hcfg.W_zero hcfg.revR hcfg.revL hcfg.visR
  have hψ' : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1) (ψ ω) := by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ
  have hv := hP.mem_visitSet ht hvisit
  obtain ⟨hpos, hlive⟩ := relCap_pos_lt_of_visit hP hcfg.attach hψ' hv
  have hlive' : ((relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t).toNNReal : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hpos.le]
    exact hlive
  refine ⟨hpos, hlive', ?_⟩
  rw [← activeDom_eq_relChart_dom hω hlive' ((hcfg.isDrivenCurve hψ).1) hc,
    activeDom_cfPocket_eq_stopHull hω hcfg hψ hc hdom heq hlive']
  simp only [stopHull]
  rw [Real.coe_toNNReal _ hpos.le, ambTime_relCap_of_visit hP hcfg.attach hψ' hv]

/-- **Lemma R.5's reference chart at an original visit** (bounded change pocket): conformal, containing the current
domain at every later live capacity, with domain the reference complement. -/
theorem reference_chart_at_visit {A : Set Ω} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordan (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : Ω → Set ℂ}
    {s : ℝ≥0} (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) (hHull : F ω = fwdHull (W ω) s) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (hord : (visitCap R L r η ψ ω s).toNNReal ≤ q) :
    (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
        (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom ∧
      ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom : Set ℂ) =
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) F 0 ω := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨-, hlive, hdomQ⟩ := visitCap_spec hω hcfg hψ hc hdom heq s.coe_nonneg hvisit
  refine ⟨isConformal_relChart_of_driven hγ hlive hc, relChart_dom_antitone hc hγ hq hord, ?_⟩
  rw [hdomQ, H_diff_liveExt_zero hω hγ, hHull]

end Bounded

section Inf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- **At an original visit the relative capacity is positive and live, and the relative chart there has the
original-time domain** (pocket opening at the flow seed). -/
theorem visitCapInf_spec {A : Set Ω} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : η ω t ∈ cfPocket (R ω) (L ω) r) :
    0 < visitCapInf R L r η ψ ω t ∧
      ((visitCapInf R L r η ψ ω t).toNNReal : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω t).toNNReal ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (W ω) t) := by
  unfold visitCapInf
  have hP := hcfg.isReversePocketInf
  have hψ' : IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
    rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  have hv := hP.mem_visitSet ht hvisit
  obtain ⟨hpos, hlive⟩ := relCapInf_pos_lt_of_visit hP hcfg.attach hψ' hv
  have hlive' : ((relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)
      t).toNNReal : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hpos.le]
    exact hlive
  refine ⟨hpos, hlive', ?_⟩
  rw [← activeDom_eq_relChart_dom hω hlive' ((hcfg.isDrivenCurve hψ).1) hc,
    activeDom_cfPocketInf_eq_stopHull hω hcfg hψ hc hdom heq hlive']
  simp only [stopHullInf]
  rw [Real.coe_toNNReal _ hpos.le, ambTimeInf_relCapInf_of_visit hP hcfg.attach hψ' hv]

/-- **Lemma R.5's reference chart at an original visit** (pocket opening at the flow seed). -/
theorem reference_chart_at_visitInf {A : Set Ω} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : Ω → Set ℂ}
    {s : ℝ≥0} (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) (hHull : F ω = fwdHull (W ω) s) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (hord : (visitCapInf R L r η ψ ω s).toNNReal ≤ q) :
    (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
        (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom ∧
      ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom : Set ℂ) =
        H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) F 0 ω := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨-, hlive, hdomQ⟩ := visitCapInf_spec hω hcfg hψ hc hdom heq s.coe_nonneg hvisit
  refine ⟨isConformal_relChart_of_driven hγ hlive hc, relChart_dom_antitone hc hγ hq hord, ?_⟩
  rw [hdomQ, H_diff_liveExt_zero hω hγ, hHull]

end Inf

end InteractingSLE.Sec7.R5Phase
