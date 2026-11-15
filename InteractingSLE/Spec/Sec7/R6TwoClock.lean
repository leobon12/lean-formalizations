/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoGrow

/-!
# R.6: the physical tip and strict capacity growth of an outer pocket

PROVE-R6-TWO. These are the outer-pocket versions of the landed contained
pocket clock identities. They use erasure and driven traversal, without
reverse visit order on the outer incoming arm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal PocketStopMarked Lemma71C
open PocketStopMarked.Outer

/-- Undoing the capacity and erasure clocks at a physical visit of an
outer pocket returns precisely the initial chart of that physical point. -/
theorem capTrace_relCap_outer_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {x₀ y₀ : ℂ} {τ σ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) (ht : t ∈ visitSet η C τ σ) :
    capTrace (trav η C τ σ ψ) (relCap η C τ σ ψ t).toNNReal = ψ (η t) := by
  have htI : t ∈ Ico τ σ := ⟨ht.1.1.le, ht.1.2⟩
  have hc0 : 0 ≤ relCap η C τ σ ψ t :=
    hP.driven.capClock_nonneg (Outer.relTime_nonneg hP htI)
  dsimp only [capTrace]
  rw [Real.coe_toNNReal _ hc0]
  change trav η C τ σ ψ (capInv (trav η C τ σ ψ)
    (capClock (trav η C τ σ ψ) (relTime η C τ σ t))) = _
  rw [hP.driven.capInv_eq (Outer.relTime_nonneg hP htI)]
  change ψ (η (pocketFibre η C τ σ
    (clockOf (pocketClock η C τ σ σ) (relTime η C τ σ t)))) = _
  rw [Outer.clockOf_relTime hP htI, hP.erase.fibre_clock_of_mem ht]

/-- The same clock identity for an outer pocket opening at the seed. -/
theorem capTrace_relCapInf_outer_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {y₀ : ℂ} {τ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsOuterPocketInf W η C y₀ τ ψ) (ht : t ∈ visitSetInf η C τ) :
    capTrace (travInf η C τ ψ) (relCapInf η C τ ψ t).toNNReal = ψ (η t) := by
  have hc0 : 0 ≤ relCapInf η C τ ψ t :=
    hP.driven.capClock_nonneg (Outer.relTimeInf_nonneg hP ht.1.le)
  dsimp only [capTrace]
  rw [Real.coe_toNNReal _ hc0]
  change travInf η C τ ψ (capInv (travInf η C τ ψ)
    (capClock (travInf η C τ ψ) (relTimeInf η C τ t))) = _
  rw [hP.driven.capInv_eq (Outer.relTimeInf_nonneg hP ht.1.le)]
  change ψ (η (pocketFibreInf η C τ
    (clockOf (clockEnd η C τ) (relTimeInf η C τ t)))) = _
  rw [Outer.clockOf_relTimeInf hP ht.1.le, hP.erase.fibre_clock_of_mem ht]

/-- The relative capacity of an outer pocket increases strictly after
every actual interior visit. No visit order on its walls is needed. -/
theorem relCap_outer_lt_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {x₀ y₀ : ℂ} {τ σ a b : ℝ} {ψ : ℂ → ℂ}
    (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) (ha : a ∈ visitSet η C τ σ)
    (hb : b ∈ Ico τ σ) (hab : a < b) :
    relCap η C τ σ ψ a < relCap η C τ σ ψ b := by
  obtain ⟨t', ht', ht'I⟩ := hP.erase.exists_mem_Ioo_of_mem hab ⟨le_rfl, hab.le⟩ ha
  have hne : pocketClock η C τ σ a ≠ pocketClock η C τ σ b := fun h =>
    Set.disjoint_left.1 ((erasureClock_eq_iff hP.erase.isOpen_visitSet hab).1 h) ht' ht'I
  have hlt := lt_of_le_of_ne (hP.erase.monotone_clock hab.le) hne
  have hL := hP.erase.clock_lt_clock_σ hb
  have hrt : relTime η C τ σ a < relTime η C τ σ b := by
    unfold relTime
    rw [div_lt_div_iff₀ (sub_pos.2 (hlt.trans hL)) (sub_pos.2 hL)]
    nlinarith only [hlt, hP.erase.clock_σ_pos]
  exact hP.driven.strictMonoOn_capClock
    (Outer.relTime_nonneg hP ⟨ha.1.1.le, ha.1.2⟩) (Outer.relTime_nonneg hP hb) hrt

/-- Strict capacity growth after a seed-opening outer-pocket visit. -/
theorem relCapInf_outer_lt_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {y₀ : ℂ} {τ a b : ℝ} {ψ : ℂ → ℂ}
    (hP : IsOuterPocketInf W η C y₀ τ ψ) (ha : a ∈ visitSetInf η C τ) (hab : a < b) :
    relCapInf η C τ ψ a < relCapInf η C τ ψ b := by
  obtain ⟨t', ht', ht'I⟩ := hP.erase.exists_mem_Ioo_of_mem hab ⟨le_rfl, hab.le⟩ ha
  have hne : pocketClockInf η C τ a ≠ pocketClockInf η C τ b := fun h =>
    Set.disjoint_left.1 ((erasureClock_eq_iff hP.erase.isOpen_visitSet hab).1 h) ht' ht'I
  have hlt := lt_of_le_of_ne (hP.erase.monotone_clock hab.le) hne
  have hb : τ ≤ b := ha.1.le.trans hab.le
  have hL := hP.erase.clock_lt_clockEnd hb
  have hrt : relTimeInf η C τ a < relTimeInf η C τ b := by
    unfold relTimeInf
    rw [div_lt_div_iff₀ (sub_pos.2 (hlt.trans hL)) (sub_pos.2 hL)]
    nlinarith only [hlt, hP.erase.clockEnd_pos]
  exact hP.driven.strictMonoOn_capClock (Outer.relTimeInf_nonneg hP ha.1.le)
    (Outer.relTimeInf_nonneg hP hb) hrt

/-- Current relative domains decrease with their own capacity time. This
uses each traversal's relative hull, not an ambient hull identity. -/
theorem relChart_dom_antitone {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ}
    {ω : Ω} (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω)) {q q' : ℝ≥0}
    (hq' : (q' : ℝ≥0∞) < capLife (γ ω)) (hqq' : q ≤ q') :
    ((PocketStop.relChart c γ q' ω).dom : Set ℂ) ⊆ (PocketStop.relChart c γ q ω).dom := by
  have hq : (q : ℝ≥0∞) < capLife (γ ω) := (ENNReal.coe_le_coe.2 hqq').trans_lt hq'
  rw [← PocketStopSide.activeDom_eq_relChart_dom (A := univ) (mem_univ ω) hq' hγ hc,
    ← PocketStopSide.activeDom_eq_relChart_dom (A := univ) (mem_univ ω) hq hγ hc,
    PocketCoupling.activeDom_eq (mem_univ ω) hq', PocketCoupling.activeDom_eq (mem_univ ω) hq]
  exact image_mono (sdiff_subset_sdiff_right (fwdHull_mono'
    (show (q : ℝ) ≤ q' from hqq')))

end InteractingSLE.Sec7.R6Two
