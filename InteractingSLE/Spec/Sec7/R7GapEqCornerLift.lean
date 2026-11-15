/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerAttach

/-!
# The incoming arm at a first-visit minimum, including outer arms

PROVE-R7-GAPEQ. The minimum itself makes the preceding prefix unvisited. That preconnected
prefix joins the fresh pocket target, so no entry into filled components puts it in the
ambient domain. The landed first-exit lifting theorem then supplies its simple current arm.
No reverse order or regularity of the first-visit parameter is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn

/-- **The entire incoming prefix is in the current ambient domain.** The target is still
fresh, and the arm's endpoint has been seen. The first-visit minimum splits the arm into an
unvisited prefix in the domain and an attained endpoint outside it. -/
theorem firstVisit_prefix_domain {W : ℝ → ℝ} {η A : ℝ → ℂ} {τ σ r : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hAc : ContinuousOn A (Icc 0 1)) (hAH : ∀ v ∈ Ico (0 : ℝ) 1, A v ∈ H)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ) (hτ : η τ = A 1)
    (hσ : η σ = A 0) (hxf : A 0 ∉ η '' Ico 0 σ) :
    let u := firstVisit (fun t => η '' Icc 0 t) A r;
    0 < u ∧ u ≤ 1 ∧ (∀ v ∈ Ico (0 : ℝ) u, A v ∈ H \ fwdHull W r) ∧
      A u ∉ H \ fwdHull W r := by
  dsimp only
  let u := firstVisit (fun t => η '' Icc 0 t) A r
  have hr0 : 0 ≤ r := hτ0.trans hτr
  have hm := firstVisit_mem (R := fun t => η '' Icc 0 t) hAc
    (isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun _ ht => ht.1)).isClosed
    ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτr⟩, hτ⟩
  have hu0 : 0 < u := lt_of_le_of_ne hm.1.1 fun he => by
    obtain ⟨t, ht, htA⟩ := hm.2
    exact hxf ⟨t, ⟨ht.1, ht.2.trans_lt hrσ⟩, htA.trans (congrArg A he.symm)⟩
  have hnot : ∀ v ∈ Ico (0 : ℝ) u, A v ∉ η '' Icc 0 r := by
    intro v hv hvis
    exact (not_le.2 hv.2) (firstVisit_le ⟨hv.1, hv.2.le.trans hm.1.2⟩ hvis)
  have hxnot : A 0 ∉ η '' Icc 0 r := hnot 0 ⟨le_rfl, hu0⟩
  have hxD : A 0 ∈ H \ fwdHull W r :=
    ⟨hAH 0 ⟨le_rfl, zero_lt_one⟩, hσ ▸ trace_notMem_fwdHull hη hW hW0 hr0 hrσ.le (hσ ▸ hxnot)⟩
  have hpre : IsPreconnected (A '' Ico 0 u) := isPreconnected_Ico.image _
    (hAc.mono fun v hv => ⟨hv.1, hv.2.le.trans hm.1.2⟩)
  have hD : A '' Ico 0 u ⊆ H \ fwdHull W r := subset_domain_of_isPreconnected hη hr0 hpre
    (by rintro _ ⟨v, hv, rfl⟩; exact hAH v ⟨hv.1, hv.2.trans_le hm.1.2⟩)
    (Set.disjoint_left.2 (by rintro _ ⟨v, hv, rfl⟩ hvis; exact hnot v hv hvis))
    ⟨0, ⟨le_rfl, hu0⟩, rfl⟩ hxD
  exact ⟨hu0, hm.1.2, fun v hv => hD ⟨v, hv, rfl⟩, notMem_domain_of_mem_trace hη hr0 hm.2⟩

/-- **A simple current incoming arm exists for an outer or contained side.** Its gate is
the boundary value of the attained first-visit point. It need not be the current driver. -/
theorem exists_firstVisit_arm {W : ℝ → ℝ} {η A : ℝ → ℂ} {τ σ r : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hAc : ContinuousOn A (Icc 0 1)) (hAi : InjOn A (Icc 0 1))
    (hAH : ∀ v ∈ Ico (0 : ℝ) 1, A v ∈ H)
    (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ) (hτ : η τ = A 1)
    (hσ : η σ = A 0) (hxf : A 0 ∉ η '' Ico 0 σ) :
    let u := firstVisit (fun t => η '' Icc 0 t) A r;
    ∃ (q : ℝ) (a : ℝ → ℂ), ContinuousOn a (Icc 0 1) ∧ InjOn a (Icc 0 1) ∧
      a 0 = q ∧ a 1 = fwdMap W r (A 0) ∧ (∀ v ∈ Ioc (0 : ℝ) 1, a v ∈ H) ∧
      trMap W 0 r q = A u ∧ a '' Ioc 0 1 = fwdMap W r '' (A '' Ico 0 u) := by
  obtain ⟨hu0, hu1, hD, huK⟩ := firstVisit_prefix_domain hη hW hW0 hAc hAH hτ0 hτr hrσ hτ hσ hxf
  exact exists_arm hη hW hW0 (hτ0.trans hτr) hu0
    (hAc.mono (Icc_subset_Icc_right hu1)) (hAi.mono (Icc_subset_Icc_right hu1)) hD huK

end InteractingSLE.Sec7.R7GapEqCorner
