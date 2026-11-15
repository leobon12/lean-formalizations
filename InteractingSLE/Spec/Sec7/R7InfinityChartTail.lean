/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceChart

/-!
# Proper incoming outer arms at their last visited points

PROVE-R7-GAPEQ. Last-visit maximality and properness give the surviving tail and
its real gate without reverse visit order on the outer arm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6

/-- The tail beyond a proper arm's last visited parameter survives. Reverse visit
order is not needed, and earlier unvisited portions may also survive. -/
theorem lastVisit_tail_domain {W : ℝ → ℝ} {η A : ℝ → ℂ} {s : ℝ}
    (hη : IsLoewnerTrace W η) (hs : 0 ≤ s)
    (hAc : ContinuousOn A (Ici 0)) (hAt : Tendsto (fun v => ‖A v‖) atTop atTop)
    (hAH : ∀ v ∈ Ioi (0 : ℝ), A v ∈ H) (hy : A 0 ∈ η '' Icc 0 s) :
    let u := lastVisit (fun t => η '' Icc 0 t) A s;
    0 ≤ u ∧ A u ∉ H \ fwdHull W s ∧ ∀ v ∈ Ioi u, A v ∈ H \ fwdHull W s := by
  dsimp only
  let u := lastVisit (fun t => η '' Icc 0 t) A s
  have hRc : IsCompact (η '' Icc 0 s) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun _ ht => ht.1)
  have hm := lastVisit_mem (R := fun t => η '' Icc 0 t) hAc hAt hRc ⟨0, self_mem_Ici, hy⟩
  have hu : 0 ≤ u := hm.1
  have hpre : IsPreconnected (A '' Ioi u) := isPreconnected_Ioi.image _
    (hAc.mono fun _ hv => hu.trans hv.le)
  have hunb : ¬ IsBounded (A '' Ioi u) := not_isBounded_image_of_tendsto
    (tendsto_norm_atTop_iff_cobounded.1 hAt) (Ioi_mem_atTop u)
  have hD : A '' Ioi u ⊆ H \ fwdHull W s := subset_domain_of_not_isBounded hη hs hpre
    (by rintro _ ⟨v, hv, rfl⟩; exact hAH v (hu.trans_lt hv))
    (Set.disjoint_left.2 (by
      rintro _ ⟨v, hv, rfl⟩ hvis
      exact (not_le.2 hv) (le_lastVisit hAt hRc.isBounded (hu.trans hv.le) hvis))) hunb
  exact ⟨hu, notMem_domain_of_mem_trace hη hs hm.2, fun v hv => hD ⟨v, hv, rfl⟩⟩

/-- A compactified proper incoming arm, from its real gate to the original target
at zero in the compactifying chart. The last field records its physical landing. -/
def IsLastVisitArm (W : ℝ → ℝ) (η A : ℝ → ℂ) (s a q : ℝ) (b : ℝ → ℂ) : Prop :=
  ContinuousOn b (Icc 0 1) ∧ InjOn b (Icc 0 1) ∧
    b 0 = ((-(q - a)⁻¹ : ℝ) : ℂ) ∧ b 1 = 0 ∧
    (∀ v ∈ Ioo (0 : ℝ) 1, b v ∈ H) ∧
    b '' Ioo 0 1 = psiMap a '' (fwdMap W s ''
      (A '' Ioi (lastVisit (fun t => η '' Icc 0 t) A s))) ∧
    trMap W 0 s q = A (lastVisit (fun t => η '' Icc 0 t) A s)

/-- Real gates and compactified arms exist for a proper outer or contained side. -/
theorem exists_lastVisit_arm {W : ℝ → ℝ} {η A : ℝ → ℂ} {s : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hAc : ContinuousOn A (Ici 0)) (hAi : InjOn A (Ici 0))
    (hAt : Tendsto (fun v => ‖A v‖) atTop atTop)
    (hAH : ∀ v ∈ Ioi (0 : ℝ), A v ∈ H) (hy : A 0 ∈ η '' Icc 0 s) :
    ∃ q : ℝ, ∀ a < q, ∃ b : ℝ → ℂ, IsLastVisitArm W η A s a q b := by
  obtain ⟨hu, huK, hD⟩ := lastVisit_tail_domain hη hs hAc hAt hAH hy
  let u := lastVisit (fun t => η '' Icc 0 t) A s
  obtain ⟨q, hq, hlim⟩ := exists_tendsto_lift_right hη hW hW0 hs
    (hAc.mono fun _ hv => hu.trans hv.1) (fun v hv => hD v hv.1) huK
  refine ⟨q, fun a haq => ?_⟩
  obtain ⟨b, hbc, hbi, hb0, hb1, hbH, hbimg⟩ := exists_psiArm hW hW0 hs
    (hAc.mono (Ici_subset_Ici.2 hu)) (hAi.mono (Ici_subset_Ici.2 hu)) hD hAt hlim haq
  exact ⟨b, hbc, hbi, hb0, hb1, hbH, hbimg, hq⟩

end InteractingSLE.Sec7.R7InfinityChart
