/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRealTrace

/-!
# G8: exclusion of every real contact of the restarted trace

The continuous trace is adherent to the retained domain, including at both
endpoints. Its real inverse values miss the retained prefix. The upper
frontier lemma therefore excludes all these real points from the obstacle.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.RLC.G8Det.RealBoundary

variable {α β : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ}

/-- Cut-relative time lies in the original closed interval. -/
theorem cutTime_mem_Icc {a σ : ℝ≥0} {t : ℝ} (ht : t ∈ Icc 0 ((σ : ℝ) - a)) :
    ((a : ℝ) + t).toNNReal ∈ Icc a σ := by
  have hnonneg : (0 : ℝ) ≤ a + t := add_nonneg a.2 ht.1
  constructor
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hnonneg]
    linarith only [ht.1]
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hnonneg]
    linarith only [ht.2]

/-- The open restarted trace lies in the retained cut-domain complement. -/
theorem cutTrace_mem_compl (hcα : Continuous α) (hcβ : Continuous β)
    (hi : Function.Injective α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a σ r : ℝ≥0}
    (hfuture : ∀ u ∈ Ioo a σ, α u ∈ activeDomain α a β r)
    {t : ℝ} (ht : t ∈ Ioo 0 ((σ : ℝ) - a)) : cutTrace w a t ∈ H \ cutObstacle α β a r := by
  have hu : ((a : ℝ) + t).toNNReal ∈ Ioo a σ := by
    have hnonneg : (0 : ℝ) ≤ a + t := add_nonneg a.2 ht.1.le
    constructor
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hnonneg]
      linarith only [ht.1]
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hnonneg]
      linarith only [ht.2]
  have hp := hfuture _ hu
  have hpH := (Late.domain_subset_own hcα hcβ a r hp).1
  refine ⟨cutTrace_mem_H hi hw hw0 hgen ht.1 hpH, fun hzA => ?_⟩
  have hzJ := cutInv_mem_joint hcα hw hw0 hgen hzA
  rw [cutInv_cutTrace hw hw0 hgen a ht.1.le] at hzJ
  rw [domain_eq hcα hcβ] at hp
  exact hp.2 hzJ

/-- Continuity includes both endpoint prime ends in the closure of the
retained domain. No boundary-mark order or closed separation is assumed. -/
theorem cutTrace_mem_closure_compl (hcα : Continuous α) (hcβ : Continuous β)
    (hi : Function.Injective α) (hw : Continuous w) (hw0 : w 0 = 0)
    (hgen : IsGeneratingTrace w ⊤ α) {a σ r : ℝ≥0} (haσ : a < σ)
    (hfuture : ∀ u ∈ Ioo a σ, α u ∈ activeDomain α a β r)
    {t : ℝ} (ht : t ∈ Icc 0 ((σ : ℝ) - a)) :
    cutTrace w a t ∈ closure (H \ cutObstacle α β a r) := by
  have hT : (0 : ℝ) < σ - a := sub_pos.2 (by exact_mod_cast haσ)
  have htcl : t ∈ closure (Ioo 0 ((σ : ℝ) - a)) := by
    rw [closure_Ioo hT.ne]
    exact ht
  have him : cutTrace w a '' Ioo 0 ((σ : ℝ) - a) ⊆ H \ cutObstacle α β a r :=
    image_subset_iff.2 (fun _ hs => cutTrace_mem_compl hcα hcβ hi hw hw0 hgen hfuture hs)
  apply closure_mono him
  exact ((continuousOn_cutTrace hw hw0 hgen a t ht.1).mono
    (fun _ hs => hs.1.le)).mem_closure_image htcl

/-- Every real point on the compact restarted trace is outside the closed
image obstacle, provided the physical remaining trace misses beta. -/
theorem real_cutTrace_notMem_closure (hcα : Continuous α) (hcβ : Continuous β)
    (hi : Function.Injective α) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} (haσ : a < σ)
    (hfuture : ∀ u ∈ Ioo a σ, α u ∈ activeDomain α a β r)
    (hoff : ∀ u ∈ Icc a σ, α u ∉ β '' Icc 0 r)
    {t : ℝ} (ht : t ∈ Icc 0 ((σ : ℝ) - a)) {x : ℝ}
    (he : cutTrace w a t = (x : ℂ)) : (x : ℂ) ∉ closure (cutObstacle α β a r) := by
  apply notMem_closure_of_inverse_frontier
    (isHPHull_cutObstacle hcα hcβ hgen.1 hβ0 a r) (isCompact_Icc.image hcβ).isClosed
    (continuousOn_cutInv hw hw0 hgen a)
    (fun _ hz hzcl => cutInv_upper_frontier_mem_beta hcα hcβ hw hw0 hgen hz hzcl)
  · rw [← he]
    exact cutTrace_mem_closure_compl hcα hcβ hi hw hw0 hgen haσ hfuture ht
  · rw [← he, cutInv_cutTrace hw hw0 hgen a ht.1]
    exact hoff _ (cutTime_mem_Icc ht)

/-- Interior hull disjointness, a late retained domain and absence of new
physical contacts imply the full remaining real-boundary assertion. -/
theorem real_boundary_of_late_domain (hcα : Continuous α) (hcβ : Continuous β)
    (hi : Function.Injective α) (hβ0 : β 0 = 0)
    (hw : Continuous w) (hw0 : w 0 = 0) (hgen : IsGeneratingTrace w ⊤ α)
    {a σ r : ℝ≥0} (haσ : a < σ)
    (hfuture : ∀ u ∈ Ioo a σ, α u ∈ activeDomain α a β r)
    (hoff : ∀ u ∈ Icc a σ, α u ∉ β '' Icc 0 r)
    (hd : Disjoint (cutObstacle α β a r) (fwdHull (cutDrive w a) ((σ : ℝ) - a))) :
    ∀ x : ℝ, (x : ℂ) ∈ closure (cutObstacle α β a r) →
      (x : ℂ) ∉ closure (fwdHull (cutDrive w a) ((σ : ℝ) - a)) := by
  have hT : (0 : ℝ) ≤ σ - a := sub_nonneg.2 (by exact_mod_cast haσ.le)
  have hK := fwdHull_eq_fillH_cutTrace hw hw0 hgen a hT
  have hS : IsCompact (cutTrace w a '' Icc 0 ((σ : ℝ) - a)) :=
    isCompact_Icc.image_of_continuousOn
    ((continuousOn_cutTrace hw hw0 hgen a).mono Icc_subset_Ici_self)
  rw [hK] at hd ⊢
  intro x hxA hxK
  obtain ⟨t, ht, he⟩ := mem_trace_of_common_real_closures hS.isClosed
    (isHPHull_cutObstacle hcα hcβ hgen.1 hβ0 a r).1 hd hxA hxK
  exact real_cutTrace_notMem_closure hcα hcβ hi hβ0 hw hw0 hgen haσ hfuture hoff ht he hxA

end InteractingSLE.RLC.G8Det.RealBoundary
