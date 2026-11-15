/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateLift

/-!
# GB11: gate-base intersections and transport of the current frontier

The base intersection proof uses only the old trace preimage on the real line:
if it is order connected, the interval between two attachment gates maps to the
old trace and cannot meet any unvisited part of a lifted wall. The non-real
frontier is transported to the physical pocket frontier by the continuous
ambient inverse. Real frontier enclosure remains a separate planar assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- The real prime ends whose images belong to the explored physical trace. -/
def oldRealBase (W : ℝ → ℝ) (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℝ :=
  {x | trMap W 0 t x ∈ γ '' Icc 0 t}

/-- Order connectedness of the old real filled base is the exact global input
used to exclude extra real contacts from the incident gate interval. -/
def GB11OldRealBaseStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 →
    IsGeneratingTrace W' ⊤ γ → ∀ t : ℝ≥0,
      OrdConnected (oldRealBase (fun r : ℝ => W' r.toNNReal) γ t)

/-- The gate interval maps to the old trace whenever both gates belong to its
order-connected real preimage. -/
theorem mapsTo_gate_interval_oldTrace {W : ℝ → ℝ} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hbase : OrdConnected (oldRealBase W γ t)) {qR qL : ℝ}
    (hR : qR ∈ oldRealBase W γ t) (hL : qL ∈ oldRealBase W γ t) :
    MapsTo (trMap W 0 t) (Complex.ofReal '' Icc qR qL) (γ '' Icc 0 t) := by
  rintro z ⟨x, hx, rfl⟩
  exact hbase.out hR hL hx

/-- An incoming compactified wall meets a base that maps to the old trace only
at its attachment. The point `0 = μ(∞)` is allowed on the wall. -/
theorem wall_inter_gateBase_subset {W : ℝ → ℝ} {γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    {qR qL : ℝ} {a : ℝ → ℂ}
    (hbase : MapsTo (trMap W 0 t) (Complex.ofReal '' Icc qR qL) (γ '' Icc 0 t))
    (hfree : ∀ u ∈ Ioc (0 : ℝ) 1, a u ≠ 0 →
      trMap W 0 t (muInv (a u)) ∉ γ '' Icc 0 t) :
    a '' Icc 0 1 ∩ gateBase qR qL ⊆ {a 0} := by
  rintro z ⟨⟨u, hu, rfl⟩, ⟨v, ⟨x, hx, rfl⟩, he⟩⟩
  rcases eq_or_lt_of_le hu.1 with he0 | hu0
  · simp only [← he0, mem_singleton_iff]
  · have hz0 : a u ≠ 0 := by
      rw [← he]
      exact mu_ne_zero_of_mem_Hbar (ofReal_mem_Hbar x)
    have hp : muInv (a u) = (x : ℂ) := by rw [← he, muInv_mu]
    exact False.elim (hfree u ⟨hu0, hu.2⟩ hz0 (hp ▸ hbase ⟨x, hx, rfl⟩))

/-- Every finite frontier point of the current domain lies in the closed upper
half-plane, and its inverse image is adherent to the reversed physical pocket. -/
theorem frontier_ownDomain_image_closure {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {C : Set ℂ} {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ frontier (ownDomain W C t)) :
    w ∈ Hbar ∧ trMap W 0 t w ∈ closure (relDom C) := by
  have hsub : ownDomain W C t ⊆ Hbar := fun _ hz => H_subset_Hbar hz.1
  have hwH : w ∈ Hbar := closure_minimal hsub isClosed_Hbar hw.1
  have hFc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ht
  have hcl := ((hFc w hwH).mono hsub).mem_closure_image hw.1
  exact ⟨hwH, closure_mono (by rintro _ ⟨z, hz, rfl⟩; exact hz.2) hcl⟩

/-- Away from the real line, the current frontier maps to the physical pocket
frontier, and the physical image lies in the active ambient domain. -/
theorem frontier_ownDomain_inter_H {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {t : ℝ} (ht : 0 ≤ t)
    {w : ℂ} (hw : w ∈ frontier (ownDomain W C t)) (hwH : w ∈ H) :
    trMap W 0 t w ∈ frontier (relDom C) ∩ (H \ fwdHull W t) := by
  have hcl := (frontier_ownDomain_image_closure hη hW hW0 ht hw).2
  refine ⟨⟨hcl, ?_⟩, Sec6.trMap_zero_mem_domain hW hW0 ht hwH⟩
  rw [(isOpen_relDom hCo hCH).interior_eq]
  intro hrel
  exact hw.2 (by
    rw [(isOpen_ownDomain hη hW hW0 ht hCo hCH).interior_eq]
    exact ⟨hwH, hrel⟩)

/-- A point with a physical wall image outside the open pocket cannot lie in
the current domain. This proves wall/domain disjointness from inverse identities. -/
theorem wall_disjoint_ownDomain {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ} {a : ℝ → ℂ}
    (hwall : ∀ u ∈ Icc (0 : ℝ) 1, a u ≠ 0 →
      trMap W 0 t (muInv (a u)) ∉ relDom C) :
    Disjoint (a '' Icc 0 1) (mu '' ownDomain W C t) := by
  refine disjoint_left.2 ?_
  rintro z ⟨u, hu, rfl⟩ ⟨w, hw, he⟩
  have hz0 : a u ≠ 0 := he ▸ mu_ne_zero_of_mem_Hbar (H_subset_Hbar hw.1)
  have hew : muInv (a u) = w := by rw [← he, muInv_mu]
  exact hwall u hu hz0 (hew ▸ hw.2)

/-- Inverting a nonzero frontier point of the reversed pocket gives a point of
the original pocket frontier. -/
theorem negInv_mem_frontier_of_mem_frontier_relDom {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    {z : ℂ} (hz : z ∈ frontier (relDom C)) (hz0 : z ≠ 0) :
    -z⁻¹ ∈ frontier C := by
  have hc : ContinuousAt (fun z : ℂ => -z⁻¹) z := (continuousAt_id.inv₀ hz0).neg
  have hcl := hc.continuousWithinAt.mem_closure_image hz.1
  have hsub : (fun z : ℂ => -z⁻¹) '' relDom C ⊆ C := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw
  refine ⟨closure_mono hsub hcl, ?_⟩
  rw [hCo.interior_eq]
  intro hp
  have hrel : z ∈ relDom C := hp
  exact hz.2 (by rw [(isOpen_relDom hCo hCH).interior_eq]; exact hrel)


/-- A pocket separated from the original target has bounded inverted domain. -/
theorem isBounded_relDom_of_zero_notMem_closure {C : Set ℂ} (h0 : (0 : ℂ) ∉ closure C) :
    IsBounded (relDom C) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl 0 h0
  refine isBounded_iff_forall_norm_le.2 ⟨ε⁻¹, fun z hz => ?_⟩
  have hεz : ε ≤ ‖-z⁻¹‖ := le_of_not_gt (fun hlt =>
    hball (by simpa only [mem_ball, dist_zero_right] using hlt) (subset_closure hz))
  rw [norm_neg, norm_inv] at hεz
  exact le_inv_of_le_inv₀ hε hεz

/-- Bounded physical active domains have bounded current images, by the uniform
bounded-displacement estimate for the continuous ambient inverse. -/
theorem isBounded_ownDomain_of_isBounded_relDom {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {C : Set ℂ} {t : ℝ} (ht : 0 ≤ t) (hC : IsBounded (relDom C)) :
    IsBounded (ownDomain W C t) := by
  obtain ⟨B, hB⟩ := hC.exists_norm_le
  obtain ⟨M, hM⟩ := hη.exists_norm_extendFrom_sub_le hW hW0 ht
  refine isBounded_iff_forall_norm_le.2 ⟨B + M, fun w hw => ?_⟩
  have hdis := hM w (H_subset_Hbar hw.1)
  rw [← YuanSimpleApprox.trMap_zero_left hW0 t] at hdis
  have hnorm := norm_le_norm_add_norm_sub' w (trMap W 0 t w)
  rw [norm_sub_rev] at hdis
  linarith [hB _ hw.2]

/-- Compactifying a bounded current domain cannot add the point at infinity
to its closure, since `μ` is continuous and nonzero on its compact closure. -/
theorem zero_notMem_closure_mu_ownDomain_of_isBounded {W : ℝ → ℝ}
    {C : Set ℂ} {t : ℝ} (hb : IsBounded (ownDomain W C t)) :
    (0 : ℂ) ∉ closure (mu '' ownDomain W C t) := by
  have hbar : closure (ownDomain W C t) ⊆ Hbar := closure_minimal
    (fun _ hz => H_subset_Hbar hz.1) isClosed_Hbar
  have hc : IsCompact (mu '' closure (ownDomain W C t)) :=
    hb.isCompact_closure.image_of_continuousOn (continuousOn_mu_Hbar.mono hbar)
  have hcl : closure (mu '' ownDomain W C t) ⊆ mu '' closure (ownDomain W C t) :=
    closure_minimal (image_mono subset_closure) hc.isClosed
  intro hz
  obtain ⟨w, hw, he⟩ := hcl hz
  exact mu_ne_zero_of_mem_Hbar (hbar hw) he

end InteractingSLE.Theorem14.GB11Chart
