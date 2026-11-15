/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11OwnFuture

/-!
# GB11: uniqueness and interior values of the relative trace

The continuous relative point `relPt` is the inverse, including boundary limits, of the
inverse relative chart. Consequently `IsRelCurve` determines the trace uniquely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

variable {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {s₁ t₁ : ℝ≥0}
    {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}

/-- Interior points of the reversed pocket belong to its closed-point domain. -/
theorem relDom_subset_relDomBar (hCH : C ⊆ H) (hPC : αR s₁ ∉ C) :
    relDom C ⊆ relDomBar C E (αR s₁) := by
  intro w hw
  exact Or.inr ⟨ne_zero_of_mem_H' (relDom_subset_H hCH hw), subset_closure hw,
    fun he => hPC (he ▸ hw)⟩

/-- The relative point inverts the inverse relative chart in the open half-plane. -/
theorem relPt_relInvC (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k)
    (hc : IsComponentChart (range αR) (range αL) C c) (hCH : C ⊆ H)
    {v : ℂ} (hv : v ∈ H) : relPt E ψ k (relInvC c v) = v := by
  set q : ℂ := (k : ℂ) * -v⁻¹
  have hqH : q ∈ H := by
    show 0 < ((k : ℂ) * -v⁻¹).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      using mul_pos hpc.pos (negInv_mem_H' hv)
  have hw0 : relInvC c v ≠ 0 :=
    ne_zero_of_mem_H' (relDom_subset_H hCH (relInvC_mem hc hv))
  have hG0 : G q ≠ 0 := by
    intro heq
    apply hw0
    rw [relInvC_eq hpc hv]
    change -(G q)⁻¹ = 0
    rw [heq, inv_zero, neg_zero]
  rw [relInvC_eq hpc hv]
  have hnot : -(-(G q)⁻¹)⁻¹ ∉ E := by
    rw [negInv_negInv']
    exact (hpc.mapsTo_G (H_subset_Hbar hqH)).2
  have hn0 : -(G q)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hG0)
  change relPt E ψ k (-(G q)⁻¹) = v
  rw [relPt, ite_eq_right (not_or.mpr ⟨hn0, hnot⟩), negInv_negInv',
    hpc.left_inv q (H_subset_Hbar hqH)]
  dsimp [q]
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpc.pos.ne'
  have hv0 : v ≠ 0 := ne_zero_of_mem_H' hv
  field_simp

/-- The relative point agrees with the conformal relative coordinate inside the pocket. -/
theorem relPt_eq_relMapC (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k)
    (hc : IsComponentChart (range αR) (range αL) C c) (hCH : C ⊆ H)
    {w : ℂ} (hw : w ∈ relDom C) : relPt E ψ k w = relMapC c w := by
  have h := relPt_relInvC hpc hc hCH (relMapC_mem_H hc hw)
  rwa [relInvC_relMapC hc hw] at h

/-- A prescribed finite boundary limit of the inverse chart fixes the relative point. -/
theorem eq_relPt_of_tendsto (hpc : IsPocketCoord αR αL C c s₁ t₁ E ψ G k)
    (hc : IsComponentChart (range αR) (range αL) C c) (hCH : C ⊆ H) (hPC : αR s₁ ∉ C)
    (hptc : ContinuousOn (relPt E ψ k) (relDomBar C E (αR s₁)))
    {v w : ℂ} (hv : v ∈ Hbar) (hw : w ∈ relDomBar C E (αR s₁))
    (hlim : Tendsto (relInvC c) (𝓝[H] v) (𝓝 w)) : v = relPt E ψ k w := by
  have : (𝓝[H] v).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_H]; exact hv)
  have hlim' : Tendsto (relInvC c) (𝓝[H] v) (𝓝[relDomBar C E (αR s₁)] w) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun z hz =>
      relDom_subset_relDomBar hCH hPC (relInvC_mem hc hz)⟩
  have h := (hptc w hw).tendsto.comp hlim'
  have hid : Tendsto (fun z : ℂ => z) (𝓝[H] v) (𝓝 (relPt E ψ k w)) :=
    h.congr' (eventually_nhdsWithin_of_forall fun z hz => relPt_relInvC hpc hc hCH hz)
  exact tendsto_nhds_unique (tendsto_id.mono_left nhdsWithin_le_nhds) hid

end InteractingSLE.Theorem14.GB11Chart
