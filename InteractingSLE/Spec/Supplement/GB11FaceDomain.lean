/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11FacePlanar

/-!
# GB11: the current domain is open and connected

The existing GB11 boundary correspondence and Janiszewski argument give connectivity
of the active pocket. Transport by the ambient map and `mu` gives the domain on which
the generalized two-wall Jordan boundary is to be identified.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- The current domain is the forward image of the unfilled reversed pocket. -/
theorem ownDomain_eq_image_fwdMap {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) (hCH : C ⊆ H) :
    ownDomain W C t = fwdMap W t '' (relDom C \ fwdHull W t) := by
  have hf := isConformalBijection_trMap_ownDomain hW hW0 ht hCH
  ext w
  constructor
  · intro hw
    exact ⟨trMap W 0 t w, hf.2.mapsTo hw,
      Sec6.fwdMap_trMap_zero hW hW0 ht hw.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hzD : z ∈ H \ fwdHull W t := ⟨relDom_subset_H hCH hz.1, hz.2⟩
    refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hzD, ?_⟩
    rw [Sec6.trMap_zero_fwdMap hW hW0 ht hzD]
    exact hz.1

/-- The current domain is open, including when the physical pocket is unbounded. -/
theorem isOpen_ownDomain {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {t : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hCo : IsOpen C) (hCH : C ⊆ H) : IsOpen (ownDomain W C t) := by
  have hf := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ht
  exact (hf.mono H_subset_Hbar).isOpen_inter_preimage QuantumZipper.isOpen_H
    (isOpen_relDom hCo hCH)

/-- The active reversed pocket has an interior point: the relative hull is bounded
and consequently cannot exhaust the upper half-plane. -/
theorem relDom_diff_nonempty_of_relHull_bounded {W : ℝ → ℝ} {C : Set ℂ}
    {R L : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) {t : ℝ}
    (hb : IsBounded (relMapC c '' (fwdHull W t ∩ relDom C))) :
    (relDom C \ fwdHull W t).Nonempty := by
  by_contra hn
  have he := not_nonempty_iff_eq_empty.1 hn
  have hdiff : H \ relMapC c '' (fwdHull W t ∩ relDom C) = ∅ := by
    rw [H_diff_relHull_eq hc, he, image_empty]
  exact not_isBounded_H (hb.subset (sdiff_eq_empty.1 hdiff))

/-- Connectivity and nonemptiness of the current ambient domain, from the already
proved pocket boundary correspondence and its Janiszewski connectivity argument. -/
theorem isConnected_ownDomain_of_pocket {W' : ℝ≥0 → ℝ} {γ αR αL : ℝ≥0 → ℂ}
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hB : GB11.IsGB11Barrier αR αL γ) {C : Set ℂ} {s₁ t₁ : ℝ≥0}
    {s₂ t₂ : ℝ≥0∞} (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)))
    {e : ℝ → ℂ} {rR rL : ℝ → ℝ≥0} (hbc : ChartBdryCorr αR αL c s₂ e rR rL)
    {t : ℝ≥0} (hτt : entryTime γ αR s₂ ≤ t)
    (ht : (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁)) :
    IsConnected (ownDomain (fun r : ℝ => W' r.toNNReal) C t) := by
  have hW : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => W' r.toNNReal) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hW'0
  have hA := isPreconnected_relDom_diff_fwdHull hW' hW'0 hγ hB hs hc hCo hCH hxC hbc hτt ht
  have hAb := isBounded_relHull hW' hW'0 hγ hB hc hxC ht
  have hAn := relDom_diff_nonempty_of_relHull_bounded hc hAb
  have heq : ownDomain (fun r : ℝ => W' r.toNNReal) C (t : ℝ) =
      fwdMap (fun r : ℝ => W' r.toNNReal) (t : ℝ) ''
        (relDom C \ fwdHull (fun r : ℝ => W' r.toNNReal) (t : ℝ)) :=
    ownDomain_eq_image_fwdMap hW hW0 t.2 hCH
  rw [heq]
  exact ⟨hAn.image _, hA.image _
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW t.2).continuousOn.mono
      fun w hw => ⟨relDom_subset_H hCH hw.1, hw.2⟩)⟩

/-- Compactification preserves the openness and connectivity needed to select the
current Jordan face. -/
theorem isOpen_isConnected_mu_ownDomain {W : ℝ → ℝ} {C : Set ℂ} {t : ℝ}
    (hOo : IsOpen (ownDomain W C t)) (hOc : IsConnected (ownDomain W C t)) :
    IsOpen (mu '' ownDomain W C t) ∧ IsConnected (mu '' ownDomain W C t) :=
  ⟨isOpen_mu_image hOo (fun _ hw => hw.1),
    hOc.image _ (continuousOn_mu_Hbar.mono (fun _ hw => H_subset_Hbar hw.1))⟩

end InteractingSLE.Theorem14.GB11Chart
