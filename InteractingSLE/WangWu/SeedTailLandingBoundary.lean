/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingClock
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Finite nonzero boundary limits in the reverse slit chart

PROVE-WW-B27. The curve form of the landed Carathéodory fibre lemma supplies a
single real limit. The remaining side question is its sign.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex Bornology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open ImgWord

theorem arcEnd_Ico {T : ℝ} (hT : 0 < T) : arcEnd (Ico 0 T) = 𝓝[<] T :=
  map_coe_atTop_of_Ioo_subset Ico_subset_Iio_self (fun _ _ => ⟨0, hT, Ioo_subset_Ico_self⟩)

theorem arcEnd_Ici : arcEnd (Ici (0 : ℝ)) = atTop := map_val_Ici_atTop 0

theorem arcEnd_neBot {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P) : (arcEnd P).NeBot := by
  have : Nonempty P := ⟨⟨0, hγ.zero_mem⟩⟩
  unfold arcEnd
  infer_instance

/-- Connected positive-time tails form a basis at the end of a killed interval. -/
theorem arcEnd_connected_basis {γ : ℝ → ℂ} {P A : Set ℝ} (hγ : IsKilledArc γ P)
    (hA : A ∈ arcEnd P) :
    ∃ S ∈ arcEnd P, S ⊆ A ∧ IsPreconnected S ∧ S ⊆ P ∩ Ioi 0 := by
  obtain ⟨a, ha, hAa⟩ := (mem_arcEnd_iff hγ).1 hA
  obtain ⟨b, hb, hb0⟩ := hγ.exists_gt 0 hγ.zero_mem
  have hm : max a b ∈ P := by
    rcases le_total a b with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using ha
  have hP : P.OrdConnected := ⟨fun c hc d hd u hu =>
    hγ.icc d hd ⟨(hγ.nonneg c hc).trans hu.1, hu.2⟩⟩
  refine ⟨P ∩ Ici (max a b), (mem_arcEnd_iff hγ).2 ⟨max a b, hm, fun u hu hmu => ⟨hu, hmu⟩⟩,
    fun u hu => hAa u hu.1 ((le_max_left _ _).trans hu.2),
    (hP.inter ordConnected_Ici).isPreconnected, ?_⟩
  exact fun u hu => ⟨hu.1, hb0.trans_le ((le_max_right _ _).trans hu.2)⟩

/-- A pre-contact curve approaching a non-tip point in inverse coordinates has
a finite nonzero real limit in the reverse slit chart. -/
theorem exists_real_chart_limit {w : ℝ → ℝ} {η α : ℝ → ℂ} {s : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (hs : 0 ≤ s)
    (hα : IsProperArc α) (hK : IsKilledArc (imgCurve w s α) (preContact α (negInv '' fwdHull w s)))
    {y : ℂ} (hy : y ∉ H \ fwdHull w s) (hytip : y ≠ η s)
    (hlim : Tendsto (fun u => negInv (α u)) (arcEnd (preContact α (negInv '' fwdHull w s))) (𝓝 y)) :
    ∃ x : ℝ, x ≠ 0 ∧ Tendsto (imgCurve w s α)
      (arcEnd (preContact α (negInv '' fwdHull w s))) (𝓝 (x : ℂ)) := by
  let P := preContact α (negInv '' fwdHull w s)
  let G := fun u => fwdMap w s (negInv (α u))
  let F := extendFrom H (fwdMapInv w s)
  have : (arcEnd P).NeBot := arcEnd_neBot hK
  have hmem : ∀ u ∈ P ∩ Ioi 0, α u ∈ H \ negInv '' fwdHull w s := fun u hu =>
    ⟨hα.mem_H u hu.2, hu.1.2 u ⟨hu.1.1, le_rfl⟩⟩
  have hcont : ∀ S ⊆ P ∩ Ioi 0, ContinuousOn G S := by
    intro S hS
    have hcα := hα.cont.mono fun u hu => (hK.nonneg u (hS hu).1)
    have hcn : ContinuousOn (fun u => negInv (α u)) S := continuousOn_negInv.comp hcα
      (fun u hu => hα.mem_H u (hS hu).2)
    exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn.comp hcn
      fun u hu => negInv_notMem_fwdHull (hmem u (hS hu))
  have hpos : ∀ᶠ u in arcEnd P, u ∈ P ∩ Ioi 0 := by
    obtain ⟨S, hS, -, -, hSP⟩ := arcEnd_connected_basis hK (Filter.univ_mem : univ ∈ arcEnd P)
    exact Filter.mem_of_superset hS hSP
  have hGH : ∀ᶠ u in arcEnd P, G u ∈ H := hpos.mono fun u hu =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (negInv_notMem_fwdHull (hmem u hu))
  obtain ⟨C, -, hC⟩ := exists_norm_fwdMap_sub_le hw hw0 hs
  obtain ⟨R, hR⟩ := hlim.norm.isBoundedUnder_le
  have hGR : ∀ᶠ u in arcEnd P, ‖G u‖ ≤ C + R := by
    filter_upwards [hpos, hR] with u hu hur
    have hb := hC _ (negInv_notMem_fwdHull (hmem u hu))
    have hn := norm_sub_norm_le (G u) (negInv (α u))
    change ‖negInv (α u)‖ ≤ R at hur
    change ‖G u - negInv (α u)‖ ≤ C at hb
    linarith only [hb, hur, hn]
  obtain ⟨hFd, hFc, hFi, hFr⟩ := hη.fiber_hyps hw hw0 hs
  have hFG : Tendsto (fun u => F (G u)) (arcEnd P) (𝓝 y) := by
    apply hlim.congr'
    filter_upwards [hpos] with u hu
    exact (extendFrom_fwdMap hw hw0 hs (negInv_notMem_fwdHull (hmem u hu))).symm
  obtain ⟨ξ, hξ, hFξ, hGξ⟩ := YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter
    hFd hFc hFi hFr (fun A hA => by
      obtain ⟨S, hS, hSA, hSc, hSP⟩ := arcEnd_connected_basis hK hA
      exact ⟨S, hS, hSA, hSc, hcont S hSP⟩)
    (hGH.mono fun u hu => (show 0 < (G u).im from hu).le) hGR hFG
  have hξnH : ξ ∉ H := by
    intro hξH
    have hξD := (isConformalBijection_fwdMapInv hw hw0 hs).2.mapsTo hξH
    rw [← extendFrom_fwdMapInv_eq hw hw0 hs hξH, hFξ] at hξD
    exact hy hξD
  have hξreal : ξ = (ξ.re : ℂ) := eq_ofReal_re_of_im_eq_zero
    (le_antisymm (not_lt.1 hξnH) hξ)
  have hξ0 : ξ ≠ 0 := by
    intro he
    have h := hFξ
    rw [he, extendFrom_zero hη hw hw0 hs] at h
    exact hytip h.symm
  refine ⟨-ξ.re⁻¹, neg_ne_zero.2 (inv_ne_zero (by exact_mod_cast hξreal ▸ hξ0)), ?_⟩
  have hchart := (continuousAt_negInv hξ0).tendsto.comp hGξ
  have hval : negInv ξ = ((-ξ.re⁻¹ : ℝ) : ℂ) := by
    rw [hξreal]
    simp only [negInv, ofReal_inv, ofReal_neg, ofReal_re]
  rw [hval] at hchart
  apply hchart.congr'
  filter_upwards [hpos] with u hu
  exact (imgCurve_of_pos hu.2).symm

end InteractingSLE.WangWu.SeedTail
