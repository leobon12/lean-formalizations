/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBBdry
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# The relative chart along a transient safe path has a limit

Packet PROVE-GW2-NEARIMG2, decision D56 (`UncEndStatement`). Let `U` be a continuous driver from `0` (the retained
counterflow, in GB6's relative chart `relMap U s : w ↦ −1/f_s(−1/w)`) whose inverse map at time `s` has boundary
limits, and let `P` be a continuous path of safe points (off the closed retained hull) tending to `∞`. In the sphere
picture `P` tends to the base `α(0) = 0` of the retained curve, which is not its tip `F̄_s(0)`. Then
`relBdry U s (P t)` converges as `t → ∞`, to a finite nonzero limit.

Proof: `G(t) = −1/relBdry(P t)` is the forward map `f_s` at the sphere point `−1/P(t)` (by continuity at real visits),
so `F̄_s(G t) = −1/P(t) → 0`; `G` is bounded (`f_s` moves points a bounded distance); Yuan's cluster-set lemma along
the time parameter (`exists_tendsto_of_tendsto_comp_filter`: the boundary extension `F̄_s` is constant on no real
interval) gives a limit `ξ` of `G` with `F̄_s(ξ) = 0`; `ξ ≠ 0` because `F̄_s(0)` is the tip.

* `exists_norm_fwdMap_sub_le`, **`relBdry_spec`** (one safe point `z ≠ 0`);
* **`tendsto_relBdry_of_transient`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Ni

open Supp8.GB6 Supp8.GB6.CoordB

variable {U : ℝ → ℝ} {s : ℝ}

/-- **The forward map moves points a bounded distance.** -/
theorem exists_norm_fwdMap_sub_le (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ q ∈ H \ fwdHull U s, ‖fwdMap U s q - q‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hU hU0 hs
  refine ⟨C, fun q hq => ?_⟩
  have hmem : fwdMap U s q ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs hq
  have h := hC _ hmem
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hs hq, norm_sub_rev] at h
  exact h

/-- The relative chart at a point of its domain is `−1/f_s(−1/w)`, with `f_s(−1/w) ∈ ℍ`. -/
theorem fwdMap_mem_of_relDomain (hU : Continuous U) (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ relDomain U s) :
    -w⁻¹ ∈ H \ fwdHull U s ∧ fwdMap U s (-w⁻¹) ∈ H := by
  have hwH : w ∈ H := hw.1
  have h1 : -w⁻¹ ∈ H := by
    have : w ≠ 0 := ne_zero_of_mem_H hwH
    change 0 < (-w⁻¹).im
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos hwH (normSq_pos.2 this)
  have h2 : -w⁻¹ ∉ fwdHull U s := fun h => hw.2 ⟨-w⁻¹, h, neg_inv_neg_inv w⟩
  exact ⟨⟨h1, h2⟩, QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs ⟨h1, h2⟩⟩

/-- **The relative chart at a safe point `z ≠ 0`**: its value is nonzero, `G = −1/relBdry(z)` lies in `ℍ̄`, is at most
`‖1/z‖ + C` in norm, and is sent by the boundary extension of the inverse map to the sphere point `−1/z`. -/
theorem relBdry_spec (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv U s))
    {C : ℝ} (hC : ∀ q ∈ H \ fwdHull U s, ‖fwdMap U s q - q‖ ≤ C) {z : ℂ} (hz : z ∈ relSafe U s)
    (hz0 : z ≠ 0) :
    relBdry U s z ≠ 0 ∧ -(relBdry U s z)⁻¹ ∈ Hbar ∧ ‖-(relBdry U s z)⁻¹‖ ≤ ‖z⁻¹‖ + C ∧
      extendFrom H (fwdMapInv U s) (-(relBdry U s z)⁻¹) = -z⁻¹ := by
  set l := 𝓝[relDomain U s] z with hl
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 (relSafe_subset_closure_relDomain U s hz)
  have hT : Tendsto (relMap U s) l (𝓝 (relBdry U s z)) := tendsto_relMap_relBdry hU hU0 hs hz
  have hdom : ∀ᶠ w in l, w ∈ relDomain U s := self_mem_nhdsWithin
  -- the forward values `φ w = f_s(−1/w) = −1/relMap w`
  have hφ : ∀ w ∈ relDomain U s, fwdMap U s (-w⁻¹) = -(relMap U s w)⁻¹ := fun w hw => by
    have hne : fwdMap U s (-w⁻¹) ≠ 0 := ne_zero_of_mem_H (fwdMap_mem_of_relDomain hU hs hw).2
    simp only [relMap, inv_neg, inv_inv, neg_neg]
  have hzinv : Tendsto (fun w : ℂ => w⁻¹) l (𝓝 z⁻¹) :=
    ((continuousAt_inv₀ hz0).tendsto).mono_left nhdsWithin_le_nhds
  -- the forward values are bounded by `‖1/w‖ + C`
  have hbd : ∀ᶠ w in l, ‖fwdMap U s (-w⁻¹)‖ ≤ ‖w⁻¹‖ + C := by
    filter_upwards [hdom] with w hw
    have h := hC _ (fwdMap_mem_of_relDomain hU hs hw).1
    have h2 := norm_sub_norm_le (fwdMap U s (-w⁻¹)) (-w⁻¹)
    rw [norm_neg] at h2
    linarith
  -- the value is nonzero
  set B : ℝ := max (‖z⁻¹‖ + 1 + C) 1 with hB'
  have hBpos : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlow : ∀ᶠ w in l, B⁻¹ ≤ ‖relMap U s w‖ := by
    have hnear : ∀ᶠ w in l, ‖w⁻¹‖ < ‖z⁻¹‖ + 1 :=
      (hzinv.norm).eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [hdom, hbd, hnear] with w hw hb hn
    have hpos : 0 < ‖fwdMap U s (-w⁻¹)‖ :=
      norm_pos_iff.2 (ne_zero_of_mem_H (fwdMap_mem_of_relDomain hU hs hw).2)
    have hle : ‖fwdMap U s (-w⁻¹)‖ ≤ B := by
      refine (hb.trans ?_).trans (le_max_left _ _)
      linarith
    have hrel : ‖relMap U s w‖ = ‖fwdMap U s (-w⁻¹)‖⁻¹ := by
      simp only [relMap, norm_neg, norm_inv]
    rw [hrel]
    exact inv_anti₀ hpos hle
  have hne : relBdry U s z ≠ 0 := by
    intro h0
    have hge := ge_of_tendsto (hT.norm) hlow
    rw [h0, norm_zero] at hge
    exact absurd hge (not_le.2 (inv_pos.2 hBpos))
  refine ⟨hne, ?_⟩
  -- the forward values converge to `G = −1/relBdry z`
  have hφT : Tendsto (fun w => fwdMap U s (-w⁻¹)) l (𝓝 (-(relBdry U s z)⁻¹)) := by
    refine ((hT.inv₀ hne).neg).congr' ?_
    filter_upwards [hdom] with w hw
    exact (hφ w hw).symm
  have hφH : ∀ᶠ w in l, fwdMap U s (-w⁻¹) ∈ H := by
    filter_upwards [hdom] with w hw
    exact (fwdMap_mem_of_relDomain hU hs hw).2
  have hGbar : -(relBdry U s z)⁻¹ ∈ Hbar := by
    have := mem_closure_of_tendsto hφT hφH
    rwa [closure_H] at this
  refine ⟨hGbar, ?_, ?_⟩
  · have h := le_of_tendsto ((hφT.norm).sub (hzinv.norm))
      (hbd.mono fun w hw => (sub_le_iff_le_add').2 hw)
    rw [norm_neg] at h ⊢
    exact (sub_le_iff_le_add').1 h
  · -- the boundary extension at `G`
    have hext : ∀ v ∈ H, extendFrom H (fwdMapInv U s) v = fwdMapInv U s v := fun v hv =>
      extendFrom_eq (subset_closure hv) (((QuantumZipper.RS.differentiableOn_fwdMapInv hU hU0 hs).differentiableAt
        (QuantumZipper.isOpen_H.mem_nhds hv)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have h1 : Tendsto (fun w => extendFrom H (fwdMapInv U s) (fwdMap U s (-w⁻¹))) l
        (𝓝 (extendFrom H (fwdMapInv U s) (-(relBdry U s z)⁻¹))) :=
      (hB.continuousOn _ hGbar).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hφT, hφH.mono fun w hw => H_subset_Hbar hw⟩)
    have h2 : Tendsto (fun w => extendFrom H (fwdMapInv U s) (fwdMap U s (-w⁻¹))) l (𝓝 (-z⁻¹)) := by
      refine (hzinv.neg).congr' ?_
      filter_upwards [hdom] with w hw
      rw [hext _ (fwdMap_mem_of_relDomain hU hs hw).2,
        QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hs (fwdMap_mem_of_relDomain hU hs hw).1]
    exact tendsto_nhds_unique h1 h2

/-- The boundary extension of the inverse map is the inverse map on `ℍ`. -/
theorem extendFrom_fwdMapInv_eq (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) {v : ℂ} (hv : v ∈ H) :
    extendFrom H (fwdMapInv U s) v = fwdMapInv U s v :=
  extendFrom_eq (subset_closure hv) (((QuantumZipper.RS.differentiableOn_fwdMapInv hU hU0 hs).differentiableAt
    (QuantumZipper.isOpen_H.mem_nhds hv)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- **The relative chart along a transient safe path converges**, to a finite nonzero limit: the path tends to the
base of the retained curve, which the boundary extension `F̄_s` of the inverse map does not send to its tip. -/
theorem tendsto_relBdry_of_transient (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv U s))
    (hR : ∀ x : ℂ, x.im = 0 → extendFrom H (fwdMapInv U s) x ∉ extendFrom H (fwdMapInv U s) '' H)
    (htip : extendFrom H (fwdMapInv U s) 0 ≠ 0) {P : ℝ≥0 → ℂ} (hPc : Continuous P)
    (hP : ∀ t, P t ∈ relSafe U s) (htr : Tendsto (fun t => ‖P t‖) atTop atTop) :
    ∃ ξ : ℂ, ξ ≠ 0 ∧ Tendsto (fun t => relBdry U s (P t)) atTop (𝓝 ξ) := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 hs
  set F := extendFrom H (fwdMapInv U s) with hF
  have hext : ∀ v ∈ H, F v = fwdMapInv U s v := fun v hv => extendFrom_fwdMapInv_eq hU hU0 hs hv
  have hd : DifferentiableOn ℂ F H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hU hU0 hs).congr fun v hv => hext v hv
  have hinj : InjOn F H := fun a ha b hb hab => by
    rw [hext a ha, hext b hb] at hab
    have := congrArg (fwdMap U s) hab
    rwa [QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs ha, QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs hb] at this
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (htr.eventually (eventually_ge_atTop (1 : ℝ)))
  have hP0 : ∀ t, T₀ ≤ t → P t ≠ 0 := fun t ht h => by
    have := hT₀ t ht
    rw [h, norm_zero] at this
    exact absurd this (not_le.2 one_pos)
  set G : ℝ≥0 → ℂ := fun t => -(relBdry U s (P t))⁻¹ with hG
  have hspec : ∀ t, T₀ ≤ t → relBdry U s (P t) ≠ 0 ∧ G t ∈ Hbar ∧ ‖G t‖ ≤ ‖(P t)⁻¹‖ + C ∧
      F (G t) = -(P t)⁻¹ := fun t ht => relBdry_spec hU hU0 hs hB hC (hP t) (hP0 t ht)
  have hcontB : Continuous fun t => relBdry U s (P t) :=
    (continuousOn_relBdry hU hU0 hs).comp_continuous hPc hP
  have hconn : ∀ U' ∈ (atTop : Filter ℝ≥0), ∃ S ∈ (atTop : Filter ℝ≥0), S ⊆ U' ∧ IsPreconnected S ∧
      ContinuousOn G S := by
    intro U' hU'
    obtain ⟨T₁, hT₁⟩ := mem_atTop_sets.1 hU'
    refine ⟨Ici (max T₀ T₁), Ici_mem_atTop _, fun t ht => hT₁ t (le_trans (le_max_right _ _) ht),
      isPreconnected_Ici, ?_⟩
    exact (hcontB.continuousOn.inv₀ fun t ht => (hspec t (le_trans (le_max_left _ _) ht)).1).neg
  have hGH : ∀ᶠ t in atTop, G t ∈ Hbar := (eventually_ge_atTop T₀).mono fun t ht => (hspec t ht).2.1
  have hGR : ∀ᶠ t in atTop, ‖G t‖ ≤ 1 + C := by
    filter_upwards [eventually_ge_atTop T₀] with t ht
    refine (hspec t ht).2.2.1.trans (add_le_add ?_ le_rfl)
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (hT₀ t ht)
  have hFG : Tendsto (fun t => F (G t)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t => -(P t)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := tendsto_inv_atTop_zero.comp htr
      simp only [Function.comp_def] at h
      simpa only [norm_neg, norm_inv] using h
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop T₀] with t ht
    exact (hspec t ht).2.2.2.symm
  obtain ⟨ξ, -, hFξ, hGξ⟩ := YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hd hB.continuousOn hinj hR
    hconn hGH hGR hFG
  have hξ0 : ξ ≠ 0 := fun h => htip (by rw [h] at hFξ; exact hFξ)
  refine ⟨-ξ⁻¹, neg_ne_zero.2 (inv_ne_zero hξ0), ((hGξ.inv₀ hξ0).neg).congr' ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with t _
  simp only [hG, inv_neg, inv_inv, neg_neg]

end InteractingSLE.Theorem14.GW2Ni
