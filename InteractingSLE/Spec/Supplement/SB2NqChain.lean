/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Supplement.SB2GLift
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftChart

/-!
# The relative chain of a lifted curve through a domain chart, with no head (SB2(2)'s (G2))

Packet PROVE-GW2-GEOM2 (SB2(2) F1 / (G2), decisions D5 and D11). SB2(1)'s relative chain
(`FinRel.exists_relConfig`) is built from S2's data: a left entry chart of `ℍ ∖ fill A`, a continuous boundary
extension `g` of its inverse, and a witness whose portion before the head time lies in `K_A`. At SB2(2)'s later stages
the explored piece starts at the stage chart's `0`, off the retained set, and the per-stage correspondence
(`Mn.StageChainAtR`) gives the lift only through boundary limits of the chart inverse along it. This file builds the
relative chain from exactly that:

* `lim_mem_closure_or_real`: a boundary limit of the inverse of a domain chart of `ℍ ∖ fill A` at a real point lies on
  `closure A` or on `ℝ`;
* `fwd_mem_fillH_of_mem_fillH_lim`: the hull transport `hullIn` with the physical points covered by inverse images of
  relative points in `ℍ` (no boundary extension);
* **`exists_isSB2RelChain_of_lim`**: for a domain chart of `ℍ ∖ fill A` whose inverse grows at least linearly, a proper
  lift `γ` from `0` whose inverse boundary limits are the explored curve `β'` after `t_L`, an explored curve that
  avoids `ℍ ∖ fill A` up to `t_L` (for `t_L = 0` it suffices that `β' 0` is real), and no open time interval of the
  explored curve on `closure A` or on `ℝ` after `t_L`: the relative chain `FinRel.IsSB2RelChain` exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.Supp9B (IsProperCurve)

namespace InteractingSLE.Theorem14.SB.Nq

open Sec7.Lemma71C FinRel

variable {A : Set ℂ} {c : Chart}

/-- **A boundary limit of the chart inverse at a real point lies on the retained set or on `ℝ`.** -/
theorem lim_mem_closure_or_real (hD : IsDomainChart (H \ fillH A) c) {x : ℝ} {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : p ∈ closure A ∪ {z : ℂ | z.im = 0} := by
  have hnD : p ∉ H \ fillH A := by
    have h := FinRel.notMem_image_of_tendsto_inv hD.isConformal hp
    rwa [hD.image_eq] at h
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (x : ℂ)) (by simp)
  have hcl : p ∈ closure (H \ fillH A) := by
    refine mem_closure_of_tendsto hp ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hD.inv_mem hw
  by_cases hpH : p ∈ H
  · left
    have hfill : p ∈ fillH A := by
      by_contra h
      exact hnD ⟨hpH, h⟩
    have hfr : p ∈ frontier (fillH A) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hfill, closure_mono (fun z hz => hz.2) hcl⟩
    exact frontier_fillH_inter_H_subset A ⟨hfr, hpH⟩
  · right
    have h1 : p ∈ closure {z : ℂ | 0 ≤ z.im} :=
      closure_mono (fun (z : ℂ) (hz : z ∈ H \ fillH A) => (le_of_lt (show (0 : ℝ) < z.im from hz.1) :
        (0 : ℝ) ≤ z.im)) hcl
    rw [(isClosed_le continuous_const Complex.continuous_im).closure_eq] at h1
    exact le_antisymm (not_lt.1 hpH) h1

/-- **The hull transport into the relative filling, from inverse images** (`hullIn` without a boundary extension):
let `X` and `Y` be closed and every point of `X` in `D_A` be the chart inverse of a point of `Y ∩ ℍ`. If the inverse
grows at least linearly, every point of `fill X` in `D_A` has its chart image in `fill Y`. -/
theorem fwd_mem_fillH_of_mem_fillH_lim (hD : IsDomainChart (H \ fillH A) c) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂) {X Y : Set ℂ} (hXc : IsClosed X) (hYc : IsClosed Y)
    (hXY : X ∩ (H \ fillH A) ⊆ c.2.1 '' (Y ∩ H)) {z : ℂ} (hz : z ∈ fillH X) (hzA : z ∉ fillH A) :
    c.1 z ∈ fillH Y := by
  have hzD : z ∈ H \ fillH A := ⟨hz.1, hzA⟩
  have hyH : c.1 z ∈ H := hD.fwd_mem hzD
  by_contra hy
  obtain ⟨hyY, hyb⟩ := not_isBounded_of_notMem_fillH hyH hy
  rw [hYc.closure_eq] at hyY hyb
  set C := connectedComponentIn (H \ Y) (c.1 z)
  have hCH : C ⊆ H := fun w hw => (connectedComponentIn_subset _ _ hw).1
  have hCY : ∀ w ∈ C, w ∉ Y := fun w hw => (connectedComponentIn_subset _ _ hw).2
  refine notMem_fillH_of_isPreconnected (S := c.2.1 '' C) ⟨c.1 z, mem_connectedComponentIn ⟨hyH, hyY⟩,
    hD.inv_fwd hzD⟩ ((isPreconnected_connectedComponentIn).image _ (hD.1.1.continuousOn.mono hCH)) ?_ ?_ hz
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨(hD.inv_mem (hCH hw)).1, ?_⟩
    rw [hXc.closure_eq]
    intro hX
    obtain ⟨y, ⟨hyY', hyH'⟩, hyw⟩ := hXY ⟨hX, hD.inv_mem (hCH hw)⟩
    exact hCY w hw ((inv_injOn hD hyH' (hCH hw) hyw) ▸ hyY')
  · intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    refine hyb (isBounded_iff_forall_norm_le.2 ⟨C₁ * R + C₂, fun w hw => ?_⟩)
    have h1 := hgrow w (hCH hw)
    have h2 := hR _ (mem_image_of_mem _ hw)
    nlinarith

section Chain

variable {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The relative chain of a lifted curve through a domain chart, from boundary limits along the lift** (SB2(2)'s
(G2); the head-free form of `FinRel.exists_relConfig`), with the lift's no-real-arc condition as input (it holds for
instance when the lift is a reparametrized Loewner trace). -/
theorem exists_isSB2RelChain_of_lim_real (hD : IsDomainChart (H \ fillH A) c) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hβc : ContinuousOn β' (Icc 0 (tL + S.toNNReal))) (hpre : ∀ r ≤ tL, β' r ∉ H \ fillH A)
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' (tL + s))))
    (hR : interior {r ∈ Ioo (0 : ℝ) S | (γ r.toNNReal).im = 0} = ∅) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain A c β' γ tL S₀ Wr ηr := by
  have hS : 0 < S := lt_of_le_of_lt hS₀ hS₀S
  -- the lift in `ℍ` is the chart inverse
  have hliftH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → γ s ∈ H → c.2.1 (γ s) = β' (tL + s) := by
    intro s hs hsH
    have hca : ContinuousAt c.2.1 (γ s) :=
      (hD.1.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hsH))
    have h1 : Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (c.2.1 (γ s))) :=
      hca.tendsto.mono_left nhdsWithin_le_nhds
    have : (𝓝[H] (γ s)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hsH)
    exact tendsto_nhds_unique h1 (hlim s hs)
  obtain ⟨hcr, hinj, hH, hinf⟩ := isProperCurve_real hγ
  have h0 : (fun r : ℝ => γ r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hγ0]
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hc0, hcm, hcc, hK⟩ := exists_relChain hcr hinj hH h0 hinf hS hR hS₀ hS₀S
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hc0, hcm, hcc, fun s hs => ?_⟩
  obtain ⟨ha0, hηa, hKa⟩ := hK s hs
  have himg : (fun r : ℝ => γ r.toNNReal) '' Icc 0 s = γ '' Icc 0 s.toNNReal := image_toNNReal_Icc γ hs.1
  rw [himg] at hKa
  have hsS : s.toNNReal ≤ S.toNNReal := Real.toNNReal_le_toNNReal (hs.2.trans hS₀S.le)
  have hYc : IsClosed (γ '' Icc 0 s.toNNReal) := (isCompact_Icc.image hγ.1).isClosed
  have hXc : IsClosed (β' '' Icc 0 (tL + s.toNNReal)) :=
    (isCompact_Icc.image_of_continuousOn (hβc.mono (Icc_subset_Icc le_rfl
      ((add_le_add_iff_left tL).2 hsS)))).isClosed
  have hreal : ∀ r : ℝ≥0, r ≤ s.toNNReal → (r : ℝ) ≤ S := fun r hr =>
    (NNReal.coe_le_coe.2 hr).trans (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans hS₀S.le)
  refine ⟨ha0, hηa, hKa, fun z hz hzA => ?_, fun z hz hfr => ?_⟩
  · rw [hKa]
    refine fwd_mem_fillH_of_mem_fillH_lim hD hC₁ hgrow hXc hYc ?_ hz hzA
    rintro _ ⟨⟨r, hr, rfl⟩, hDr⟩
    by_cases hrt : r ≤ tL
    · exact absurd hDr (hpre r hrt)
    · have hle : tL ≤ r := le_of_lt (not_le.1 hrt)
      have hrs : r - tL ≤ s.toNNReal := tsub_le_iff_left.2 hr.2
      have heq : tL + (r - tL) = r := add_tsub_cancel_of_le hle
      have hl := hlim (r - tL) (hreal _ hrs)
      rw [heq] at hl
      by_cases hγH : γ (r - tL) ∈ H
      · refine ⟨γ (r - tL), ⟨⟨r - tL, ⟨zero_le, hrs⟩, rfl⟩, hγH⟩, ?_⟩
        rw [hliftH _ (hreal _ hrs) hγH, heq]
      · exfalso
        have hγr : γ (r - tL) = ((γ (r - tL)).re : ℂ) :=
          Complex.ext (by simp) (by
            simp only [ofReal_im]
            exact le_antisymm (not_lt.1 hγH) (hγ.2.2.1 _))
        rw [hγr] at hl
        have h := FinRel.notMem_image_of_tendsto_inv hD.isConformal hl
        rw [hD.image_eq] at h
        exact h hDr
  · rw [hKa] at hfr
    refine mem_fillH_of_fwd_mem_frontier_fillH (g := c.2.1) hD (fun _ _ => rfl) hYc ?_ hz hfr
    rintro _ ⟨r, hr, rfl⟩ hrH
    have hl := hliftH r (hreal r hr.2) hrH
    rw [hl]
    exact ⟨tL + r, ⟨zero_le, (add_le_add_iff_left tL).2 hr.2⟩, rfl⟩

/-- **The lift spends no open time interval on `ℝ`** if the explored curve after `t_L` spends none on `closure A` (no
common arc) nor on `ℝ` (no original-real arc), its points being the inverse boundary limits along the lift. -/
theorem interior_lift_real_eq_empty_lim (hD : IsDomainChart (H \ fillH A) c) {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S : ℝ}
    (hβc : ContinuousOn β' (Icc 0 (tL + S.toNNReal)))
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' (tL + s))))
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ closure A} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) :
    interior {r ∈ Ioo (0 : ℝ) S | (γ r.toNNReal).im = 0} = ∅ := by
  have hf : ContinuousOn (fun r : ℝ => β' (tL + r.toNNReal)) (Ioo 0 S) := by
    refine hβc.comp (continuous_const.add continuous_real_toNNReal).continuousOn fun r hr => ?_
    exact ⟨zero_le, (add_le_add_iff_left tL).2 (Real.toNNReal_le_toNNReal hr.2.le)⟩
  have hU := interior_union_eq_empty (f := fun r : ℝ => β' (tL + r.toNNReal)) hf isClosed_closure hnA hnR
  refine subset_empty_iff.1 (hU ▸ interior_mono fun r hr => ⟨hr.1, ?_⟩)
  have hγr : γ r.toNNReal = ((γ r.toNNReal).re : ℂ) := Complex.ext (by simp) (by simp [hr.2])
  have hrS : ((r.toNNReal : ℝ≥0) : ℝ) ≤ S := by
    rw [Real.coe_toNNReal _ hr.1.1.le]; exact hr.1.2.le
  have hl := hlim r.toNNReal hrS
  rw [hγr] at hl
  exact lim_mem_closure_or_real hD hl

/-- **The relative chain of a lifted curve through a domain chart, from boundary limits along the lift** (SB2(2)'s
(G2); the head-free form of `FinRel.exists_relConfig`), with the no-common-arc and no-real-arc conditions of the
explored curve. -/
theorem exists_isSB2RelChain_of_lim (hD : IsDomainChart (H \ fillH A) c) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hβc : ContinuousOn β' (Icc 0 (tL + S.toNNReal))) (hpre : ∀ r ≤ tL, β' r ∉ H \ fillH A)
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' (tL + s))))
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ closure A} = ∅)
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsSB2RelChain A c β' γ tL S₀ Wr ηr :=
  exists_isSB2RelChain_of_lim_real hD hC₁ hgrow hS₀ hS₀S hβc hpre hγ hγ0 hlim
    (interior_lift_real_eq_empty_lim hD hβc hlim hnA hnR)

end Chain

/-! ### The growth bound and the filling of a domain-chart complement -/

section Growth

variable {A : Set ℂ} {c : Chart}

/-- **A domain chart of `ℍ ∖ fill A` taking `∞` to `∞` grows at most linearly** (it is a real affine map of the
mapping-out function of `fill A`; `SB.IsLeftEntryChart.exists_norm_fwd_le` without the entry normalization). -/
theorem exists_norm_fwd_le_of_cobounded (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hD : IsDomainChart (H \ fillH A) c)
    (hinf : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (cobounded ℂ)) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w ∈ H \ fillH A, ‖c.1 w‖ ≤ C₁ * ‖w‖ + C₂ := by
  have hK : IsHPHull (fillH A) := isHPHull_fillH_of_isPreconnected hAb hAc
  obtain ⟨gK, hgK⟩ := hK.exists_isMapOut
  obtain ⟨M₀, hM₀⟩ := hgK.exists_norm_sub_le hK
  have hDo : IsOpen (H \ fillH A) := hK.2.2.1
  obtain ⟨a, b, c', d, hdet, hEq⟩ :=
    HChart.exists_realMobius (⟨gK, hgK.1⟩ : HChart (H \ fillH A)) hDo hD.hChart
  have hc'0 : c' = 0 := by
    by_contra hc'
    have hne := SB.neBot_cobounded_inf_H_diff hK
    have h2 : Tendsto gK (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (cobounded ℂ) :=
      (hgK.tendsto_cobounded hK subset_rfl hgK.1.2.mapsTo).mono_right inf_le_left
    have h3 : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (𝓝 ((a : ℂ) / c')) := by
      refine ((SB.tendsto_realMobius_cobounded (b := b) (d := d) hc').comp h2).congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self (H \ fillH A))] with w hw
      exact (hEq hw).symm
    have h4 := (tendsto_norm_atTop_iff_cobounded.2 hinf)
    have h5 := (continuous_norm.tendsto _).comp h3
    exact h4.not_tendsto (disjoint_nhds_atTop _).symm h5
  have had : 0 < a * d := by simpa [hc'0] using hdet
  have hd : d ≠ 0 := fun h => by simp [h] at had
  have hdpos : 0 < |d| := abs_pos.2 hd
  refine ⟨|a| / |d|, (|a| * M₀ + |b|) / |d|, by positivity, fun w hw => ?_⟩
  have hfw : c.1 w = ((a : ℂ) * gK w + b) / d := by
    have h := hEq hw
    change c.1 w = QuantumZipper.CA.realMobius a b c' d (gK w) at h
    rw [h, QuantumZipper.CA.realMobius, hc'0]
    simp
  have hg : ‖gK w‖ ≤ ‖w‖ + M₀ := by
    have := hM₀ w hw
    have h2 := norm_sub_norm_le (gK w) w
    linarith
  have hnum : ‖(a : ℂ) * gK w + b‖ ≤ |a| * (‖w‖ + M₀) + |b| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
  rw [hfw, norm_div, norm_real, Real.norm_eq_abs,
    show |a| / |d| * ‖w‖ + (|a| * M₀ + |b|) / |d| = (|a| * (‖w‖ + M₀) + |b|) / |d| by field_simp; ring]
  exact div_le_div_of_nonneg_right hnum hdpos.le

/-- **The growth bound of the chart inverse** used by `exists_isSB2RelChain_of_lim`. -/
theorem exists_growth_inv_of_cobounded (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hD : IsDomainChart (H \ fillH A) c)
    (hinf : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (cobounded ℂ)) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂ := by
  obtain ⟨C₁, C₂, hC₁, hb⟩ := exists_norm_fwd_le_of_cobounded hAb hAc hD hinf
  refine ⟨C₁, C₂, hC₁, fun w hw => ?_⟩
  have h := hb _ (hD.inv_mem hw)
  rwa [hD.fwd_inv hw] at h

/-- **The filling of a bounded, relatively closed set whose complement in `ℍ` has a domain chart is the set
itself** (the complement is connected and unbounded). -/
theorem fillH_eq_self_of_isDomainChart {X : Set ℂ} (hXH : X ⊆ H) (hXb : IsBounded X)
    (hXc : closure X ∩ H ⊆ X) (hD : IsDomainChart (H \ X) c) : fillH X = X := by
  have hdiff : H \ closure X = H \ X := by
    ext z
    constructor
    · exact fun h => ⟨h.1, fun hz => h.2 (subset_closure hz)⟩
    · exact fun h => ⟨h.1, fun hz => h.2 (hXc ⟨hz, h.1⟩)⟩
  have hconn : IsPreconnected (H \ X) := hD.isPreconnected
  have hunb : ¬ IsBounded (H \ X) := by
    intro hb
    obtain ⟨R, hR⟩ := (hb.union hXb).exists_norm_le
    have hpH : ((|R| + 1 : ℝ) : ℂ) * I ∈ H := by
      show 0 < (((|R| + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      positivity
    have hmem : ((|R| + 1 : ℝ) : ℂ) * I ∈ (H \ X) ∪ X := by
      by_cases h : ((|R| + 1 : ℝ) : ℂ) * I ∈ X
      · exact Or.inr h
      · exact Or.inl ⟨hpH, h⟩
    have h1 := hR _ hmem
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < |R| + 1)] at h1
    linarith [le_abs_self R]
  ext z
  constructor
  · intro hz
    change z ∈ H ∧ (z ∈ closure X ∨ IsBounded (connectedComponentIn (H \ closure X) z)) at hz
    obtain ⟨hzH, hz | hb⟩ := hz
    · exact hXc ⟨hz, hzH⟩
    · by_contra hzX
      rw [hdiff] at hb
      exact hunb (hb.subset (hconn.subset_connectedComponentIn ⟨hzH, hzX⟩ subset_rfl))
  · intro hz
    show z ∈ H ∧ (z ∈ closure X ∨ IsBounded (connectedComponentIn (H \ closure X) z))
    exact ⟨hXH hz, Or.inl (subset_closure hz)⟩

end Growth

end InteractingSLE.Theorem14.SB.Nq
