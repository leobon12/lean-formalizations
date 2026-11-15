/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaAmbient

/-! # GW4: current-time reflection including real boundary contacts

This is the R5Lf reflection and common-integer argument with its exact
open-domain exclusion hypothesis. Real contacts and hull contacts are
therefore treated by the same positive reflection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd isOpen_H)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7 Sec7.R5Lift

/-- Local reflection of the actual ambient transition whenever the real
diameter lands outside the ambient open domain. -/
theorem reflect_data_of_notMem {old : Chart} (hold : old.IsConformal) {Fo : ℂ → ℂ}
    (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (hK : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    {x ρ : ℝ} (hland : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∉ H \ fwdHull W s) :
    EqOn (fun y => fwdMap W s (old.2.1 y)) (extendFrom H fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) ρ) ∧
      ContinuousOn (extendFrom H fun y => fwdMap W s (old.2.1 y)) (Hbar ∩ ball (x : ℂ) ρ) ∧
      (∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → ((extendFrom H fun y => fwdMap W s (old.2.1 y)) z).im = 0) ∧
      (∀ z ∈ H ∩ ball (x : ℂ) ρ, (extendFrom H fun y => fwdMap W s (old.2.1 y)) z ∈ H) ∧
      InjOn (extendFrom H fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) ρ) ∧
      DifferentiableOn ℂ (extendFrom H fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) ρ) ∧
      ∀ z ∈ Hbar ∩ ball (x : ℂ) ρ, Tendsto (fun y => fwdMap W s (old.2.1 y)) (𝓝[H] z)
        (𝓝 ((extendFrom H fun y => fwdMap W s (old.2.1 y)) z)) := by
  set Φ : ℂ → ℂ := fun y => fwdMap W s (old.2.1 y) with hΦ
  have hmapsK : ∀ y ∈ H, old.2.1 y ∈ H \ fwdHull W s := fun y hy => hK (hold.inv_mem_dom hy)
  have hΦd : DifferentiableOn ℂ Φ H :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).comp hold.1 hmapsK
  -- real limits at the real points of the disc
  have hreal_lim : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → ∃ x' : ℝ, Tendsto Φ (𝓝[H] (u : ℂ)) (𝓝 (x' : ℂ)) := by
    intro u hu
    have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
    have hland' : Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝 (Fo u)) :=
      ((hFoc _ hubar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
        (eventually_nhdsWithin_of_forall fun y hy => hFo hy)
    obtain ⟨x', -, hx'⟩ := exists_ambient_access_of_notMem hη hW hW0 hs hold hK hland' (hland u hu)
    exact ⟨x', hx'⟩
  set g := extendFrom H Φ with hg
  have hlim : ∀ z ∈ Hbar ∩ ball (x : ℂ) ρ, ∃ y, Tendsto Φ (𝓝[H] z) (𝓝 y) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact ⟨Φ z, ((hΦd.differentiableAt (isOpen_H.mem_nhds hzH)).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · have hz0 : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
      obtain ⟨x', hx'⟩ := hreal_lim z.re (hzr ▸ hz.2)
      exact ⟨x', hzr ▸ hx'⟩
  have hcl : Hbar ∩ ball (x : ℂ) ρ ⊆ closure H := by
    rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact inter_subset_left
  have hgc : ContinuousOn g (Hbar ∩ ball (x : ℂ) ρ) := continuousOn_extendFrom hcl hlim
  have hgΦ : EqOn Φ g (H ∩ ball (x : ℂ) ρ) := fun z hz => by
    have hzc : z ∈ closure H := subset_closure hz.1
    exact (extendFrom_eq hzc
      ((hΦd.differentiableAt (isOpen_H.mem_nhds hz.1)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)).symm
  have hgreal : ∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → (g z).im = 0 := by
    intro z hz hz0
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    obtain ⟨x', hx'⟩ := hreal_lim z.re (hzr ▸ hz)
    have hzc : (z.re : ℂ) ∈ closure H := by
      rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
      show (0 : ℝ) ≤ (z.re : ℂ).im
      rw [ofReal_im]
    rw [hzr, hg, extendFrom_eq hzc hx', ofReal_im]
  have hinj : InjOn g (H ∩ ball (x : ℂ) ρ) := by
    intro z₁ hz₁ z₂ hz₂ h
    rw [← hgΦ hz₁, ← hgΦ hz₂] at h
    have h' := congrArg (fwdMapInv W s) h
    simp only [hΦ] at h'
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (hmapsK z₁ hz₁.1),
      QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs (hmapsK z₂ hz₂.1)] at h'
    exact hold.injOn hz₁.1 hz₂.1 h'
  refine ⟨hgΦ, hgc, hgreal, fun z hz => ?_, hinj,
    (hΦd.mono inter_subset_left).congr fun z hz => (hgΦ hz).symm, fun z hz => ?_⟩
  · rw [← hgΦ hz]; exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hmapsK z hz.1)
  · obtain ⟨y, hy⟩ := hlim z hz
    rw [hg, extendFrom_eq (hcl hz) hy]
    exact hy

/-- The reflected derivative is positive at both hull and real landings. -/
theorem exists_pos_tendsto_deriv_of_notMem {old : Chart} (hold : old.IsConformal) {Fo : ℂ → ℂ}
    (hFo : EqOn Fo old.2.1 H) (hFoc : ContinuousOn Fo Hbar) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (hK : (old.dom : Set ℂ) ⊆ H \ fwdHull W s)
    {x ρ : ℝ} (hρ : 0 < ρ) (hland : ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ → Fo u ∉ H \ fwdHull W s) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, -⟩ :=
    reflect_data_of_notMem hold hFo hFoc hη hW hW0 hs hK hland
  obtain ⟨b, hb, hder⟩ := exists_pos_tendsto_deriv_of_reflect' hρ hgd hgc hgreal hmaps hinj
  refine ⟨b, hb, hder.congr' ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hρ))] with y hy
  exact (Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy)
    fun z hz => (hgΦ hz).symm).deriv_eq


/-- One current-time integer on an open interval, allowing real contacts. -/
theorem exists_int_forall_tendsto_cur_notMem {cur : Chart} (hcur : cur.IsConformal) {Lc : ℂ → ℂ}
    (hLc : IsDerivLog cur.1 Lc cur.dom) (hlift : ∀ z ∈ cur.dom, cur.2.2 z = (Lc z).im)
    {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) {a b : ℝ} (hland : ∀ u ∈ Ioo a b, Fc u ∉ H \ fwdHull W T) :
    ∃ n : ℤ, ∀ u ∈ Ioo a b, Tendsto (fun y => cur.2.2 (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im)
      (𝓝[H] (u : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  refine exists_int_forall_tendsto_lift_sub hcur hLc hlift (isDerivLog_fwdMap hW hT) isPreconnected_Ioo
    fun u hu => ?_
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo u hu
  exact ⟨ρ, hρ, fun y hy => hK (hcur.inv_mem_dom hy.1), exists_pos_tendsto_deriv_of_notMem hcur hFc hFcc
    hη hW hW0 hT hK hρ fun v hv => hland v (hball (mem_ball_of_ofReal_mem_ball hv))⟩


end InteractingSLE.Theorem14.GW4Fix
