/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetLateMain
import InteractingSLE.Spec.Sec7.Lemma76GOrder

/-!
# G8: order in the initial joint chart

Packet PROVE-G8-DET. Recover the boundary and displacement properties of
an initial joint inverse, then apply the landed inverse-chart order lemma.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.G8Det.Late.InitialChart

variable {α β : ℝ≥0 → ℂ} {a r : ℝ≥0} (d : InitialChart α β a r)

/-- The inverse in an initial chart is a bijection on the open half-plane. -/
theorem bijOn_inv : BijOn d.inv H (activeDomain α a β r) := by
  refine ⟨d.maps_inv, ?_, ?_⟩
  · intro x hx y hy he
    calc
      x = obstacleMap α β a r (cutMap α a (d.inv x)) := (d.fwd_inv x hx).symm
      _ = obstacleMap α β a r (cutMap α a (d.inv y)) :=
        congrArg (fun z => obstacleMap α β a r (cutMap α a z)) he
      _ = y := d.fwd_inv y hy
  · intro z hz
    exact ⟨_, d.maps_fwd hz, d.inv_fwd z hz⟩

/-- The initial hydrodynamic inverse has bounded displacement on `Hbar`. -/
theorem exists_bound (hcα : Continuous α) (hcβ : Continuous β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) :
    ∃ M : ℝ, ∀ w ∈ Hbar, ‖d.inv w - w‖ ≤ M := by
  have hB := isHPHull_jointHull hcα hcβ hα0 hβ0 a r
  have hg := ConformalImage.isMapOut_mapOut hB
  have hfac := initial_factorization hcα hcβ hα0 hβ0 a r
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hB
  have hb : ∀ w ∈ H, ‖d.inv w - w‖ ≤ M := by
    intro w hw
    have h := hM _ (domain_eq hcα hcβ a r ▸ d.maps_inv hw)
    have he := (hfac (d.maps_inv hw)).trans (d.fwd_inv w hw)
    rw [he, norm_sub_rev] at h
    exact h
  refine ⟨M, fun w hw => ?_⟩
  have : (𝓝[H] w).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hw
  have hlim := (((d.continuous_inv w hw).mono QuantumZipper.H_subset_Hbar).sub
    continuousWithinAt_id).norm
  exact le_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun z hz => hb z hz)

/-- A real boundary argument cannot have its inverse in the open joint domain. -/
theorem inv_real_notMem (hcα : Continuous α) (hcβ : Continuous β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (x : ℝ) :
    d.inv x ∉ activeDomain α a β r := by
  intro hx
  have hB := isHPHull_jointHull hcα hcβ hα0 hβ0 a r
  have hg := ConformalImage.isMapOut_mapOut hB
  have hfac := initial_factorization hcα hcβ hα0 hβ0 a r
  have hbar : (x : ℂ) ∈ Hbar := by change 0 ≤ (x : ℂ).im; simp only [ofReal_im, le_refl]
  have : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hbar
  have hlim := (hg.1.1.continuousOn.continuousAt
    (hB.isOpen.mem_nhds (domain_eq hcα hcβ a r ▸ hx))).tendsto.comp
      ((d.continuous_inv _ hbar).mono QuantumZipper.H_subset_Hbar)
  have heq : ∀ᶠ z in 𝓝[H] (x : ℂ), ConformalImage.mapOut (jointHull α β a r) (d.inv z) = z :=
    eventually_mem_nhdsWithin.mono fun z hz => (hfac (d.maps_inv hz)).trans (d.fwd_inv z hz)
  have he := tendsto_nhds_unique (hlim.congr' heq) (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hH := hg.1.2.mapsTo (domain_eq hcα hcβ a r ▸ hx)
  rw [he] at hH
  change 0 < (x : ℂ).im at hH
  simp only [ofReal_im, lt_self_iff_false] at hH

/-- Every inverse point on the connected prefix is left of the untouched
real mark `1`, when all real prefix points precede `1`. -/
theorem lt_right_of_inv_mem (hcα : Continuous α) (hcβ : Continuous β)
    (hHα : ∀ t, 0 ≤ (α t).im) (hHβ : ∀ t, 0 ≤ (β t).im)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hreal : ∀ z ∈ Restart.prefixSet α a β r, z.im = 0 → z.re < 1)
    {y : ℝ} (hy : d.inv y ∈ Restart.prefixSet α a β r) : y < hydroMark α β a r 1 := by
  classical
  let ψ : ℂ → ℂ := fun z => if z ∈ Hbar then d.inv z else 0
  have heq : EqOn ψ d.inv Hbar := fun z hz => ite_eq_left hz
  have hc : ContinuousOn ψ Hbar := d.continuous_inv.congr fun z hz => heq hz
  have hbij : BijOn ψ H (H \ fillH (Restart.prefixSet α a β r)) := by
    change BijOn ψ H (H \ jointHull α β a r)
    rw [← domain_eq hcα hcβ]
    exact d.bijOn_inv.congr (heq.symm.mono QuantumZipper.H_subset_Hbar)
  have hr : ∀ z ∉ H, ψ z ∉ H \ fillH (Restart.prefixSet α a β r) := by
    intro z hz
    by_cases hb : z ∈ Hbar
    · have him : z.im = 0 := le_antisymm (not_lt.1 hz) hb
      rw [heq hb, ← Restart.ofReal_re_eq him]
      change d.inv (z.re : ℂ) ∉ H \ jointHull α β a r
      rw [← domain_eq hcα hcβ]
      exact d.inv_real_notMem hcα hcβ hα0 hβ0 z.re
    · dsimp only [ψ]
      rw [ite_eq_right hb]
      exact fun h => lt_irrefl 0 (show 0 < (0 : ℂ).im from h.1)
  obtain ⟨M, hM⟩ := d.exists_bound hcα hcβ hα0 hβ0
  have hMb : ∀ z ∈ Hbar, ‖ψ z - z‖ ≤ M := by
    intro z hz
    rw [heq hz]
    exact hM z hz
  have hK : IsCompact (Restart.prefixSet α a β r) :=
    (isCompact_Icc.image hcα).union (isCompact_Icc.image hcβ)
  have hpc : IsPreconnected (Restart.prefixSet α a β r) :=
    IsPreconnected.union' ⟨0, ⟨0, ⟨le_rfl, zero_le⟩, hα0⟩, ⟨0, ⟨le_rfl, zero_le⟩, hβ0⟩⟩
      (isPreconnected_Icc.image _ hcα.continuousOn) (isPreconnected_Icc.image _ hcβ.continuousOn)
  have h1off : (1 : ℂ) ∉ Restart.prefixSet α a β r := by
    intro h
    have := hreal 1 h (by rfl)
    simp only [one_re, lt_self_iff_false] at this
  have hbR : (hydroMark α β a r 1 : ℂ) ∈ Hbar := by
    change 0 ≤ (hydroMark α β a r 1 : ℂ).im; simp only [ofReal_im, le_refl]
  have hby : (y : ℂ) ∈ Hbar := by change 0 ≤ (y : ℂ).im; simp only [ofReal_im, le_refl]
  apply Sec7.Lemma76G.lt_of_inv_mem hK hc hbij hr hMb isCompact_singleton isPreconnected_singleton
    (fun z hz => by rw [mem_singleton_iff.1 hz]; exact le_rfl)
    (fun z hz h => by
      rw [mem_singleton_iff.1 hz] at h
      have hh : 0 < (1 : ℂ).im := h.1
      simp only [one_im, lt_self_iff_false] at hh)
    hK hpc (fun z hz => ?_) (fun z hz h => h.2 ⟨h.1, Or.inl (subset_closure hz)⟩)
    (disjoint_singleton_left.2 h1off) (x := 1) (by simp only [ofReal_one, mem_singleton_iff]) hreal
    (x₀ := 0) (Or.inl ⟨0, ⟨le_rfl, zero_le⟩, by simpa only [ofReal_zero] using hα0⟩)
    (by rw [heq hbR, d.inv_right]; exact mem_singleton _) (by rw [heq hby]; exact hy)
  rcases hz with ⟨t, _, rfl⟩ | ⟨t, _, rfl⟩
  · exact hHα t
  · exact hHβ t

end InteractingSLE.RLC.G8Det.Late.InitialChart
