import InteractingSLE.Spec.Sec5.Aux61RestartEventChart

/-!
# A positive fresh segment in the incident component

Packet PROVE-AUX61-R1. A simple extension of the original own path, positive
tip clearance and current-access incidence give a positive interior segment
in that component. Membership of a whole future segment is a conclusion.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Restart

/-- At a separated simple interior tip, a simple extension remains in the
incident retained component for a positive time. The original own time is
used throughout; no relative-capacity time is substituted for it. -/
theorem exists_fresh_segment_in_incident_component
    {W : ℝ → ℝ} {η : ℝ → ℂ} {r T : ℝ} {K : Set ℂ} {b : ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (hr : 0 ≤ r) (hrT : r < T) (hi : InjOn η (Icc 0 T))
    (hH : MapsTo η (Ioc 0 r) H) (htip : η r ∈ H)
    (hKo : IsOpen (H \ K)) (hclear : 0 < infDist (η r) K)
    (hincident : ∃ᶠ w in 𝓝[H] 0, fwdMapInv W r w ∈ restartComponent K η r b) :
    ∃ t : ℝ, r < t ∧ t ≤ T ∧ InjOn η (Icc 0 t) ∧
      MapsTo η (Ioc r t) (restartComponent K η r b) := by
  obtain ⟨δ, hδ, _, hcollar⟩ := exists_restart_halfDisk_collar_of_pos_infDist
    hW hW0 hr hη hKo htip hclear
  obtain ⟨ε, hε, hcurrent⟩ := exists_current_collar_of_frequent_component
    ⟨δ, hδ, hcollar⟩ hincident
  have hhull : fwdHull W r = η '' Ioc 0 r := by
    rw [hη.2.2 r hr]
    exact YuanCharacterisation.fillH_image_eq hr
      (hη.2.1.mono Icc_subset_Ici_self)
      (hi.mono (Icc_subset_Icc le_rfl hrT.le))
      (by rw [hη.1, zero_im]) hH
  have hlimη : Tendsto η (𝓝[>] r) (𝓝 (η r)) :=
    (hη.2.1 r hr).tendsto.mono_left
      (nhdsWithin_mono r fun t ht => hr.trans (show r < t from ht).le)
  have hηH : ∀ᶠ t in 𝓝[>] r, η t ∈ H :=
    hlimη.eventually (QuantumZipper.isOpen_H.mem_nhds htip)
  have hown : ∀ᶠ t in 𝓝[>] r, η t ∈ H \ fwdHull W r := by
    filter_upwards [hηH, Ioc_mem_nhdsGT hrT] with t htH ht
    refine ⟨htH, ?_⟩
    rw [hhull]
    rintro ⟨u, hu, heq⟩
    have hut : u = t := hi ⟨hu.1.le, hu.2.trans hrT.le⟩
      ⟨hr.trans ht.1.le, ht.2⟩ heq
    exact (not_le_of_gt ht.1) (hut ▸ hu.2)
  have hv := tendsto_own_chart_at_restart hW hW0 hη hr hown
  have hsmall : ∀ᶠ t in 𝓝[>] r, fwdMap W r (η t) ∈ ball 0 ε ∩ H := by
    apply hv.eventually
    have hball : ∀ᶠ w in 𝓝[H] (0 : ℂ), w ∈ ball 0 ε :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hε)
    exact hball.and self_mem_nhdsWithin
  have hev : ∀ᶠ t in 𝓝[>] r,
      η t ∈ restartComponent K η r b ∧ t ∈ Ioc r T := by
    filter_upwards [hsmall, hown, Ioc_mem_nhdsGT hrT] with t hsmallt hownt ht
    refine ⟨?_, ht⟩
    have h := hcurrent hsmallt
    rwa [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr hownt] at h
  obtain ⟨t, hrt, ht⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  have htT : t ≤ T := (ht ⟨hrt, le_rfl⟩).2.2
  exact ⟨t, hrt, htT, hi.mono (Icc_subset_Icc le_rfl htT), fun u hu => (ht hu).1⟩

end InteractingSLE.Sec5.Aux61Restart
