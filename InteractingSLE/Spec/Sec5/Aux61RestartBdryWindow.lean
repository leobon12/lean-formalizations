import InteractingSLE.Spec.Sec5.Aux61RestartBdryHistory

/-!
# The actual window event supplies the restart geometry

Packet PROVE-AUX61-R1. On a simple proper own trace and a good counterflow
history, the consumer's window supplies positive tip clearance and incidence
of the own prime-end approach in the physical original-target component.
The earlier contact proves the hull is nonempty; no convention about distance
to the empty set is used. The entire old own prefix remains removed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMapInv)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 Aux61Kernel

/-- The earlier contact in a window excursion makes the retained hull
nonempty. Closedness and noncontact at the restart then give strict clearance. -/
theorem positive_clearance_of_windowExcursion
    {w : ℝ → ℝ} {s t u₀ : ℝ} {η : ℝ → ℂ} {c : WinCode}
    (hη : IsProperArc η) (hK : IsClosed (Prop51G.cfHullQ w s))
    (hwin : IsWindow w s η t c) (hexc : WindowExcursion w s η t c u₀) :
    0 < infDist (η t) (Prop51G.cfHullQ w s) := by
  obtain ⟨⟨τ, hτ, hcontact⟩, hfree, -, -, -⟩ := hexc
  have hne : (Prop51G.cfHullQ w s).Nonempty := by
    refine ⟨η τ, ?_⟩
    by_contra hnot
    exact hcontact ⟨hη.mem_H τ hτ.1, hnot⟩
  have htfree := hfree t ⟨sub_le_self t hwin.δ_pos.le, le_rfl⟩
  exact (hK.notMem_iff_infDist_pos hne).1 htfree.2

/-- A fresh point in the window selects the component of the entire fresh
excursion. Simplicity excludes every point of the retained own prefix. -/
theorem window_excursion_subset_restartComponent
    {w : ℝ → ℝ} {s t u₀ u : ℝ} {η : ℝ → ℂ} {c : WinCode}
    (hη : IsProperArc η) (ht : 0 ≤ t)
    (hexc : WindowExcursion w s η t c u₀) (hu : u ∈ Ioo t u₀) :
    η '' Ioo t u₀ ⊆ restartComponent (Prop51G.cfHullQ w s) η t (η u) := by
  have huD : η u ∈ retainedDomain (Prop51G.cfHullQ w s) η t := by
    refine ⟨(hexc.2.2.2.1 u hu).1.1, ?_⟩
    rintro (hK | ⟨v, hv, heq⟩)
    · exact (hexc.2.2.2.1 u hu).1.2 hK
    · have hvu := hη.inj hv.1 (ht.trans hu.1.le) heq
      exact (not_le.2 hu.1) (hvu ▸ hv.2)
  exact image_preContact_subset_component ht
    (hη.cont.mono Icc_subset_Ici_self) (hη.inj.mono Icc_subset_Ici_self)
    (fun v hv => (hexc.2.2.2.1 v hv).1)
    ⟨η u, ⟨u, hu, rfl⟩, mem_connectedComponentIn huD⟩

/-- A window in the target component yields the actual own inverse-chart
approach in the component marked by the physical original target 1. -/
theorem physical_current_access_of_restart_window
    {W w : ℝ → ℝ} {s t : ℝ} {η : ℝ → ℂ} {c : WinCode}
    (hW : Continuous W) (hW0 : W 0 = 0)
    (htrace : IsLoewnerTrace W η) (hη : IsProperArc η)
    (hboundary : ∀ x : ℝ, 0 < x → (x : ℂ) ∉ closure (Prop51G.cfHullQ w s))
    (hwin : RestartWindowEvent w s η t c) :
    ∃ b : ℂ, (1 : ℂ) ∈ closure (restartComponent (Prop51G.cfHullQ w s) η t b) ∧
      ∃ᶠ z in 𝓝[H] 0, fwdMapInv W t z ∈
        restartComponent (Prop51G.cfHullQ w s) η t b := by
  obtain ⟨hwin, u₀, hexc, u, hu, htarget⟩ := hwin
  have ht : 0 < t := hwin.δ_pos.trans hwin.δ_lt
  have hmark := (isTargetComp_iff_original_target
    (hη.cont.mono Icc_subset_Ici_self) hη.zero
    (fun v hv => hη.mem_H v hv.1) hboundary).1 htarget
  have hseg := window_excursion_subset_restartComponent hη ht.le hexc hu
  have hown : restartComponent (Prop51G.cfHullQ w s) η t (η u) ⊆ H \ fwdHull W t := by
    intro z hz
    have hzD := connectedComponentIn_subset _ _ hz
    rw [fwdHull_eq_image_Ioc htrace hη ht.le]
    exact ⟨hzD.1, fun hzP => hzD.2
      (Or.inr (image_mono Ioc_subset_Icc_self hzP))⟩
  obtain ⟨T, htT, hTu⟩ := exists_between hexc.2.2.1
  refine ⟨η u, hmark, frequent_current_access_of_fresh_continuation
    hW hW0 htrace ht.le htT hown ?_⟩
  intro v hv
  exact hseg ⟨v, ⟨hv.1, hv.2.trans_lt hTu⟩, rfl⟩

/-- Pointwise application bridge: an actual window sample is a member of the
full geometric event on which the measurable chart has already been built. -/
theorem mem_restartConfigurationEvent_of_window
    {Ω : Type*} {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q)
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hUc : Continuous fun t => U t ω) (hU0 : U 0 ω = 0)
    (htrace : IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hη : IsProperArc (η ω)) (hgood : Y ω ∈ goodHitSet) {c : WinCode}
    (hwin : RestartWindowEvent (cfDrv0 s (Y ω)) s (η ω) q c) :
    ω ∈ restartConfigurationEvent s r q Y η U := by
  have hclear := positive_clearance_of_windowExcursion hη
    (isClosed_stopped_reflected_hull_of_goodHit hgood s) hwin.1 hwin.2.choose_spec.1
  have haccess := physical_current_access_of_restart_window
    (Chart.continuous_rpath_of_continuous hUc) (Chart.rpath_zero_of hU0) htrace hη
    (fun _ hx => real_boundary_protected_of_goodHit hgood s hx.ne') hwin
  refine ⟨⟨hη.inj.mono Icc_subset_Ici_self, fun t ht => hη.mem_H t ht.1, hclear⟩,
    original_target_protected_of_goodHit hgood s, ?_⟩
  change ∃ b : ℂ,
    (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
    ∃ᶠ z in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 z ∈
      restartComponent (historyHull s Y ω) (η ω) q b
  change ∃ b : ℂ,
    (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
    ∃ᶠ z in 𝓝[H] 0, fwdMapInv (Ito.rpath (U · ω)) (r : ℝ) z ∈
      restartComponent (historyHull s Y ω) (η ω) q b
  rw [hrq]
  exact haccess

end InteractingSLE.Sec5.Aux61Restart
