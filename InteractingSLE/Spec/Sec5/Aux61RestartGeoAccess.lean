import InteractingSLE.Spec.Sec5.Aux61RestartGeoSelect

/-!
# Membership of the current collar in the original-target component

Packet PROVE-AUX61-R1. Positive tip clearance already constructs a collar in
some retained component. If the current access meets the selected original-
target component arbitrarily near zero, the two components coincide. Thus
source current-access incidence implies the whole-collar hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu WangWu.ImgWord LawUnique GlueCond CrossCond.Word49

/-- A collar in one component lies in a second component if its access visits
the second arbitrarily near zero. This is incidence of the actual current
access, rather than a boundary-extension hypothesis. -/
theorem exists_current_collar_of_frequent_component
    {U : Set ℂ} {F : ℂ → ℂ} {b : ℂ}
    (hcollar : ∃ δ > 0,
      F '' (ball 0 δ ∩ H) ⊆ connectedComponentIn U (F ((δ / 2 : ℝ) * I)))
    (haccess : ∃ᶠ w in 𝓝[H] 0, F w ∈ connectedComponentIn U b) :
    ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) (connectedComponentIn U b) := by
  obtain ⟨δ, hδ, hF⟩ := hcollar
  have hev : ∀ᶠ w in 𝓝[H] 0, w ∈ ball (0 : ℂ) δ ∩ H := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hδ),
      self_mem_nhdsWithin] with w hw hwH
    exact ⟨hw, hwH⟩
  obtain ⟨w, hwD, hws⟩ := (haccess.and_eventually hev).exists
  have hwC := hF ⟨w, hws, rfl⟩
  have heq := (connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwD).symm
  refine ⟨δ, hδ, fun z hz => ?_⟩
  rw [← heq]
  exact hF ⟨z, hz, rfl⟩

/-- At the actual separated original own time, current-access incidence in the
target component supplies its entire own inverse-chart collar. -/
theorem history_current_collar_of_frequent
    {Ω : Type*} {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q)
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hq : 0 ≤ (q : ℝ)) (htip : ∀ ω, η ω q ∈ H)
    (hclear : ∀ ω, 0 < infDist (η ω q) (historyHull s Y ω))
    {b : Ω → ℂ}
    (haccess : ∀ ω, ∃ᶠ w in 𝓝[H] 0,
      (ownHistoryChart U r ω).2.1 w ∈ historyComponent s q Y η b ω) :
    ∀ ω, ∃ δ > 0,
      MapsTo (ownHistoryChart U r ω).2.1 (ball 0 δ ∩ H) (historyComponent s q Y η b ω) := by
  intro ω
  obtain ⟨δ, hδ, _, hf⟩ := exists_history_current_collar (fun ω =>
    Chart.continuous_rpath_of_continuous (hUc ω))
    (fun ω => Chart.rpath_zero_of (hU0 ω)) hη hq htip hclear ω
  have hfreq := haccess ω
  change ∃ᶠ w in 𝓝[H] 0, QuantumZipper.fwdMapInv (Ito.rpath (U · ω)) (r : ℝ) w ∈
    historyComponent s q Y η b ω at hfreq
  rw [hrq] at hfreq
  change ∃ δ > 0, MapsTo (QuantumZipper.fwdMapInv (Ito.rpath (U · ω)) (r : ℝ))
    (ball 0 δ ∩ H) (historyComponent s q Y η b ω)
  rw [hrq]
  exact exists_current_collar_of_frequent_component ⟨δ, hδ, hf⟩ hfreq

end InteractingSLE.Sec5.Aux61Restart
