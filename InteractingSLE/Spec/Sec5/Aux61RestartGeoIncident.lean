import InteractingSLE.Spec.Sec5.Aux61RestartGeoActual

/-!
# Reading current-access incidence from the fresh interior continuation

Packet PROVE-AUX61-R1. The own-chart access theorem puts the fresh continuation
at zero in its original own coordinate. Its inverse images therefore visit
the incident component arbitrarily near zero. The component selector itself
is still constructed exclusively from the retained past.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

/-- A fresh interior continuation in a specified retained component supplies
incidence of its current inverse-chart access. The full approach theorem is
reused; no boundary-extension premise is added. -/
theorem frequent_current_access_of_fresh_continuation
    {W : ℝ → ℝ} {η : ℝ → ℂ} {r T : ℝ} {D : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (hr : 0 ≤ r) (hrT : r < T) (hown : D ⊆ H \ fwdHull W r)
    (hnew : MapsTo η (Ioc r T) D) :
    ∃ᶠ w in 𝓝[H] 0, fwdMapInv W r w ∈ D := by
  have hηown : ∀ᶠ t in 𝓝[>] r, η t ∈ H \ fwdHull W r := by
    filter_upwards [Ioc_mem_nhdsGT hrT] with t ht
    exact hown (hnew ht)
  have hv := tendsto_own_chart_at_restart hW hW0 hη hr hηown
  apply hv.frequently
  have hm : ∀ᶠ t in 𝓝[>] r, fwdMapInv W r (fwdMap W r (η t)) ∈ D := by
    filter_upwards [Ioc_mem_nhdsGT hrT] with t ht
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr (hown (hnew ht))]
    exact hnew ht
  exact hm.frequently

/-- Actual-history version, ready to discharge the incidence premise of the
geometric chart from any compact fresh pre-contact segment in that component. -/
theorem frequent_history_current_access_of_continuation
    {Ω : Type*} {U : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ} {r : ℝ≥0} {T : ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω)) (hrT : (r : ℝ) < T)
    {D : Ω → Set ℂ} (hown : ∀ ω, D ω ⊆ (ownHistoryChart U r ω).dom)
    (hnew : ∀ ω, MapsTo (η ω) (Ioc (r : ℝ) T) (D ω)) :
    ∀ ω, ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈ D ω := by
  intro ω
  have hsub : D ω ⊆ H \ fwdHull (Ito.rpath (U · ω)) r := by
    simpa only [coe_dom_ownHistoryChart hUc hU0] using hown ω
  exact frequent_current_access_of_fresh_continuation
    (Chart.continuous_rpath_of_continuous (hUc ω)) (Chart.rpath_zero_of (hU0 ω))
    (hη ω) r.coe_nonneg hrT hsub (hnew ω)

end InteractingSLE.Sec5.Aux61Restart
