import InteractingSLE.Spec.Sec5.Aux61RestartBdryWindow

/-!
# Charted clearance pieces cover the consumer's actual window event

Packet PROVE-AUX61-R1. The consumer reads the original driver `cfDrv`, whereas
the retained chart reads `cfDrv0`. Their hulls at the retained time agree on
good histories. This adapter proves window coverage without changing the
window event or assuming a measurable future endpoint or component selector.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 Aux61Kernel

/-- The application bridge for the consumer's original counterflow driver.
Only equality of the retained hulls is used; the window code is unchanged. -/
theorem mem_restartConfigurationEvent_of_cfDrv_window
    {Ω : Type*} {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q)
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hUc : Continuous fun t => U t ω) (hU0 : U 0 ω = 0)
    (htrace : IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hη : IsProperArc (η ω)) (hgood : Y ω ∈ goodHitSet) {c : WinCode}
    (hwin : RestartWindowEvent (Prop411Q.cfDrv (Y ω)) s (η ω) q c) :
    ω ∈ restartConfigurationEvent s r q Y η U := by
  have heq : Prop51G.cfHullQ (Prop411Q.cfDrv (Y ω)) s = historyHull s Y ω :=
    congrArg (fun A : Set ℂ => WangWu.negInv '' A) (fwdHull_cfDrv0 hgood.1 s).symm
  have hclear := positive_clearance_of_windowExcursion hη
    (isClosed_negInv_fwdHull_of_mem_goodHitSet hgood s.coe_nonneg).1
    hwin.1 hwin.2.choose_spec.1
  have hboundary : ∀ x : ℝ, 0 < x →
      (x : ℂ) ∉ closure (Prop51G.cfHullQ (Prop411Q.cfDrv (Y ω)) s) := by
    rw [heq]
    exact fun _ hx => real_boundary_protected_of_goodHit hgood s hx.ne'
  have haccess := physical_current_access_of_restart_window
    (Chart.continuous_rpath_of_continuous hUc) (Chart.rpath_zero_of hU0) htrace hη
    hboundary hwin
  rw [heq] at hclear haccess
  refine ⟨⟨hη.inj.mono Icc_subset_Ici_self, fun t ht => hη.mem_H t ht.1, hclear⟩,
    original_target_protected_of_goodHit hgood s, ?_⟩
  change ∃ b : ℂ,
    (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
    ∃ᶠ z in 𝓝[H] 0, QuantumZipper.fwdMapInv (Ito.rpath (U · ω)) (r : ℝ) z ∈
      restartComponent (historyHull s Y ω) (η ω) q b
  rw [hrq]
  exact haccess

/-- Almost-sure window coverage follows from the actual own-path regularity
and the counterflow's already transferred good hitting event. These conditions
need hold only almost surely. No window-to-configuration premise is assumed. -/
theorem ae_window_mem_restartConfigurationEvent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q)
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ᵐ ω ∂μ, Continuous fun t => U t ω)
    (hU0 : ∀ᵐ ω ∂μ, U 0 ω = 0)
    (htrace : ∀ᵐ ω ∂μ, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hη : ∀ᵐ ω ∂μ, IsProperArc (η ω)) (hgood : ∀ᵐ ω ∂μ, Y ω ∈ goodHitSet) :
    ∀ᵐ ω ∂μ, ∀ c : WinCode,
      RestartWindowEvent (Prop411Q.cfDrv (Y ω)) s (η ω) q c →
        ω ∈ restartConfigurationEvent s r q Y η U := by
  filter_upwards [hUc, hU0, htrace, hη, hgood] with ω hc h0 htr ha hg c hw
  exact mem_restartConfigurationEvent_of_cfDrv_window hrq hc h0 htr ha hg hw

/-- A single probability-one event covers every positive rational original
own restart and every window code by the retained geometric configuration. -/
theorem ae_all_windows_mem_restartConfigurationEvent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {s : ℝ≥0}
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ᵐ ω ∂μ, Continuous fun t => U t ω)
    (hU0 : ∀ᵐ ω ∂μ, U 0 ω = 0)
    (htrace : ∀ᵐ ω ∂μ, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hη : ∀ᵐ ω ∂μ, IsProperArc (η ω)) (hgood : ∀ᵐ ω ∂μ, Y ω ∈ goodHitSet) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 < q → ∀ c : WinCode,
      RestartWindowEvent (Prop411Q.cfDrv (Y ω)) s (η ω) q c →
        ω ∈ restartConfigurationEvent s (Real.toNNReal q) q Y η U := by
  filter_upwards [hUc, hU0, htrace, hη, hgood] with ω hc h0 htr ha hg q hq c hw
  exact mem_restartConfigurationEvent_of_cfDrv_window
    (Real.coe_toNNReal _ (by exact_mod_cast hq.le)) hc h0 htr ha hg hw

/-- The consumer's actual windows are covered almost surely by the existing
countable measurable clearance pieces, each carrying the inherited restart
chart. Future windows and endpoints do not enter the chart's construction. -/
theorem has_charted_clearance_cover_of_windows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q) (hq : 0 < (q : ℝ))
    {Y : Ω → HistorySpace 0 0} (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (htrace : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    (hη : ∀ᵐ ω ∂μ, IsProperArc (η ω)) (hgood : ∀ᵐ ω ∂μ, Y ω ∈ goodHitSet)
    {e : ℕ → ℂ} (he : DenseRange e) :
    (∀ᵐ ω ∂μ, ∀ c : WinCode,
      RestartWindowEvent (Prop411Q.cfDrv (Y ω)) s (η ω) q c →
        ∃ n : ℕ, ω ∈ restartClearancePiece s r q Y η U n) ∧
    ∀ n : ℕ, MeasurableSet (restartClearancePiece s r q Y η U n) ∧
      HasOriginalTargetRestartChart s r q
        (fun ω : restartClearancePiece s r q Y η U n => Y ω.1)
        (fun ω : restartClearancePiece s r q Y η U n => η ω.1)
        (fun t (ω : restartClearancePiece s r q Y η U n) => U t ω.1) e := by
  have hcover := has_countable_charted_clearance_cover hrq hq hY hUc hU0 hUm htrace hm he
  refine ⟨?_, hcover.2⟩
  filter_upwards [ae_window_mem_restartConfigurationEvent hrq
    (ae_of_all μ hUc) (ae_of_all μ hU0) (ae_of_all μ htrace) hη hgood] with ω hω c hw
  have hmem := hω c hw
  rw [hcover.1] at hmem
  exact mem_iUnion.1 hmem

end InteractingSLE.Sec5.Aux61Restart
