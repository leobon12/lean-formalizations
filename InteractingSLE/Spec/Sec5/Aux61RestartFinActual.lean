import InteractingSLE.Spec.Sec5.Aux61RestartFinLog

/-!
# The actual-history restart chart with the original right strip end

Packet PROVE-AUX61-R1. The original target is `1` in Q. Counterflow protection
there and the selected component's closure mark prove its physical collar.
The two prime-end approaches and their distinctness are proved, not supplied
as a `CollarPrimeEndComparison` input. No `junR` access is used as target.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu WangWu.ImgWord LawUnique GlueCond CrossCond.Word49
open Sec7.Lemma71E

/-- The actual measurable restart chart, with the original right end kept as
target. The remaining geometric inputs are counterflow protection at `1`, the
selected component's closure mark at `1`, and membership of its current collar.
The target collar and prime-end comparison are conclusions of the construction. -/
theorem exists_history_original_right_target_chart
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    (hrq : (r : ℝ) = q) (hq : 0 < (q : ℝ)) {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hi : ∀ ω, InjOn (η ω) (Icc (0 : ℝ) q))
    (hH : ∀ ω, MapsTo (η ω) (Ioc (0 : ℝ) q) H)
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} (he : DenseRange e) {N : Ω → ℕ} (hN : Measurable N)
    (hb : ∀ ω, e (N ω) ∈ retainedDomain (historyHull s Y ω) (η ω) q)
    (hprotected : ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω)) :
    let D := historyComponent s q Y η (fun ω => e (N ω))
    (∀ ω, (1 : ℂ) ∈ closure (D ω)) →
    (∀ ω, ∃ δ > 0, MapsTo (ownHistoryChart U r ω).2.1 (ball 0 δ ∩ H) (D ω)) →
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = D ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (D ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (D ω) ∧
        ∀ z ∈ D ω, (c ω).2.2 z = (L z).im) ∧
      (∀ ω, Tendsto ((c ω).1 ∘ (ownHistoryChart U r ω).2.1) (𝓝[H] 0) (𝓝 0) ∧
        Tendsto (fun w : ℂ => ‖(c ω).1 (w + 1)‖) (𝓝[H] 0) atTop) := by
  dsimp only
  intro hmark hcurrent
  let D := historyComponent s q Y η (fun ω => e (N ω))
  have hprops := historyComponent_properties hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) (fun ω => (hη ω).1) hm hN hb
  have hmem := measurableSet_mem_of_closedBall (fun ω => (hprops.1 ω).1) hprops.2
  have hown := historyComponent_subset_own_dom (s := s) (Y := Y) hrq hUc hU0 hη hi hH
    (fun ω => e (N ω))
  have hO := fun ω => Chart.isConformal_loewnerChartAtTime (τ := fun _ => r) hUc hU0 ω
  have htarget : ∀ ω, ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D ω := fun ω =>
    exists_original_right_target_component_collar ((hη ω).2.1.mono Icc_subset_Ici_self)
      (hη ω).1 (hH ω) (hprotected ω) (hmark ω)
  have hcmp : ∀ ω, CollarPrimeEndComparison (D ω) (ownHistoryChart U r ω).2.1
      (fun w => w + 1) := by
    intro ω
    have hW := Chart.continuous_rpath_of_continuous (hUc ω)
    have hW0 := Chart.rpath_zero_of (hU0 ω)
    have hsc : IsSimplyConnected ((ownHistoryChart U r ω).dom : Set ℂ) := by
      rw [coe_dom_ownHistoryChart hUc hU0]
      exact (isHPHull_fwdHull hW r.coe_nonneg).2.2.2
    apply collarPrimeEndComparison_of_original_target (ownHistoryChart U r ω).dom.isOpen
      hsc (hO ω).dom_subset (hprops.1 ω).1 (hprops.1 ω).2.2.1 (hown ω)
      (hO ω).isConformalBijection
      (z₀ := η ω r) (by rw [hrq]; exact hH ω ⟨hq, le_rfl⟩)
      ((hη ω).tendsto_fwdMapInv_tip hW hW0 r.coe_nonneg)
      (hcurrent ω) (htarget ω)
  have htargetInv : ∀ ω, ∃ δ > 0,
      MapsTo (fun w : ℂ => w + 1) (ball 0 δ ∩ H) (D ω) := by
    intro ω
    obtain ⟨δ, hδ, hf⟩ := htarget ω
    refine ⟨δ, hδ, fun w hw => hf ⟨?_, ?_⟩⟩
    · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw.1
    · change 0 < (w + 1).im
      simpa only [add_im, one_im, add_zero] using (show 0 < w.im from hw.2)
  exact exists_measurable_chart_of_retained_collars
    (fun ω => (hprops.1 ω).1) (fun ω => (hprops.1 ω).2.1)
    (fun ω => (hprops.1 ω).2.2.1) (fun ω => (hprops.1 ω).2.2.2) hprops.2 he
    (fun ω => ((hO ω).differentiableOn_fwd.continuousOn).mono (hown ω))
    (fun _ => continuousOn_id.sub continuousOn_const)
    (measurable_indicator_restrict_domain hmem hown
      (measurable_indicator_ownHistoryChart hUc hU0 hUm))
    (fun z => measurable_const.indicator (hmem z))
    (fun ω z hz => (hO ω).fwd_mem (hown ω hz))
    (fun ω z hz => by
      change 0 < (z - 1).im
      simpa only [sub_im, one_im, sub_zero] using
        (show 0 < z.im from (hprops.1 ω).2.2.2 hz))
    (fun ω => (hO ω).2.2) (fun _ w _ => add_sub_cancel_right w 1)
    (fun ω z hz => (hO ω).inv_fwd (hown ω hz)) (fun _ z _ => sub_add_cancel z 1)
    hcurrent htargetInv hcmp

end InteractingSLE.Sec5.Aux61Restart
