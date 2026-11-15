import InteractingSLE.Spec.Sec5.Aux61RestartInstRecords

/-!
# The restart chart for the actual stopped histories

Packet PROVE-AUX61-R1; Astra follow-up 4, section 1.1. This assembly uses the
actual counterflow record and original own-time prefix. The current collar is
the one supplied by `exists_history_current_collar`, in the selected target
component. The two explicit remaining geometric inputs are the collar at the
original right-target junction and `CollarPrimeEndComparison` for these exact
two inverse maps. The latter is not replaced by physical convergence of points.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu WangWu.ImgWord LawUnique GlueCond CrossCond.Word49
open Sec7.Lemma71E

/-- Before the original first boundary contact a simple prefix has no filled
pockets. Every retained component therefore lies in the own-chart domain. -/
theorem historyComponent_subset_own_dom
    {Ω : Type*} {s r : ℝ≥0} {q : ℚ} (hrq : (r : ℝ) = q)
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hi : ∀ ω, InjOn (η ω) (Icc (0 : ℝ) q))
    (hH : ∀ ω, MapsTo (η ω) (Ioc (0 : ℝ) q) H) (b : Ω → ℂ) (ω : Ω) :
    historyComponent s q Y η b ω ⊆ (ownHistoryChart U r ω).dom := by
  have hW := Chart.continuous_rpath_of_continuous (hUc ω)
  have hW0 := Chart.rpath_zero_of (hU0 ω)
  have hr : 0 ≤ (q : ℝ) := hrq ▸ r.coe_nonneg
  have hhull : fwdHull (Ito.rpath (U · ω)) r = η ω '' Ioc 0 q := by
    rw [hrq, (hη ω).2.2 _ hr]
    exact YuanCharacterisation.fillH_image_eq hr
      ((hη ω).2.1.mono Icc_subset_Ici_self) (hi ω)
      (by rw [(hη ω).1, zero_im]) (hH ω)
  intro z hz
  have hzD := connectedComponentIn_subset _ _ hz
  change z ∈ H \ (historyHull s Y ω ∪ η ω '' Icc 0 q) at hzD
  rw [(Chart.isConformal_loewnerChartAtTime hUc hU0 ω).coe_dom]
  change z ∈ QuantumZipper.fwdMapInv (Ito.rpath (U · ω)) r '' H
  rw [QuantumZipper.RS.image_fwdMapInv_H hW hW0 r.coe_nonneg, hhull]
  exact ⟨hzD.1, fun hzslit => hzD.2 (Or.inr (image_mono Ioc_subset_Icc_self hzslit))⟩

/-- The measurable normalized chart for the actual pair of retained histories.
The rational time `q` is the original own time, represented by `r` in the
Loewner APIs. All driver measurability is restricted to times at most `r`.

`hcurrent` says that the own collar is in the history-selected component.
`htarget` and `hcomparison` are the exact remaining boundary geometry inputs;
the theorem is a conditional helper, not an unconditional source theorem. -/
theorem exists_history_restart_chart
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    (hrq : (r : ℝ) = q) {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hi : ∀ ω, InjOn (η ω) (Icc (0 : ℝ) q))
    (hH : ∀ ω, MapsTo (η ω) (Ioc (0 : ℝ) q) H)
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} (he : DenseRange e) {N : Ω → ℕ} (hN : Measurable N)
    (hb : ∀ ω, e (N ω) ∈ retainedDomain (historyHull s Y ω) (η ω) q) :
    let D := historyComponent s q Y η (fun ω => e (N ω))
    (∀ ω, ∃ δ > 0, MapsTo (ownHistoryChart U r ω).2.1 (ball 0 δ ∩ H) (D ω)) →
    (∀ ω, ∃ δ > 0, MapsTo (historyTargetInv s Y ω) (ball 0 δ ∩ H) (D ω)) →
    (∀ ω, CollarPrimeEndComparison (D ω) (ownHistoryChart U r ω).2.1
      (historyTargetInv s Y ω)) →
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
        Tendsto (fun w => ‖(c ω).1 (historyTargetInv s Y ω w)‖) (𝓝[H] 0) atTop) := by
  dsimp only
  intro hcurrent htarget hcomparison
  let D := historyComponent s q Y η (fun ω => e (N ω))
  have hr : 0 ≤ (q : ℝ) := hrq ▸ r.coe_nonneg
  have hprops := historyComponent_properties hr hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) (fun ω => (hη ω).1) hm hN hb
  have hmem := measurableSet_mem_of_closedBall (fun ω => (hprops.1 ω).1) hprops.2
  have hown := historyComponent_subset_own_dom (s := s) (Y := Y) hrq hUc hU0 hη hi hH
    (fun ω => e (N ω))
  have hcf : ∀ ω, D ω ⊆ H \ historyHull s Y ω := by
    intro ω z hz
    have h := connectedComponentIn_subset _ _ hz
    exact ⟨h.1, fun hzK => h.2 (Or.inl hzK)⟩
  have hT := historyTarget_access_properties hcf
  have hO := fun ω => Chart.isConformal_loewnerChartAtTime (τ := fun _ => r) hUc hU0 ω
  exact exists_measurable_chart_of_retained_collars
    (fun ω => (hprops.1 ω).1) (fun ω => (hprops.1 ω).2.1)
    (fun ω => (hprops.1 ω).2.2.1) (fun ω => (hprops.1 ω).2.2.2) hprops.2 he
    (fun ω => ((hO ω).differentiableOn_fwd.continuousOn).mono (hown ω))
    (fun ω => (hT ω).1)
    (measurable_indicator_restrict_domain hmem hown
      (measurable_indicator_ownHistoryChart hUc hU0 hUm))
    (measurable_indicator_historyTargetMap hY hmem hcf)
    (fun ω z hz => (hO ω).fwd_mem (hown ω hz)) (fun ω => (hT ω).2.1)
    (fun ω => (hO ω).2.2) (fun ω => (hT ω).2.2.1)
    (fun ω z hz => (hO ω).inv_fwd (hown ω hz)) (fun ω => (hT ω).2.2.2)
    hcurrent htarget hcomparison

end InteractingSLE.Sec5.Aux61Restart
