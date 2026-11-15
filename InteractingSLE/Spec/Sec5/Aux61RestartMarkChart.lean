import InteractingSLE.Spec.Sec5.Aux61RestartMarkHit
import InteractingSLE.Spec.Sec5.Aux61RestartGeo

/-!
# The geometric restart chart on good hitting histories

Packet PROVE-AUX61-R1. The physical-target protection input is discharged by
the actual glued history's existing Borel good-hitting certificate. The
remaining incidence premise specifies the source's right-target component.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open InteractingSLE.Restart WangWu LawUnique GlueCond CrossCond.Word49
open Sec7.Lemma71E

/-- The complete measurable chart output, including the literal inherited
physical derivative branch and the current and original-target limits. -/
def HasOriginalTargetRestartChart {Ω : Type*} [MeasurableSpace Ω]
    (s r : ℝ≥0) (q : ℚ) (Y : Ω → HistorySpace 0 0) (η : Ω → ℝ → ℂ)
    (U : ℝ≥0 → Ω → ℝ) (e : ℕ → ℂ) : Prop :=
  ∃ N : Ω → ℕ, Measurable N ∧
    (∀ ω, e (N ω) ∈ retainedDomain (historyHull s Y ω) (η ω) q) ∧
    let D := historyComponent s q Y η (fun ω => e (N ω))
    (∀ ω, (1 : ℂ) ∈ closure (D ω)) ∧
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = D ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (D ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω z, z ∈ D ω →
        (c ω).2.2 z = (physicalRestartLog (stripTargetHull (D ω)) z).im) ∧
      (∀ ω, Tendsto ((c ω).1 ∘ (ownHistoryChart U r ω).2.1) (𝓝[H] 0) (𝓝 0) ∧
        Tendsto (fun w : ℂ => ‖(c ω).1 (w + 1)‖) (𝓝[H] 0) atTop)

/-- Assemble the landed selector, canonical hull record and inherited chart
directly from target protection. No real-flow witness is needed by this API. -/
theorem has_original_target_restart_chart_of_protection
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
    (hclear : ∀ ω, 0 < infDist (η ω q) (historyHull s Y ω))
    (hprotected : ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω))
    (hincident : ∀ ω, ∃ b : ℂ,
      (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
      ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈
        restartComponent (historyHull s Y ω) (η ω) q b)
    {e : ℕ → ℂ} (he : DenseRange e) :
    HasOriginalTargetRestartChart s r q Y η U e := by
  have hUobs := measurableSet_closedBall_subset_historyDomain hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) hm
  have htarget := fun ω => exists_original_right_target_collar
    ((hη ω).2.1.mono Icc_subset_Ici_self) (hη ω).1 (hH ω) (hprotected ω)
  obtain ⟨N, hNm, hb, htc, hmark⟩ :=
    exists_measurable_original_target_component hUobs htarget he
  let D := historyComponent s q Y η (fun ω => e (N ω))
  have hprops := historyComponent_properties hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) (fun ω => (hη ω).1) hm hNm hb
  have hfreq : ∀ ω, ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈ D ω := by
    intro ω
    obtain ⟨b, hbmark, hbaccess⟩ := hincident ω
    have hbc := exists_original_right_target_component_collar
      ((hη ω).2.1.mono Icc_subset_Ici_self) (hη ω).1 (hH ω) (hprotected ω) hbmark
    have heq : D ω = restartComponent (historyHull s Y ω) (η ω) q b :=
      connectedComponentIn_eq_of_original_target_collars (htc ω) hbc
    rw [heq]
    exact hbaccess
  have hcurrent := history_current_collar_of_frequent hrq hUc hU0 hη hq.le
    (fun ω => hH ω ⟨hq, le_rfl⟩) hclear hfreq
  let K : Ω → Set ℂ := fun ω => originalTargetRecord (D ω)
  have hKprops := fun ω => originalTargetRecord_properties (hprops.1 ω).1
    (hprops.1 ω).2.2.1 (hprops.1 ω).2.2.2 (htc ω)
  have hKm : IsDyadicHitMeasurable K := isDyadicHitMeasurable_originalTargetRecord
    (fun ω => (hprops.1 ω).2.2.2) hprops.2
  have hrecord : IsOriginalTargetHullRecord K D := fun ω => (hKprops ω).2.2
  obtain ⟨c, hc, hdom, hbij, hdm, hfm, hlm, hlc, hphase, hlimits⟩ :=
    exists_history_original_right_target_inherited_chart hrq hq hY hUc hU0 hUm hη hi hH hm
      he hNm hb hprotected hKm (fun ω => (hKprops ω).1)
      (fun ω => (hKprops ω).2.1) hmark hcurrent hrecord
  refine ⟨N, hNm, hb, hmark, c, hc, hdom, hbij, hdm, hfm, hlm, hlc, ?_, hlimits⟩
  intro ω z hz
  simpa only [hrecord ω] using hphase ω z hz

/-- On the actual good-hitting histories the live-target input is a theorem.
Incidence still specifies which component contains the current access. -/
theorem has_original_target_restart_chart_of_goodHit
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
    (hclear : ∀ ω, 0 < infDist (η ω q) (historyHull s Y ω))
    (hgood : ∀ ω, Y ω ∈ GlueCond.goodHitSet)
    (hincident : ∀ ω, ∃ b : ℂ,
      (1 : ℂ) ∈ closure (restartComponent (historyHull s Y ω) (η ω) q b) ∧
      ∃ᶠ w in 𝓝[H] 0, (ownHistoryChart U r ω).2.1 w ∈
        restartComponent (historyHull s Y ω) (η ω) q b)
    {e : ℕ → ℂ} (he : DenseRange e) :
    HasOriginalTargetRestartChart s r q Y η U e :=
  has_original_target_restart_chart_of_protection hrq hq hY hUc hU0 hUm hη hi hH hm
    hclear (history_original_target_protected_of_goodHit hgood s) hincident he

end InteractingSLE.Sec5.Aux61Restart
