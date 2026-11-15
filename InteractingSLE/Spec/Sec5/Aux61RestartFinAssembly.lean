import InteractingSLE.Spec.Sec5.Aux61RestartFinCanonical

/-!
# The actual original-target restart chart with its inherited branch

Packet PROVE-AUX61-R1. The chart, full collar limits, and measurable integer
branch correction are assembled for the actual stopped histories. The one
remaining random-hull input is stated as an exact compact filled-hull record.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open Restart WangWu WangWu.ImgWord LawUnique GlueCond CrossCond.Word49
open Sec7.Lemma71E

/-- Exact remaining filled-hull representation, separate from measurable-hit,
compactness and lower-half-plane connectivity properties of the raw record.
It concerns the component at the original right target, in the retargeted Q
coordinate. It is not a supplied prime-end or logarithm hypothesis. -/
def IsOriginalTargetHullRecord {Ω : Type*} (K D : Ω → Set ℂ) : Prop :=
  ∀ ω, fillH (K ω) = stripTargetHull (D ω)

/-- The measurable original-target chart, now with the literal inherited
physical phase. Its additional canonical logarithm, phase-zero access, and
anchor measurability are supplied by `Aux61RestartFinLog`, not assumed here.
The remaining geometric inputs are displayed as named premises. -/
theorem exists_history_original_right_target_inherited_chart
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
    (hprotected : ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω))
    {K : Ω → Set ℂ} (hKm : IsDyadicHitMeasurable K)
    (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf)) :
    let D := historyComponent s q Y η (fun ω => e (N ω))
    (∀ ω, (1 : ℂ) ∈ closure (D ω)) →
    (∀ ω, ∃ δ > 0, MapsTo (ownHistoryChart U r ω).2.1 (ball 0 δ ∩ H) (D ω)) →
    IsOriginalTargetHullRecord K D →
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ((c ω).dom : Set ℂ) = D ω) ∧
      (∀ ω, IsConformalBijection (c ω).1 (D ω) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω z, z ∈ D ω → (c ω).2.2 z = (physicalRestartLog (fillH (K ω)) z).im) ∧
      (∀ ω, Tendsto ((c ω).1 ∘ (ownHistoryChart U r ω).2.1) (𝓝[H] 0) (𝓝 0) ∧
        Tendsto (fun w : ℂ => ‖(c ω).1 (w + 1)‖) (𝓝[H] 0) atTop) := by
  dsimp only
  intro hmark hcurrent hrecord
  let D := historyComponent s q Y η (fun ω => e (N ω))
  obtain ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, hlimits⟩ :=
    exists_history_original_right_target_chart hrq hq hY hUc hU0 hUm hη hi hH hm
      he hN hb hprotected hmark hcurrent
  have hprops := historyComponent_properties hq.le hY
    (fun ω => (hη ω).2.1.mono Icc_subset_Ici_self) (fun ω => (hη ω).1) hm hN hb
  have hown := historyComponent_subset_own_dom (s := s) (Y := Y) hrq hUc hU0 hη hi hH
    (fun ω => e (N ω))
  have hO := fun ω => Chart.isConformal_loewnerChartAtTime (τ := fun _ => r) hUc hU0 ω
  have htarget : ∀ ω, ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D ω := fun ω =>
    exists_original_right_target_component_collar ((hη ω).2.1.mono Icc_subset_Ici_self)
      (hη ω).1 (hH ω) (hprotected ω) (hmark ω)
  have hDH : ∀ ω, (c ω).dom ≤ upperHalfPlaneOpens := by
    intro ω z hz
    exact (hprops.1 ω).2.2.2 (by rwa [← hdom ω])
  have hscale : ∀ ω, ∃ a x : ℝ, 0 < a ∧ EqOn (c ω).1
      (fun z => (a : ℂ) * (ConformalImage.mapOut (fillH (K ω)) (stripRightRetarget z) - x))
      (c ω).dom := by
    intro ω
    have hW := Chart.continuous_rpath_of_continuous (hUc ω)
    have hW0 := Chart.rpath_zero_of (hU0 ω)
    have hsc : IsSimplyConnected ((ownHistoryChart U r ω).dom : Set ℂ) := by
      rw [coe_dom_ownHistoryChart hUc hU0]
      exact (isHPHull_fwdHull hW r.coe_nonneg).2.2.2
    obtain ⟨a, x, ha, heq⟩ := exists_original_target_chart_scale
      (ownHistoryChart U r ω).dom.isOpen hsc (hO ω).dom_subset
      (hprops.1 ω).1 (hprops.1 ω).2.2.1 (hown ω) (hO ω).isConformalBijection
      (z₀ := η ω r) (by rw [hrq]; exact hH ω ⟨hq, le_rfl⟩)
      ((hη ω).tendsto_fwdMapInv_tip hW hW0 r.coe_nonneg)
      (hcurrent ω) (htarget ω) (hbij ω) (hlimits ω).1 (hlimits ω).2
    refine ⟨a, x, ha, ?_⟩
    rw [hrecord ω, hdom ω]
    exact heq
  have hK : ∀ ω, fillH (K ω) = stripTargetHull ((c ω).dom : Set ℂ) := by
    intro ω
    rw [hdom ω]
    exact hrecord ω
  have hNC : ∀ ω, e (N ω) ∈ (c ω).dom := by
    intro ω
    change e (N ω) ∈ ((c ω).dom : Set ℂ)
    rw [hdom ω]
    exact mem_connectedComponentIn (hb ω)
  have hLc : ∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (L z).im := by
    intro ω
    obtain ⟨L, hlog, hlift⟩ := hL ω
    refine ⟨L, by simpa only [hdom ω] using hlog, fun z hz => hlift z ?_⟩
    change z ∈ ((c ω).dom : Set ℂ) at hz
    rwa [hdom ω] at hz
  obtain ⟨n, hnm, hnphase, hnmeas, hncont⟩ :=
    exists_measurable_original_target_inherited_shift
      (fun ω => by rw [hdom ω]; exact (hprops.1 ω).2.1.isPreconnected)
      hDH hLc hdm hlm
      hKm hKc hKp hK hscale hN hNC
  refine ⟨fun ω => shiftLift (c ω) (n ω), fun ω => isConformal_shiftLift (hconf ω) _,
    hdom, hbij, hdm, hfm, hnmeas, hncont, ?_, hlimits⟩
  intro ω z hz
  apply hnphase ω z
  change z ∈ ((c ω).dom : Set ℂ)
  rwa [hdom ω]

end InteractingSLE.Sec5.Aux61Restart
