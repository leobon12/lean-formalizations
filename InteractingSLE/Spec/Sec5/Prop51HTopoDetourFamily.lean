/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourCrosscuts

/-!
# The finite crosscuts actually crossed by a gate path

For each crossed excursion bounded above in time, construct its full interval
and completed western crosscut. An unbounded component instead gives an actual
terminal excursion tail. No last contact excludes that second case.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- A completed western crosscut parametrizing exactly one time component.
The component identity prevents replacing an excursion by a smaller subarc. -/
structure WesternFiniteCrosscut (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) (C : Set ℝ) where
  start : ℝ
  finish : ℝ
  start_nonneg : 0 ≤ start
  start_lt_finish : start < finish
  times_eq : C = Ioo start finish
  in_domain : MapsTo η (Ioo start finish) (H \ cfHullQ w s)
  crosscut : FiniteExcursionCrosscut η w s start finish
  finish_neg : crosscut.finish < 0

/-- A bounded actual excursion component has all the asserted crosscut data. -/
theorem exists_westernFiniteCrosscut_of_bddAbove
    {η β : ℝ → ℂ} {w : ℝ → ℝ} {s t : ℝ}
    (hη : IsProperArc η) (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (htip : negInv (β s) ∉ arcRange η) (hends : HasWesternExcursionEnds η w s)
    (ht : t ∈ excursionTimes η w s)
    (hbd : BddAbove (connectedComponentIn (excursionTimes η w s) t)) :
    Nonempty (WesternFiniteCrosscut η w s
      (connectedComponentIn (excursionTimes η w s) t)) := by
  obtain ⟨e⟩ := exists_boundedExcursionInterval_of_bddAbove hη hw hs ht hbd
  obtain ⟨c⟩ := e.exists_crosscut hη hβ hw hw0 hs htip
  have hab := e.start_lt.trans e.lt_finish
  exact ⟨⟨e.start, e.finish, e.start_nonneg, hab, e.component_eq, e.mapsTo, c,
    c.finish_neg_of_western e.start_nonneg hab e.mapsTo e.finish_outside hends⟩⟩

/-- A path's visiting times belong to genuine positive-time excursions. -/
theorem GateExitPath.visiting_mem_excursionTimes
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {c : PositiveGateComponent η w s}
    (p : GateExitPath c) (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) {t : ℝ}
    (ht : t ∈ Ici 0 ∩ η ⁻¹' (revChartInv w s '' (p.curve '' Icc 0 1))) :
    t ∈ excursionTimes η w s := by
  obtain ⟨z, ⟨u, hu, rfl⟩, hz⟩ := ht.2
  have hD : η t ∈ H \ cfHullQ w s := hz ▸ revChartInv_mem hw hw0 hs (p.in_H hu)
  refine ⟨?_, hD⟩
  show 0 < t
  refine lt_of_le_of_ne ht.1 ?_
  intro he
  have hH := hD.1
  rw [← he, hη.zero] at hH
  exact ne_zero_of_mem_H hH rfl

/-- No last contact supplies a finite western crosscut for every crossed
excursion. These are constructed data, rather than a bypass hypothesis. -/
theorem GateExitPath.westernFiniteCrosscuts_of_noLastContact
    {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {c : PositiveGateComponent η w s}
    (p : GateExitPath c) (hη : IsProperArc η) (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (htip : negInv (β s) ∉ arcRange η) (hends : HasWesternExcursionEnds η w s)
    (hno : NoLastCounterflowContact η w s) :
    ∀ C ∈ p.crossed, Nonempty (WesternFiniteCrosscut η w s C) := by
  rintro C ⟨t, ht, rfl⟩
  have htU := p.visiting_mem_excursionTimes hη hw hw0 hs ht
  exact exists_westernFiniteCrosscut_of_bddAbove hη hβ hw hw0 hs htip hends htU
    (bddAbove_excursionComponent_of_noLastContact hno htU)

/-- An unbounded component contains every later time, so it is a terminal
excursion. Connectedness is enough; no last-exit existence is assumed. -/
theorem tail_mem_of_not_bddAbove_excursionComponent
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s t : ℝ} (ht : t ∈ excursionTimes η w s)
    (hbd : ¬ BddAbove (connectedComponentIn (excursionTimes η w s) t)) :
    ∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s := by
  intro v hv
  obtain ⟨u, hu, hvu⟩ := not_bddAbove_iff.1 hbd v
  exact (connectedComponentIn_subset _ _
    (isPreconnected_connectedComponentIn.Icc_subset (mem_connectedComponentIn ht)
      hu ⟨hv.le, hvu.le⟩)).2

/-- The exact alternative left by a finite crossed family: completed finite
crosscuts, or a crossed terminal component with its actual western limit.
The new no-last-contact theorem removes the terminal alternative on its regime. -/
theorem GateExitPath.finiteCrosscuts_or_terminal
    {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {c : PositiveGateComponent η w s}
    (p : GateExitPath c) (hη : IsProperArc η) (hβ : IsLoewnerTrace w β)
    (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (htip : negInv (β s) ∉ arcRange η) (hends : HasWesternExcursionEnds η w s) :
    (∀ C ∈ p.crossed, Nonempty (WesternFiniteCrosscut η w s C)) ∨
      ∃ t x : ℝ, 0 < t ∧ x < 0 ∧
        connectedComponentIn (excursionTimes η w s) t ∈ p.crossed ∧
        (∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s) ∧
        Tendsto (fun v => revChart w s (η v)) atTop (𝓝 (x : ℂ)) := by
  classical
  by_cases hbd : ∀ C ∈ p.crossed, BddAbove C
  · left
    rintro C ⟨t, ht, rfl⟩
    exact exists_westernFiniteCrosscut_of_bddAbove hη hβ hw hw0 hs htip hends
      (p.visiting_mem_excursionTimes hη hw hw0 hs ht) (hbd _ ⟨t, ht, rfl⟩)
  · push Not at hbd
    obtain ⟨C, hC, hbd⟩ := hbd
    obtain ⟨t, ht, rfl⟩ := hC
    have htU := p.visiting_mem_excursionTimes hη hw hw0 hs ht
    have htail := tail_mem_of_not_bddAbove_excursionComponent htU hbd
    obtain ⟨x, hx, hlim⟩ := hends.2 t htU.1.le htail
    exact Or.inr ⟨t, x, htU.1, hx, ⟨t, ht, rfl⟩, htail, hlim⟩

end InteractingSLE.Sec5.Prop51HTopo
