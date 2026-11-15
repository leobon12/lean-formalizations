/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoGateNoWrap
import Mathlib.Topology.Order.IntermediateValue

/-!
# Finite time intervals from no last counterflow contact

The no-last-contact property bounds each actual excursion component above.
Its endpoints are constructed as the infimum and supremum of that component,
using the standard connected-interval lemmas. No path detour is inferred from
boundedness of an excursion in time.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- Every time is followed by a contact with the counterflow hull. This is the
pathwise property in `Prop51I.FwdNoLastContactQOn`, with no angle assumption
silently attached to arbitrary deterministic curves. -/
def NoLastCounterflowContact (η : ℝ → ℂ) (w : ℝ → ℝ) (s : ℝ) : Prop :=
  ∀ t : ℝ, ∃ v : ℝ, t < v ∧ η v ∉ H \ cfHullQ w s

/-- No last contact rules out every unbounded time component. -/
theorem bddAbove_excursionComponent_of_noLastContact
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s t : ℝ}
    (hno : NoLastCounterflowContact η w s) (ht : t ∈ excursionTimes η w s) :
    BddAbove (connectedComponentIn (excursionTimes η w s) t) := by
  obtain ⟨v, htv, hv⟩ := hno t
  refine ⟨v, fun u hu => le_of_not_gt fun hvu => ?_⟩
  have hvC := isPreconnected_connectedComponentIn.Icc_subset
    (mem_connectedComponentIn ht) hu ⟨htv.le, hvu.le⟩
  exact hv (connectedComponentIn_subset _ _ hvC).2

/-- Conversely, finite excursion components exclude a last contact. Thus
there is no unrecorded regularity premise in the preceding conversion. -/
theorem noLastContact_of_bddAbove_excursionComponents
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}
    (hbd : ∀ t ∈ excursionTimes η w s,
      BddAbove (connectedComponentIn (excursionTimes η w s) t)) :
    NoLastCounterflowContact η w s := by
  intro t
  by_contra hn
  push Not at hn
  let a : ℝ := max 0 t
  have hsub : Ioi a ⊆ excursionTimes η w s := fun u hu =>
    ⟨(le_max_left 0 t).trans_lt hu, hn u ((le_max_right 0 t).trans_lt hu)⟩
  have ha : a + 1 ∈ Ioi a := by simp
  have hC : Ioi a ⊆ connectedComponentIn (excursionTimes η w s) (a + 1) :=
    isPreconnected_Ioi.subset_connectedComponentIn ha hsub
  obtain ⟨M, hM⟩ := hbd (a + 1) (hsub ha)
  have hm : max a M + 1 ∈ Ioi a := by
    change a < max a M + 1
    linarith [le_max_left a M]
  have := hM (hC hm)
  linarith [le_max_right a M]

/-- The exact maximal finite excursion interval through `t`. Starting at
zero is retained as a genuine case, rather than assuming every start positive. -/
structure BoundedExcursionInterval (η : ℝ → ℂ) (w : ℝ → ℝ) (s t : ℝ) where
  start : ℝ
  finish : ℝ
  start_nonneg : 0 ≤ start
  start_lt : start < t
  lt_finish : t < finish
  component_eq : connectedComponentIn (excursionTimes η w s) t = Ioo start finish
  start_outside : η start ∉ H \ cfHullQ w s
  finish_outside : η finish ∉ H \ cfHullQ w s

/-- An actual finite maximal excursion, including its two contact times.
The proof uses the component's connected interval, not an assumed first or
last contact time. -/
theorem exists_boundedExcursionInterval_of_bddAbove
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s t : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hs : 0 ≤ s)
    (ht : t ∈ excursionTimes η w s)
    (habove : BddAbove (connectedComponentIn (excursionTimes η w s) t)) :
    Nonempty (BoundedExcursionInterval η w s t) := by
  let C := connectedComponentIn (excursionTimes η w s) t
  have htC : t ∈ C := mem_connectedComponentIn ht
  have hCU : C ⊆ excursionTimes η w s := connectedComponentIn_subset _ _
  have hCo : IsOpen C := (isOpen_excursionTimes hη hw hs).connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 ht
  have hbelow : BddBelow C := ⟨0, fun _ hy => (hCU hy).1.le⟩
  have hstrict : ∀ y ∈ C, sInf C < y ∧ y < sSup C := by
    intro y hy
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hCo y hy
    have hminus : y - ε / 2 ∈ C := hb (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    have hplus : y + ε / 2 ∈ C := hb (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    exact ⟨(csInf_le hbelow hminus).trans_lt (by linarith),
      (show y < y + ε / 2 by linarith).trans_le (le_csSup habove hplus)⟩
  have hCeq : C = Ioo (sInf C) (sSup C) :=
    Subset.antisymm hstrict (hCc.Ioo_csInf_csSup_subset hbelow habove)
  have hend : ∀ e ∈ closure C, e ∉ C → e ∉ excursionTimes η w s := by
    intro e he hen heU
    have hinsert : IsPreconnected (insert e C) := hCc.isPreconnected.subset_closure
      (subset_insert e C) (insert_subset he subset_closure)
    have hsub : insert e C ⊆ C := hinsert.subset_connectedComponentIn
      (mem_insert_of_mem _ htC) (insert_subset heU hCU)
    exact hen (hsub (mem_insert e C))
  have hinf : sInf C ∉ excursionTimes η w s := hend (sInf C)
    (csInf_mem_closure ⟨t, htC⟩ hbelow)
    (fun h => (hstrict _ h).1.false)
  have hsup : sSup C ∉ excursionTimes η w s := hend (sSup C)
    (csSup_mem_closure ⟨t, htC⟩ habove)
    (fun h => (hstrict _ h).2.false)
  have h0 : 0 ≤ sInf C := le_csInf ⟨t, htC⟩ fun _ hy => (hCU hy).1.le
  refine ⟨⟨sInf C, sSup C, h0, (hstrict _ htC).1, (hstrict _ htC).2, hCeq,
    ?_, fun hD => hsup ⟨ht.1.trans (hstrict _ htC).2, hD⟩⟩⟩
  intro hD
  rcases h0.eq_or_lt with he | he
  · have hH := hD.1
    rw [← he, hη.zero] at hH
    exact ne_zero_of_mem_H hH rfl
  · exact hinf ⟨he, hD⟩

/-- No last contact supplies the boundedness needed by the interval constructor. -/
theorem exists_boundedExcursionInterval {η : ℝ → ℂ} {w : ℝ → ℝ} {s t : ℝ}
    (hη : IsProperArc η) (hw : Continuous w) (hs : 0 ≤ s)
    (hno : NoLastCounterflowContact η w s) (ht : t ∈ excursionTimes η w s) :
    Nonempty (BoundedExcursionInterval η w s t) :=
  exists_boundedExcursionInterval_of_bddAbove hη hw hs ht
    (bddAbove_excursionComponent_of_noLastContact hno ht)

/-- The interval represents the entire excursion, with its original physical
time direction. -/
theorem BoundedExcursionInterval.mapsTo {η : ℝ → ℂ} {w : ℝ → ℝ} {s t : ℝ}
    (e : BoundedExcursionInterval η w s t) :
    MapsTo η (Ioo e.start e.finish) (H \ cfHullQ w s) := by
  intro u hu
  rw [← e.component_eq] at hu
  exact (connectedComponentIn_subset _ _ hu).2

end InteractingSLE.Sec5.Prop51HTopo
